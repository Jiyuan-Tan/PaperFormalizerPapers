module
public import Papers.TbsNeuralCausalPi.Helpers.HilbertCurve
public import Papers.TbsNeuralCausalPi.Helpers.WideComponentErrors
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorMixing
/-! # Hölder first blocks for deep distribution generators -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

/-- For [a positive chart dimension](hyp:hq), [a probability law](hyp:mu),
[a homeomorphism from its unit cube onto a component](hyp:f), [a Lipschitz bound](hyp:L),
and [a volume domination constant](hyp:Cf), assume [the component is compact, has full
mass, and its chart has the given Lipschitz bound and positive volume domination constant](hyp:hdom)
and [coordinate approximation is available](hyp:hgate).
[There is a positive constant such that every depth of at least four admits a ReLU
network of width twelve times the chart dimension, mapping the unit interval into
the chart cube, whose generated law approximates the chart pullback law in Wasserstein
distance at most that constant times depth to the power minus two over the chart dimension](goal). -/
-- @node: exists_deep_relu_cube_generator
lemma exists_deep_relu_cube_generator {D q : ℕ} (hq : 0 < q)
    (mu : ProbabilityMeasure (L1Vec D)) {S : Set (L1Vec D)}
    (f : homeoClass (unitCube q) S) (L : ℝ≥0) (Cf : ℝ)
    (hdom : lowerBoundDominationAt (mu : Measure _) S f L Cf)
    (hgate : YarotskyCoordinateApprox) :
    ∃ A : ℝ, 0 < A ∧ ∀ depth : ℕ, 4 ≤ depth →
      ∃ Q : ReLUNet 1 q (12*q) depth,
        Set.MapsTo Q.eval (unitCube 1) (unitCube q) ∧
        wasserstein1 ((mu : Measure _).map (chartInverse f))
          ((uniformCubeLaw 1).map Q.eval) ≤
            ENNReal.ofReal (A * (depth : ℝ) ^ (-(2 : ℝ) / q)) := by
  classical
  obtain ⟨gamma, H, hcont, hmem, hlaw, hmod⟩ :=
    exists_component_network_input_curve hq mu f L Cf hdom
  obtain ⟨c, hc, happ⟩ := relu_deep_approx_holder hgate 1 rfl
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have halpha : 0 < 1 / (q : ℝ) := by positivity
  have halpha1 : 1 / (q : ℝ) ≤ 1 := (div_le_one (by positivity)).2 hqR
  refine ⟨1 + 4 * q * c * H, by positivity, ?_⟩
  intro depth hdepth
  have hrate : -(2 * (1 / (q : ℝ))) / (1 : ℕ) = -(2 : ℝ) / q := by
    push_cast
    ring
  have hscalar (j : Fin q) := happ (1 / q) H halpha halpha1 H.coe_nonneg
    (fun x => (gamma x).ofLp j) (fun x hx y hy => hmod x hx y hy j)
    (depth-2) (by omega)
  choose Q hQ using hscalar
  obtain ⟨R, hR⟩ := relu_parallel_stack Q
  obtain ⟨T, hT, hcube⟩ := relu_unitCube_clipping R
  have hwidth : max (q * (2*1+10)) q ≤ 12*q := by omega
  have hdepthEq : depth-2+2 = depth := by omega
  let U : ReLUNet 1 q (12*q) depth :=
    { T.widen hwidth with depth := T.depth.trans hdepthEq }
  have hU : U.eval = T.eval := rfl
  have herr (x : L1Vec 1) (hx : x ∈ unitCube 1) :
      ‖gamma x - U.eval x‖ ≤
        (q : ℝ) * c * H * ((depth-2 : ℕ) : ℝ) ^ (-(2 : ℝ) / q) := by
    rw [hU, hT, Function.comp_apply, norm_sub_rev]
    refine (coordinateClamp_norm_error 0 1 (R.eval x) (gamma x) (hmem hx)).trans ?_
    simp only [PiLp.norm_eq_of_L1, PiLp.sub_apply, Real.norm_eq_abs]
    calc
      _ ≤ ∑ _j : Fin q, c * H * ((depth-2 : ℕ) : ℝ) ^ (-(2 : ℝ) / q) := by
        apply Finset.sum_le_sum
        intro j _
        rw [hR]
        simpa only [hrate] using hQ j x hx
      _ = _ := by simp [mul_assoc]
  refine ⟨U, fun x _ => by rw [hU]; exact hcube x, ?_⟩
  let G := gamma ∘ coordinateClamp (d := 1) 0 1
  have hGcont : Continuous G := hcont.comp_continuous
    (coordinateClamp_lipschitz 0 1).continuous (coordinateClamp_mapsTo 0 1 zero_le_one)
  have hfix (x : L1Vec 1) (hx : x ∈ unitCube 1) : G x = gamma x := by
    dsimp [G]
    rw [coordinateClamp_fixes 0 1 x hx]
  let := uniformCubeLaw_probability 1
  have hae : ∀ᵐ x ∂uniformCubeLaw 1, x ∈ unitCube 1 :=
    (mem_ae_iff_prob_eq_one (unitCube_isCompact 1).measurableSet).2
      (uniformCubeLaw_cube_mass 1)
  have hGlaw : (uniformCubeLaw 1).map G = (mu : Measure _).map (chartInverse f) := by
    rw [← hlaw]
    exact Measure.map_congr (hae.mono hfix)
  rw [← hGlaw]
  refine (wasserstein_maps_le_common_cost (uniformCubeLaw 1) G U.eval
    hGcont.measurable U.eval_measurable).trans ?_
  calc
    _ ≤ ∫⁻ _x : L1Vec 1, ENNReal.ofReal
        ((q : ℝ) * c * H * ((depth-2 : ℕ) : ℝ) ^ (-(2 : ℝ) / q)) ∂uniformCubeLaw 1 := by
      apply lintegral_mono_ae
      filter_upwards [hae] with x hx
      rw [hfix x hx, edist_dist, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal (herr x hx)
    _ = ENNReal.ofReal ((q : ℝ) * c * H *
        ((depth-2 : ℕ) : ℝ) ^ (-(2 : ℝ) / q)) := by simp
    _ ≤ ENNReal.ofReal ((1 + 4 * q * c * H) * (depth : ℝ) ^ (-(2 : ℝ) / q)) := by
      apply ENNReal.ofReal_le_ofReal
      have hr := mul_le_mul_of_nonneg_left (wide_reserved_depth_rate_le hq hdepth)
        (by positivity : 0 ≤ (q : ℝ) * c * H)
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg depth) (-(2 : ℝ) / q)]

/-- Given [a probability law](hyp:P), [component sets](hyp:S), [their chart dimensions](hyp:dC),
and [a common Lipschitz bound](hyp:L), suppose [the sets are the finite support components](hyp:hsupp)
and [admit Lipschitz cube charts](hyp:hcharts). For [chosen cube charts](hyp:f) and
[domination constants](hyp:Cf), assume [each conditional law has full mass on its compact
component and dominates cube volume through its Lipschitz chart with a positive constant](hyp:hdom)
and [coordinate approximation is available](hyp:hgate); [there is a positive error constant
such that every depth at least four admits cube-valued first-block networks of common
width twelve times the maximum of one and the largest chart dimension, with every
positive-dimensional pullback-law Wasserstein error bounded by the constant times depth
to the power minus two divided by that same maximum](goal). -/
-- @node: exists_deep_relu_first_blocks
lemma exists_deep_relu_first_blocks {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (f : ∀ i, homeoClass (unitCube (dC i)) (S i)) (Cf : Fin N → ℝ)
    (hdom : ∀ i, lowerBoundDominationAt
      (ProbabilityTheory.cond (P : Measure _) (S i)) (S i) (f i) L (Cf i))
    (hgate : YarotskyCoordinateApprox) :
    ∃ A : ℝ, 0 < A ∧ ∀ depth : ℕ, 4 ≤ depth →
      ∃ Q : ∀ i, ReLUNet 1 (dC i) (12 * max 1 (Finset.univ.sup dC)) depth,
        (∀ i, Set.MapsTo (Q i).eval (unitCube 1) (unitCube (dC i))) ∧
        ∀ i, 0 < dC i → wasserstein1
          ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse (f i)))
          ((uniformCubeLaw 1).map (Q i).eval) ≤
            ENNReal.ofReal (A * (depth : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC))) := by
  classical
  let D := max 1 (Finset.univ.sup dC)
  have hdim (i : Fin N) : dC i ≤ D :=
    (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  have hcomponent (i : Fin N) : ∃ A : ℝ, 0 < A ∧
      ∀ depth : ℕ, 4 ≤ depth → ∃ Q : ReLUNet 1 (dC i) (12*D) depth,
        Set.MapsTo Q.eval (unitCube 1) (unitCube (dC i)) ∧
        (0 < dC i → wasserstein1
          ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse (f i)))
          ((uniformCubeLaw 1).map Q.eval) ≤
            ENNReal.ofReal (A * (depth : ℝ) ^ (-(2 : ℝ) / dC i))) := by
    by_cases hi : 0 < dC i
    · let mu : ProbabilityMeasure (L1Vec d) :=
        ⟨ProbabilityTheory.cond (P : Measure _) (S i),
          support_component_cond_probability P hsupp hcharts i⟩
      obtain ⟨A, hA, happ⟩ :=
        exists_deep_relu_cube_generator hi mu (f i) L (Cf i) (hdom i) hgate
      refine ⟨A, hA, ?_⟩
      intro depth hdepth
      obtain ⟨Q, hcube, herr⟩ := happ depth hdepth
      exact ⟨Q.widen (Nat.mul_le_mul_left 12 (hdim i)), hcube, fun _ => herr⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      intro depth hdepth
      refine ⟨zeroNet 1 (dC i) (12*D) depth, ?_, fun h => (hi h).elim⟩
      intro x hx j
      exact (hi (Nat.zero_lt_of_lt j.isLt)).elim
  choose A hA hQ using hcomponent
  let Amax : ℝ := 1 + ∑ i, A i
  have hAmax : 0 < Amax := by
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hA i).le)
    dsimp [Amax]
    linarith
  have hAle (i : Fin N) : A i ≤ Amax := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hA j).le)
      (Finset.mem_univ i)
    dsimp [Amax]
    linarith
  refine ⟨Amax, hAmax, ?_⟩
  intro depth hdepth
  choose Q hcube herr using fun i => hQ i depth hdepth
  refine ⟨Q, hcube, ?_⟩
  intro i hi
  refine (herr i hi).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul (hAle i)
    (wide_component_rate_le hi (hdim i)
      (by exact_mod_cast (show 1 ≤ depth by omega)) (by norm_num : (0 : ℝ) ≤ 2))
    (Real.rpow_nonneg (Nat.cast_nonneg depth) _) hAmax.le

end Papers.TbsNeuralCausalPi
