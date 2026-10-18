module
public import Papers.TbsNeuralCausalPi.Helpers.WideSecondBlocks
/-! # Transporting wide-generator component errors through the support charts -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

-- @node: uniformCubeLaw_cube_mass
/-- In every finite dimension, [the uniform cube law assigns mass one to the
unit cube](goal). -/
lemma uniformCubeLaw_cube_mass (d : ℕ) : (uniformCubeLaw d) (unitCube d) = 1 := by
  unfold uniformCubeLaw
  rw [Measure.map_apply (by fun_prop) (unitCube_isCompact d).measurableSet]
  have hpre : WithLp.toLp 1 ⁻¹' unitCube d =
      Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp [unitCube, Pi.le_def, forall_and]
  rw [hpre]
  rw [Measure.pi_pi]
  simp

/-- Suppose [a chart image is compact](hyp:hS), [the target probability law
gives it full mass](hyp:hmass), and [the chart has nonnegative Lipschitz bound L](hyp:L,hf).
If [the first ReLU block maps the scalar unit interval into the chart's cube](hyp:hcube),
[the chart image lies in a bounded box](hyp:hbox), [the second block always
outputs into that box](hyp:hbounded), and [its one-norm chart approximation error
is at most E throughout the cube](hyp:herror), then [the composed generator's
Wasserstein error is at most L times the first block's error for the inverse-chart
target law plus the nonnegative part of E](goal). -/
-- @node: wide_component_transport_le
lemma wide_component_transport_le {d q W1 L1 W2 L2 : ℕ}
    (mu : ProbabilityMeasure (L1Vec d)) {S : Set (L1Vec d)}
    (f : homeoClass (unitCube q) S) (hS : IsCompact S)
    (hmass : (mu : Measure _) S = 1) (L : ℝ≥0) (hf : LipschitzWith L f)
    (g1 : ReLUNet 1 q W1 L1) (g2 : ReLUNet q d W2 L2)
    (hcube : Set.MapsTo g1.eval (unitCube 1) (unitCube q))
    (K : ℝ) (hbox : S ⊆ boundedCube d K)
    (hbounded : ∀ x, g2.eval x ∈ boundedCube d K)
    (E : ℝ) (herror : ∀ x : unitCube q, ‖(f x).val-g2.eval x.val‖ ≤ E) :
    wasserstein1 (mu : Measure _) ((uniformCubeLaw 1).map (g2.eval ∘ g1.eval)) ≤
      (L : ℝ≥0∞) * wasserstein1 ((mu : Measure _).map (chartInverse f))
        ((uniformCubeLaw 1).map g1.eval) + ENNReal.ofReal E := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  let : BorelSpace (L1Vec q) := ⟨rfl⟩
  let : IsProbabilityMeasure (uniformCubeLaw 1) := uniformCubeLaw_probability 1
  let m := (mu : Measure _).map (chartInverse f)
  let nu := (uniformCubeLaw 1).map g1.eval
  have hm : Measurable (chartInverse f) := by fun_prop
  let : IsProbabilityMeasure m := Measure.isProbabilityMeasure_map hm.aemeasurable
  let : IsProbabilityMeasure nu := Measure.isProbabilityMeasure_map (by fun_prop)
  let c : L1Vec q → unitCube q := fun x =>
    ⟨coordinateClamp 0 1 x, coordinateClamp_mapsTo 0 1 zero_le_one x⟩
  let F : L1Vec q → L1Vec d := fun x => (f (c x)).val
  let Fhat : L1Vec q → L1Vec d := fun x => g2.eval (c x).val
  have hc : LipschitzWith 1 c := by
    intro x y
    exact (coordinateClamp_lipschitz 0 1).edist_le_mul x y
  have hF : LipschitzWith L F := by
    intro x y
    calc
      _ ≤ (L : ℝ≥0∞) * edist (c x) (c y) := hf _ _
      _ ≤ (L : ℝ≥0∞) * edist x y := by
        gcongr
        simpa only [ENNReal.coe_one, one_mul] using hc x y
  have hFhat : Measurable Fhat := by
    dsimp [Fhat, c]
    fun_prop
  have hmCube : m (unitCube q) = 1 := chartInverse_pullback_mass mu f hS hmass
  have hnCube : nu (unitCube q) = 1 := by
    rw [Measure.map_apply (by fun_prop) (unitCube_isCompact q).measurableSet]
    apply le_antisymm prob_le_one
    rw [← uniformCubeLaw_cube_mass 1]
    exact measure_mono hcube
  have ha : ∀ᵐ x ∂m, x ∈ unitCube q :=
    (mem_ae_iff_prob_eq_one (unitCube_isCompact q).measurableSet).2 hmCube
  have hb : ∀ᵐ x ∂nu, x ∈ unitCube q :=
    (mem_ae_iff_prob_eq_one (unitCube_isCompact q).measurableSet).2 hnCube
  have hmap : m.map F = (mu : Measure _) := by
    calc
      m.map F = m.map (chartForward f) := by
        apply Measure.map_congr
        filter_upwards [ha] with x hx
        have hcfix : c x = ⟨x, hx⟩ :=
          Subtype.ext (coordinateClamp_fixes 0 1 x hx)
        change (f (c x)).val = chartForward f x
        rw [hcfix]
        simp only [chartForward, dif_pos hx]
      _ = (mu : Measure _) := chartForward_map_pullback mu f hS hmass
  have hmaphat : nu.map Fhat = (uniformCubeLaw 1).map (g2.eval ∘ g1.eval) := by
    calc
      nu.map Fhat = nu.map g2.eval := by
        apply Measure.map_congr
        filter_upwards [hb] with x hx
        dsimp [Fhat, c]
        rw [coordinateClamp_fixes 0 1 x hx]
      _ = _ := Measure.map_map (by fun_prop) (by fun_prop)
  have he (x : L1Vec q) : edist (F x) (Fhat x) ≤ ENNReal.ofReal E := by
    rw [edist_dist, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (herror (c x))
  have h := PushForward.map_le_of_compact_range m nu F Fhat
    hF.continuous.measurable hFhat L hF (ENNReal.ofReal E) he
    (boundedCube d K) (boundedCube_isCompact d K)
    (fun x => hbox (f (c x)).property) (fun x => hbounded _)
  rw [hmap, hmaphat] at h
  exact h

/-- On a metric space with at most one point, [the Wasserstein distance between
any two probability laws is zero](goal). -/
-- @node: wasserstein_subsingleton_eq_zero
lemma wasserstein_subsingleton_eq_zero {X : Type*} [MeasurableSpace X]
    [MetricSpace X] [BorelSpace X] [Subsingleton X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    wasserstein1 mu nu = 0 := by
  apply le_antisymm _ bot_le
  have hp : mu.prod nu ∈ couplings mu nu := by
    refine ⟨inferInstance, ?_, ?_⟩ <;> simp
  rw [wasserstein1_eq_couplings]
  refine iInf_le_of_le ⟨mu.prod nu, hp⟩ ?_
  have he : (fun z : X × X => edist z.1 z.2) = fun _ => (0 : ℝ≥0∞) := by
    funext z
    rw [Subsingleton.elim z.1 z.2, edist_self]
  rw [he, lintegral_zero]
  exact le_rfl

/-- If [a set is compact](hyp:hS) and [a probability law assigns it full mass](hyp:hmass),
[the norm is integrable under that law, so its first moment is finite](goal). -/
-- @node: integrable_norm_of_compact_mass
lemma integrable_norm_of_compact_mass {d : ℕ} (mu : Measure (L1Vec d))
    [IsProbabilityMeasure mu] {S : Set (L1Vec d)} (hS : IsCompact S)
    (hmass : mu S = 1) : Integrable (fun x => ‖x‖) mu := by
  have hi := continuous_norm.continuousOn.integrableOn_compact (μ := mu) hS
  have ha : ∀ᵐ x ∂mu, x ∈ S := (mem_ae_iff_prob_eq_one hS.measurableSet).2 hmass
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi

/-- For a probability law [supported on finitely many components](hyp:hsupp)
with [cube charts sharing a nonnegative Lipschitz bound L](hyp:L,hcharts), take
[a homeomorphic chart for each component](hyp:f) [with Lipschitz constant at most L](hyp:hf).
Suppose [each first generator block stays in its cube](hyp:hcube), [all chart
images lie in a common bounded box](hyp:hbox), and [all second-block outputs
lie in that box](hyp:hbounded). If [the first error constant A1 is nonnegative](hyp:hA1),
[the second error constant A2 is nonnegative](hyp:hA2), [positive-dimensional
components have inverse-chart Wasserstein error at most A1 times first-block
width to the power minus one over the maximum of one and the largest chart
dimension](hyp:hfirst), and [second-block chart error is at most A2 times its
depth to the power minus two over that same dimension, or zero when all chart
dimensions vanish](hyp:hsecond), then [every composed component has Wasserstein
error at most L times A1 plus A2, multiplied by the sum of those width and depth
rates, with zero error when all chart dimensions vanish](goal). -/
-- @node: wide_generator_component_errors_le
lemma wide_generator_component_errors_le {d N W1 L1 W2 L2 : ℕ}
    {dC : Fin N → ℕ} {tau : ℝ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (L : ℝ≥0) (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (f : ∀ i, homeoClass (unitCube (dC i)) (S i))
    (hf : ∀ i, LipschitzWith L (f i))
    (Q : ThreePartGenerator N d dC W1 L1 W2 L2 tau)
    (hcube : ∀ i, Set.MapsTo (Q.g1 i).eval (unitCube 1) (unitCube (dC i)))
    (K : ℝ) (hbox : ∀ i, S i ⊆ boundedCube d K)
    (hbounded : ∀ i x, (Q.g2 i).eval x ∈ boundedCube d K)
    (A1 A2 : ℝ) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hfirst : ∀ i, 0 < dC i → wasserstein1
      ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse (f i)))
      ((uniformCubeLaw 1).map (Q.g1 i).eval) ≤
        ENNReal.ofReal (A1 * (W1 : ℝ) ^ (-(1 : ℝ) / max 1 (Finset.univ.sup dC))))
    (hsecond : ∀ i, ∀ x : unitCube (dC i), ‖((f i) x).val-(Q.g2 i).eval x.val‖ ≤
      if 0 < Finset.univ.sup dC then
        A2 * (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0) :
    ∀ i, wasserstein1 (ProbabilityTheory.cond (P : Measure _) (S i))
      ((uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)) ≤
      ENNReal.ofReal (((L : ℝ) * A1 + A2) *
        (if 0 < Finset.univ.sup dC then
          (W1 : ℝ) ^ (-(1 : ℝ) / max 1 (Finset.univ.sup dC)) +
          (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0)) := by
  intro i
  let mu : ProbabilityMeasure (L1Vec d) :=
    ⟨ProbabilityTheory.cond (P : Measure _) (S i),
      support_component_cond_probability P hsupp hcharts i⟩
  have hm : (mu : Measure _) (S i) = 1 :=
    ProbabilityTheory.cond_apply_self
      (ne_of_gt (support_component_mass_pos P hsupp hcharts i)) (measure_ne_top _ _)
  have ht := wide_component_transport_le mu (f i) (component_isCompact hcharts i)
    hm L (hf i) (Q.g1 i) (Q.g2 i) (hcube i) K (hbox i) (hbounded i)
    _ (hsecond i)
  have hinput : wasserstein1 ((mu : Measure _).map (chartInverse (f i)))
      ((uniformCubeLaw 1).map (Q.g1 i).eval) ≤
      ENNReal.ofReal (if 0 < Finset.univ.sup dC then
        A1 * (W1 : ℝ) ^ (-(1 : ℝ) / max 1 (Finset.univ.sup dC)) else 0) := by
    by_cases hi : 0 < dC i
    · have hsup : 0 < Finset.univ.sup dC :=
        hi.trans_le (Finset.le_sup (Finset.mem_univ i))
      rw [if_pos hsup]
      exact hfirst i hi
    · have hzero : dC i = 0 := by omega
      let : Subsingleton (L1Vec (dC i)) := hzero ▸ inferInstanceAs (Subsingleton (L1Vec 0))
      let : IsProbabilityMeasure (uniformCubeLaw 1) := uniformCubeLaw_probability 1
      let : IsProbabilityMeasure ((mu : Measure _).map (chartInverse (f i))) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      let : IsProbabilityMeasure ((uniformCubeLaw 1).map (Q.g1 i).eval) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      rw [wasserstein_subsingleton_eq_zero]
      exact bot_le
  have hmul := mul_le_mul_right hinput (L : ℝ≥0∞)
  refine ht.trans ((add_le_add hmul le_rfl).trans ?_)
  by_cases hsup : 0 < Finset.univ.sup dC
  · simp only [if_pos hsup]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul L.coe_nonneg,
      ← ENNReal.ofReal_add (mul_nonneg L.coe_nonneg
        (mul_nonneg hA1 (Real.rpow_nonneg (Nat.cast_nonneg W1) _)))
        (mul_nonneg hA2 (Real.rpow_nonneg (Nat.cast_nonneg L2) _))]
    apply ENNReal.ofReal_le_ofReal
    have hcross1 := mul_nonneg (mul_nonneg L.coe_nonneg hA1)
      (Real.rpow_nonneg (Nat.cast_nonneg L2) (-(2 : ℝ) / max 1 (Finset.univ.sup dC)))
    have hcross2 := mul_nonneg hA2
      (Real.rpow_nonneg (Nat.cast_nonneg W1) (-(1 : ℝ) / max 1 (Finset.univ.sup dC)))
    nlinarith only [hcross1, hcross2]
  · simp [hsup]

/-- For a probability law [supported on finitely many components](hyp:hsupp)
with [Lipschitz homeomorphic cube charts](hyp:hcharts), suppose [the generator's
mixture weights equal the true component masses](hyp:hp) and [every second-block
output lies in a common bounded box](hyp:hbounded). Given [a common extended
nonnegative error bound E](hyp:E) such that [each composed component generator
is within E of its conditional target law in Wasserstein distance](hyp:herror),
[the mixture of the composed generators is within E of the full target law](goal). -/
-- @node: wide_generator_mixture_error_le
lemma wide_generator_mixture_error_le {d N W1 L1 W2 L2 : ℕ}
    {dC : Fin N → ℕ} {tau : ℝ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    {L : ℝ≥0} (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (Q : ThreePartGenerator N d dC W1 L1 W2 L2 tau)
    (hp : ∀ i, Q.p i = ((P : Measure _) (S i)).toReal)
    (K : ℝ) (hbounded : ∀ i x, (Q.g2 i).eval x ∈ boundedCube d K)
    (E : ℝ≥0∞) (herror : ∀ i, wasserstein1
      (ProbabilityTheory.cond (P : Measure _) (S i))
      ((uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)) ≤ E) :
    wasserstein1 (P : Measure _) (∑ i, ENNReal.ofReal (Q.p i) •
      (uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)) ≤ E := by
  classical
  let : IsProbabilityMeasure (uniformCubeLaw 1) := uniformCubeLaw_probability 1
  let mu := fun i => ProbabilityTheory.cond (P : Measure _) (S i)
  let nu := fun i => (uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)
  have hm (i) : IsProbabilityMeasure (mu i) :=
    support_component_cond_probability P hsupp hcharts i
  have hn (i) : IsProbabilityMeasure (nu i) := Measure.isProbabilityMeasure_map (by fun_prop)
  have hmom : ComponentsFiniteFirstMoment mu nu := by
    intro i
    let := hm i
    let := hn i
    constructor
    · apply integrable_norm_of_compact_mass _ (component_isCompact hcharts i)
      exact ProbabilityTheory.cond_apply_self
        (ne_of_gt (support_component_mass_pos P hsupp hcharts i)) (measure_ne_top _ _)
    · apply integrable_norm_of_compact_mass _ (boundedCube_isCompact d K)
      rw [Measure.map_apply (by fun_prop) (boundedCube_isCompact d K).measurableSet]
      have heq : ((Q.g2 i).eval ∘ (Q.g1 i).eval) ⁻¹' boundedCube d K = Set.univ :=
        Set.eq_univ_of_forall (fun x => hbounded i _)
      rw [heq, measure_univ]
  have hN : 1 ≤ N := by
    by_contra h
    have hz : N = 0 := by omega
    subst N
    have hw := Q.weights.2
    simp at hw
  have hmix := wasserstein_mixture_le hN Q.p mu nu Q.weights hmom
    (fun i => ⟨hm i, hn i⟩)
  have heq : (P : Measure _) = ∑ i, ENNReal.ofReal (Q.p i) • mu i := by
    simp_rw [hp]
    exact support_components_cond_mixture P hsupp hcharts
  rw [← heq] at hmix
  have hw : ∑ i, ENNReal.ofReal (Q.p i) = 1 := by
    simp_rw [hp, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact support_component_masses_sum P hsupp hcharts
  refine hmix.trans ?_
  calc
    ∑ i, ENNReal.ofReal (Q.p i) * wasserstein1 (mu i) (nu i) ≤
        ∑ i, ENNReal.ofReal (Q.p i) * E := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact herror i
    _ = E := by rw [← Finset.sum_mul, hw, one_mul]

/-- For a probability law [supported on finitely many components](hyp:hsupp)
with [cube charts sharing a nonnegative Lipschitz bound L](hyp:L,hcharts),
assume [the Perekrestenko quantized generation result](hyp:hPerekrestenko_of_gate)
and [the Yarotsky coordinate approximation result](hyp:hYarotskyCoordinate_of_gate).
Then [there exist positive integer architecture factors, positive error and box
constants, and a common budget threshold at least four such that every larger
first-block width and second-block depth, and every positive gating parameter,
admit a three-part generator with the true component weights, first blocks
staying in their cubes, bounded second-block outputs, and exact support membership
for zero-dimensional components; the mixture of its first two blocks has
Wasserstein error at most the error constant times the sum of width to the power
minus one over the maximum chart dimension and depth to the power minus two over
that dimension, with zero error when all chart dimensions vanish](goal).

The dimension in the two rates is bounded below by one. The first-block depth
is the first architecture factor times that dimension; the second-block width
is the second architecture factor times the ambient dimension times that dimension. -/
-- @node: exists_wide_relu_generator_mixture_bound
lemma exists_wide_relu_generator_mixture_bound {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧ ∃ A K : ℝ, 0 < A ∧ 0 < K ∧
      ∃ B : ℕ, 4 ≤ B ∧ ∀ W1 L2 : ℕ, B ≤ W1 → B ≤ L2 →
        ∀ tau : ℝ, 0 < tau →
          ∃ Q : ThreePartGenerator N d dC W1 (c1 * max 1 (Finset.univ.sup dC))
              (c2 * d * max 1 (Finset.univ.sup dC)) L2 tau,
            (∀ i, Q.p i = ((P : Measure _) (S i)).toReal) ∧
            (∀ i, Set.MapsTo (Q.g1 i).eval (unitCube 1) (unitCube (dC i))) ∧
            (∀ i x, (Q.g2 i).eval x ∈ boundedCube d K) ∧
            (∀ i, dC i = 0 → Set.MapsTo (Q.g2 i).eval (unitCube (dC i)) (S i)) ∧
            wasserstein1 (P : Measure _) (∑ i, ENNReal.ofReal (Q.p i) •
              (uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)) ≤
              ENNReal.ofReal (A * (if 0 < Finset.univ.sup dC then
                (W1 : ℝ) ^ (-(1 : ℝ) / max 1 (Finset.univ.sup dC)) +
                (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0)) := by
  obtain ⟨f, hf, c1, c2, hc1, hc2, A1, A2, K, hA1, hA2, hK, hbox, B, hB, hblocks⟩ :=
    exists_wide_relu_generator_blocks P S dC L hsupp hcharts
      hPerekrestenko_of_gate hYarotskyCoordinate_of_gate
  refine ⟨c1, c2, hc1, hc2, (L : ℝ) * A1 + A2, K,
    by positivity, hK, B, hB, ?_⟩
  intro W1 L2 hW hL tau htau
  obtain ⟨Q, hp, hcube, hbounded, hzero, hfirst, hsecond⟩ := hblocks W1 L2 hW hL tau htau
  refine ⟨Q, hp, hcube, hbounded, hzero, ?_⟩
  exact wide_generator_mixture_error_le P S hsupp hcharts Q hp K hbounded _
    (wide_generator_component_errors_le P S L hsupp hcharts f hf Q hcube K hbox hbounded
      A1 A2 hA1.le hA2.le hfirst hsecond)

end Papers.TbsNeuralCausalPi
