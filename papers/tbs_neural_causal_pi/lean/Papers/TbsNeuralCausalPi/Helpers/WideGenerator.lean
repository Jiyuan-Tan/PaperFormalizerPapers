module
public import Papers.TbsNeuralCausalPi.Setup.Networks
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.NetworkClipping
public import Papers.TbsNeuralCausalPi.Helpers.WideQuantization
public import Papers.TbsNeuralCausalPi.Helpers.WideGeneratorSupport
/-! # Scalar-input wide generators for cube-supported laws
The cited component approximation is clipped and padded in the paper one-norm.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

/-- Assuming [the Perekrestenko quantized generation result](hyp:hPerekrestenko_of_gate),
[there is a universal positive integer depth multiplier such that, for every
probability law supported on finitely many Lipschitz cube charts and every
positive-dimensional component with a Lipschitz chart, positive error constants
and a width threshold can be chosen so that every larger width admits a
scalar-input ReLU generator staying in the component's unit cube, with depth
equal to the multiplier times its dimension and Wasserstein error for the
inverse-chart conditional law bounded by a constant times width to the power
minus one over that dimension](goal). -/
-- @node: exists_wide_relu_cube_generator_uniform_depth
lemma exists_wide_relu_cube_generator_uniform_depth
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration) :
    ∃ c : ℕ, 0 < c ∧ ∀ {d N : ℕ}
      (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
      (dC : Fin N → ℕ) (L : ℝ≥0),
      SupportFiniteComponents (P : Measure _) S →
      ComponentsLipschitzHomeomorphic S dC L →
      ∀ (i : Fin N), 0 < dC i →
      ∀ (f : homeoClass (unitCube (dC i)) (S i)), LipschitzWith L f →
      ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, 1 ≤ B ∧
        ∀ W : ℕ, B ≤ W → ∃ q : ReLUNet 1 (dC i) W (c * dC i),
          Set.MapsTo q.eval (unitCube 1) (unitCube (dC i)) ∧
          wasserstein1 ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse f))
            ((uniformCubeLaw 1).map q.eval) ≤
              ENNReal.ofReal (A * (W : ℝ) ^ (-(1 : ℝ) / dC i)) := by
  obtain ⟨c, hc, hgate⟩ := hPerekrestenko_of_gate
  refine ⟨c+2, by omega, ?_⟩
  intro d N P S dC L hsupp hcharts i hk f hf
  obtain ⟨A, hA, hgate⟩ := hgate (dC i) hk
  obtain ⟨E, hE, hbudget⟩ := hgate d N P S dC L hsupp hcharts i rfl f hf
  let B := max 1 (max (dC i) ⌈A * (2 : ℝ) ^ (dC i)⌉₊)
  refine ⟨E, hE, B, le_max_left _ _, ?_⟩
  intro W hW
  have hdim : dC i ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hceil : ⌈A * (2 : ℝ) ^ (dC i)⌉₊ ≤ W :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hthreshold : A * (2 : ℝ) ^ (dC i) ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  obtain ⟨hn, hwidth, Phi, hhidden, hquantized, herror⟩ := hbudget W hthreshold
  obtain ⟨Q, hQ, hcube⟩ := relu_unitCube_clipping Phi
  have hdepth : c * dC i + 2 ≤ (c+2) * dC i := by
    rw [Nat.add_mul]
    have : 2 ≤ 2 * dC i := by omega
    omega
  obtain ⟨R, hR⟩ := relu_pad_depth
    (Q.widen (max_le le_rfl hdim)) (by omega) hdepth
  refine ⟨R, ?_, ?_⟩
  · intro x hx
    rw [hR, ReLUNet.widen_eval]
    exact hcube x
  · have hcompact := component_isCompact hcharts i
    have hinv : Measurable (chartInverse f) := by fun_prop
    letI := support_component_cond_probability P hsupp hcharts i
    letI : IsProbabilityMeasure
        ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse f)) :=
      Measure.isProbabilityMeasure_map hinv.aemeasurable
    letI := uniformCubeLaw_probability 1
    letI : IsProbabilityMeasure ((uniformCubeLaw 1).map Phi.eval) :=
      Measure.isProbabilityMeasure_map Phi.eval_measurable.aemeasurable
    have hcontract := wasserstein_coordinateClamp_le
      ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse f))
      ((uniformCubeLaw 1).map Phi.eval)
    have hclamp : Measurable (coordinateClamp (d := dC i) 0 1) := by fun_prop
    rw [Measure.map_map hclamp hinv, coordinateClamp_chartInverse,
      Measure.map_map hclamp Phi.eval_measurable] at hcontract
    rw [hR, ReLUNet.widen_eval, hQ]
    exact hcontract.trans herror

/-- For a probability law [supported on finitely many components](hyp:hsupp)
with [cube charts sharing a nonnegative Lipschitz bound L](hyp:L,hcharts),
choose [a positive-dimensional component](hyp:hk) and a chart [whose Lipschitz
constant is at most L](hyp:hf). Assuming [the Perekrestenko quantized generation
result](hyp:hPerekrestenko_of_gate), [there exist a positive integer depth
multiplier, a positive error constant, and a width threshold at least one such
that every larger width admits a scalar-input ReLU generator staying in the
component's unit cube, with depth proportional to its dimension and Wasserstein
error for the inverse-chart conditional law bounded by the error constant times
width to the power minus one over that dimension](goal). -/
-- @node: exists_wide_relu_cube_generator
lemma exists_wide_relu_cube_generator {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (i : Fin N) (hk : 0 < dC i)
    (f : homeoClass (unitCube (dC i)) (S i)) (hf : LipschitzWith L f)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration) :
    ∃ c : ℕ, 0 < c ∧ ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, 1 ≤ B ∧
      ∀ W : ℕ, B ≤ W → ∃ q : ReLUNet 1 (dC i) W (c * dC i),
        Set.MapsTo q.eval (unitCube 1) (unitCube (dC i)) ∧
        wasserstein1 ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse f))
          ((uniformCubeLaw 1).map q.eval) ≤
            ENNReal.ofReal (A * (W : ℝ) ^ (-(1 : ℝ) / dC i)) := by
  obtain ⟨c, hc, h⟩ := exists_wide_relu_cube_generator_uniform_depth hPerekrestenko_of_gate
  exact ⟨c, hc, h P S dC L hsupp hcharts i hk f hf⟩

/-- For a probability law [supported on finitely many components](hyp:hsupp)
with [cube charts sharing a nonnegative Lipschitz bound L](hyp:L,hcharts),
take [one homeomorphic cube chart for each component](hyp:f) with [Lipschitz
constant at most L](hyp:hf). Assuming [the Perekrestenko quantized generation
result](hyp:hPerekrestenko_of_gate), [there exist a positive integer depth
multiplier, a positive error constant, and a common width threshold at least one
such that every larger width admits first-block ReLU generators of that width
and common depth equal to the multiplier times the maximum of one and the
largest component dimension; each stays in its cube, and every positive-dimensional
component has inverse-chart Wasserstein error bounded by the error constant
times width to the power minus one over that maximum dimension](goal). -/
-- @node: exists_wide_relu_first_blocks
lemma exists_wide_relu_first_blocks {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (f : ∀ i, homeoClass (unitCube (dC i)) (S i))
    (hf : ∀ i, LipschitzWith L (f i))
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration) :
    ∃ c : ℕ, 0 < c ∧ ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, 1 ≤ B ∧
      ∀ W : ℕ, B ≤ W →
        ∃ q : ∀ i, ReLUNet 1 (dC i) W (c * max 1 (Finset.univ.sup dC)),
          (∀ i, Set.MapsTo (q i).eval (unitCube 1) (unitCube (dC i))) ∧
          ∀ i, 0 < dC i →
            wasserstein1
              ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse (f i)))
              ((uniformCubeLaw 1).map (q i).eval) ≤
                ENNReal.ofReal (A * (W : ℝ) ^ (-(1 : ℝ) / max 1 (Finset.univ.sup dC))) := by
  classical
  obtain ⟨c, hc, h⟩ := exists_wide_relu_cube_generator_uniform_depth hPerekrestenko_of_gate
  let D := max 1 (Finset.univ.sup dC)
  have hdim (i : Fin N) : dC i ≤ D :=
    (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  have hcomponent (i : Fin N) :
      ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, 1 ≤ B ∧ ∀ W : ℕ, B ≤ W →
        ∃ q : ReLUNet 1 (dC i) W (c * D),
          Set.MapsTo q.eval (unitCube 1) (unitCube (dC i)) ∧
          ∀ _hk : 0 < dC i,
            wasserstein1
              ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse (f i)))
              ((uniformCubeLaw 1).map q.eval) ≤
                ENNReal.ofReal (A * (W : ℝ) ^ (-(1 : ℝ) / dC i)) := by
    by_cases hk : 0 < dC i
    · obtain ⟨A, hA, B, hB, hq⟩ := h P S dC L hsupp hcharts i hk (f i) (hf i)
      refine ⟨A, hA, B, hB, ?_⟩
      intro W hW
      obtain ⟨q, hcube, herr⟩ := hq W hW
      obtain ⟨Q, hQ⟩ := relu_pad_depth q (Nat.mul_pos hc hk)
        (Nat.mul_le_mul_left c (hdim i))
      refine ⟨Q, ?_, ?_⟩
      · simpa only [hQ] using hcube
      · intro _
        simpa only [hQ] using herr
    · refine ⟨1, zero_lt_one, 1, le_rfl, ?_⟩
      intro W hW
      refine ⟨zeroNet 1 (dC i) W (c * D), ?_, ?_⟩
      · intro x hx j
        exact (hk (Nat.zero_lt_of_lt j.isLt)).elim
      · intro hpos
        exact (hk hpos).elim
  choose A hA B hB hq using hcomponent
  let Amax : ℝ := 1 + ∑ i, A i
  let Bmax : ℕ := 1 + ∑ i, B i
  have hAmax : 0 < Amax := by
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hA i).le)
    dsimp [Amax]
    linarith
  have hAle (i : Fin N) : A i ≤ Amax := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hA j).le)
      (Finset.mem_univ i)
    dsimp [Amax]
    linarith
  have hBle (i : Fin N) : B i ≤ Bmax := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (B j))
      (Finset.mem_univ i)
    dsimp [Bmax]
    omega
  refine ⟨c, hc, Amax, hAmax, Bmax, by dsimp [Bmax]; omega, ?_⟩
  intro W hW
  choose q hcube herr using fun i => hq i W ((hBle i).trans hW)
  refine ⟨q, hcube, ?_⟩
  intro i hk
  have hWreal : (1 : ℝ) ≤ W := by
    have : 1 ≤ W := (hB i).trans ((hBle i).trans hW)
    exact_mod_cast this
  refine (herr i hk).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul (hAle i)
    (wide_component_rate_le hk (hdim i) hWreal (by norm_num : (0 : ℝ) ≤ 1))
    (Real.rpow_nonneg (Nat.cast_nonneg W) _) hAmax.le

end Papers.TbsNeuralCausalPi
