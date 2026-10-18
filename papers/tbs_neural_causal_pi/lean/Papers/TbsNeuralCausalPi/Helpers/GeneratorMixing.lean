module
public import Papers.TbsNeuralCausalPi.Helpers.GumbelSoftmax
public import Papers.TbsNeuralCausalPi.Helpers.WideGeneratorSupport
/-! # Transport cost of bounded generator mixing -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
set_option linter.unusedVariables false
open scoped ENNReal

-- @node: norm_le_of_mem_boundedCube
/-- If [a d-dimensional vector lies in the coordinate cube of radius K](hyp:hv),
[its sum-of-absolute-values norm is at most d times K](goal). -/
lemma norm_le_of_mem_boundedCube {d : ℕ} {K : ℝ} {v : L1Vec d}
    (hv : v ∈ boundedCube d K) : ‖v‖ ≤ d * K := by
  rw [PiLp.norm_eq_sum (p := 1) (by norm_num)]
  simpa [Real.norm_eq_abs] using
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hv j)

-- @node: bounded_mix_dist_le
/-- If [K is nonnegative](hyp:hK) and [every d-dimensional component vector lies
in the coordinate cube of radius K](hyp:hV), [the distance between two weighted
sums of these vectors, measured in the sum-of-absolute-values norm, is at most
d times K times the corresponding distance between their weight vectors](goal). -/
lemma bounded_mix_dist_le {n d : ℕ} (V : Fin n → L1Vec d)
    (K : ℝ) (hK : 0 ≤ K) (hV : ∀ i, V i ∈ boundedCube d K)
    (a b : L1Vec n) :
    dist (∑ i, a.ofLp i • V i) (∑ i, b.ofLp i • V i) ≤
      (d * K) * dist a b := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  calc
    ‖∑ i, (a.ofLp i - b.ofLp i) • V i‖ ≤
        ∑ i, ‖(a.ofLp i - b.ofLp i) • V i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |a.ofLp i - b.ofLp i| * (d * K) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_of_mem_boundedCube (hV i)) (abs_nonneg _)
    _ = (d * K) * dist a b := by
      rw [PiLp.dist_eq_sum (p := 1) (by norm_num)]
      simp only [ENNReal.toReal_one, Real.rpow_one, div_one, Real.dist_eq]
      rw [← Finset.sum_mul, mul_comm]

-- @node: wasserstein_maps_le_common_cost
/-- If [the first output map is measurable](hyp:hf) and [the second output map
is measurable](hyp:hg), [the Wasserstein-1 distance between their laws under a
common probability input is at most the expected extended distance between
their outputs evaluated at that same input](goal). -/
lemma wasserstein_maps_le_common_cost {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (mu : Measure Ω) [IsProbabilityMeasure mu]
    (f g : Ω → L1Vec d) (hf : Measurable f) (hg : Measurable g) :
    wasserstein1 (mu.map f) (mu.map g) ≤ ∫⁻ z, edist (f z) (g z) ∂mu := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  let pair := fun z => (f z, g z)
  have hp : Measurable pair := hf.prodMk hg
  have hc : mu.map pair ∈ couplings (mu.map f) (mu.map g) := by
    refine ⟨Measure.isProbabilityMeasure_map hp.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hp]
      rfl
    · rw [Measure.map_map measurable_snd hp]
      rfl
  calc
    _ ≤ ∫⁻ z, edist z.1 z.2 ∂mu.map pair :=
      (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
    _ = _ := by rw [lintegral_map (by fun_prop) hp]

-- @node: bounded_mix_edist_le
/-- If [K is nonnegative](hyp:hK) and [every d-dimensional component vector lies
in the coordinate cube of radius K](hyp:hV), [the extended distance between two
weighted sums of these vectors is at most d times K times the extended distance
between their weight vectors](goal). -/
lemma bounded_mix_edist_le {n d : ℕ} (V : Fin n → L1Vec d)
    (K : ℝ) (hK : 0 ≤ K) (hV : ∀ i, V i ∈ boundedCube d K)
    (a b : L1Vec n) :
    edist (∑ i, a.ofLp i • V i) (∑ i, b.ofLp i • V i) ≤
      ENNReal.ofReal (d * K) * edist a b := by
  simp only [edist_dist]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg d) hK)]
  exact ENNReal.ofReal_le_ofReal (bounded_mix_dist_le V K hK hV a b)

-- @node: bounded_random_mix_wasserstein_le
/-- Suppose [each random component vector is measurable](hyp:hV), [K is
nonnegative](hyp:hK), [all component vectors lie in the d-dimensional coordinate
cube of radius K at every input](hyp:hbox), [the first random weight vector is
measurable](hyp:ha), and [the second random weight vector is measurable](hyp:hb).
With component randomness
independent of the common weight input, [the Wasserstein-1 distance between the
two weighted-output laws is at most d times K times the expected extended
distance between the weight vectors at that common input](goal). -/
lemma bounded_random_mix_wasserstein_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {n d : ℕ}
    (mu : Measure Ω) (nu : Measure Ξ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (V : Ω → Fin n → L1Vec d) (hV : ∀ i, Measurable (fun x => V x i))
    (K : ℝ) (hK : 0 ≤ K) (hbox : ∀ x i, V x i ∈ boundedCube d K)
    (a b : Ξ → L1Vec n) (ha : Measurable a) (hb : Measurable b) :
    wasserstein1
      ((mu.prod nu).map (fun z => ∑ i, (a z.2).ofLp i • V z.1 i))
      ((mu.prod nu).map (fun z => ∑ i, (b z.2).ofLp i • V z.1 i)) ≤
      ENNReal.ofReal (d * K) * ∫⁻ y, edist (a y) (b y) ∂nu := by
  let : BorelSpace (L1Vec n) := ⟨rfl⟩
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  have hf : Measurable (fun z : Ω × Ξ => ∑ i, (a z.2).ofLp i • V z.1 i) := by
    fun_prop
  have hg : Measurable (fun z : Ω × Ξ => ∑ i, (b z.2).ofLp i • V z.1 i) := by
    fun_prop
  refine (wasserstein_maps_le_common_cost (mu.prod nu) _ _ hf hg).trans ?_
  calc
    _ ≤ ∫⁻ z : Ω × Ξ, ENNReal.ofReal (d * K) * edist (a z.2) (b z.2) ∂mu.prod nu := by
      apply lintegral_mono
      intro z
      exact bounded_mix_edist_le (V z.1) K hK (hbox z.1) (a z.2) (b z.2)
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      simp only [lintegral_const, measure_univ, mul_one]
      exact lintegral_const_mul _ (by fun_prop)

-- @node: bounded_gumbel_mix_wasserstein_le
/-- Suppose [there is at least one component](hyp:hn), [each random component
vector is measurable](hyp:hV), [K is nonnegative](hyp:hK), [all component vectors
lie in the d-dimensional coordinate cube of radius K](hyp:hbox), and [the
weights are strictly positive and the temperature lies strictly between zero
and one](hyp:hparameters). For independent component randomness and Gumbel noise,
[the Wasserstein-1 distance between soft and zero-temperature mixture laws is
at most d times K times $2(n-1)\tau - 2n(n-1)e^{-1}\tau\log\tau$, where n is the
number of components and $\tau$ is the temperature](goal). -/
lemma bounded_gumbel_mix_wasserstein_le
    {Ω : Type*} [MeasurableSpace Ω] {n d : ℕ}
    (mu : Measure Ω) [IsProbabilityMeasure mu] (hn : 1 ≤ n)
    (V : Ω → Fin n → L1Vec d) (hV : ∀ i, Measurable (fun x => V x i))
    (K : ℝ) (hK : 0 ≤ K) (hbox : ∀ x i, V x i ∈ boundedCube d K)
    (p : Fin n → ℝ) (tau : ℝ) (hparameters : SoftmaxParameters p tau) :
    wasserstein1
      ((mu.prod (gumbelInputs n)).map (fun z => gumbelSoftmaxMix (V z.1) p tau z.2))
      ((mu.prod (gumbelInputs n)).map (fun z => gumbelSoftmaxMix (V z.1) p 0 z.2)) ≤
      ENNReal.ofReal (d * K) * ENNReal.ofReal (2 * (n-1 : ℕ) * tau -
        2 * n * (n-1 : ℕ) * Real.exp (-1) * tau * Real.log tau) := by
  let := gumbelInputs_probability n
  have htau : tau ≠ 0 := ne_of_gt hparameters.1
  simp only [gumbelSoftmaxMix_eq_sum, if_neg htau, ite_true]
  exact (bounded_random_mix_wasserstein_le mu (gumbelInputs n) V hV K hK hbox
    (softmaxWeights p tau) (hardWeights p) (by fun_prop)
    (hardWeights_measurable (by omega) p)).trans
      (mul_le_mul_right (gumbelSoftmax_coupling_cost_le hn p tau hparameters) _)

-- @node: generator_soft_hard_wasserstein_le
/-- If [the generator has at least one component](hyp:hn), [K is
nonnegative](hyp:hK), [every second-stage component output lies in the
d-dimensional coordinate cube of radius K](hyp:hbox), and [the generator's
temperature is less than one](hyp:htau), [the Wasserstein-1 distance from its
output law to the law obtained by replacing its soft selector with the hard
selector on the same independent uniform and Gumbel inputs is at most d times K
times $2(n-1)\tau - 2n(n-1)e^{-1}\tau\log\tau$, where n is the number of components
and $\tau$ is the temperature](goal). -/
lemma generator_soft_hard_wasserstein_le {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (Q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (hn : 1 ≤ n)
    (K : ℝ) (hK : 0 ≤ K)
    (hbox : ∀ i x, (Q.g2 i).eval x ∈ boundedCube d K) (htau : tau < 1) :
    wasserstein1 (generatorLaw Q)
      ((generatorInputLaw n).map (fun z => gumbelSoftmaxMix
        (fun i => (Q.g2 i).eval ((Q.g1 i).eval (WithLp.toLp 1 (fun _ => z.1 i))))
        Q.p 0 z.2)) ≤
      ENNReal.ofReal (d * K) * ENNReal.ofReal (2 * (n-1 : ℕ) * tau -
        2 * n * (n-1 : ℕ) * Real.exp (-1) * tau * Real.log tau) := by
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  exact bounded_gumbel_mix_wasserstein_le
    (Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) hn
    (fun u i => (Q.g2 i).eval ((Q.g1 i).eval (WithLp.toLp 1 (fun _ => u i))))
    (by intros; fun_prop) K hK (fun u i => hbox i _) Q.p tau
    ⟨Q.temperature, htau, Q.positiveWeights⟩

end Papers.TbsNeuralCausalPi
