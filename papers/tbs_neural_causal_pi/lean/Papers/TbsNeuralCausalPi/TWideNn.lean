module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorMixing
public import Papers.TbsNeuralCausalPi.Helpers.ComponentLaws
public import Papers.TbsNeuralCausalPi.Helpers.NetworkClipping
public import Papers.TbsNeuralCausalPi.Helpers.WideGenerator
public import Papers.TbsNeuralCausalPi.Helpers.WideSecondBlocks
public import Papers.TbsNeuralCausalPi.Helpers.WideComponentErrors
public import Papers.TbsNeuralCausalPi.Helpers.WideQuantization
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorMixtureLaw
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinSpace
/-! # Wide distribution generators -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- For [a target probability distribution](hyp:P), [a carrier set](hyp:C),
[a three-part generator](hyp:Q), and [an output-box radius](hyp:K), suppose
[the target carrier is compact](hyp:hC), [the target probability
distribution gives it full mass](hyp:hP), [the generator has at least one
component](hyp:hN), [the output-box radius is nonnegative](hyp:hK), [every
second generator block maps all inputs into that box](hyp:hbox), and [the
temperature is below one](hyp:htau). Then [the Wasserstein distance from the
soft generator law to the target is at most the distance from the target to
the mixture of component generator laws, plus the output dimension times the
box radius times the selector penalty, which is twice temperature times one
less than the component count, minus twice the component count times one less
than that count times the reciprocal of the exponential of one times
temperature times its logarithm](goal). -/
-- @node: generator_total_error_le_of_compact_mass
lemma generator_total_error_le_of_compact_mass {d N : ℕ} {dC : Fin N → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (P : ProbabilityMeasure (L1Vec d)) (C : Set (L1Vec d))
    (hC : IsCompact C) (hP : (P : Measure _) C = 1)
    (Q : ThreePartGenerator N d dC W1 L1 W2 L2 tau) (hN : 0 < N)
    (K : ℝ) (hK : 0 ≤ K) (hbox : ∀ i x, (Q.g2 i).eval x ∈ boundedCube d K)
    (htau : tau < 1) :
    wasserstein1 (generatorLaw Q) (P : Measure _) ≤
      wasserstein1 (P : Measure _) (∑ i, ENNReal.ofReal (Q.p i) •
        (uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)) +
      ENNReal.ofReal (d*K) * ENNReal.ofReal (2 * (N-1 : ℕ) * tau -
        2 * N * (N-1 : ℕ) * Real.exp (-1) * tau * Real.log tau) := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  let := generatorInputLaw_probability N
  let V := fun (z : (Fin N → ℝ) × (Fin N → ℝ)) i =>
    (Q.g2 i).eval ((Q.g1 i).eval (WithLp.toLp 1 (fun _ => z.1 i)))
  let f := fun z => gumbelSoftmaxMix (V z) Q.p 0 z.2
  have hf : Measurable f :=
    gumbelSoftmaxMix_measurable hN V (by intro i; fun_prop) Q.p 0 _ measurable_snd
  let hard := (generatorInputLaw N).map f
  let : IsProbabilityMeasure hard := Measure.isProbabilityMeasure_map hf.aemeasurable
  let : IsProbabilityMeasure (generatorLaw Q) :=
    Measure.isProbabilityMeasure_map Q.eval_measurable.aemeasurable
  let U := C ∪ boundedCube d K
  have hU : IsCompact U := hC.union (boundedCube_isCompact d K)
  have hmass (g : ((Fin N → ℝ) × (Fin N → ℝ)) → L1Vec d)
      (hg : Measurable g) (hb : ∀ z, g z ∈ boundedCube d K) :
      ((generatorInputLaw N).map g) U = 1 := by
    rw [Measure.map_apply hg hU.measurableSet]
    have heq : g ⁻¹' U = Set.univ :=
      Set.eq_univ_of_forall (fun z => Set.mem_union_right C (hb z))
    rw [heq, measure_univ]
  have hsoftmass : generatorLaw Q U = 1 := hmass Q.eval Q.eval_measurable (fun z =>
    gumbelSoftmaxMix_mem_boundedCube hN (V z) Q.p Q.positiveWeights tau
      (ne_of_gt Q.temperature) z.2 K (fun i => hbox i _))
  have hhardmass : hard U = 1 := hmass f hf (by
    intro z
    dsimp [f]
    rw [gumbelSoftmaxMix_zero_eq_selected ⟨0, hN⟩]
    exact hbox _ _)
  have hPmass : (P : Measure _) U = 1 := by
    apply le_antisymm prob_le_one
    rw [← hP]
    exact measure_mono Set.subset_union_left
  have htri := wasserstein1_triangle_compact_mass (generatorLaw Q) hard (P : Measure _)
    U hU hsoftmass hhardmass hPmass
  have hsym := wasserstein1_symm P (⟨hard, inferInstance⟩ : ProbabilityMeasure (L1Vec d))
  change wasserstein1 (P : Measure _) hard = wasserstein1 hard (P : Measure _) at hsym
  have hsoft := generator_soft_hard_wasserstein_le Q (by omega) K hK hbox htau
  change wasserstein1 (generatorLaw Q) hard ≤ _ at hsoft
  refine htri.trans ((add_le_add hsoft le_rfl).trans_eq ?_)
  rw [← hsym]
  have hlaw : hard = ∑ i, ENNReal.ofReal (Q.p i) •
      (uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval) :=
    generator_hard_law_eq_mixture Q hN
  rw [hlaw, add_comm]

-- @node: thm:wide-nn
/-- For [a target distribution](hyp:P), [its proposed support components](hyp:S),
[their intrinsic dimensions](hyp:dC), and [a common chart Lipschitz bound](hyp:L),
suppose [the support consists of these finitely many components](hyp:hsupp)
and [each component is Lipschitz homeomorphic to its dimensional cube](hyp:hcharts).
Assuming [quantized generation](hyp:hPerekrestenko_of_gate) and [coordinate
neural approximation](hyp:hYarotskyCoordinate_of_gate), [there exist positive
architecture factors and an error constant, a minimum budget, and a positive
temperature ceiling below one, such that every larger first-block width and
second-block depth and smaller positive temperature admit a three-part
generator with exact component probabilities, first blocks mapping scalar
unit cubes into component cubes, and second blocks mapping zero-dimensional
cubes into their components; its Wasserstein error is at most the error
constant times the sum of first-block width to power minus one divided by maximum positive
component dimension, plus second-block depth to power minus two divided by
that dimension, plus temperature minus temperature times its logarithm, with
both budget terms omitted when every component has dimension zero](goal). -/
theorem wide_generator_approximation {d N : ℕ}

    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)

    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧ ∃ A : ℝ, 0 < A ∧
      ∃ B : ℕ, 1 ≤ B ∧ ∃ tauBar : ℝ, 0 < tauBar ∧ tauBar < 1 ∧
      ∀ W1 L2 : ℕ, B ≤ W1 → B ≤ L2 → ∀ tau : ℝ, 0 < tau → tau < tauBar →
        ∃ q : ThreePartGenerator N d dC W1 (c1 * max 1 (Finset.univ.sup dC))
          (c2 * d * max 1 (Finset.univ.sup dC)) L2 tau,
          (∀ i, q.p i = ((P : Measure _) (S i)).toReal) ∧
          (∀ i, Set.MapsTo (q.g1 i).eval (unitCube 1) (unitCube (dC i))) ∧ -- @realizes \hat{g}_1(constructed first blocks take their scalar cubes into component cubes)
          (∀ i, dC i = 0 → Set.MapsTo (q.g2 i).eval (unitCube (dC i)) (S i)) ∧
          wasserstein1 (generatorLaw q) (P : Measure _) ≤ ENNReal.ofReal (A * (
(if 0 < Finset.univ.sup dC then
          (W1 : ℝ)^(-(1:ℝ)/max 1 (Finset.univ.sup dC)) +
          (L2 : ℝ)^(-(2:ℝ)/max 1 (Finset.univ.sup dC)) else 0) + tau - tau * Real.log tau)) := by
  obtain ⟨c1, c2, hc1, hc2, A, K, hA, hK, B, hB, hblocks⟩ :=
    exists_wide_relu_generator_mixture_bound P S dC L hsupp hcharts
      hPerekrestenko_of_gate hYarotskyCoordinate_of_gate
  let a : ℝ := 2 * (N-1 : ℕ)
  let b : ℝ := 2 * N * (N-1 : ℕ) * Real.exp (-1)
  let M : ℝ := (d : ℝ) * K * (a+b)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hK.le) (add_nonneg ha hb)
  refine ⟨c1, c2, hc1, hc2, A+M+1, by linarith, B, by omega,
    1/2, by norm_num, by norm_num, ?_⟩
  intro W1 L2 hW hL tau htau htauBar
  obtain ⟨Q, hp, hcube, hbox, hzero, hmix⟩ := hblocks W1 L2 hW hL tau htau
  refine ⟨Q, hp, hcube, hzero, ?_⟩
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    subst N
    have hw := Q.weights.2
    simp at hw
  have hC : IsCompact (⋃ i, S i) := isCompact_iUnion (fun i => component_isCompact hcharts i)
  have hP : (P : Measure _) (⋃ i, S i) = 1 := by
    apply (mem_ae_iff_prob_eq_one hC.measurableSet).mp
    rw [← hsupp.1, measureSupport_eq_support]
    exact Measure.support_mem_ae
  have htotal := generator_total_error_le_of_compact_mass P _ hC hP Q hN K hK.le hbox
    (by linarith : tau < 1)
  let R : ℝ := if 0 < Finset.univ.sup dC then
    (W1 : ℝ)^(-(1:ℝ)/max 1 (Finset.univ.sup dC)) +
    (L2 : ℝ)^(-(2:ℝ)/max 1 (Finset.univ.sup dC)) else 0
  have hR : 0 ≤ R := by dsimp [R]; split_ifs <;> positivity
  have hlog : Real.log tau ≤ 0 := Real.log_nonpos htau.le (by linarith)
  have hneglog : 0 ≤ -(tau * Real.log tau) := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos htau.le hlog)
  have hT : 0 ≤ tau - tau * Real.log tau := by linarith
  have hselector : ENNReal.ofReal (d*K) * ENNReal.ofReal
      (a*tau - b*tau*Real.log tau) ≤ ENNReal.ofReal (M*(tau-tau*Real.log tau)) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg d) hK.le)]
    apply ENNReal.ofReal_le_ofReal
    have hlocal : a*tau - b*tau*Real.log tau ≤ (a+b)*(tau-tau*Real.log tau) := by
      nlinarith [mul_nonneg ha hneglog, mul_nonneg hb htau.le]
    simpa only [M, mul_assoc] using
      mul_le_mul_of_nonneg_left hlocal (mul_nonneg (Nat.cast_nonneg d) hK.le)
  refine htotal.trans ((add_le_add hmix hselector).trans ?_)
  rw [← ENNReal.ofReal_add (mul_nonneg hA.le hR) (mul_nonneg hM hT)]
  apply ENNReal.ofReal_le_ofReal
  change A * R + M * (tau-tau*Real.log tau) ≤
    (A+M+1)*(R+tau-tau*Real.log tau)
  nlinarith [mul_nonneg hA.le hT, mul_nonneg hM hR]

end
end Papers.TbsNeuralCausalPi
