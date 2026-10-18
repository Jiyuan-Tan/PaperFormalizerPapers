module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.DeepReLUApprox
public import Papers.TbsNeuralCausalPi.Helpers.HilbertCurve
public import Papers.TbsNeuralCausalPi.Helpers.SingletonGenerator
public import Papers.TbsNeuralCausalPi.Helpers.DeepGeneratorAssembly
/-! # Deep distribution generators -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: thm:cor-fix-3c402872
/-- For [a probability law P on d-dimensional real vectors](hyp:P), [a finite family of support sets S](hyp:S), [assigned component dimensions](hyp:dC), and [a common nonnegative chart Lipschitz bound L](hyp:L), assume [the sets are exactly the distinct connected components of P's support](hyp:hsupp), [each component has an L-Lipschitz homeomorphism from its assigned unit cube](hyp:hcharts), [each conditional component law admits a chart under which it dominates a positive multiple of cube Lebesgue measure](hyp:hdom), [each such law admits a dominating chart whose inverse transports zero mass to the cube boundary in positive dimension](hyp:hboundary), and [Yarotsky's coordinate approximation bound holds](hyp:hYarotskyCoordinate_of_gate). Then [there are a positive error constant, a depth threshold at least one, and a temperature threshold strictly between zero and one such that all larger pairs of depths and all positive smaller temperatures admit a three-part generator with the prescribed explicit width factors, exact component probabilities, first blocks mapping the scalar unit cube into component cubes, and zero-dimensional second blocks mapping into their support components; its Wasserstein error is at most the error constant times the sum of the two depths to the power minus two divided by the maximum component dimension and the temperature minus temperature times its logarithm, omitting the depth terms when every component dimension is zero](goal). -/
theorem deep_generator_approximation {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (hdom : ∀ i, LowerBoundDomination (d := dC i) (ProbabilityTheory.cond (P : Measure _) (S i))
      (S i) L)
    (hboundary : ∀ i, PullbackVanishesOnBoundary (d := dC i)
      (ProbabilityTheory.cond (P : Measure _) (S i)) (S i) L)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox) :
    ∃ A : ℝ, 0 < A ∧
      ∃ B : ℕ, 1 ≤ B ∧ ∃ tauBar : ℝ, 0 < tauBar ∧ tauBar < 1 ∧
      ∀ L1 L2 : ℕ, B ≤ L1 → B ≤ L2 → ∀ tau : ℝ, 0 < tau → tau < tauBar →
        ∃ q : ThreePartGenerator N d dC (deepFirstWidthFactor * max 1 (Finset.univ.sup dC)) L1
          (deepSecondWidthFactor * d * max 1 (Finset.univ.sup dC)) L2 tau,
          (∀ i, q.p i = ((P : Measure _) (S i)).toReal) ∧
          (∀ i, Set.MapsTo (q.g1 i).eval (unitCube 1) (unitCube (dC i))) ∧ -- @realizes \hat{g}_1(constructed first blocks take their scalar cubes into component cubes)
          (∀ i, dC i = 0 → Set.MapsTo (q.g2 i).eval (unitCube (dC i)) (S i)) ∧
          wasserstein1 (generatorLaw q) (P : Measure _) ≤ ENNReal.ofReal (A * (
(if 0 < Finset.univ.sup dC then
          (L1 : ℝ)^(-(2:ℝ)/max 1 (Finset.univ.sup dC)) +
          (L2 : ℝ)^(-(2:ℝ)/max 1 (Finset.univ.sup dC)) else 0) + tau - tau * Real.log tau)) := by
  obtain ⟨A, K, hA, hK, hblocks⟩ :=
    exists_deep_relu_generator_mixture_bound_explicit P S dC L hsupp hcharts
      hdom hYarotskyCoordinate_of_gate
  let a : ℝ := 2 * (N-1 : ℕ)
  let b : ℝ := 2 * N * (N-1 : ℕ) * Real.exp (-1)
  let M : ℝ := (d : ℝ) * K * (a+b)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hK.le) (add_nonneg ha hb)
  refine ⟨A+M+1, by linarith, 4, by norm_num,
    1/2, by norm_num, by norm_num, ?_⟩
  intro L1 L2 hW hL tau htau htauBar
  obtain ⟨Q, hp, hcube, hbox, hzero, hmix⟩ := hblocks L1 L2 hW hL tau htau
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
    (L1 : ℝ)^(-(2:ℝ)/max 1 (Finset.univ.sup dC)) +
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


/-- For [a probability law P on real vectors](hyp:P), [a finite family of support sets S](hyp:S), [assigned component dimensions](hyp:dC), and [a common nonnegative chart Lipschitz bound L](hyp:L), assume [the sets are exactly the distinct connected components of P's support](hyp:hsupp), [each component has an L-Lipschitz homeomorphism from its assigned unit cube](hyp:hcharts), [each conditional component law admits a chart under which it dominates a positive multiple of cube Lebesgue measure](hyp:hdom), [each conditional law admits a dominating chart with zero inverse-transported boundary mass in positive dimension](hyp:hboundary), and [Yarotsky's coordinate approximation bound holds](hyp:hYarotskyCoordinate_of_gate). Then [positive integer width factors, a positive error constant, a depth threshold at least one, and a temperature threshold strictly between zero and one can be chosen so that all larger depths and all positive smaller temperatures admit a three-part generator with those width factors, exact component probabilities, cube-preserving first blocks, and second blocks mapping zero-dimensional cubes into their components, whose Wasserstein error is bounded by the constant times the sum of the two inverse-depth powers with exponent two divided by the maximum positive component dimension and temperature minus temperature times its logarithm; the depth terms vanish if every component dimension is zero](goal). -/
theorem deep_generator_approximation_exists_factors {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (hdom : ∀ i, LowerBoundDomination (d := dC i) (ProbabilityTheory.cond (P : Measure _) (S i))
      (S i) L)
    (hboundary : ∀ i, PullbackVanishesOnBoundary (d := dC i)
      (ProbabilityTheory.cond (P : Measure _) (S i)) (S i) L)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧ ∃ A : ℝ, 0 < A ∧
      ∃ B : ℕ, 1 ≤ B ∧ ∃ tauBar : ℝ, 0 < tauBar ∧ tauBar < 1 ∧
      ∀ L1 L2 : ℕ, B ≤ L1 → B ≤ L2 → ∀ tau : ℝ, 0 < tau → tau < tauBar →
        ∃ q : ThreePartGenerator N d dC (c1 * max 1 (Finset.univ.sup dC)) L1
          (c2 * d * max 1 (Finset.univ.sup dC)) L2 tau,
          (∀ i, q.p i = ((P : Measure _) (S i)).toReal) ∧
          (∀ i, Set.MapsTo (q.g1 i).eval (unitCube 1) (unitCube (dC i))) ∧ -- @realizes \hat{g}_1(constructed first blocks take their scalar cubes into component cubes)
          (∀ i, dC i = 0 → Set.MapsTo (q.g2 i).eval (unitCube (dC i)) (S i)) ∧
          wasserstein1 (generatorLaw q) (P : Measure _) ≤ ENNReal.ofReal (A * (
(if 0 < Finset.univ.sup dC then
          (L1 : ℝ)^(-(2:ℝ)/max 1 (Finset.univ.sup dC)) +
          (L2 : ℝ)^(-(2:ℝ)/max 1 (Finset.univ.sup dC)) else 0) + tau - tau * Real.log tau)) := by
  obtain ⟨A, hA, hrest⟩ := deep_generator_approximation P S dC L hsupp hcharts hdom
    hboundary hYarotskyCoordinate_of_gate
  exact ⟨deepFirstWidthFactor, deepSecondWidthFactor, by decide, by decide, A, hA, hrest⟩

end
end Papers.TbsNeuralCausalPi
