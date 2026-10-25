module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRecursion
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSetup
/-! Deterministic bounded-radius branch of iterative RDIV stability.

The supportwise hypothesis envelope controls both errors without concentration.
An inverse-square-root radius floor absorbs any fixed finite sample prefix into
one population-only recursion coefficient. No probability budget is spent.
-/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

-- @node: rdiv_hypothesis_norm_le
/-- Assume [the IV sampling and density identities](hyp:hIV), [density realizability](hyp:hDensity), [the density support and magnitude bounds](hyp:hBounds), [the hypothesis envelope B on that support](hyp:hBound), and [nonnegative B](hyp:hB). For [a primal function h](hyp:h) [belonging to the hypothesis class](hyp:hh), [its square-integrable norm is at most B](goal). -/
lemma rdiv_hypothesis_norm_le {W X Z : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Z]
    (V : IVWorld W X Z) (mu : Measure X) (G : Set (X → Z → ℝ))
    (g₀ : X → Z → ℝ) (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hBound : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) : ‖h‖ ≤ B := by
  have hm : Measurable (fun p : X × Z => |primalVersion V h p.1|) := by
    exact ((V.primal_measurable h).comp measurable_fst).abs
  have hj : ∀ᵐ p ∂V.law.map (fun w => (V.xOf w, V.zOf w)),
      |primalVersion V h p.1| ≤ B := by
    rw [hIV.2.1]
    apply (ae_withDensity_iff (show Measurable (fun p : X × Z =>
      ENNReal.ofReal (g₀ p.1 p.2)) from (hDensity.2 g₀ hDensity.1).1.ennreal_ofReal)).2
    exact ae_of_all _ fun p hp => hBound h hh p (by
      by_contra hs
      have hz := hBounds.2.2.2.2 g₀ hDensity.1 p hs
      simp [hz] at hp)
  have ha := (ae_map_iff (V.measurable_x.prodMk V.measurable_z).aemeasurable
    (measurableSet_le hm measurable_const)).1 hj
  have hn : ∀ᵐ w ∂V.law, ‖(h : Lp ℝ 2 V.law) w‖ ≤ B := by
    filter_upwards [ha, V.primal_coherent h] with w hw he
    simpa only [← he, Real.norm_eq_abs, primalVersion] using hw
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hB hn

variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld W X Z)

-- @node: iter_rdiv_bounded_error_energy
/-- Assume [the IV sampling and density identities](hyp:hIV), [density realizability](hyp:hDensity), [the density support and magnitude bounds](hyp:hBounds), [the hypothesis envelope B](hyp:hBound), [nonnegative B](hyp:hB), and [a penalty in `(0, 2]`](hyp:hlam). For [a primal function h](hyp:h) with [h in the hypothesis class](hyp:hh) and [a in the hypothesis class](hyp:ha), [their squared distance is at most 4B², and the penalty times that squared distance plus their squared conditional-expectation image distance is at most 12B²](goal). -/
lemma iter_rdiv_bounded_error_energy
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG lam : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hBound : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 2)
    (h a : V.Hbar.toSubmodule) (hh : h ∈ V.H) (ha : a ∈ V.H) :
    ‖h - a‖ ^ 2 ≤ 4 * B ^ 2 ∧
      lam * ‖h - a‖ ^ 2 + ‖projCondExpOp V (h - a)‖ ^ 2 ≤ 12 * B ^ 2 := by
  have hhB := rdiv_hypothesis_norm_le V mu G g₀ support B c₀ CG
    hIV hDensity hBounds hBound hB h hh
  have haB := rdiv_hypothesis_norm_le V mu G g₀ support B c₀ CG
    hIV hDensity hBounds hBound hB a ha
  have hd : ‖h - a‖ ≤ 2 * B := (norm_sub_le h a).trans (by linarith)
  have hsq : ‖h - a‖ ^ 2 ≤ 4 * B ^ 2 := by
    nlinarith only [hd, norm_nonneg (h - a), hB]
  have hT : ‖projCondExpOp V (h - a)‖ ≤ ‖h - a‖ := by
    simpa only [one_mul] using
      (projCondExpOp V).le_of_opNorm_le (projCondExpOp_norm_le_one V) (h - a)
  have hTsq : ‖projCondExpOp V (h - a)‖ ^ 2 ≤ ‖h - a‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hT 2
  have hpen := mul_le_mul_of_nonneg_right hlam.2 (sq_nonneg ‖h - a‖)
  exact ⟨hsq, by linarith only [hsq, hTsq, hpen]⟩

-- @node: iter_rdiv_bounded_stability
/-- Assume [the IV sampling and density identities](hyp:hIV), [density realizability](hyp:hDensity), [the density support and magnitude bounds](hyp:hBounds), [the hypothesis envelope B](hyp:hBound), [nonnegative B](hyp:hB), [a penalty λ in `(0, 2]`](hyp:hlam), [positive N](hyp:hN), and [r² at least 1/N](hyp:hr). For [a primal function h](hyp:h) with [h in the hypothesis class](hyp:hh) and [a in the hypothesis class](hyp:ha), if [C is at least one](hyp:hC), [C is at least 24B²N](hyp:hCB), and [j is at least one](hyp:hj), [their regularized error energy is at most the j-th recursion coefficient times r²/λ, and their squared distance is at most the same coefficient times r²/λ²](goal). -/
lemma iter_rdiv_bounded_stability
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG lam r N : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hBound : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 2) (hN : 0 < N) (hr : 1 / N ≤ r ^ 2)
    (h a : V.Hbar.toSubmodule) (hh : h ∈ V.H) (ha : a ∈ V.H)
    (C : ℝ) (hC : 1 ≤ C) (hCB : 24 * B ^ 2 * N ≤ C) (j : ℕ) (hj : 1 ≤ j) :
    lam * ‖h - a‖ ^ 2 + ‖projCondExpOp V (h - a)‖ ^ 2 ≤
        iterRdivStabilityCoefficients C j * r ^ 2 / lam ∧
      ‖h - a‖ ^ 2 ≤ iterRdivStabilityCoefficients C j * r ^ 2 / lam ^ 2 := by
  obtain ⟨hsq, henergy⟩ := iter_rdiv_bounded_error_energy V mu G g₀ support
    B c₀ CG lam hIV hDensity hBounds hBound hB hlam h a hh ha
  have hseq : C ≤ iterRdivStabilityCoefficients C j := by
    cases j with
    | zero => omega
    | succ k =>
      change C ≤ C * (1 + iterRdivStabilityCoefficients C k)
      nlinarith only [mul_nonneg (show 0 ≤ C by linarith)
        ((iterRdivStabilityCoefficients_bounds C hC).2.1 k)]
  have hNr : 1 ≤ N * r ^ 2 := by
    simpa only [mul_comm] using (div_le_iff₀ hN).mp hr
  have hscale : 24 * B ^ 2 ≤ iterRdivStabilityCoefficients C j * r ^ 2 := by
    calc
      _ ≤ (24 * B ^ 2) * (N * r ^ 2) :=
        le_mul_of_one_le_right (by positivity) hNr
      _ = (24 * B ^ 2 * N) * r ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hCB.trans hseq) (sq_nonneg r)
  have hE : lam * ‖h - a‖ ^ 2 + ‖projCondExpOp V (h - a)‖ ^ 2 ≤
      iterRdivStabilityCoefficients C j * r ^ 2 / lam := by
    apply (le_div_iff₀ hlam.1).2
    have hmul := mul_le_mul_of_nonneg_right henergy hlam.1.le
    have htwo := mul_le_mul_of_nonneg_left hlam.2 (by positivity : 0 ≤ 12 * B ^ 2)
    nlinarith only [hmul, htwo, hscale]
  refine ⟨hE, ?_⟩
  apply (le_div_iff₀ (sq_pos_of_pos hlam.1)).2
  have hm := mul_le_mul_of_nonneg_right hE hlam.1.le
  rw [div_mul_cancel₀ _ hlam.1.ne'] at hm
  have hz := mul_nonneg hlam.1.le (sq_nonneg ‖projCondExpOp V (h - a)‖)
  nlinarith only [hm, hz]

-- @node: iter_rdiv_bounded_iterate_stability
/-- Assume [the IV sampling and density identities](hyp:hIV), [density realizability](hyp:hDensity), [the density support and magnitude bounds](hyp:hBounds), [the hypothesis envelope B](hyp:hBound), [nonnegative B](hyp:hB), [positive sample size n](hyp:hn), [n at most N](hyp:hnN), [r² at least 1/n](hyp:hr), [C at least one](hyp:hC), and [C at least 24B²N](hyp:hCB). If [all penalties in the segment lie in `(0, 2]`](hyp:hDom), [the fitted sequence consists of empirical iterates through horizon t on the segment](hyp:hEst), and [all positive population iterates through t belong to the hypothesis class there](hyp:hStar), [for every sample outcome, penalty in the segment, and positive stage j through t, the fitted-to-population regularized error energy is at most the j-th recursion coefficient times r²/λ and the squared error is at most that coefficient times r²/λ²](goal). -/
lemma iter_rdiv_bounded_iterate_stability
    (P : Measure Ω) (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG r C : ℝ) (n N t : ℕ)
    (iter : ℕ → ℝ → Ω → V.Hbar.toSubmodule) (segment : Set ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hBound : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hn : 0 < n) (hnN : n ≤ N) (hr : 1 / (n : ℝ) ≤ r ^ 2)
    (hC : 1 ≤ C) (hCB : 24 * B ^ 2 * N ≤ C)
    (hDom : ∀ lam ∈ segment, lam ∈ Set.Ioc (0 : ℝ) 2)
    (hEst : ∀ lam ∈ segment,
      IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
        (primalEmpDistanceSq V P sample split n) (fun j => iter j lam) t lam)
    (hStar : ∀ lam ∈ segment, ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) :
    ∀ ω : Ω, ∀ lam ∈ segment, ∀ j, 1 ≤ j → j ≤ t →
      lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
          ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
        iterRdivStabilityCoefficients C j * r ^ 2 / lam ∧
      ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
        iterRdivStabilityCoefficients C j * r ^ 2 / lam ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hfloor : 1 / (N : ℝ) ≤ r ^ 2 :=
    (one_div_le_one_div_of_le hn' (by exact_mod_cast hnN)).trans hr
  intro ω lam hlam j hj hjt
  exact iter_rdiv_bounded_stability V mu G g₀ support B c₀ CG lam r N
    hIV hDensity hBounds hBound hB (hDom lam hlam) hN hfloor
    (iter j lam ω) (populationIterate V lam j)
    ((hEst lam hlam).2 j hj hjt ω).1 (hStar lam hlam j hj hjt) C hC hCB j hj

end Papers.TsAdaptiveEstimationInference
