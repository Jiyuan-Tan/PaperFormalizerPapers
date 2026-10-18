module
public import Papers.TbsPrteOptimalTransport.Helpers.Transport
public import Toolkit.Tricks.Probability.Moments.ProductCouplingBounds
/-! One-dimensional transport extrema for the product cost. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Causalean.Stat
/-- If [the two marginal laws are probability laws with the given lower quantile functions](hyp:hprob),
[one marginal has bounded support and the other has a finite first moment](hyp:hmoment), and
[the cost is multiplication](hyp:hcost), then [the cost is integrable under every coupling;
its minimum and maximum are the countermonotone and comonotone quantile-product integrals,
and the corresponding shared-uniform constructions are couplings attaining those values](goal).

Product-cost extrema, attributed to Cédric Villani, Topics in Optimal Transportation,
2021 cited edition, section 2.2, beginning on p. 73; DOI 10.1090/gsm/058 (cite:villani2021topics).
The lower inverse is used throughout; strict inverses give the same laws and integrals. -/
-- @node: thm:1d-ot
lemma productCost_transport_extrema (mu nu : Measure ℝ) (Qmu Qnu : ℝ → ℝ)
    (c : ℝ → ℝ → ℝ)
    (hprob : IsQuantilePair mu nu Qmu Qnu)
    (hmoment : BoundedSupportOrFirstMoment mu nu) (hcost : IsProductCost c) :
    (∀ pi : Measure (ℝ × ℝ), IsCoupling pi mu nu → Integrable (fun a => c a.1 a.2) pi) ∧
    IsLeast {v : ℝ | ∃ pi, IsCoupling pi mu nu ∧ v = ∫ a, c a.1 a.2 ∂pi}
      (∫ t in Ioo (0 : ℝ) 1, Qmu t * Qnu (1 - t)) ∧
    IsGreatest {v : ℝ | ∃ pi, IsCoupling pi mu nu ∧ v = ∫ a, c a.1 a.2 ∂pi}
      (∫ t in Ioo (0 : ℝ) 1, Qmu t * Qnu t) ∧
    IsCoupling (unifOI.map (fun t => (Qmu t, Qnu (1 - t)))) mu nu ∧
    IsCoupling (unifOI.map (fun t => (Qmu t, Qnu t))) mu nu ∧
    (∫ a, c a.1 a.2 ∂(unifOI.map (fun t => (Qmu t, Qnu (1 - t))))) =
      (∫ t in Ioo (0 : ℝ) 1, Qmu t * Qnu (1 - t)) ∧
    (∫ a, c a.1 a.2 ∂(unifOI.map (fun t => (Qmu t, Qnu t)))) =
      (∫ t in Ioo (0 : ℝ) 1, Qmu t * Qnu t) := by
  letI : IsProbabilityMeasure mu := hprob.1
  letI : IsProbabilityMeasure nu := hprob.2.1
  have hc : c = fun a b => a * b := funext fun a => funext fun b => hcost a b
  rw [hc]
  have hbounded (rho : Measure ℝ) (h : ∃ B : ℝ, rho (Icc (-B) B)ᶜ = 0) :
      MemLp (fun x : ℝ => x) ⊤ rho := by
    obtain ⟨B, hB⟩ := h
    apply memLp_top_of_bound (by fun_prop) B
    filter_upwards [ae_iff.mpr hB] with x hx
    exact abs_le.mpr (show -B ≤ x ∧ x ≤ B from hx)
  have hbase :
      (∀ pi : Measure (ℝ × ℝ), IsCoupling pi mu nu →
        Integrable (fun a => a.1 * a.2) pi) ∧
      IsLeast {v : ℝ | ∃ pi, IsCoupling pi mu nu ∧ (∫ a, a.1 * a.2 ∂pi) = v}
        (∫ t in Ioo (0 : ℝ) 1, quantile mu t * quantile nu (1 - t)) ∧
      IsGreatest {v : ℝ | ∃ pi, IsCoupling pi mu nu ∧ (∫ a, a.1 * a.2 ∂pi) = v}
        (∫ t in Ioo (0 : ℝ) 1, quantile mu t * quantile nu t) := by
    rcases hmoment with ⟨hmu, hnu⟩ | ⟨hnu, hmu⟩
    · exact Toolkit.Tricks.Probability.Moments.isLeast_and_isGreatest_integral_mul_of_isCoupling
        mu nu (hbounded mu hmu) (memLp_one_iff_integrable.mpr hnu)
    · exact Toolkit.Tricks.Probability.Moments.isLeast_and_isGreatest_integral_mul_of_isCoupling
        mu nu (memLp_one_iff_integrable.mpr hmu) (hbounded nu hnu)
  have hQmu : Qmu =ᵐ[unifOI] quantile mu := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hprob.2.2.1 t ht
  have hQnu : Qnu =ᵐ[unifOI] quantile nu := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hprob.2.2.2 t ht
  have hQref : (fun t => Qnu (1 - t)) =ᵐ[unifOI]
      (fun t => quantile nu (1 - t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hprob.2.2.2 (1 - t) ⟨sub_pos.mpr ht.2, sub_lt_self 1 ht.1⟩
  have hmaplo : unifOI.map (fun t => (Qmu t, Qnu (1 - t))) =
      countermonotoneCoupling mu nu := by
    apply Measure.map_congr
    filter_upwards [hQmu, hQref] with t hmu hnu
    exact Prod.ext hmu hnu
  have hmaphi : unifOI.map (fun t => (Qmu t, Qnu t)) =
      comonotoneCoupling mu nu := by
    apply Measure.map_congr
    filter_upwards [hQmu, hQnu] with t hmu hnu
    exact Prod.ext hmu hnu
  have hintlo : (∫ t in Ioo (0 : ℝ) 1, Qmu t * Qnu (1 - t)) =
      (∫ t in Ioo (0 : ℝ) 1, quantile mu t * quantile nu (1 - t)) :=
    integral_congr_ae (hQmu.mul hQref)
  have hinthi : (∫ t in Ioo (0 : ℝ) 1, Qmu t * Qnu t) =
      (∫ t in Ioo (0 : ℝ) 1, quantile mu t * quantile nu t) :=
    integral_congr_ae (hQmu.mul hQnu)
  refine ⟨hbase.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hintlo]
    simpa only [eq_comm] using hbase.2.1
  · rw [hinthi]
    simpa only [eq_comm] using hbase.2.2
  · rw [hmaplo]
    exact isCoupling_countermonotoneCoupling mu nu
  · rw [hmaphi]
    exact isCoupling_comonotoneCoupling mu nu
  · rw [hmaplo, hintlo]
    exact Toolkit.Tricks.Probability.Moments.integral_mul_countermonotoneCoupling mu nu
  · rw [hmaphi, hinthi]
    exact Toolkit.Tricks.Probability.Moments.integral_mul_comonotoneCoupling mu nu
  -- @realizes \xi(shared uniform coordinate under unifOI)
  -- @realizes \mathcal A(first state space ℝ) @realizes \mathcal B(second state space ℝ)
end Papers.TbsPrteOptimalTransport
