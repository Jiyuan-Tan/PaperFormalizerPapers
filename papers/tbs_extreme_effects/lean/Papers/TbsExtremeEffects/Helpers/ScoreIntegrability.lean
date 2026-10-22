module
public import Papers.TbsExtremeEffects.Helpers.ScoreSampling

/-! IPW score integrability derived from the fitted pseudo-outcome and overlap.
The construction supplies the pseudo-outcome moment almost surely on the
training event, so the event transfer preserves that almost-sure reading. -/

public section
set_option linter.unusedTactic false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
variable {q d : ℕ} {M : ExtremeModel q d}

/-- If [the overlap constant is positive](hyp:hc), [the propensity is at least that constant](hyp:hp), and [its complement is also at least that constant](hyp:hp'), then [the inverse-probability weight for either treatment arm has absolute value at most the reciprocal overlap constant](goal). -/
-- @node: ipw_inverse_weight_bound
lemma ipw_inverse_weight_bound {p c : ℝ} (hc : 0 < c)
    (hp : c ≤ p) (hp' : c ≤ 1 - p) (a : Bool) :
    |(if a then (1 : ℝ) else 0) / p -
      (if a then (0 : ℝ) else 1) / (1 - p)| ≤ 1 / c := by
  have hp0 : 0 < p := hc.trans_le hp
  have hp0' : 0 < 1 - p := hc.trans_le hp'
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_div, zero_sub, abs_neg,
      abs_of_pos (one_div_pos.mpr hp0')]
    exact one_div_le_one_div_of_le hc hp'
  · simp only [↓reduceIte, zero_div, sub_zero, abs_of_pos (one_div_pos.mpr hp0)]
    exact one_div_le_one_div_of_le hc hp

/-- [The norm of the pseudo-outcome](goal) equals the absolute outcome divided by the covariate-norm power fitted from the training data. -/
-- @node: pseudoOutcome_norm
lemma pseudoOutcome_norm (E : NeteExperiment M) (n : ℕ) (w : E.Om) (z : Obs q d) :
    ‖pseudoOutcome E n w z‖ =
      |z.2.2.1| / l1Norm z.2.2.2 ^ E.alphaHat n w := by
  rw [Real.norm_eq_abs, pseudoOutcome, abs_div,
    abs_of_nonneg (Real.rpow_nonneg (by unfold l1Norm; positivity) _)]

-- @node: pseudoOutcome_integrable_of_absolute
/-- If [the displayed absolute pseudo-outcome is integrable under the tail law](hyp:h), then [the signed pseudo-outcome is integrable under that tail law](goal). -/
lemma pseudoOutcome_integrable_of_absolute (E : NeteExperiment M)
    (n : ℕ) (t : ℝ) (w : E.Om)
    (h : Integrable (fun z : Obs q d =>
      |z.2.2.1| / l1Norm z.2.2.2 ^ E.alphaHat n w) (obsTailLaw M t)) :
    Integrable (pseudoOutcome E n w) (obsTailLaw M t) := by
  have hm : Measurable (pseudoOutcome E n w) := by
    unfold pseudoOutcome
    fun_prop
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  simpa only [pseudoOutcome_norm] using h

-- @node: ipw_score_integrable_of_pseudoOutcome
/-- If [the sample size is even](hyp:hn), [the estimated propensity satisfies overlap](hyp:hOverlap), and [the pseudo-outcome is integrable under the tail law](hyp:h), then [the inverse-probability-weighted score is integrable under that law](goal). -/
lemma ipw_score_integrable_of_pseudoOutcome (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n) {c t : ℝ}
    (hOverlap : EstimatedOverlap E c) (w : E.Om)
    (h : Integrable (pseudoOutcome E n w) (obsTailLaw M t)) :
    Integrable (score E .ipw n w) (obsTailLaw M t) := by
  let weight : Obs q d → ℝ := fun z =>
    (if z.2.1 then (1 : ℝ) else 0) / E.pHat n w z.1 -
      (if z.2.1 then (0 : ℝ) else 1) / (1 - E.pHat n w z.1)
  have hp : Measurable (fun z : Obs q d => E.pHat n w z.1) :=
    (E.pHat_training n).comp (measurable_const.prodMk measurable_fst)
  have hm : Measurable weight := by
    first | fun_prop | skip
    have h1 : Measurable (fun z : Obs q d => if z.2.1 then (1 : ℝ) else 0) :=
      (measurable_of_finite (fun a : Bool => if a then (1 : ℝ) else 0)).comp
        (measurable_fst.comp measurable_snd)
    have h0 : Measurable (fun z : Obs q d => if z.2.1 then (0 : ℝ) else 1) :=
      (measurable_of_finite (fun a : Bool => if a then (0 : ℝ) else 1)).comp
        (measurable_fst.comp measurable_snd)
    exact (h1.div hp).sub (h0.div (measurable_const.sub hp))
  apply h.mul_bdd (c := 1 / c) hm.aestronglyMeasurable
  filter_upwards [estimatedOverlap_obsTailLaw E hn hOverlap t w] with z hov
  rw [Real.norm_eq_abs]
  exact ipw_inverse_weight_bound hOverlap.1 hov.1 (by linarith [hov.2]) z.2.1

/-- If [the sample size is even](hyp:hn), [the estimated propensity satisfies overlap](hyp:hOverlap), and [the fitted pseudo-outcome is integrable on the nuisance event](hyp:h), then [the inverse-probability-weighted score is integrable under the tail law almost surely on that event](goal). -/
-- @node: ipw_score_integrable_on_nuisance_event
lemma ipw_score_integrable_on_nuisance_event (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n) {c t : ℝ}
    (hOverlap : EstimatedOverlap E c) {G : Set E.Om}
    (h : FittedPseudoOutcomeIntegrable E n t G) :
    ∀ᵐ w ∂E.P, w ∈ G → Integrable (score E .ipw n w) (obsTailLaw M t) := by
  filter_upwards [h] with w hw hG
  exact ipw_score_integrable_of_pseudoOutcome E hn hOverlap w
    (pseudoOutcome_integrable_of_absolute E n t w (hw hG))

end Papers.TbsExtremeEffects
