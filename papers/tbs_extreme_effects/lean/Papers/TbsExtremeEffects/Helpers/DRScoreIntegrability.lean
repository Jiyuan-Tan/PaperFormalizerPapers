module
public import Papers.TbsExtremeEffects.Helpers.ScoreIntegrability

/-! Integrability of the frozen DR score from its pseudo-outcome and fitted regressions. -/

public section
set_option linter.unusedTactic false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
variable {q d : ℕ} {M : ExtremeModel q d}

/-- If [the treated propensity is nonzero](hyp:hp) and [the control propensity is nonzero](hyp:hp'),
then for [the treatment indicator](hyp:a), [the residual inverse-propensity weight has the stated
treated-minus-control representation](goal). -/
-- @node: dr_residual_weight_identity
lemma dr_residual_weight_identity {p : ℝ} (hp : p ≠ 0) (hp' : 1 - p ≠ 0)
    (a : Bool) :
    ((if a then (1 : ℝ) else 0) - p) / (p * (1 - p)) =
      (if a then (1 : ℝ) else 0) / p -
        (if a then (0 : ℝ) else 1) / (1 - p) := by
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp; ring

/-- If [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap), [the fitted
pseudo-outcome is integrable](hyp:h), and [each treatment-specific fitted regression is integrable](hyp:hg),
then [the frozen DR score is integrable](goal) under the evaluation tail law. -/
-- @node: dr_score_integrable_of_pseudoOutcome
lemma dr_score_integrable_of_pseudoOutcome (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n) {c t : ℝ}
    (hOverlap : EstimatedOverlap E c) (w : E.Om)
    (h : Integrable (pseudoOutcome E n w) (obsTailLaw M t))
    (hg : ∀ a : Bool, Integrable
      (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z)) (obsTailLaw M t)) :
    Integrable (score E .dr n w) (obsTailLaw M t) := by
  let weight : Obs q d → ℝ := fun z =>
    ((if z.2.1 then (1 : ℝ) else 0) - E.pHat n w z.1) /
      (E.pHat n w z.1 * (1 - E.pHat n w z.1))
  have hm : Measurable weight := by
    first | fun_prop | skip
    have hp : Measurable (fun z : Obs q d => E.pHat n w z.1) :=
      (E.pHat_training n).comp (measurable_const.prodMk measurable_fst)
    have hD : Measurable (fun z : Obs q d => if z.2.1 then (1 : ℝ) else 0) :=
      (measurable_of_finite (fun a : Bool => if a then (1 : ℝ) else 0)).comp
        (measurable_fst.comp measurable_snd)
    exact (hD.sub hp).div (hp.mul (measurable_const.sub hp))
  have hgD : Integrable
      (fun z : Obs q d => E.gHat n w z.1 z.2.1 (obsDirection z)) (obsTailLaw M t) := by
    classical
    have hs : MeasurableSet {z : Obs q d | z.2.1 = true} :=
      (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
    have hi := Integrable.piecewise hs (hg true).integrableOn (hg false).integrableOn
    apply hi.congr
    exact Eventually.of_forall fun z => by cases hd : z.2.1 <;> simp [Set.piecewise, hd]
  have hResidual : Integrable
      (fun z : Obs q d => (pseudoOutcome E n w z - E.gHat n w z.1 z.2.1 (obsDirection z)) *
        weight z) (obsTailLaw M t) := by
    apply (h.sub hgD).mul_bdd (c := 1 / c) hm.aestronglyMeasurable
    filter_upwards [estimatedOverlap_obsTailLaw E hn hOverlap t w] with z hov
    have hp : 0 < E.pHat n w z.1 := hOverlap.1.trans_le hov.1
    have hp' : 0 < 1 - E.pHat n w z.1 := by linarith [hOverlap.1, hov.2]
    dsimp only [weight]
    rw [Real.norm_eq_abs, dr_residual_weight_identity hp.ne' hp'.ne']
    exact ipw_inverse_weight_bound hOverlap.1 hov.1 (by linarith [hov.2]) z.2.1
  apply ((hg true).sub (hg false) |>.add hResidual).congr
  exact Eventually.of_forall fun z => by
    change E.gHat n w z.1 true (obsDirection z) - E.gHat n w z.1 false (obsDirection z) +
      (pseudoOutcome E n w z - E.gHat n w z.1 z.2.1 (obsDirection z)) * weight z = _
    simp only [score, drScore, weight]
    ring

/-- If [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap), [the fitted
pseudo-outcome is integrable on the event](hyp:h), and [both fitted regressions are integrable for
every outcome in that event](hyp:hg), then [the DR score is almost surely integrable for outcomes
in that event](goal). -/
-- @node: dr_score_integrable_on_nuisance_event
lemma dr_score_integrable_on_nuisance_event (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n) {c t : ℝ}
    (hOverlap : EstimatedOverlap E c) {G : Set E.Om}
    (h : FittedPseudoOutcomeIntegrable E n t G)
    (hg : ∀ w ∈ G, ∀ a : Bool, Integrable
      (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z)) (obsTailLaw M t)) :
    ∀ᵐ w ∂E.P, w ∈ G → Integrable (score E .dr n w) (obsTailLaw M t) := by
  filter_upwards [h] with w hw hG
  exact dr_score_integrable_of_pseudoOutcome E hn hOverlap w
    (pseudoOutcome_integrable_of_absolute E n t w (hw hG)) (hg w hG)

end Papers.TbsExtremeEffects
