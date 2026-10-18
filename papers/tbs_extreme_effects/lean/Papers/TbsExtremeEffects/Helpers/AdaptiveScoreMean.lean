module
public import Papers.TbsExtremeEffects.Helpers.EtaDR

/-! Conditional DR mean decomposition from the bandwise second-moment premise.
Recovering the pseudo-outcome from the score avoids choosing exceptional training
samples separately at each threshold. -/

public section
set_option linter.unusedTactic false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- For [an experiment](hyp:E), if [the sample size is even](hyp:hn), [estimated treatment probabilities satisfy overlap](hyp:hOverlap), [the doubly robust score is integrable](hyp:hScore), and [both fitted outcome regressions are integrable](hyp:hg), then [the pseudo-outcome is integrable under the tail law](goal). -/
-- @node: pseudoOutcome_integrable_of_dr_score
lemma pseudoOutcome_integrable_of_dr_score (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n) {c t : ℝ}
    (hOverlap : EstimatedOverlap E c) (w : E.Om)
    (hScore : Integrable (score E .dr n w) (obsTailLaw M t))
    (hg : ∀ a : Bool, Integrable
      (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z)) (obsTailLaw M t)) :
    Integrable (pseudoOutcome E n w) (obsTailLaw M t) := by
  let invWeight : Obs q d → ℝ := fun z =>
    if z.2.1 then E.pHat n w z.1 else -(1 - E.pHat n w z.1)
  have hm : Measurable invWeight := by
    first | fun_prop | skip
    have hp : Measurable (fun z : Obs q d => E.pHat n w z.1) :=
      (E.pHat_training n).comp (measurable_const.prodMk measurable_fst)
    exact hp.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
      (measurable_const.sub hp).neg
  have hb : ∀ᵐ z ∂obsTailLaw M t, ‖invWeight z‖ ≤ 1 := by
    filter_upwards [estimatedOverlap_obsTailLaw E hn hOverlap t w] with z hp
    have hp0 : 0 ≤ E.pHat n w z.1 := hOverlap.1.le.trans hp.1
    have hp1 : E.pHat n w z.1 ≤ 1 := by linarith [hOverlap.1, hp.2]
    cases hd : z.2.1 <;> simp only [invWeight, hd, Bool.false_eq_true, ↓reduceIte,
      norm_neg, Real.norm_eq_abs]
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - E.pHat n w z.1)]
      linarith
    · rw [abs_of_nonneg hp0]
      exact hp1
  have hgD : Integrable
      (fun z : Obs q d => E.gHat n w z.1 z.2.1 (obsDirection z)) (obsTailLaw M t) := by
    have hs : MeasurableSet {z : Obs q d | z.2.1 = true} :=
      (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
    apply (Integrable.piecewise hs (hg true).integrableOn (hg false).integrableOn).congr
    exact Eventually.of_forall fun z => by cases hd : z.2.1 <;> simp [Set.piecewise, hd]
  have hi := ((hScore.sub (hg true)).add (hg false)).mul_bdd hm.aestronglyMeasurable hb
  apply (hi.add hgD).congr
  filter_upwards [estimatedOverlap_obsTailLaw E hn hOverlap t w] with z hp
  have hp0 := (hOverlap.1.trans_le hp.1).ne'
  have hp1 : 1 - E.pHat n w z.1 ≠ 0 := by linarith [hOverlap.1, hp.2]
  change (score E .dr n w z - E.gHat n w z.1 true (obsDirection z) +
    E.gHat n w z.1 false (obsDirection z)) * invWeight z +
    E.gHat n w z.1 z.2.1 (obsDirection z) = pseudoOutcome E n w z
  simp only [score, drScore]
  rw [dr_residual_weight_identity hp0 hp1]
  cases hd : z.2.1 <;> simp only [invWeight, hd, Bool.false_eq_true, ↓reduceIte, zero_div]
  all_goals field_simp; ring

/-- For [an experiment](hyp:E), if [the noise is regularly varying](hyp:hRV), [independent of covariates](hyp:hNoise), [covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the conditional-mean version is valid](hyp:hMean), [the identification side conditions hold](hyp:hSide), [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap), [the regression is bounded](hyp:hG), [the threshold is at least one](hyp:ht), [the tail covariate image is bounded above](hyp:hb), [the radial rate is antitone](hyp:hRp), [the regression equals the tail conditional regression almost surely](hyp:hreg), [the nuisance fits satisfy their stated tail error bounds](hyp:hNuisance), [the exponent estimate has the stated error](hyp:hErr), [the radial power is integrable](hyp:hRad), and [the score has a finite second moment](hyp:hLp), then [the doubly robust mean has the stated decomposition](goal). -/
-- @node: dr_mean_decomposition_of_score_moment
lemma dr_mean_decomposition_of_score_moment (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) (hSide : IdentificationSideConditions M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t eps a : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 1 ≤ t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hreg : IsTailRegressionVersion M t reg) (w : E.Om)
    (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w)
    (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t))
    (hLp : MemLp (score E .dr n w) 2 (obsTailLaw M t)) :
    DrMeanDecomposition E n t reg w := by
  let := obsTailLaw_probability M hRV t
  have htpos := zero_lt_one.trans_le ht
  have hProjection := tail_regression_normalized_projection M hRV hX hHom hMean
    hG htpos hb reg hreg
  have hBound := tail_regression_bound_of_normalized_projection M hX hHom
    hG htpos hb reg hProjection
  have hr := tail_regression_sections_integrable_of_bound M hRV hNoise hSide t
    (C + eBar M t) reg hreg.1 hBound
  have hg := fun b => fitted_regression_integrable_of_tail_regression E hRV
    Rp Rg Ralpha reg w hNuisance b (hr b)
  have hPseudo := pseudoOutcome_integrable_of_dr_score E hn hOverlap w
    (hLp.integrable (by norm_num)) hg
  have hObs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk
      (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  have hgPopulation (b : Bool) : Integrable
      (fun v => E.gHat n w (M.X v) b (direction M v)) (tailLaw M t) := by
    have hi := hg b
    rw [← observation_tailLaw_map M t] at hi
    exact hi.comp_aemeasurable hObs.aemeasurable
  have hAverage := dr_regression_average_of_normalized_projection E hRV hNoise
    hX hHom hMean hn hOverlap hG ht hb reg hreg.1 hProjection hr w
    hgPopulation hErr hRad
  have hContrast := tail_regression_contrast_integral_of_normalized_projection M hRV
    hNoise hX hHom hMean hSide hG htpos hb reg hreg.1 hProjection
  have hIdentity := dr_conditional_score_mean_of_regression_moments E hRV hNoise hX hHom
    hMean hn hOverlap hG ht hb Rp Rg Ralpha reg w hNuisance hPseudo hErr hRad
    hr hAverage hContrast
  exact dr_mean_decomposition_of_conditional_score_mean E hRV hX hHom hMean hn
    hOverlap hG ht hb Rp Rg Ralpha hRp reg hreg.1 w hNuisance hErr hRad hIdentity

end Papers.TbsExtremeEffects
