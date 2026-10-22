module
public import Papers.TbsExtremeEffects.Helpers.EtaDR
public import Papers.TbsExtremeEffects.Helpers.EtaIPW
public import Papers.TbsExtremeEffects.Helpers.ProductBounds

/-! Both population score identities on one nuisance event, with optional
second-moment control on that same event. -/

public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.unusedTactic false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- Given [regularly varying noise](hyp:hRV), [noise independence](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional-mean version](hyp:hMean), [identification side conditions](hyp:hSide), [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression bound](hyp:hG), [a threshold at least one](hyp:ht), [bounded tail error](hyp:hb), [a nonincreasing propensity rate](hyp:hRp), [a tail-regression version](hyp:hreg), [a nuisance event on the training sample](hyp:hNuisance), [integrable fitted pseudo-outcomes on that event](hyp:hInt), and [an integrable radial increment](hyp:hRad), [both score kinds are integrable and satisfy their respective population mean decompositions on the event](goal).
@node: joint_nuisance_score_mean_decompositions -/
lemma joint_nuisance_score_mean_decompositions (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) (hSide : IdentificationSideConditions M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t eps : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 1 ≤ t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hreg : IsTailRegressionVersion M t reg) (G : Set E.Om)
    (hNuisance : ∀ w ∈ G, NuisanceAt E n t eps Rp Rg Ralpha reg w)
    (hInt : FittedPseudoOutcomeIntegrable E n t G)
    (hRad : Integrable (fun v => radius M v ^ Ralpha n eps - 1) (tailLaw M t)) :
    (∀ kind, ∀ᵐ w ∂E.P, w ∈ G → Integrable (score E kind n w) (obsTailLaw M t)) ∧
    (∀ᵐ w ∂E.P, w ∈ G → DrMeanDecomposition E n t reg w) ∧
    (∀ᵐ w ∂E.P, w ∈ G → IpwMeanDecomposition E n t w) := by
  have htpos := zero_lt_one.trans_le ht
  have hProjection := tail_regression_normalized_projection M hRV hX hHom
    hMean hG htpos hb reg hreg
  have hBound := tail_regression_bound_of_normalized_projection M hX hHom
    hG htpos hb reg hProjection
  have hMoments := tail_regression_sections_integrable_of_bound M hRV hNoise
    hSide t (C + eBar M t) reg hreg.1 hBound
  have hContrast := tail_regression_contrast_integral_of_normalized_projection M hRV
    hNoise hX hHom hMean hSide hG htpos hb reg hreg.1 hProjection
  have hg : ∀ w ∈ G, ∀ b : Bool, Integrable
      (fun z : Obs q d => E.gHat n w z.1 b (obsDirection z)) (obsTailLaw M t) := by
    intro w hw b
    exact fitted_regression_integrable_of_tail_regression E hRV
      Rp Rg Ralpha reg w (hNuisance w hw) b (hMoments b)
  have hScores : ∀ kind, ∀ᵐ w ∂E.P, w ∈ G →
      Integrable (score E kind n w) (obsTailLaw M t) := by
    intro kind
    cases kind with
    | dr => exact dr_score_integrable_on_nuisance_event E hn hOverlap hInt hg
    | ipw => exact ipw_score_integrable_on_nuisance_event E hn hOverlap hInt
  refine ⟨hScores, ?_, ?_⟩
  · have hObs : Measurable (observation M) := by
      first | fun_prop | skip
      exact M.measurable_X.prodMk
        (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
    have hgPopulation : ∀ w ∈ G, ∀ b : Bool, Integrable
        (fun v => E.gHat n w (M.X v) b (direction M v)) (tailLaw M t) := by
      intro w hw b
      have hi := hg w hw b
      rw [← observation_tailLaw_map M t] at hi
      exact hi.comp_aemeasurable hObs.aemeasurable
    filter_upwards [hInt] with w hi hw
    have hErr : |M.alpha - E.alphaHat n w| ≤ Ralpha n eps := by
      simpa only [abs_sub_comm] using (hNuisance w hw).1
    have hAverage := dr_regression_average_of_normalized_projection E hRV hNoise
      hX hHom hMean hn hOverlap hG ht hb reg hreg.1 hProjection hMoments w
      (hgPopulation w hw) hErr hRad
    have hIdentity := dr_conditional_score_mean_of_regression_moments E hRV hNoise
      hX hHom hMean hn hOverlap hG ht hb Rp Rg Ralpha reg w (hNuisance w hw)
      (pseudoOutcome_integrable_of_absolute E n t w (hi hw)) hErr hRad hMoments
      hAverage hContrast
    exact dr_mean_decomposition_of_conditional_score_mean E hRV hX hHom hMean
      hn hOverlap hG ht hb Rp Rg Ralpha hRp reg hreg.1 w (hNuisance w hw)
      hErr hRad hIdentity
  · filter_upwards [hScores .ipw] with w hi hw
    have hErr : |M.alpha - E.alphaHat n w| ≤ Ralpha n eps := by
      simpa only [abs_sub_comm] using (hNuisance w hw).1
    have hOutcome := ipw_outcome_score_mean_of_integrable E hRV hMean n t w (hi hw)
    have hIdentity := ipw_conditional_score_mean_of_outcome_score_mean E hRV hNoise
      hX hHom hMean hn hOverlap hG ht hb w hErr hRad hOutcome
    exact ipw_mean_decomposition_of_conditional_score_mean E hRV hX hHom hMean
      hn hOverlap hG ht hb Rp Rg Ralpha hRp reg w (hNuisance w hw) hErr hRad hIdentity

/-- Given [regularly varying noise](hyp:hRV), [noise independence](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional-mean version](hyp:hMean), [identification side conditions](hyp:hSide), [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression bound](hyp:hGBound), [a threshold at least one](hyp:ht), [bounded tail error](hyp:hb), [nuisance error bounds](hyp:hErrors), [nuisance integrability guarantees](hyp:hInt), [an accuracy level in `(0,1)`](hyp:heps,heps1), and [an integrable radial increment](hyp:hRad), [there are a regression version and measurable high-probability event on which both population score decompositions hold, with the stated optional variance control](goal).
@node: product_population_nuisance_event -/
lemma product_population_nuisance_event (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) (hSide : IdentificationSideConditions M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t eps : ℝ}
    (hOverlap : EstimatedOverlap E c) (hGBound : GBound M C) (ht : 1 ≤ t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hErrors : NuisanceErrorBounds E n Rp Rg Ralpha)
    (hInt : NuisanceIntegrability E n Rp Rg Ralpha)
    (heps : 0 < eps) (heps1 : eps < 1) (V : ℝ)
    (hRad : Integrable (fun v => radius M v ^ Ralpha n eps - 1) (tailLaw M t)) :
    ∃ (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G : Set E.Om),
      MeasurableSet[trainSigma E n] G ∧ 1 - eps ≤ E.P.real G ∧
      (∀ w ∈ G, NuisanceAt E n t eps Rp Rg Ralpha reg w) ∧
      (∀ kind, ∀ᵐ w ∂E.P, w ∈ G → Integrable (score E kind n w) (obsTailLaw M t)) ∧
      (∀ᵐ w ∂E.P, w ∈ G → DrMeanDecomposition E n t reg w) ∧
      (∀ᵐ w ∂E.P, w ∈ G → IpwMeanDecomposition E n t w) ∧
      (secondMomentsOnNuisance E n t eps Rp Rg Ralpha V →
        ∀ kind, ∀ᵐ w ∂E.P, w ∈ G →
          MemLp (score E kind n w) 2 (obsTailLaw M t) ∧
            (scoreVariance E kind n t w).toReal ≤ V) := by
  classical
  have hEvent : ∃ reg, IsTailRegressionVersion M t reg ∧ ∃ G : Set E.Om,
      MeasurableSet[trainSigma E n] G ∧ 1 - eps ≤ E.P.real G ∧
      (∀ w ∈ G, NuisanceAt E n t eps Rp Rg Ralpha reg w) ∧
      FittedPseudoOutcomeIntegrable E n t G ∧
      (secondMomentsOnNuisance E n t eps Rp Rg Ralpha V →
        ∀ w ∈ G, ∀ kind, MemLp (score E kind n w) 2 (obsTailLaw M t) ∧
          scoreSecondMoment E kind n t w ≤ V) := by
    by_cases hm : secondMomentsOnNuisance E n t eps Rp Rg Ralpha V
    · obtain ⟨reg, hreg, G, hG, hprob, hIntG, hNG⟩ := hm
      exact ⟨reg, hreg, G, hG, hprob, fun w hw => (hNG w hw).1,
        hIntG, fun _ w hw => (hNG w hw).2⟩
    · obtain ⟨reg, hreg, hEvents⟩ := hInt t (zero_lt_one.trans_le ht)
      obtain ⟨G, hG, hprob, hNG, hIntG⟩ := hEvents eps heps heps1
      exact ⟨reg, hreg, G, hG, hprob, hNG, hIntG, fun h => (hm h).elim⟩
  obtain ⟨reg, hreg, G, hG, hprob, hNG, hIntG, hMom⟩ := hEvent
  obtain ⟨hScores, hDR, hIPW⟩ := joint_nuisance_score_mean_decompositions E hRV
    hNoise hX hHom hMean hSide hn hOverlap hGBound ht hb Rp Rg Ralpha
    ((nuisanceErrorBounds_components _ _ _ _ _ hErrors).1 eps heps heps1).1.2 reg hreg G hNG hIntG hRad
  refine ⟨reg, G, hG, hprob, hNG, hScores, hDR, hIPW, ?_⟩
  intro hm kind
  letI := obsTailLaw_probability M hRV t
  apply Eventually.of_forall
  intro w hw
  have hSecond := hMom hm w hw kind
  refine ⟨hSecond.1, ?_⟩
  exact (variance_le_expectation_sq hSecond.1.aestronglyMeasurable).trans hSecond.2

end Papers.TbsExtremeEffects
