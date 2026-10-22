module
public import Papers.TbsExtremeEffects.Helpers.AngularDual
public import Papers.TbsExtremeEffects.Helpers.ScoreMeasurability
public import Papers.TbsExtremeEffects.Helpers.DRConditionalMean
public import Papers.TbsExtremeEffects.Helpers.Count
public import Papers.TbsExtremeEffects.Helpers.DRScoreIntegrability
public import Papers.TbsExtremeEffects.Helpers.DRAugmentation
public import Papers.TbsExtremeEffects.Helpers.TrainingScore
public import Papers.TbsExtremeEffects.Helpers.TailRegressionSections
public import Papers.TbsExtremeEffects.Helpers.UnweightedRegressionProjection
public import Papers.TbsExtremeEffects.Helpers.GeneralizedRegressionProjection

/-! The DR first-factor bound, including the untruncated variance alternative. -/

@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical
variable {q d m : ℕ}
variable {M : ExtremeModel q d}

/-- If [the noise has regularly varying tails](hyp:hRV), [the nuisance fit satisfies its error
bounds](hyp:hNuisance), and [the corresponding population regression section is integrable](hyp:hreg),
then [the fitted regression section is integrable under the evaluation observation law](goal). -/
-- @node: fitted_regression_integrable_of_tail_regression
lemma fitted_regression_integrable_of_tail_regression (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) {n : ℕ} {t eps : ℝ}
    (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (w : E.Om) (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w)
    (a : Bool) (hreg : Integrable
      (fun v => reg (M.X v, a, direction M v)) (tailLaw M t)) :
    Integrable (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z))
      (obsTailLaw M t) := by
  let := tailLaw_probability M hRV t
  have hg : Measurable (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z)) := by
    first | fun_prop | skip
    exact (E.gHat_training n).comp (measurable_const.prodMk
      (measurable_fst.prodMk (measurable_const.prodMk (by
        try unfold obsDirection
        fun_prop))))
  have hObs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk
      (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  rw [obsTailLaw_eq_map_tailLaw]
  apply (integrable_map_measure hg.aestronglyMeasurable hObs.aemeasurable).mpr
  have herror := ae_of_ae_map
    (M.measurable_X.prodMk (measurable_direction M)).aemeasurable (hNuisance.2.2 a)
  have hbound : ∀ᵐ v ∂tailLaw M t,
      ‖E.gHat n w (M.X v) a (direction M v)‖ ≤
        ‖reg (M.X v, a, direction M v)‖ + Rg (trainCount E n t w) eps := by
    filter_upwards [herror] with v hv
    change |reg (M.X v, a, direction M v) - E.gHat n w (M.X v) a
      (direction M v)| ≤ _ at hv
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      _ ≤ |E.gHat n w (M.X v) a (direction M v) - reg (M.X v, a, direction M v)| +
          |reg (M.X v, a, direction M v)| := by
        simpa only [sub_zero] using abs_sub_le (E.gHat n w (M.X v) a (direction M v))
          (reg (M.X v, a, direction M v)) 0
      _ ≤ _ := by rw [abs_sub_comm]; linarith only [hv]
  apply (hreg.norm.add (integrable_const (Rg (trainCount E n t w) eps))).mono'
  · exact (hg.comp hObs).aestronglyMeasurable
  · change ∀ᵐ v ∂tailLaw M t, ‖E.gHat n w (M.X v) a (direction M v)‖ ≤
      ‖reg (M.X v, a, direction M v)‖ + Rg (trainCount E n t w) eps
    exact hbound

/-- If [the noise has regularly varying tails](hyp:hRV), [it is independent of the covariates](hyp:hNoise),
[covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the conditional
mean version is available](hyp:hMean), [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap),
[the angular regression is bounded](hyp:hG), [the threshold is at least one](hyp:ht), [the tail envelope
is bounded above](hyp:hb), [the nuisance fit satisfies its error bounds](hyp:hNuisance), [the pseudo-outcome
is integrable](hyp:hPseudo), [the exponent error is bounded](hyp:hErr), [the radial error is integrable](hyp:hRad),
[both regression sections are integrable](hyp:hreg), [the IPW and augmentation means average to the fitted
regression mean](hyp:hAverage), and [that regression contrast equals the normalized contrast](hyp:hTarget),
then [the conditional DR-score mean identity holds](goal). -/
-- @node: dr_conditional_score_mean_of_regression_moments
lemma dr_conditional_score_mean_of_regression_moments (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) {n : ℕ} (hn : EvenSampleSize n)
    {c C t eps a : ℝ} (hOverlap : EstimatedOverlap E c) (hG : GBound M C)
    (ht : 1 ≤ t) (hb : BddAbove (M.e '' Set.Ici t))
    (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w)
    (hPseudo : Integrable (pseudoOutcome E n w) (obsTailLaw M t))
    (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t))
    (hreg : ∀ b : Bool, Integrable (fun v => reg (M.X v, b, direction M v))
      (tailLaw M t))
    (hAverage : (∫ v, ipwFittedMeanIntegrand E n w v ∂tailLaw M t) +
      (∫ v, drAugmentationMean E n w v ∂tailLaw M t) =
        ∫ v, drFittedRegressionMean E n reg w v ∂tailLaw M t)
    (hTarget : (∫ v, reg (M.X v, true, direction M v) -
      reg (M.X v, false, direction M v) ∂tailLaw M t) =
        ∫ v, normalizedRegressionContrast M v ∂tailLaw M t) :
    DrConditionalScoreMean E n t reg w := by
  have hi := ipw_score_integrable_of_pseudoOutcome E hn hOverlap w hPseudo
  have hOutcome := ipw_outcome_score_mean_of_integrable E hRV hMean n t w hi
  have hIpw := ipw_conditional_score_mean_of_outcome_score_mean E hRV hNoise
    hX hHom hMean hn hOverlap hG ht hb w hErr hRad hOutcome
  have hg := fun b => fitted_regression_integrable_of_tail_regression E hRV
    Rp Rg Ralpha reg w hNuisance b (hreg b)
  exact dr_conditional_score_mean_of_treatment_averaged E hRV hNoise hn hOverlap
    reg w hi hg ⟨hIpw, hAverage, (hreg true).sub (hreg false), hTarget⟩


/-- For the [experiment and sample size](hyp:E,n), [threshold and error level](hyp:t,delta), [overlap,
regression, and exponent constants](hyp:c,Cgb,K), [nuisance-rate functions](hyp:Rp,Rg,Ralpha), [sampling
bound](hyp:B), and [auxiliary event](hyp:N), [the truncated-transfer data condition](goal) records:
[a high-probability good event](step:1), [score integrability on that event](step:2),
[a remainder bound for its conditional score means](step:3), and [a transfer bound for failures](step:4). -/
-- @node: DrTruncatedTransferData
noncomputable def DrTruncatedTransferData (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (B : E.Om → ℝ) (N : Set E.Om) : Prop :=
  let R := {w | |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
    scoreSamplingRadius (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) (B w) delta}
  ∃ G : Set E.Om, 1 - delta / 4 ≤ E.P.real G ∧
    (∀ w ∈ G, Integrable (score E .dr n w) (obsTailLaw M t)) ∧
    (∀ w ∈ G, |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| ≤
      etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w) ∧
    E.P.real ((G ∩ N) \ R) ≤ ∫ w, if w ∈ G ∩ N then
      scoreIidFailure (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) (B w) delta
      else 0 ∂E.P

/-- If [the noise has regularly varying tails](hyp:hRV), [the training exponent is valid](hyp:hTraining),
[the sampling bound is measurable](hyp:hB), and [the truncated-transfer data condition holds](hyp:h), then
[the corresponding truncated law-transfer condition holds](goal). -/
-- @node: dr_truncated_lawTransfer_of_data
lemma dr_truncated_lawTransfer_of_data (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) {n : ℕ} (hTraining : ExponentTraining E n)
    (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (B : E.Om → ℝ) (hB : Measurable B) (N : Set E.Om)
    (h : DrTruncatedTransferData E n t delta c Cgb K Rp Rg Ralpha B N) :
    DrTruncatedLawTransfer E n t delta c Cgb K Rp Rg Ralpha B N := by
  obtain ⟨G, hGprob, hInt, hMean, hTransfer⟩ := h
  exact ⟨G, hGprob, hInt, hMean,
    measurableSet_score_truncation_event E .dr hRV hTraining t delta B hB, hTransfer⟩

/-- For the [experiment and sample size](hyp:E,n), [threshold and error level](hyp:t,delta), [regression
function](hyp:reg), and [good and auxiliary events](hyp:G,N), [the variance conditional-law condition](goal)
requires [a conditional DR mean decomposition on the good event](step:1) and [a variance sampling-failure
transfer bound](step:2). -/
-- @node: DrVarianceConditionalLaw
noncomputable def DrVarianceConditionalLaw (E : NeteExperiment M)
    (n : ℕ) (t delta : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G N : Set E.Om) : Prop :=
  let R := {w | |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
    Real.sqrt (4 * (scoreVariance E .dr n t w).toReal / (delta * evalCount E n t w))}
  (∀ w ∈ G, DrMeanDecomposition E n t reg w) ∧
    E.P.real ((G ∩ N) \ R) ≤ ∫ w, if w ∈ G ∩ N then
      scoreIidVarianceFailure (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) delta
      else 0 ∂E.P

/-- If [the noise has regularly varying tails](hyp:hRV), [the exponent training condition holds](hyp:hTraining),
[the error level is positive](hyp:hd), [the auxiliary event is measurable](hyp:hN), [the good event has the
stated probability](hyp:hGprob), [the auxiliary event has the stated probability](hyp:hNprob), [its evaluation
count is sufficiently large and nonzero](hyp:hNcount), [on the good event the nuisance bounds and finite score
variance hold](hyp:hNuisance), [the DR mean-bound provider holds](hyp:hProvider), and [the variance conditional-law
condition holds](hyp:hLaw), then [with probability at least `1 - delta`, the evaluation count is large enough, the score variance is finite, and the DR error is at most its variance radius plus its remainder](goal). -/
-- @node: dr_variance_probability_of_conditional_law
lemma dr_variance_probability_of_conditional_law (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (n : ℕ) (hTraining : ExponentTraining E n)
    (t delta c Cgb K : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (G N : Set E.Om)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hd : 0 < delta) (hN : MeasurableSet N)
    (hGprob : 1 - delta / 4 ≤ E.P.real G) (hNprob : 1 - delta / 4 ≤ E.P.real N)
    (hNcount : ∀ w ∈ N, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ) ∧
      evalCount E n t w ≠ 0)
    (hNuisance : ∀ w ∈ G, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w ∧
      scoreVariance E .dr n t w ≠ ∞)
    (hProvider : DrMeanBoundProvider E n t (delta / 4) c Cgb K Rp Rg Ralpha)
    (hLaw : DrVarianceConditionalLaw E n t delta reg G N) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      scoreVariance E .dr n t w ≠ ∞ ∧
      (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder) |etaEstimate E .dr n t w - etaTarget M|
        (scoreVariance E .dr n t w).toReal delta (evalCount E n t w)
        (etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w)} := by
  let := obsTailLaw_probability M hRV t
  obtain ⟨hIdentity, hTransfer⟩ := hLaw
  have hR := measurableSet_score_variance_event E .dr hRV hTraining t delta
  have hf : ∀ᵐ w ∂E.P, w ∈ G → MemLp (score E .dr n w) 2 (obsTailLaw M t) := by
    apply Eventually.of_forall
    intro w hw
    apply (evariance_lt_top_iff_memLp
      (measurable_score_frozen E .dr n w).aestronglyMeasurable).mp
    exact lt_top_iff_ne_top.mpr (hNuisance w hw).2
  have hprob := score_variance_probability_of_transfer_ae E.P (obsTailLaw M t)
    (fun w => score E .dr n w) (evalCount E n t) (etaEstimate E .dr n t)
    G N hN hd hGprob hNprob (fun w hw => Nat.pos_of_ne_zero (hNcount w hw).2)
    hf hR hTransfer
  apply hprob.trans
  apply measureReal_mono (h₂ := measure_ne_top E.P _)
  intro w hw
  refine ⟨(hNcount w hw.1.2).1, (hNuisance w hw.1.1).2, ?_⟩
  exact dr_variance_bound_of_components E n t delta c Cgb K Rp Rg Ralpha w
    hw.2 (hProvider reg w (hNuisance w hw.1.1).1 (hIdentity w hw.1.1))

/-- For the [experiment and sample size](hyp:E,n), [threshold and error level](hyp:t,delta), [overlap,
regression, and exponent constants](hyp:c,Cgb,K), [nuisance-rate functions](hyp:Rp,Rg,Ralpha), [sampling
bound](hyp:B), and [auxiliary event](hyp:N), [the truncated conditional-mean data condition](goal) records:
[a tail regression version](step:1), [a high-probability good event](step:2), [nuisance
bounds there](step:3), [score integrability there](step:4), [conditional score means there](step:5), and
[a sampling-failure transfer bound](step:6). -/
-- @node: DrTruncatedConditionalMeanData
noncomputable def DrTruncatedConditionalMeanData (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (B : E.Om → ℝ) (N : Set E.Om) : Prop :=
  let R := {w | |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
    scoreSamplingRadius (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) (B w) delta}
  ∃ reg, IsTailRegressionVersion M t reg ∧ ∃ G : Set E.Om,
    1 - delta / 4 ≤ E.P.real G ∧
    (∀ w ∈ G, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w) ∧
    (∀ w ∈ G, Integrable (score E .dr n w) (obsTailLaw M t)) ∧
    (∀ w ∈ G, DrConditionalScoreMean E n t reg w) ∧
    E.P.real ((G ∩ N) \ R) ≤ ∫ w, if w ∈ G ∩ N then
      scoreIidFailure (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) (B w) delta
      else 0 ∂E.P

/-- If [the DR mean-bound provider holds](hyp:hProvider), [measurable nuisance fits with conditional score means
have the DR decomposition](hyp:hClosure), and [the truncated conditional-mean data condition holds](hyp:hData),
then [the truncated-transfer data condition holds](goal). -/
-- @node: dr_truncated_data_of_conditional_mean
lemma dr_truncated_data_of_conditional_mean (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (B : E.Om → ℝ) (N : Set E.Om)
    (hProvider : DrMeanBoundProvider E n t (delta / 4) c Cgb K Rp Rg Ralpha)
    (hClosure : ∀ reg, Measurable reg → ∀ w,
      NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w →
      DrConditionalScoreMean E n t reg w → DrMeanDecomposition E n t reg w)
    (hData : DrTruncatedConditionalMeanData E n t delta c Cgb K Rp Rg Ralpha B N) :
    DrTruncatedTransferData E n t delta c Cgb K Rp Rg Ralpha B N := by
  obtain ⟨reg, hreg, G, hGprob, hNuisance, hInt, hIdentity, hTransfer⟩ := hData
  refine ⟨G, hGprob, hInt, ?_, hTransfer⟩
  intro w hw
  exact hProvider reg w (hNuisance w hw)
    (hClosure reg hreg.1 w (hNuisance w hw) (hIdentity w hw))

/-- For the [experiment and sample size](hyp:E,n), [threshold and error level](hyp:t,delta), [regression
function](hyp:reg), and [good and auxiliary events](hyp:G,N), [the variance conditional-mean law](goal)
requires [conditional DR score means on the good event](step:1) and [a variance sampling-failure transfer
bound](step:2). -/
-- @node: DrVarianceConditionalMeanLaw
noncomputable def DrVarianceConditionalMeanLaw (E : NeteExperiment M)
    (n : ℕ) (t delta : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G N : Set E.Om) : Prop :=
  let R := {w | |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
    Real.sqrt (4 * (scoreVariance E .dr n t w).toReal / (delta * evalCount E n t w))}
  (∀ w ∈ G, DrConditionalScoreMean E n t reg w) ∧
    E.P.real ((G ∩ N) \ R) ≤ ∫ w, if w ∈ G ∩ N then
      scoreIidVarianceFailure (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) delta
      else 0 ∂E.P

/-- If [every conditional DR score mean on the good event yields its mean decomposition](hyp:hClosure) and
[the variance conditional-mean law holds](hyp:hLaw), then [the variance conditional-law condition holds](goal). -/
-- @node: dr_variance_law_of_conditional_mean
lemma dr_variance_law_of_conditional_mean (E : NeteExperiment M)
    (n : ℕ) (t delta : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G N : Set E.Om)
    (hClosure : ∀ w ∈ G, DrConditionalScoreMean E n t reg w →
      DrMeanDecomposition E n t reg w)
    (hLaw : DrVarianceConditionalMeanLaw E n t delta reg G N) :
    DrVarianceConditionalLaw E n t delta reg G N := by
  exact ⟨fun w hw => hClosure w hw (hLaw.1 w hw), hLaw.2⟩

/-- For the [experiment and sample size](hyp:E,n), [threshold, error level, and sampling bound](hyp:t,delta,B),
[regression function](hyp:reg), and [good and auxiliary events](hyp:G,N), [the truncated conditional law](goal)
requires [integrable fitted regression sections on the good event](step:1), [treatment-averaged DR means there](step:2),
and [a sampling-failure transfer bound](step:3). -/
-- @node: DrTruncatedConditionalLaw
noncomputable def DrTruncatedConditionalLaw (E : NeteExperiment M)
    (n : ℕ) (t delta : ℝ) (B : E.Om → ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G N : Set E.Om) : Prop :=
  let R := {w | |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
    scoreSamplingRadius (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) (B w) delta}
  (∀ w ∈ G, ∀ a : Bool, Integrable
    (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z)) (obsTailLaw M t)) ∧
  (∀ w ∈ G, DrTreatmentAveragedMean E n t reg w) ∧
  E.P.real ((G ∩ N) \ R) ≤ ∫ w, if w ∈ G ∩ N then
    scoreIidFailure (obsTailLaw M t) (score E .dr n w) (evalCount E n t w) (B w) delta
    else 0 ∂E.P

/-- If [the noise has regularly varying tails](hyp:hRV), [it is independent of covariates](hyp:hNoise), [the
sample size is even](hyp:hn), [exponent training holds](hyp:hTraining), [estimated overlap holds](hyp:hOverlap),
[the sampling bound is measurable](hyp:hBmeas), [the error level is positive](hyp:hd), [the sampling bound is
positive](hyp:hB), [the auxiliary event is measurable](hyp:hN), [the good event has the stated probability](hyp:hGprob),
[the auxiliary event has the stated probability](hyp:hNprob), [its evaluation count is sufficiently large and
nonzero](hyp:hNcount), [nuisance bounds hold on the good event](hyp:hNuisance), [the fitted pseudo-outcome is
integrable there](hyp:hInt), [the DR mean-bound provider holds](hyp:hProvider), [conditional means imply the
mean decomposition](hyp:hMean), and [the truncated conditional law holds](hyp:hLaw), then [with probability at least `1 - delta`, the evaluation count is large enough and the DR error is at most its truncated sampling radius plus its remainder](goal). -/
-- @node: dr_truncated_probability_of_conditional_law
lemma dr_truncated_probability_of_conditional_law (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M) {n : ℕ} (hn : EvenSampleSize n)
    (hTraining : ExponentTraining E n)
    {t delta c Cgb K : ℝ} (hOverlap : EstimatedOverlap E c)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (B : E.Om → ℝ) (hBmeas : Measurable B)
    (G N : Set E.Om)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hd : 0 < delta) (hB : ∀ w, 0 < B w) (hN : MeasurableSet N)
    (hGprob : 1 - delta / 4 ≤ E.P.real G) (hNprob : 1 - delta / 4 ≤ E.P.real N)
    (hNcount : ∀ w ∈ N, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ) ∧
      evalCount E n t w ≠ 0)
    (hNuisance : ∀ w ∈ G, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w)
    (hInt : FittedPseudoOutcomeIntegrable E n t G)
    (hProvider : DrMeanBoundProvider E n t (delta / 4) c Cgb K Rp Rg Ralpha)
    (hMean : ∀ w ∈ G, DrConditionalScoreMean E n t reg w → DrMeanDecomposition E n t reg w)
    (hLaw : DrTruncatedConditionalLaw E n t delta B reg G N) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      |etaEstimate E .dr n t w - etaTarget M| ≤
        etaTruncatedError E .dr c Cgb K Rp Rg Ralpha n t delta B w} := by
  let := obsTailLaw_probability M hRV t
  obtain ⟨hg, hIdentity, hTransfer⟩ := hLaw
  have hR := measurableSet_score_truncation_event E .dr hRV hTraining t delta B hBmeas
  have hScore := dr_score_integrable_on_nuisance_event E hn hOverlap hInt hg
  have hf : ∀ᵐ w ∂E.P, w ∈ G →
      Measurable (score E .dr n w) ∧ Integrable (score E .dr n w) (obsTailLaw M t) := by
    filter_upwards [hScore] with w hw hG
    exact ⟨measurable_score_frozen E .dr n w, hw hG⟩
  have hprob := score_sampling_probability_of_transfer_ae E.P (obsTailLaw M t)
    (fun w => score E .dr n w) (evalCount E n t) B (etaEstimate E .dr n t)
    G N hN hd hGprob hNprob (fun w hw => Nat.pos_of_ne_zero (hNcount w hw).2)
    (fun w => (hB w).le) hf hR hTransfer
  apply hprob.trans
  apply ENNReal.toReal_mono (measure_ne_top E.P _)
  apply measure_mono_ae
  filter_upwards [ipw_score_integrable_on_nuisance_event E hn hOverlap hInt] with w hi
  intro hw
  refine ⟨(hNcount w hw.1.2).1, ?_⟩
  calc
    _ ≤ |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| +
        |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| := abs_sub_le _ _ _
    _ ≤ scoreSamplingRadius (obsTailLaw M t) (score E .dr n w)
        (evalCount E n t w) (B w) delta +
        etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w :=
      add_le_add hw.2 (hProvider reg w (hNuisance w hw.1.1)
        (hMean w hw.1.1 (dr_conditional_score_mean_of_treatment_averaged E hRV hNoise
          hn hOverlap reg w (hi hw.1.1) (hg w hw.1.1) (hIdentity w hw.1.1))))
    _ = _ := rfl

/-- If [the auxiliary event has the stated evaluation-count lower bound](hyp:hNcount), [the conditional DR
mean error is bounded almost surely on the good event](hyp:hMean), and [the sampling event has probability at
least `1 - delta`](hyp:hSampling), then [the event that the evaluation count is large enough and the DR error is at most its truncated radius plus remainder has probability at least `1 - delta`](goal). -/
-- @node: dr_truncated_probability_of_sampling_event
lemma dr_truncated_probability_of_sampling_event (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (B : E.Om → ℝ) (G N : Set E.Om)
    (hNcount : ∀ w ∈ N, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ))
    (hMean : ∀ᵐ w ∂E.P, w ∈ G →
      |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| ≤
        etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w)
    (hSampling : 1 - delta ≤ E.P.real ((G ∩ N) ∩ {w |
      |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
        scoreSamplingRadius (obsTailLaw M t) (score E .dr n w)
          (evalCount E n t w) (B w) delta})) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      |etaEstimate E .dr n t w - etaTarget M| ≤
        etaTruncatedError E .dr c Cgb K Rp Rg Ralpha n t delta B w} := by
  apply hSampling.trans
  apply ENNReal.toReal_mono (measure_ne_top E.P _)
  apply measure_mono_ae
  filter_upwards [hMean] with w hm
  intro hw
  refine ⟨hNcount w hw.1.2, ?_⟩
  calc
    _ ≤ |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| +
        |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| := abs_sub_le _ _ _
    _ ≤ scoreSamplingRadius (obsTailLaw M t) (score E .dr n w)
        (evalCount E n t w) (B w) delta +
        etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w :=
      add_le_add hw.2 (hm hw.1.1)
    _ = _ := rfl

/-- If [the auxiliary event has the stated evaluation-count lower bound](hyp:hNcount), [the score variance is
finite on the good event](hyp:hFinite), [the conditional DR mean error is bounded almost surely there](hyp:hMean),
and [the variance sampling event has probability at least `1 - delta`](hyp:hSampling), then [the event that the evaluation count is large enough, score variance is finite, and DR error is at most its variance radius plus remainder has probability at least `1 - delta`](goal). -/
-- @node: dr_variance_probability_of_sampling_event
lemma dr_variance_probability_of_sampling_event (E : NeteExperiment M)
    (n : ℕ) (t delta c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (G N : Set E.Om)
    (hNcount : ∀ w ∈ N, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ))
    (hFinite : ∀ w ∈ G, scoreVariance E .dr n t w ≠ ∞)
    (hMean : ∀ᵐ w ∂E.P, w ∈ G →
      |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| ≤
        etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w)
    (hSampling : 1 - delta ≤ E.P.real ((G ∩ N) ∩ {w |
      |etaEstimate E .dr n t w - ∫ z, score E .dr n w z ∂obsTailLaw M t| ≤
        Real.sqrt (4 * (scoreVariance E .dr n t w).toReal / (delta * evalCount E n t w))})) :
    1 - delta ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      scoreVariance E .dr n t w ≠ ∞ ∧
      (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder) |etaEstimate E .dr n t w - etaTarget M|
        (scoreVariance E .dr n t w).toReal delta (evalCount E n t w)
        (etaRemainder E .dr c Cgb K Rp Rg Ralpha n t (delta / 4) w)} := by
  apply hSampling.trans
  apply ENNReal.toReal_mono (measure_ne_top E.P _)
  apply measure_mono_ae
  filter_upwards [hMean] with w hm
  intro hw
  exact ⟨hNcount w hw.1.2, hFinite w hw.1.1,
    dr_variance_bound_of_components E n t delta c Cgb K Rp Rg Ralpha w
      hw.2 (hm hw.1.1)⟩

/-- If [the model is consistent](hyp:hConsistency), [exogeneity holds](hyp:hExogeneity), [the noise has regularly
varying tails](hyp:hRV), [it is independent of covariates](hyp:hNoise), [covariates are bounded](hyp:hX), [the model
is asymptotically homogeneous](hyp:hHomogeneity), [a Pareto tail model exists](hyp:hTail), [the tail exponent is
below the second-order exponent](hyp:hAlpha), [the conditional mean version is available](hyp:hMean), [the
identification side conditions hold](hyp:hSide), [the angular regression is bounded](hyp:hGBound), [the exponent
allowance is positive](hyp:ha0), and [it is below the model's second-order exponent](hyp:ha0beta), then [there is
a threshold after which both DR rate conclusions hold for every overlapping experiment](goal). -/
-- @node: lem:eta-rate
lemma eta_dr_rate (M : ExtremeModel q d)
    (tp : TailParams)
    (hConsistency : Consistency M) (hExogeneity : Exogeneity M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHomogeneity : AsymptoticHomogeneity M)
    (hTail : Nonempty (ParetoTailModel M m tp))
    (hAlpha : AlphaLtBeta M)
    (hMean : ConditionalMeanVersion M)
    (hSide : IdentificationSideConditions M)
    (Cgb : ℝ) (hGBound : GBound M Cgb)
    (a0 : ℝ) (ha0 : 0 < a0) (ha0beta : a0 < M.beta) :
    ∃ t0 : ℝ, 1 ≤ t0 ∧
      ∀ (E : NeteExperiment M) (c : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ),
        EstimatedOverlap E c →
          EtaRateConclusion E .dr c Cgb (4 / (M.beta - a0)) t0 a0 Rp Rg Ralpha ∧
          EtaVarianceConclusion E .dr c Cgb (4 / (M.beta - a0)) t0 a0 Rp Rg Ralpha := by
  let K : ℝ := 4 / (M.beta - a0)
  obtain ⟨T, hT, hExponent⟩ :=
    dr_exponent_mean_explicit_bound M hRV hX hHomogeneity hGBound ha0 ha0beta
  obtain ⟨Th, hTh⟩ := eventually_atTop.mp (eBar_eventually_bddAbove M hHomogeneity)
  obtain ⟨Kr, Tr, hKr, hTr, hPower⟩ :=
    tail_power_increment_uniform_bound M hRV ha0 ha0beta
  let t0 := max (max T Th) Tr
  have ht0 : T ≤ t0 := (le_max_left T Th).trans (le_max_left _ _)
  have hth0 : Th ≤ t0 := (le_max_right T Th).trans (le_max_left _ _)
  have htr0 : Tr ≤ t0 := le_max_right _ _
  refine ⟨t0, hT.trans ht0, ?_⟩
  intro E c Rp Rg Ralpha hOverlap
  have hRegressionClosure : ∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha →
      ∀ t, t0 ≤ t → ∀ delta, 0 < delta → delta < 1 → Ralpha n (delta / 4) ≤ a0 →
      ∀ reg G, IsTailRegressionVersion M t reg →
        (∀ w ∈ G, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w) →
        FittedPseudoOutcomeIntegrable E n t G →
        (∀ w ∈ G, ∀ b : Bool, Integrable
          (fun z : Obs q d => E.gHat n w z.1 b (obsDirection z)) (obsTailLaw M t)) ∧
        (∀ᵐ w ∂E.P, w ∈ G → DrConditionalScoreMean E n t reg w) := by
    intro n hn hNuisance t ht delta hd hd1 ha reg G hreg hGNuisance hGInt
    have htpos : 0 < t := zero_lt_one.trans_le (hT.trans (ht0.trans ht))
    have hregProjection := tail_regression_normalized_projection M hRV hX hHomogeneity
      hMean hGBound htpos (hTh t (hth0.trans ht)) reg hreg
    have hregBound := tail_regression_bound_of_normalized_projection M hX hHomogeneity
      hGBound htpos (hTh t (hth0.trans ht)) reg hregProjection
    have hregMoments := tail_regression_sections_integrable_of_bound M hRV hNoise
      hSide t (Cgb + eBar M t) reg hreg.1 hregBound
    have hContrast := tail_regression_contrast_integral_of_normalized_projection M hRV
      hNoise hX hHomogeneity hMean hSide hGBound htpos
      (hTh t (hth0.trans ht)) reg hreg.1 hregProjection
    refine ⟨fun w hw b => fitted_regression_integrable_of_tail_regression E hRV
      Rp Rg Ralpha reg w (hGNuisance w hw) b (hregMoments b), ?_⟩
    have hErrors := (nuisanceErrorBounds_components _ _ _ _ _ hNuisance).1 (delta / 4) (by positivity) (by linarith)
    have hRad := (hPower t (htr0.trans ht) (Ralpha n (delta / 4))
      (hErrors.2.2.1 n) ha).1
    have hObs : Measurable (observation M) := by
      first | fun_prop | skip
      exact M.measurable_X.prodMk
        (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
    have hgPopulation : ∀ w ∈ G, ∀ b : Bool,
        Integrable (fun v => E.gHat n w (M.X v) b (direction M v)) (tailLaw M t) := by
      intro w hw b
      have hg := fitted_regression_integrable_of_tail_regression E hRV
        Rp Rg Ralpha reg w (hGNuisance w hw) b (hregMoments b)
      rw [← observation_tailLaw_map M t] at hg
      exact hg.comp_aemeasurable hObs.aemeasurable
    filter_upwards [hGInt] with w hi hw
    have hErr : |M.alpha - E.alphaHat n w| ≤ Ralpha n (delta / 4) := by
      simpa only [abs_sub_comm] using (hGNuisance w hw).1
    have hAverage := dr_regression_average_of_normalized_projection E hRV hNoise
      hX hHomogeneity hMean hn hOverlap hGBound (hT.trans (ht0.trans ht))
      (hTh t (hth0.trans ht)) reg hreg.1 hregProjection hregMoments w
      (hgPopulation w hw) hErr hRad
    exact dr_conditional_score_mean_of_regression_moments E hRV hNoise hX hHomogeneity
      hMean hn hOverlap hGBound (hT.trans (ht0.trans ht)) (hTh t (hth0.trans ht))
      Rp Rg Ralpha reg w (hGNuisance w hw)
      (pseudoOutcome_integrable_of_absolute E n t w (hi hw))
      (by simpa only [abs_sub_comm] using (hGNuisance w hw).1) hRad hregMoments
      hAverage hContrast
  have hProvider : ∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha →
      ∀ t, t0 ≤ t → ∀ delta, 0 < delta → delta < 1 → Ralpha n (delta / 4) ≤ a0 →
        DrMeanBoundProvider E n t (delta / 4) c Cgb K Rp Rg Ralpha := by
    intro n hn hNuisance t ht delta hd hd1 ha
    have hd4 : 0 < delta / 4 := by positivity
    have hd41 : delta / 4 < 1 := by linarith
    have hErrors := (nuisanceErrorBounds_components _ _ _ _ _ hNuisance).1 (delta / 4) hd4 hd41
    have htpos : 0 < t := zero_lt_one.trans_le (hT.trans (ht0.trans ht))
    exact dr_mean_bound_provider E hRV hn hOverlap Rp Rg Ralpha hErrors.1.2
      (hErrors.2.2.1 n) ha
      (hExponent t (ht0.trans ht) E c hOverlap n hn)
      (normalized_contrast_target_bound M hRV hX hHomogeneity hMean hGBound htpos
        (hTh t (hth0.trans ht)) (angularFactor_target_wasserstein_bound M hRV hNoise hX hHomogeneity htpos))
  have hMeanClosure : ∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha →
      ∀ t, t0 ≤ t → ∀ delta, 0 < delta → delta < 1 → Ralpha n (delta / 4) ≤ a0 →
      ∀ reg, Measurable reg → ∀ w, NuisanceAt E n t (delta / 4) Rp Rg Ralpha reg w →
        DrConditionalScoreMean E n t reg w → DrMeanDecomposition E n t reg w := by
    intro n hn hNuisance t ht delta hd hd1 ha reg hreg w hw hIdentity
    have hErrors := (nuisanceErrorBounds_components _ _ _ _ _ hNuisance).1 (delta / 4) (by positivity) (by linarith)
    have hRad := (hPower t (htr0.trans ht) (Ralpha n (delta / 4))
      (hErrors.2.2.1 n) ha).1
    exact dr_mean_decomposition_of_conditional_score_mean E hRV hX hHomogeneity
      hMean hn hOverlap hGBound (hT.trans (ht0.trans ht)) (hTh t (hth0.trans ht))
      Rp Rg Ralpha hErrors.1.2 reg hreg w hw
      (by simpa only [abs_sub_comm] using hw.1) hRad hIdentity
  constructor
  · intro n hn hIID hTraining hNuisance hIntegrable t ht delta hd hd1 ha hbudget B hB hBpos
    obtain ⟨hN, hNprob, hNpositive⟩ := evaluation_count_event E n t hn hIID hd hd1 hbudget
    have htpos : 0 < t := zero_lt_one.trans_le (hT.trans (ht0.trans ht))
    obtain ⟨reg, hreg, hEventsInt⟩ := hIntegrable t htpos
    obtain ⟨G, hGmeas, hGprob, hGNuisance, hGInt⟩ :=
      hEventsInt (delta / 4) (by positivity) (by linarith)
    obtain ⟨hg, hIdentity⟩ := hRegressionClosure n hn hNuisance t ht
      delta hd hd1 ha reg G hreg hGNuisance hGInt
    have hMeanProvider := hProvider n hn hNuisance t ht delta hd hd1 ha
    have hSampling := score_evaluation_truncated_sampling E .dr n hn hIID hRV hTraining
      t G {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)} hGmeas hN B hB
      (fun w => (hBpos w).le) hd hGprob hNprob (fun w hw => hNpositive w hw)
      (dr_score_integrable_on_nuisance_event E hn hOverlap hGInt hg)
    apply dr_truncated_probability_of_sampling_event E n t delta c Cgb K Rp Rg Ralpha B
      G {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)}
      (fun _ hw => hw) ?_ hSampling
    filter_upwards [hIdentity] with w hi hw
    exact hMeanProvider reg w (hGNuisance w hw)
      (hMeanClosure n hn hNuisance t ht delta hd hd1 ha reg hreg.1 w
        (hGNuisance w hw) (hi hw))
  · intro n hn hIID hTraining hNuisance t ht delta hd hd1 hMoments ha hbudget
    let := obsTailLaw_probability M hRV t
    obtain ⟨hN, hNprob, hNpositive⟩ := evaluation_count_event E n t hn hIID hd hd1 hbudget
    obtain ⟨reg, hreg, G, hGmeas, hGprob, hGInt, hGNuisance⟩ := hMoments
    obtain ⟨hg, hIdentity⟩ := hRegressionClosure n hn hNuisance t ht
      delta hd hd1 ha reg G hreg (fun w hw => (hGNuisance w hw).1) hGInt
    have hMeanProvider := hProvider n hn hNuisance t ht delta hd hd1 ha
    have hf : ∀ᵐ w ∂E.P, w ∈ G → MemLp (score E .dr n w) 2 (obsTailLaw M t) := by
      apply Eventually.of_forall
      intro w hw
      apply (evariance_lt_top_iff_memLp
        (measurable_score_frozen E .dr n w).aestronglyMeasurable).mp
      exact lt_top_iff_ne_top.mpr (hGNuisance w hw).2
    have hSampling := score_evaluation_variance_sampling E .dr n hn hIID hRV hTraining
      t G {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)} hGmeas hN
      hd hGprob hNprob (fun w hw => hNpositive w hw) hf
    apply dr_variance_probability_of_sampling_event E n t delta c Cgb K Rp Rg Ralpha
      G {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)}
      (fun _ hw => hw) (fun w hw => (hGNuisance w hw).2) ?_ hSampling
    filter_upwards [hIdentity] with w hi hw
    exact hMeanProvider reg w (hGNuisance w hw).1
      (hMeanClosure n hn hNuisance t ht delta hd hd1 ha reg hreg.1 w
        (hGNuisance w hw).1 (hi hw))


end Papers.TbsExtremeEffects
