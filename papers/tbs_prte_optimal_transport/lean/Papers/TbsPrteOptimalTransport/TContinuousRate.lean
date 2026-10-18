module
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedIV
public import Papers.TbsPrteOptimalTransport.Helpers.PluginStability
public import Papers.TbsPrteOptimalTransport.Helpers.PluginRateAlgebra
public import Papers.TbsPrteOptimalTransport.Helpers.PluginMeasurability
public import Causalean.Stat.SampleSplit.FiniteSelector
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Papers.TbsPrteOptimalTransport.Helpers.PluginSplitMoment
public import Papers.TbsPrteOptimalTransport.Helpers.PluginTraining
public import Papers.TbsPrteOptimalTransport.Helpers.PluginScoreMeasurability
public import Papers.TbsPrteOptimalTransport.Helpers.PluginScoreTransport
public import Papers.TbsPrteOptimalTransport.Helpers.PluginPopulation
public import Papers.TbsPrteOptimalTransport.Helpers.PluginPopulationRegularity
/-! TContinuousRate statements. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false
set_option linter.unnecessarySeqFocus false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
variable (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
variable {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
variable (S : ObservedSample M μ)
-- @node: split_proportions_card_lower_tail
/-- If [the three splits form a measurable partition of the observed sample](hyp:hPartition)
and [their sample fractions converge almost surely to positive limiting proportions](hyp:hSplit),
then [the probability that any selected split contains fewer than half its limiting proportion times the sample size tends to zero](goal). -/
lemma split_proportions_card_lower_tail
    (I : Fin 3 → SampleSplit A) (rho : Fin 3 → ℝ)
    (hPartition : ThreeWayPartition M μ S I) (hSplit : SplitProportions μ I rho)
    (j : Fin 3) :
    Tendsto (fun n => μ {a | ((I j n a).card : ℝ) < rho j / 2 * n})
      atTop (𝓝 0) := by
  have hr : 0 < rho j := (hSplit.2 j).1.1
  have hmeas (n : ℕ) : Measurable (fun a => ((I j n a).card : ℝ) / n) := by
    first | fun_prop | exact (measurable_of_countable
      (fun F : Finset ℕ => (F.card : ℝ) / (n : ℝ))).comp (hPartition.1 n j)
  have hprob := tendstoInMeasure_of_tendsto_ae
    (fun n => (hmeas n).aestronglyMeasurable) (hSplit.2 j).2
  have hdev := tendstoInMeasure_iff_norm.mp hprob (rho j / 2) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdev
    (Eventually.of_forall (fun n => bot_le)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measure_mono
  intro a ha
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hratio : ((I j n a).card : ℝ) / n < rho j / 2 :=
    (div_lt_iff₀ hn').mpr ha
  change rho j / 2 ≤ ‖((I j n a).card : ℝ) / n - rho j‖
  rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

/-- For [a latent instrument model](hyp:M), [a sampling probability law](hyp:μ),
[an observed sample](hyp:S), [an evaluation split](hyp:I₂), [a policy map](hyp:phi),
[propensity estimates](hyp:p), [regression estimates](hyp:g), [cumulative quantile estimates](hyp:C),
[a sample size](hyp:n), and [a sample realization](hyp:a), the [lower-bound plug-in random variable](goal)
is the unrestricted lower-bound score average over the evaluation split when it is nonempty, and zero otherwise. -/
noncomputable def plugInRV (I₂ : SampleSplit A) (phi : Z → X → ℝ → ℝ)
    (p : ℕ → A → Z → X → ℝ) (g : ℕ → A → ℝ → X → ℝ) (C : ℕ → A → X → ℝ → ℝ)
    (n : ℕ) (a : A) :=
  if h : (I₂ n a).Nonempty then unrestrictedPlugInAverage M μ S I₂ phi p g C false n a h else 0

-- @node: connected_fit_lower_score_bounded
/-- For [an admissible policy map](hyp:hPolicy), if [the jointly fitted propensity, regression, and quantile learners satisfy the connected-instrument fitting requirements](hyp:hFit)
and [the regression learner satisfies its target-rate and range restrictions](hyp:hRegression), then
[the fitted lower-bound score is bounded in absolute value by four times the maximum absolute outcome endpoint, for every sample size, training realization, and observation](goal). -/
lemma connected_fit_lower_score_bounded
    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (I : Fin 3 → SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (QHat : ℕ → A → X → ℝ → ℝ)
    (hFit : ConnectedJointFitScope M μ S I pHat gHat QHat)
    (rg : ℕ → ℝ) (hRegression : RegressionTargetRate M μ phi pHat gHat rg) :
    ∀ n a o, |fittedInt M false phi (pHat n a) (gHat n a)
      (fun x => quantilePrimitive (QHat n a x)) o| ≤ 4 * outcomeMagnitude M := by
  rcases hFit with ⟨_, _, _, _, _, _, _, hp, hmono, hQrange⟩
  have hmin : |M.yMin| ≤ outcomeMagnitude M := le_max_left _ _
  have hmax : |M.yMax| ≤ outcomeMagnitude M := le_max_right _ _
  have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg _).trans hmin
  have hlo : -outcomeMagnitude M ≤ M.yMin := by
    linarith [neg_abs_le M.yMin]
  have hhi : M.yMax ≤ outcomeMagnitude M := (le_abs_self _).trans hmax
  have hb (n : ℕ) (a : A) (x : X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |QHat n a x t| ≤ outcomeMagnitude M :=
    abs_le.mpr ⟨hlo.trans (hQrange n a x t ht).1,
      (hQrange n a x t ht).2.trans hhi⟩
  have hg (n : ℕ) (a : A) (t : ℝ) (x : X) (ht : t ∈ Icc (0 : ℝ) 1) :
      |gHat n a t x| ≤ outcomeMagnitude M := by
    have hr := hRegression.1 n a t x ht
    exact abs_le.mpr ⟨(le_min (by linarith) hlo).trans hr.1,
      hr.2.trans (max_le hC hhi)⟩
  intro n a o
  exact fittedInt_lower_bounded M phi hPolicy (pHat n a) (gHat n a) (QHat n a)
    (hp n a) hC hmin (hg n a)
    (fun x => bounded_monotone_rank_integrable _ (hmono n a x) (hb n a x)) (hb n a) o

-- @node: connected_fit_lower_score_integrable
/-- For [an admissible policy map](hyp:hPolicy), if [the jointly fitted learners satisfy the connected-instrument fitting requirements](hyp:hFit)
and [the regression learner satisfies its target-rate and range restrictions](hyp:hRegression), then
[at each sample size the fitted lower-bound score is integrable over the product of the sampling law and an independent observation law](goal). -/
lemma connected_fit_lower_score_integrable
    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (I : Fin 3 → SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (QHat : ℕ → A → X → ℝ → ℝ)
    (hFit : ConnectedJointFitScope M μ S I pHat gHat QHat)
    (rg : ℕ → ℝ) (hRegression : RegressionTargetRate M μ phi pHat gHat rg)
    (n : ℕ) :
    Integrable (fun ao : A × Obs X Z => fittedInt M false phi
      (pHat n ao.1) (gHat n ao.1)
      (fun x => quantilePrimitive (QHat n ao.1 x)) ao.2)
      (μ.prod (observationLaw M)) := by
  haveI : IsProbabilityMeasure (observationLaw M) :=
    Measure.isProbabilityMeasure_map
      ((M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable)
  have hm := connected_fit_lower_score_aemeasurable M μ S phi hPolicy I
    pHat gHat QHat hFit n
  have hb := connected_fit_lower_score_bounded M μ S phi hPolicy I
    pHat gHat QHat hFit rg hRegression
  apply Integrable.of_bound hm.aestronglyMeasurable (4 * outcomeMagnitude M)
  exact Eventually.of_forall fun ao => by
    simpa only [Real.norm_eq_abs] using hb n ao.1 ao.2

-- @node: connected_fit_lower_plugin_evaluation_isBigOp
/-- For [an admissible policy map](hyp:hPolicy), suppose [the jointly fitted learners satisfy the connected-instrument fitting requirements](hyp:hFit),
[the three split fractions converge almost surely to positive proportions](hyp:hSplit), and
[the regression learner satisfies its target-rate and range restrictions](hyp:hRegression).
Then [the evaluation-split lower-bound plug-in average minus its fitted population score mean is of order one over the square root of sample size in probability](goal). -/
lemma connected_fit_lower_plugin_evaluation_isBigOp
    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (I : Fin 3 → SampleSplit A) (rho : Fin 3 → ℝ)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (QHat : ℕ → A → X → ℝ → ℝ)
    (hFit : ConnectedJointFitScope M μ S I pHat gHat QHat)
    (hSplit : SplitProportions μ I rho)
    (rg : ℕ → ℝ) (hRegression : RegressionTargetRate M μ phi pHat gHat rg) :
    Causalean.Stat.IsBigOp
      (fun n a => plugInRV M μ S (I 2) phi pHat gHat
        (fun n a x => quantilePrimitive (QHat n a x)) n a -
        ∫ o, fittedInt M false phi (pHat n a) (gHat n a)
          (fun x => quantilePrimitive (QHat n a x)) o ∂observationLaw M)
      (fun n => (n : ℝ)^(-1/2 : ℝ)) μ := by
  have hc : 0 < rho 2 / 2 := by linarith [(hSplit.2 2).1.1]
  have hsize := split_proportions_card_lower_tail M μ S I rho hFit.1 hSplit 2
  have hrate := connected_fit_lower_score_evaluation_isBigOp M S phi hPolicy I
    pHat gHat QHat hFit rg hRegression (rho 2 / 2) hc hsize
  have hbad : Tendsto (fun n => μ {a | ¬(I 2 n a).Nonempty}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsize
      (Eventually.of_forall (fun n => bot_le)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply measure_mono
    intro a ha
    have hz : (I 2 n a).card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp ha)
    change ((I 2 n a).card : ℝ) < rho 2 / 2 * n
    rw [hz, Nat.cast_zero]
    exact mul_pos hc (by exact_mod_cast (show 0 < n by omega))
  apply isBigOp_of_eq_on_high_probability_event (fun n => {a | (I 2 n a).Nonempty})
    _ hbad hrate
  intro n a ha
  change (I 2 n a).Nonempty at ha
  simp only [plugInRV, dif_pos ha, unrestrictedPlugInAverage, splitMean]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard : (I 2 n a).card ≠ 0 := (Finset.card_pos.mpr ha).ne'
  have hcard' : ((I 2 n a).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
  field_simp

/-- Assume [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), [common instrument support](hyp:hSupport),
[finitely many instrument components](hyp:hComponents), [continuous propensity on each component](hyp:hContinuous),
and [a connected instrument domain](hyp:hConnected), with [an admissible policy](hyp:hPolicy).
If [the learners satisfy the joint fitting requirements](hyp:hFit), [split fractions converge to positive proportions](hyp:hSplit),
[endpoint-map errors obey their specified rate](hyp:hEndpoint), [regression errors obey their specified rate](hyp:hRegression)
with [a vanishing regression rate](hyp:hRegressionVanishes), and [boundary-law errors obey their specified rate](hyp:hBoundary)
with [a vanishing boundary rate](hyp:hBoundaryVanishes), then
[the absolute lower-bound plug-in estimation error is of order the sum of the inverse square root of sample size and the endpoint, regression, and boundary rates in probability](goal). -/
theorem plugin_rate_of_joint_fit
    (hDomains : DomainsCompactBorel M) (hEndpoints : OutcomeEndpointsKnown M)
    (hPotential : PotentialSupport M) (hConsistency : Consistency M)
    (hExogeneity : InstrumentExogeneity M) (hThreshold : ThresholdCrossing M)
    (hUniform : UniformResistance M) (hSupport : CommonInstrumentSupport M)
    (hComponents : FiniteInstrumentComponents Z)
    (hContinuous : PropensityContinuousOnComponents M)

    (hConnected : InstrumentConnected Z)
    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (I : Fin 3 → SampleSplit A) (rho : Fin 3 → ℝ)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (QHat : ℕ → A → X → ℝ → ℝ)
    (hFit : ConnectedJointFitScope M μ S I pHat gHat QHat)

    (hSplit : SplitProportions μ I rho) (re rg rmu : ℕ → ℝ)
    (hEndpoint : EndpointMapRates M μ phi pHat re)
    (hRegression : RegressionTargetRate M μ phi pHat gHat rg)
    (hRegressionVanishes : RegressionRateVanishes rg)
    (hBoundary : BoundaryLawRate M zeroLaw μ QHat rmu)
    (hBoundaryVanishes : BoundaryRateVanishes rmu) :
    Causalean.Stat.IsBigOp
      (fun n a => |plugInRV M μ S (I 2) phi pHat gHat
        (fun n a x => quantilePrimitive (QHat n a x)) n a -
        thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))|)
      (fun n => (n : ℝ)^(-1/2 : ℝ) + re n + rg n + rmu n) μ := by
  have hNuisance := plugin_nuisance_envelope_rate M zeroLaw μ phi pHat gHat QHat
    re rg rmu hEndpoint hRegression hBoundary
  have hEvaluationSize := split_proportions_card_lower_tail M μ S I rho hFit.1 hSplit 2
  have hScoreBound := connected_fit_lower_score_bounded M μ S phi hPolicy I
    pHat gHat QHat hFit rg hRegression
  haveI : IsProbabilityMeasure (observationLaw M) :=
    Measure.isProbabilityMeasure_map
      ((M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable)
  have hScoreMeas (n : ℕ) := connected_fit_lower_score_aemeasurable
    M μ S phi hPolicy I pHat gHat QHat hFit n
  have hScoreIntegrable (n : ℕ) := connected_fit_lower_score_integrable
    M μ S phi hPolicy I pHat gHat QHat hFit rg hRegression n
  have hScoreSections (n : ℕ) := (hScoreIntegrable n).prod_right_ae
  have hEvaluation := connected_fit_lower_plugin_evaluation_isBigOp M μ S phi hPolicy
    I rho pHat gHat QHat hFit hSplit rg hRegression
  have hStructural : StructuralAssumptions M :=
    ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
  have hParts := hFit
  rcases hParts with ⟨_, _, _, _, hpm, hgm, hqm, hp, hmono, hQrange⟩
  have hPopulationError (n : ℕ) (a : A) :=
    fitted_lower_connected_error_ae M zeroLaw hStructural hEndpoints phi hPolicy
      (pHat n a) (gHat n a) (QHat n a) (hp n a) (hmono n a) (hQrange n a)
  have hc := connected_lower_integrable M zeroLaw hStructural hEndpoints phi hPolicy
  have hTarget := connected_lower_target_identity M zeroLaw hStructural hEndpoints
    hContinuous hComponents hConnected phi hPolicy
  have hpMeas (n : ℕ) (a : A) : Measurable (Function.uncurry (pHat n a)) := by
    change Measurable (fun zx : Z × X => pHat n a zx.1 zx.2)
    simpa only [Function.comp_def, Function.uncurry, id_eq] using
      (hpm n).comp ((measurable_const (a := a)).prodMk measurable_id)
  have hgMeas (n : ℕ) (a : A) :
      Measurable (fun tx : Icc (0 : ℝ) 1 × X => gHat n a tx.1.val tx.2) := by
    simpa only [Function.comp_def, id_eq] using
      (hgm n).comp ((measurable_const (a := a)).prodMk measurable_id)
  have hqMeas (n : ℕ) (a : A) :
      Measurable (fun xt : X × Icc (0 : ℝ) 1 => QHat n a xt.1 xt.2.val) := by
    simpa only [Function.comp_def, id_eq] using
      (hqm n).comp ((measurable_const (a := a)).prodMk measurable_id)
  have hgb (n : ℕ) (a : A) (t : ℝ) (x : X) (ht : t ∈ Icc (0 : ℝ) 1) :
      |gHat n a t x| ≤ outcomeMagnitude M := by
    have hr := hRegression.1 n a t x ht
    have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
    have hmin : |M.yMin| ≤ outcomeMagnitude M := le_max_left _ _
    have hlo : -outcomeMagnitude M ≤ M.yMin := by
      linarith [neg_abs_le M.yMin]
    have hhi : M.yMax ≤ outcomeMagnitude M := (le_abs_self _).trans (le_max_right _ _)
    exact abs_le.mpr ⟨(le_min (by linarith) hlo).trans hr.1,
      hr.2.trans (max_le hC hhi)⟩
  have hEnvelope (n : ℕ) (a : A) := lowerPopulationEnvelope_integral M zeroLaw phi
    (pHat n a) (gHat n a) (QHat n a)
    (endpoint_error_integrable M phi hPolicy hThreshold (pHat n a) (hpMeas n a) (hp n a))
    (regression_error_integrable M hStructural hEndpoints phi hPolicy
      (pHat n a) (gHat n a) (hpMeas n a) (hgMeas n a) (hp n a) (hgb n a))
    (weighted_boundary_distance_integrable M zeroLaw hStructural hEndpoints
      (QHat n a) (hqMeas n a) (hmono n a) (fitted_quantile_magnitude M (hQrange n a)))
  let E := fun n a => plugInRV M μ S (I 2) phi pHat gHat
    (fun n a x => quantilePrimitive (QHat n a x)) n a -
    ∫ o, fittedInt M false phi (pHat n a) (gHat n a)
      (fun x => quantilePrimitive (QHat n a x)) o ∂observationLaw M
  let B := fun n a => ∫ zx, lowerPopulationEnvelope M zeroLaw phi
    (pHat n a) (gHat n a) (QHat n a) zx ∂zxLaw M
  let r := fun n : ℕ => (n : ℝ)^(-1/2 : ℝ) + re n + rg n + rmu n
  have hB : Causalean.Stat.IsBigOp B r μ := by
    convert hNuisance using 1
    funext n a
    exact (hEnvelope n a).2
  have hE : Causalean.Stat.IsBigOp E r μ := by
    apply Causalean.Stat.IsBigOp.mono_rate (h := hEvaluation)
    intro n
    dsimp only [r]
    linarith [hEndpoint.1 n, hRegression.2.1 n, hBoundary.1 n]
  have hEabs : Causalean.Stat.IsBigOp (fun n a => |E n a|) r μ :=
    Causalean.Stat.IsBigOp.of_abs_le (fun n a => by rw [abs_abs]) hE
  have hBabs : Causalean.Stat.IsBigOp (fun n a => |B n a|) r μ :=
    Causalean.Stat.IsBigOp.of_abs_le (fun n a => by rw [abs_abs]) hB
  apply isBigOp_of_abs_le_ae _ (hEabs.add hBabs)
  intro n
  filter_upwards [hScoreSections n] with a ha
  have hb := fitted_lower_integral_error_le_envelope M zeroLaw hStructural hEndpoints phi
    hPolicy (pHat n a) (gHat n a) (QHat n a) (hp n a) (hmono n a) (hQrange n a)
    ha hc (hEnvelope n a).1
  rw [hTarget]
  rw [abs_abs, abs_of_nonneg (add_nonneg (abs_nonneg (E n a)) (abs_nonneg (B n a)))]
  calc
    _ ≤ |E n a| + |(∫ o, fittedInt M false phi (pHat n a) (gHat n a)
        (fun x => quantilePrimitive (QHat n a x)) o ∂observationLaw M) -
        connectedValue M zeroLaw false (policyProp phi M.prop)| := by
      convert abs_add_le (E n a) ((∫ o, fittedInt M false phi (pHat n a) (gHat n a)
        (fun x => quantilePrimitive (QHat n a x)) o ∂observationLaw M) -
        connectedValue M zeroLaw false (policyProp phi M.prop)) using 1 <;> (try dsimp only [E]) <;> congr 1 <;> ring
    _ ≤ |E n a| + |B n a| := add_le_add le_rfl (hb.trans (le_abs_self _))

-- @node: thm:continuous-rate
/-- Under [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), [common instrument support](hyp:hSupport),
[finitely many instrument components](hyp:hComponents), [continuous propensity on each component](hyp:hContinuous),
and [connected instrument support](hyp:hConnected), consider [an admissible policy](hyp:hPolicy).
If [the learners satisfy the joint fitting requirements](hyp:hFit), [split fractions converge to positive proportions](hyp:hSplit),
[endpoint errors obey the endpoint rate](hyp:hEndpoint), [regression errors obey the regression rate](hyp:hRegression)
and [that rate vanishes](hyp:hRegressionVanishes), while [boundary-law errors obey the boundary rate](hyp:hBoundary)
and [that rate vanishes](hyp:hBoundaryVanishes), then
[the absolute error of the evaluation-split lower-bound plug-in estimator is bounded in probability at the sum of the inverse square root of sample size and the three nuisance rates](goal). -/
theorem plugin_rate
    (hDomains : DomainsCompactBorel M) (hEndpoints : OutcomeEndpointsKnown M)
    (hPotential : PotentialSupport M) (hConsistency : Consistency M)
    (hExogeneity : InstrumentExogeneity M) (hThreshold : ThresholdCrossing M)
    (hUniform : UniformResistance M) (hSupport : CommonInstrumentSupport M)
    (hComponents : FiniteInstrumentComponents Z)
    (hContinuous : PropensityContinuousOnComponents M)

    (hConnected : InstrumentConnected Z)
    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (I : Fin 3 → SampleSplit A) (rho : Fin 3 → ℝ)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (QHat : ℕ → A → X → ℝ → ℝ)
    (hFit : ConnectedJointFitScope M μ S I pHat gHat QHat)

    (hSplit : SplitProportions μ I rho) (re rg rmu : ℕ → ℝ)
    (hEndpoint : EndpointMapRates M μ phi pHat re)
    (hRegression : RegressionTargetRate M μ phi pHat gHat rg)
    (hRegressionVanishes : RegressionRateVanishes rg)
    (hBoundary : BoundaryLawRate M zeroLaw μ QHat rmu)
    (hBoundaryVanishes : BoundaryRateVanishes rmu) :
    Causalean.Stat.IsBigOp
      (fun n a => |plugInRV M μ S (I 2) phi pHat gHat
        (fun n a x => quantilePrimitive (QHat n a x)) n a -
        thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))|)
      (fun n => (n : ℝ)^(-1/2 : ℝ) + re n + rg n + rmu n) μ := by
  exact plugin_rate_of_joint_fit M zeroLaw μ S hDomains hEndpoints hPotential
    hConsistency hExogeneity hThreshold hUniform hSupport hComponents hContinuous
    hConnected phi hPolicy I rho pHat gHat QHat
    hFit
    hSplit re rg rmu hEndpoint hRegression hRegressionVanishes hBoundary hBoundaryVanishes

end Papers.TbsPrteOptimalTransport
