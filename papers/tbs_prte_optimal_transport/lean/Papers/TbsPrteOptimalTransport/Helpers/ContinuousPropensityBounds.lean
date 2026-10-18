module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandRegressionBounds
/-! Compact-support envelopes for continuous propensity representers. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_boundaryIndicatorMean_norm_le_one
/-- [The absolute value of the population mean of the outcome indicator at a
band boundary is at most one](goal), for either selected side, every band index,
and every covariate value. -/
lemma population_boundaryIndicatorMean_norm_le_one
    (L : LevelData Z X) (plus : Bool) (k j : ℕ) (x : X) :
    ‖boundaryIndicatorMean M L plus k j x‖ ≤ 1 := by
  by_cases hz : (!plus && k == 0) = true
  · simp [boundaryIndicatorMean, hz]
  · have hb := population_selected_integral_norm_le_of_global_bound M L
      (if plus then k + 1 else k)
      (fun x y => indicator (y ≤ bandBoundary M L k j x))
      (fun x => by
        unfold indicator
        exact Measurable.ite measurableSet_Iic measurable_const measurable_const)
      1 zero_le_one (fun x y => by unfold indicator; split_ifs <;> norm_num) x
    simpa only [boundaryIndicatorMean, if_neg hz,
      continuous_boundary_indicator_integral_eq] using hb

-- @node: population_continuous_boundary_values_norm_le_one
/-- [Both the upper-side and lower-side boundary-indicator values at the true
nuisance functions have absolute value at most one](goal), for every band
boundary and covariate value. -/
lemma population_continuous_boundary_values_norm_le_one
    (L : LevelData Z X) (k j : ℕ) (x : X) :
    ‖boundaryValue (trueNuisance M L).Mplus k j x‖ ≤ 1 ∧
      ‖minusBoundaryValue (trueNuisance M L).Mminus k j x‖ ≤ 1 := by
  constructor
  · unfold boundaryValue
    split_ifs
    · exact population_boundaryIndicatorMean_norm_le_one M L true k j x
    · norm_num
    · norm_num
  · unfold minusBoundaryValue
    split_ifs
    · exact population_boundaryIndicatorMean_norm_le_one M L false k j x
    · norm_num
    · norm_num

-- @node: population_continuous_alphaHigh_norm_bound
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), and [a level system that preserves baseline and policy
propensity ordering](hyp:hL), if [the baseline gap index is below the number of
levels](hyp:hk) and [the band index is below the number of policy levels in that
gap](hyp:hj), then [the upper propensity-correction coefficient at the truth is
almost surely bounded in absolute value by three times the maximum absolute
outcome endpoint](goal). -/
lemma population_continuous_alphaHigh_norm_bound
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    ∀ᵐ x ∂xLaw M, ‖alphaHigh M L (trueNuisance M L) k j x‖ ≤
      3 * outcomeMagnitude M := by
  have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  filter_upwards [population_treatedBandMean_norm_bound M h he L true false k j,
    population_bandBoundary_norm_bound M h he q L hL k j hk hj.le,
    population_bandBoundary_norm_bound M h he q L hL k (j + 1) hk (by omega)]
    with x hJ ha hb
  have hJ' : ‖meanValue (trueNuisance M L).Jplus k j x‖ ≤ outcomeMagnitude M := by
    simpa only [meanValue, dif_pos (show k < L.K ∧ j ≤ L.l k from ⟨hk, hj.le⟩),
      trueNuisance] using hJ
  have hMa := (population_continuous_boundary_values_norm_le_one M L k j x).1
  have hMb := (population_continuous_boundary_values_norm_le_one M L k (j + 1) x).1
  simp only [← population_nuValue_eq_bandBoundary M L k j hk hj.le] at ha
  simp only [← population_nuValue_eq_bandBoundary M L k (j + 1) hk (by omega)] at hb
  unfold alphaHigh
  calc
    _ ≤ ‖meanValue (trueNuisance M L).Jplus k j x‖ +
        ‖nuValue M (trueNuisance M L) k j x‖ *
          ‖boundaryValue (trueNuisance M L).Mplus k j x‖ +
        ‖nuValue M (trueNuisance M L) k (j + 1) x‖ *
          ‖boundaryValue (trueNuisance M L).Mplus k (j + 1) x‖ := by
      have h1 := norm_add_le (meanValue (trueNuisance M L).Jplus k j x)
        (nuValue M (trueNuisance M L) k j x * boundaryValue (trueNuisance M L).Mplus k j x)
      have h2 := norm_sub_le
        (meanValue (trueNuisance M L).Jplus k j x +
          nuValue M (trueNuisance M L) k j x * boundaryValue (trueNuisance M L).Mplus k j x)
        (nuValue M (trueNuisance M L) k (j + 1) x * boundaryValue (trueNuisance M L).Mplus k (j + 1) x)
      simp only [norm_mul] at h1 h2
      linarith
    _ ≤ outcomeMagnitude M + outcomeMagnitude M * 1 + outcomeMagnitude M * 1 := by
      gcongr
    _ = 3 * outcomeMagnitude M := by ring

-- @node: population_continuous_alphaLow_norm_bound
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), and [a level system that preserves baseline and policy
propensity ordering](hyp:hL), if [the baseline gap index is below the number of
levels](hyp:hk) and [the band index is below the number of policy levels in that
gap](hyp:hj), then [the lower propensity-correction coefficient at the truth is
almost surely bounded in absolute value by five times the maximum absolute
outcome endpoint](goal). -/
lemma population_continuous_alphaLow_norm_bound
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    ∀ᵐ x ∂xLaw M, ‖alphaLow M L (trueNuisance M L) k j x‖ ≤
      5 * outcomeMagnitude M := by
  have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  filter_upwards [population_treatedBandMean_norm_bound M h he L false false k j,
    population_bandBoundary_norm_bound M h he q L hL k j hk hj.le,
    population_bandBoundary_norm_bound M h he q L hL k (j + 1) hk (by omega)]
    with x hJ ha hb
  have hJ' : ‖minusMeanValue (trueNuisance M L).Jminus k j x‖ ≤ outcomeMagnitude M := by
    unfold minusMeanValue
    split_ifs
    · exact hJ
    · simpa using hC
  have hMa := (population_continuous_boundary_values_norm_le_one M L k j x).2
  have hMb := (population_continuous_boundary_values_norm_le_one M L k (j + 1) x).2
  have hi : ‖indicator (1 ≤ j)‖ ≤ 1 := by unfold indicator; split_ifs <;> norm_num
  simp only [← population_nuValue_eq_bandBoundary M L k j hk hj.le] at ha
  simp only [← population_nuValue_eq_bandBoundary M L k (j + 1) hk (by omega)] at hb
  unfold alphaLow
  calc
    _ ≤ ‖minusMeanValue (trueNuisance M L).Jminus k j x‖ +
        ‖nuValue M (trueNuisance M L) k j x‖ *
          ‖minusBoundaryValue (trueNuisance M L).Mminus k j x‖ +
        ‖nuValue M (trueNuisance M L) k (j + 1) x‖ *
          ‖minusBoundaryValue (trueNuisance M L).Mminus k (j + 1) x‖ +
        ‖indicator (1 ≤ j)‖ * ‖nuValue M (trueNuisance M L) k j x‖ +
        ‖nuValue M (trueNuisance M L) k (j + 1) x‖ := by
      have h1 := norm_sub_le
        (-minusMeanValue (trueNuisance M L).Jminus k j x)
        (nuValue M (trueNuisance M L) k j x * minusBoundaryValue (trueNuisance M L).Mminus k j x)
      have h2 := norm_add_le
        (-minusMeanValue (trueNuisance M L).Jminus k j x -
          nuValue M (trueNuisance M L) k j x * minusBoundaryValue (trueNuisance M L).Mminus k j x)
        (nuValue M (trueNuisance M L) k (j + 1) x * minusBoundaryValue (trueNuisance M L).Mminus k (j + 1) x)
      have h3 := norm_add_le
        (-minusMeanValue (trueNuisance M L).Jminus k j x -
          nuValue M (trueNuisance M L) k j x * minusBoundaryValue (trueNuisance M L).Mminus k j x +
          nuValue M (trueNuisance M L) k (j + 1) x * minusBoundaryValue (trueNuisance M L).Mminus k (j + 1) x)
        (indicator (1 ≤ j) * nuValue M (trueNuisance M L) k j x)
      have h4 := norm_sub_le
        (-minusMeanValue (trueNuisance M L).Jminus k j x -
          nuValue M (trueNuisance M L) k j x * minusBoundaryValue (trueNuisance M L).Mminus k j x +
          nuValue M (trueNuisance M L) k (j + 1) x * minusBoundaryValue (trueNuisance M L).Mminus k (j + 1) x +
          indicator (1 ≤ j) * nuValue M (trueNuisance M L) k j x)
        (nuValue M (trueNuisance M L) k (j + 1) x)
      simp only [norm_neg, norm_mul] at h1 h2 h3 h4
      linarith
    _ ≤ outcomeMagnitude M + outcomeMagnitude M * 1 + outcomeMagnitude M * 1 +
        1 * outcomeMagnitude M + outcomeMagnitude M := by gcongr
    _ = 5 * outcomeMagnitude M := by ring

-- @node: population_continuous_alpha_weights_integrable
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), and [ordering-compatible baseline and policy levels](hyp:hL),
consider [a baseline gap below the number of levels](hyp:hk) and [a band below
the number of policy levels in that gap](hyp:hj). If [its lower boundary is
measurable](hyp:ha), [its upper boundary is measurable](hyp:hb), and [the covariate
weight is integrable](hyp:hwi), then [multiplying that weight by either the lower
or upper propensity-correction coefficient at the truth gives an integrable
covariate function](goal). -/
lemma population_continuous_alpha_weights_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (w : X → ℝ) (hwi : Integrable w (xLaw M)) :
    Integrable (fun x => w x * alphaLow M L (trueNuisance M L) k j x) (xLaw M) ∧
    Integrable (fun x => w x * alphaHigh M L (trueNuisance M L) k j x) (xLaw M) := by
  constructor
  · simpa only [mul_comm] using hwi.bdd_mul
      (population_continuous_band_alphaLow_measurable M L k j hk hj ha hb).aestronglyMeasurable
      (population_continuous_alphaLow_norm_bound M h he q L hL k j hk hj)
  · simpa only [mul_comm] using hwi.bdd_mul
      (population_continuous_band_alphaHigh_measurable M L k j hk hj ha hb).aestronglyMeasurable
      (population_continuous_alphaHigh_norm_bound M h he q L hL k j hk hj)

-- @node: population_RpCont_integrable_of_integrable_weight
/-- Suppose [treatment follows a threshold-crossing model](hyp:h), [the level
system preserves baseline and policy propensity ordering](hyp:hL), [each
replacement assignment probability is measurable](hyp:hpi), [a common lower
bound is positive](hyp:hc0), and [all these probabilities almost surely exceed
or equal that bound](hyp:hcl). If the covariate weight is [measurable](hyp:hw)
and [integrable](hyp:hwi), then [the weight times the propensity residual at any
level, using these assignment probabilities and otherwise true nuisances, is
integrable over observations](goal). -/
lemma population_RpCont_integrable_of_integrable_weight
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c0 : ℝ) (hc0 : 0 < c0) (hcl : ∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi a x)
    (i : ℕ) (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      RpCont L {trueNuisance M L with piLev := pi} i o) (observationLaw M) := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · have hi0 : i ≠ 0 := by omega
    have hp : Measurable (L.pLev i) :=
      ordered_baseline_level_measurable M h q L hL i hi
    have hid : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S i)) := by
      unfold indicator
      exact Measurable.ite ((L.S i).finite_toSet.measurableSet.preimage measurable_snd.fst)
        measurable_const measurable_const
    have hm : Measurable (RpCont L {trueNuisance M L with piLev := pi} i) := by
      first | fun_prop | skip
      change Measurable (fun o : Obs X Z => RpCont L {trueNuisance M L with piLev := pi} i o)
      simp only [RpCont, if_neg hi0, positiveValue, dif_pos hi, trueNuisance]
      exact (hid.div ((hpi ⟨i, hi⟩).comp measurable_fst)).mul
        (measurable_snd.snd.fst.sub (hp.comp measurable_fst))
    have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    have hmap : (observationLaw M).map Prod.fst = xLaw M := by
      simpa only [observationLaw, xLaw, Function.comp_def] using
        Measure.map_map measurable_fst hobs
    have hwi' : Integrable (fun o : Obs X Z => w o.1) (observationLaw M) := by
      apply (integrable_map_measure hw.aestronglyMeasurable measurable_fst.aemeasurable).mp
      rwa [hmap]
    have ht : ∀ᵐ o : Obs X Z ∂observationLaw M, ‖o.2.2.1‖ ≤ 1 := by
      apply (ae_map_iff hobs.aemeasurable
        (measurableSet_le (by fun_prop) measurable_const)).mpr
      exact Eventually.of_forall (fun s => by rcases M.rangeW s with hs | hs <;> simp [hs])
    have hr := (canonical_level_ranges M.prop q L
      (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).1)
      (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).2) hL).1
    have hb : ∀ᵐ o : Obs X Z ∂observationLaw M,
        ‖RpCont L {trueNuisance M L with piLev := pi} i o‖ ≤ 2 / c0 := by
      filter_upwards [ht, observationLaw_covariate_ae M _ (hcl ⟨i, hi⟩)] with o hto hco
      have hpos : 0 < pi ⟨i, hi⟩ o.1 := hc0.trans_le hco
      have hpB : ‖L.pLev i o.1‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr o.1 i (by omega)).1]
        exact (hr o.1 i (by omega)).2
      have hdiff : ‖o.2.2.1 - L.pLev i o.1‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by linarith)
      have hiB : ‖indicator (o.2.1 ∈ L.S i)‖ ≤ 1 := by
        unfold indicator; split_ifs <;> norm_num
      simp only [RpCont, if_neg hi0, positiveValue, dif_pos hi, trueNuisance,
        norm_mul, norm_div, Real.norm_eq_abs, abs_of_pos hpos]
      simp only [Real.norm_eq_abs] at hiB hdiff
      calc
        _ ≤ 1 / c0 * 2 := by gcongr
        _ = 2 / c0 := by ring
    simpa only [mul_comm] using hwi'.bdd_mul hm.aestronglyMeasurable hb
  · have hz : RpCont L {trueNuisance M L with piLev := pi} i = fun _ => (0 : ℝ) := by
      funext o
      by_cases hi0 : i = 0 <;> simp [RpCont, hi0, positiveValue, hi]
    simp only [hz, mul_zero]
    exact integrable_zero _ _ _

-- @node: population_continuous_band_propensity_zero_of_integrable_weight
/-- Under [the structural model assumptions](hyp:h), [known outcome
endpoints](hyp:he), [ordering-compatible baseline and policy levels](hyp:hL), and
[baseline overlap](hyp:hov), consider [a baseline gap below the number of
levels](hyp:hk) and [a band below the number of policy levels in that gap](hyp:hj).
If [the lower band boundary is measurable](hyp:ha), [the upper band boundary is
measurable](hyp:hb), and the covariate weight is [measurable](hyp:hw) and
[integrable](hyp:hwi), then [the weighted sum of the lower and upper propensity
corrections at the truth, omitting the lower correction in the first gap, is
integrable and has population mean zero](goal). -/
lemma population_continuous_band_propensity_zero_of_integrable_weight
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
        RpCont L (trueNuisance M L) k o) +
        alphaHigh M L (trueNuisance M L) k j o.1 *
          RpCont L (trueNuisance M L) (k + 1) o)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
        RpCont L (trueNuisance M L) k o) +
        alphaHigh M L (trueNuisance M L) k j o.1 *
          RpCont L (trueNuisance M L) (k + 1) o) ∂observationLaw M) = 0 := by
  have hpi a : Measurable ((trueNuisance M L).piLev a) :=
    population_instrument_set_probability_measurable M (L.S a.val)
  have hcl a : ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).piLev a x :=
    Eventually.of_forall (fun x => hov.2 x a.val a.property.1 a.property.2)
  obtain ⟨il, ih⟩ := population_continuous_alpha_weights_integrable M h he q L hL k j hk hj ha hb w hwi
  exact population_continuous_band_propensity_correction_zero M h.2.2.2.1 q L hL
    k j hk hj ha hb w hw
    (population_RpCont_integrable_of_integrable_weight M h.2.2.2.1 q L hL
      (trueNuisance M L).piLev hpi cpi hov.1 hcl k
      (fun x => w x * alphaLow M L (trueNuisance M L) k j x)
      (hw.mul (population_continuous_band_alphaLow_measurable M L k j hk hj ha hb)) il)
    (population_RpCont_integrable_of_integrable_weight M h.2.2.2.1 q L hL
      (trueNuisance M L).piLev hpi cpi hov.1 hcl (k + 1)
      (fun x => w x * alphaHigh M L (trueNuisance M L) k j x)
      (hw.mul (population_continuous_band_alphaHigh_measurable M L k j hk hj ha hb)) ih)

-- @node: population_continuous_band_mean_without_propensity_integrability
/-- Assume [the structural model conditions](hyp:h), [known outcome
endpoints](hyp:he), [measurability of the policy derivative evaluated at true
propensities](hyp:hdphi), [ordering-compatible baseline and policy levels](hyp:hL),
[baseline overlap](hyp:hov), and [policy overlap](hyp:hpol). For [a baseline gap
below the number of levels](hyp:hk) and [a band below the number of policy levels
in that gap](hyp:hj), suppose [the lower boundary is measurable](hyp:ha), [the
upper boundary is measurable](hyp:hb), [boundary densities are bounded](hyp:hd),
[there is no atom at the lower outcome endpoint](hyp:h0), the covariate weight
is [measurable](hyp:hw) and [integrable](hyp:hwi), and the policy residuals
multiplied by the weight and respectively [the lower boundary](hyp:hql) and
[the upper boundary](hyp:hqh) are integrable over observations. Then [the
weighted continuous band score at the truth is integrable and its population
mean equals the mean of the weighted band outcome component](goal). -/
lemma population_continuous_band_mean_without_propensity_integrability
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M))
    (hql : Integrable (fun o : Obs X Z => (w o.1 * bandBoundary M L k j o.1) *
      RqCont dphi L (trueNuisance M L) k j o) (observationLaw M))
    (hqh : Integrable (fun o : Obs X Z => (w o.1 * bandBoundary M L k (j + 1) o.1) *
      RqCont dphi L (trueNuisance M L) k (j + 1) o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      contScoreComponents M phi dphi L (trueNuisance M L) k j o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      contScoreComponents M phi dphi L (trueNuisance M L) k j o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * contJ L (trueNuisance M L) k j o.1 ∂observationLaw M := by
  have hpi a : Measurable ((trueNuisance M L).piLev a) :=
    population_instrument_set_probability_measurable M (L.S a.val)
  have hcl a : ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).piLev a x :=
    Eventually.of_forall (fun x => hov.2 x a.val a.property.1 a.property.2)
  obtain ⟨il, ih⟩ := population_continuous_alpha_weights_integrable M h he
    (policyProp phi M.prop) L hL k j hk hj ha hb w hwi
  exact population_continuous_band_mean_of_integrable_weight M h he phi dphi hdphi L
    hL cpi hov hpol k j hk hj ha hb hd h0 w hw hwi
    (population_RpCont_integrable_of_integrable_weight M h.2.2.2.1 (policyProp phi M.prop)
      L hL (trueNuisance M L).piLev hpi cpi hov.1 hcl k
      (fun x => w x * alphaLow M L (trueNuisance M L) k j x)
      (hw.mul (population_continuous_band_alphaLow_measurable M L k j hk hj ha hb)) il)
    (population_RpCont_integrable_of_integrable_weight M h.2.2.2.1 (policyProp phi M.prop)
      L hL (trueNuisance M L).piLev hpi cpi hov.1 hcl (k + 1)
      (fun x => w x * alphaHigh M L (trueNuisance M L) k j x)
      (hw.mul (population_continuous_band_alphaHigh_measurable M L k j hk hj ha hb)) ih)
    hql hqh

end Papers.TbsPrteOptimalTransport
