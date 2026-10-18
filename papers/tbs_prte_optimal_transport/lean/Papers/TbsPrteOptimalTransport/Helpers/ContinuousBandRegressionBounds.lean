module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBoundaryResidualBounds
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBandAssembly
/-! Constructed boundary envelopes and integrability of the entire band regression correction. -/
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

-- The zero-rank convention and all interior ranks lie in the known outcome support.
-- @node: population_bandBoundary_supported
/-- Under the model's [structural assumptions](hyp:h), with [known outcome endpoints](hyp:he)
and [level ordering invariant between baseline and policy propensities](hyp:hL),
[every band boundary, including rank zero, lies in the outcome support for almost every covariate value](goal). -/
lemma population_bandBoundary_supported
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j ≤ L.l k, bandBoundary M L k j x ∈ M.Yset := by
  filter_upwards [discrete_gap_law_supported M h M.prop q L hL] with x hx
  intro k hk j hj
  by_cases hz : j = 0 ∨ kappa L k j x = 0
  · simpa only [bandBoundary, if_pos hz] using he.1.1
  · letI := discrete_gap_law_probability M M.prop q L hL k hk x
    have hkr := (canonical_level_ranges M.prop q L
      (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).1)
      (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).2) hL).2.2 x k j hk (by omega)
    have ht : kappa L k j x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hkr.1 (Ne.symm (not_or.mp hz).2),
        kappa_lt_one_of_policy_level M.prop q L hL x k j hk (by omega) hj⟩
    rw [bandBoundary, if_neg hz]
    exact quantile_mem_closed_of_supported _ M.Yset h.2.2.2.2.2.2.1.isClosed
      (hx k hk) _ ht

-- @node: population_bandBoundary_norm_bound
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[invariant level ordering](hyp:hL), for [a treatment interval below the level count](hyp:hk)
and [a boundary index at most its band count](hyp:hj),
[the absolute band boundary is almost surely bounded by the maximum absolute outcome endpoint](goal). -/
lemma population_bandBoundary_norm_bound
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) :
    ∀ᵐ x ∂xLaw M, ‖bandBoundary M L k j x‖ ≤ outcomeMagnitude M := by
  filter_upwards [population_bandBoundary_supported M h he q L hL] with x hx
  exact outcome_norm_le_magnitude M he (hx k hk j hj)

-- This discharges the quantile-weight integrability needed by both boundary residuals.
-- @node: population_bandBoundary_weight_integrable
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[invariant level ordering](hyp:hL), take [a valid treatment interval](hyp:hk) and
[a boundary index no greater than its band count](hyp:hj). If [the boundary is measurable](hyp:ha)
and [the covariate weight is integrable](hyp:hwi),
[their product is integrable under the covariate distribution](goal). -/
lemma population_bandBoundary_weight_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (w : X → ℝ) (hwi : Integrable w (xLaw M)) :
    Integrable (fun x => w x * bandBoundary M L k j x) (xLaw M) := by
  simpa only [mul_comm] using hwi.bdd_mul ha.aestronglyMeasurable
    (population_bandBoundary_norm_bound M h he q L hL k j hk hj)

-- No integrability of an individual correction is assumed: overlap, compact
-- support, and an L1 covariate weight give all six terms before their means cancel.
-- @node: population_continuous_band_regression_zero_of_clipped_denominator
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[invariant level ordering](hyp:hL), suppose [each fitted assignment denominator is measurable](hyp:hpi)
and [almost surely bounded below by the clipping constant](hyp:hcl), which [is positive](hyp:hc0).
For [a valid treatment interval](hyp:hk) and [a band below its band count](hyp:hj), with
[measurable lower](hyp:ha) and [upper boundaries](hyp:hb) and a [measurable](hyp:hw),
[integrable covariate weight](hyp:hwi), [the weighted band regression correction is integrable and has expectation zero](goal). -/
lemma population_continuous_band_regression_zero_of_clipped_denominator
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c0 : ℝ) (hc0 : 0 < c0) (hcl : ∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi a x)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * continuousBandRegressionCorrection M L
      {trueNuisance M L with piLev := pi} k j o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * continuousBandRegressionCorrection M L
      {trueNuisance M L with piLev := pi} k j o ∂observationLaw M) = 0 := by
  have hwa := population_bandBoundary_weight_integrable M h he q L hL k j hk hj.le ha w hwi
  have hwb := population_bandBoundary_weight_integrable M h he q L hL k (j + 1) hk
    (by omega) hb w hwi
  exact population_continuous_band_regression_correction_zero M L pi hpi k j hk hj ha hb w hw
    (fun plus => population_IFJ_fitted_denominator_integrable M h he L pi hpi c0 hc0 hcl
      plus k j hk hj ha hb w hw hwi)
    (fun plus => population_IFM_fitted_denominator_integrable M L pi hpi c0 hc0 hcl
      plus k j hk hj.le ha (fun x => w x * bandBoundary M L k j x) (hw.mul ha) hwa)
    (fun plus => population_IFM_fitted_denominator_integrable M L pi hpi c0 hc0 hcl
      plus k (j + 1) hk (by omega) hb
      (fun x => w x * bandBoundary M L k (j + 1) x) (hw.mul hb) hwb)

-- Denominator and coefficient paths can vary together: their expectation
-- remains zero in a neighborhood, without differentiation under the integral.
-- @node: population_continuous_band_regression_clipped_local_path_orthogonality
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[invariant level ordering](hyp:hL), let the clipping constant [be positive](hyp:hc0).
Suppose [near zero, all assignment denominators are measurable and almost surely bounded below by that constant, and the covariate weights are measurable and integrable](hyp:hp).
For [a valid treatment interval](hyp:hk) and [a band below its band count](hyp:hj) with
[measurable lower](hyp:ha) and [upper boundaries](hyp:hb),
[the expected weighted band regression correction has derivative zero at zero along the joint denominator and weight path](goal). -/
lemma population_continuous_band_regression_clipped_local_path_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (pi : ℝ → PositiveIndex L.K → X → ℝ) (w : ℝ → X → ℝ)
    (c0 : ℝ) (hc0 : 0 < c0)
    (hp : ∀ᶠ t in 𝓝 (0 : ℝ), (∀ a, Measurable (pi t a)) ∧
      (∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi t a x) ∧
      Measurable (w t) ∧ Integrable (w t) (xLaw M))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1))) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      continuousBandRegressionCorrection M L {trueNuisance M L with piLev := pi t}
        k j o ∂observationLaw M) 0 0 := by
  apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [hp] with t ht
  exact (population_continuous_band_regression_zero_of_clipped_denominator M h he q L hL
    (pi t) ht.1 c0 hc0 ht.2.1 k j hk hj ha hb (w t) ht.2.2.1 ht.2.2.2).2

-- @node: population_contJ_norm_bound
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[invariant level ordering](hyp:hL), for [a valid treatment interval](hyp:hk) and
[a band below its band count](hyp:hj),
[the absolute population band outcome contrast is almost surely at most twice the maximum absolute outcome endpoint](goal). -/
lemma population_contJ_norm_bound
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    ∀ᵐ x ∂xLaw M, ‖contJ L (trueNuisance M L) k j x‖ ≤ 2 * outcomeMagnitude M := by
  have hr := (canonical_level_ranges M.prop q L
    (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).1)
    (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).2) hL).1
  have hp i x : ‖positiveValue (trueNuisance M L).pLev i x‖ ≤ 1 := by
    unfold positiveValue
    split_ifs with hi
    · change ‖L.pLev i x‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hr x i (by omega)).1]
      exact (hr x i (by omega)).2
    · norm_num
  have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  filter_upwards [population_treatedBandMean_norm_bound M h he L true false k j,
    population_treatedBandMean_norm_bound M h he L false false k j] with x hplus hminus
  have hJp : ‖meanValue (trueNuisance M L).Jplus k j x‖ ≤ outcomeMagnitude M := by
    simpa only [meanValue, dif_pos (show k < L.K ∧ j ≤ L.l k from ⟨hk, hj.le⟩),
      trueNuisance] using hplus
  have hJm : ‖minusMeanValue (trueNuisance M L).Jminus k j x‖ ≤ outcomeMagnitude M := by
    unfold minusMeanValue
    split_ifs
    · exact hminus
    · simpa using hC
  calc
    ‖contJ L (trueNuisance M L) k j x‖ ≤
        ‖positiveValue (trueNuisance M L).pLev (k + 1) x‖ *
          ‖meanValue (trueNuisance M L).Jplus k j x‖ +
        ‖positiveValue (trueNuisance M L).pLev k x‖ *
          ‖minusMeanValue (trueNuisance M L).Jminus k j x‖ := by
      simpa only [contJ, norm_mul] using norm_sub_le
        (positiveValue (trueNuisance M L).pLev (k + 1) x *
          meanValue (trueNuisance M L).Jplus k j x)
        (positiveValue (trueNuisance M L).pLev k x *
          minusMeanValue (trueNuisance M L).Jminus k j x)
    _ ≤ 1 * outcomeMagnitude M + 1 * outcomeMagnitude M := by gcongr <;> apply hp
    _ = 2 * outcomeMagnitude M := by ring

-- Compact support also supplies the plug-in integrability needed for product scores.
-- @node: population_contJ_weighted_integrable
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[invariant level ordering](hyp:hL), take [a valid treatment interval](hyp:hk) and
[a band below its band count](hyp:hj) with [measurable lower](hyp:ha) and
[upper boundaries](hyp:hb). For a [measurable](hyp:hw), [integrable covariate weight](hyp:hwi),
[the weighted population band outcome contrast is integrable under the observation distribution](goal). -/
lemma population_contJ_weighted_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * contJ L (trueNuisance M L) k j o.1)
      (observationLaw M) := by
  have hm := population_continuous_band_J_measurable M h.2.2.2.1 q L hL k j hk hj ha hb
  have hi : Integrable (fun x => w x * contJ L (trueNuisance M L) k j x) (xLaw M) := by
    simpa only [mul_comm] using hwi.bdd_mul hm.aestronglyMeasurable
      (population_contJ_norm_bound M h he q L hL k j hk hj)
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using Measure.map_map measurable_fst hobs
  apply (integrable_map_measure (hw.mul hm).aestronglyMeasurable measurable_fst.aemeasurable).mp
  rwa [hmap]

-- @node: population_continuous_band_mean_of_integrable_weight
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[measurability of the policy derivative evaluated at baseline propensities](hyp:hdphi),
[invariant ordering of baseline and policy levels](hyp:hL), [baseline overlap](hyp:hov),
and [policy overlap](hyp:hpol), take [a valid treatment interval](hyp:hk) and
[a band below its band count](hyp:hj) with [measurable lower](hyp:ha) and
[upper boundaries](hyp:hb), [bounded boundary densities](hyp:hd), and
[no atom at the lower outcome endpoint](hyp:h0). If the covariate weight is
[measurable](hyp:hw) and [integrable](hyp:hwi), and the weighted
[lower propensity correction](hyp:hl), [upper propensity correction](hyp:hh),
[lower boundary policy correction](hyp:hql), and [upper boundary policy correction](hyp:hqh)
are integrable, [the weighted band score is integrable and its expectation equals the expected weighted population band outcome contrast](goal). -/
lemma population_continuous_band_mean_of_integrable_weight
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
    (hl : Integrable (fun o : Obs X Z => (w o.1 *
      alphaLow M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => (w o.1 *
      alphaHigh M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) (k + 1) o) (observationLaw M))
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
  have hbase := population_contJ_weighted_integrable M h he (policyProp phi M.prop)
    L hL k j hk hj ha hb w hw hwi
  obtain ⟨hr, zr⟩ := population_continuous_band_regression_zero_of_clipped_denominator
    M h he (policyProp phi M.prop) L hL (trueNuisance M L).piLev hpi
    cpi hov.1 hcl k j hk hj ha hb w hw hwi
  obtain ⟨hp, zp⟩ := population_continuous_band_propensity_correction_zero M h.2.2.2.1
    (policyProp phi M.prop) L hL k j hk hj ha hb w hw hl hh
  obtain ⟨hq, zq⟩ := population_continuous_band_policy_correction_zero M h.2.2.2.1
    dphi hdphi L k j hk hj ha hb w hw hql hqh
  have heq := population_continuous_band_score_ae_decomposition M h he phi dphi L
    hL cpi hov hpol k j hk hj hd h0
  have hwEq : (fun o : Obs X Z => w o.1 *
      contScoreComponents M phi dphi L (trueNuisance M L) k j o) =ᵐ[observationLaw M]
      (fun o => w o.1 * contJ L (trueNuisance M L) k j o.1 +
        w o.1 * continuousBandRegressionCorrection M L (trueNuisance M L) k j o +
        w o.1 * ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
          RpCont L (trueNuisance M L) k o) +
          alphaHigh M L (trueNuisance M L) k j o.1 *
            RpCont L (trueNuisance M L) (k + 1) o) +
        w o.1 * (-(nuValue M (trueNuisance M L) k j o.1 *
          RqCont dphi L (trueNuisance M L) k j o) +
          nuValue M (trueNuisance M L) k (j + 1) o.1 *
            RqCont dphi L (trueNuisance M L) k (j + 1) o)) := by
    filter_upwards [heq] with o ho
    rw [ho]
    ring
  refine ⟨(((hbase.fun_add hr).fun_add hp).fun_add hq).congr hwEq.symm, ?_⟩
  rw [integral_congr_ae hwEq, integral_add ((hbase.fun_add hr).fun_add hp) hq,
    integral_add (hbase.fun_add hr) hp, integral_add hbase hr, zr, zp, zq]
  ring

end Papers.TbsPrteOptimalTransport
