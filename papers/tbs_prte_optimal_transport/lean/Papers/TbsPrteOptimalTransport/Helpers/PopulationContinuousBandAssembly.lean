module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandCorrection
public import Papers.TbsPrteOptimalTransport.Helpers.GapQuantileMoments
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullProducts
public import Papers.TbsPrteOptimalTransport.Helpers.BoundaryAtomFreedom
/-! Population assembly of continuous band score moments. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_band_J_measurable
/-- Under [threshold crossing](hyp:h) and [covariate-invariant level ordering](hyp:hOrder),
for [a nonfinal bin](hyp:hk), [a band index below its policy-level count](hyp:hj),
and [measurable lower](hyp:ha) and [upper boundaries](hyp:hb),
[the population propensity-weighted difference of plus and minus treated-band means is measurable](goal). -/
@[fun_prop] lemma population_continuous_band_J_measurable
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1))) :
    Measurable (contJ L (trueNuisance M L) k j) := by
  first | fun_prop | skip
  have hp i : Measurable (positiveValue (trueNuisance M L).pLev i) := by
    unfold positiveValue
    split_ifs with hi
    · exact ordered_baseline_level_measurable M h q L hOrder i hi
    · fun_prop
  have hjp := population_treated_band_mean_measurable M L true k j ha hb
  have hjm := population_treated_band_mean_measurable M L false k j ha hb
  have hjplus : Measurable (meanValue (trueNuisance M L).Jplus k j) := by
    change Measurable (fun x => meanValue (trueNuisance M L).Jplus k j x)
    simpa only [meanValue, dif_pos (show k < L.K ∧ j ≤ L.l k from ⟨hk, hj.le⟩),
      trueNuisance] using hjp
  have hjminus : Measurable (minusMeanValue (trueNuisance M L).Jminus k j) := by
    change Measurable (fun x => minusMeanValue (trueNuisance M L).Jminus k j x)
    by_cases hk0 : k = 0
    · simp [minusMeanValue, hk0]
    · simpa only [minusMeanValue,
        dif_pos (show 1 ≤ k ∧ k < L.K ∧ j ≤ L.l k from ⟨by omega, hk, hj.le⟩),
        trueNuisance] using hjm
  exact ((hp (k + 1)).mul hjplus).sub ((hp k).mul hjminus)

-- The two explicit quantile moments vanish before integrating the score.
-- @node: population_continuous_band_score_ae_decomposition
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[covariate-invariant ordering of baseline and transformed policy levels](hyp:hL),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
[a nonfinal bin](hyp:hk), [a band index below its policy-level count](hyp:hj),
[locally bounded boundary densities](hyp:hd), and [no atom at the lower outcome endpoint](hyp:h0),
[the population band score equals, almost surely under the observation law, the
band mean contrast plus the regression correction, the lower and upper baseline
propensity residual terms, and the negative lower and positive upper boundary-weighted
policy residual terms, with the lower baseline term omitted in bin zero](goal). -/
lemma population_continuous_band_score_ae_decomposition
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L) :
    (fun o : Obs X Z => contScoreComponents M phi dphi L (trueNuisance M L) k j o)
      =ᵐ[observationLaw M] (fun o =>
        contJ L (trueNuisance M L) k j o.1 +
        continuousBandRegressionCorrection M L (trueNuisance M L) k j o +
        ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
          RpCont L (trueNuisance M L) k o) +
          alphaHigh M L (trueNuisance M L) k j o.1 *
            RpCont L (trueNuisance M L) (k + 1) o) +
        (-(nuValue M (trueNuisance M L) k j o.1 *
          RqCont dphi L (trueNuisance M L) k j o) +
          nuValue M (trueNuisance M L) k (j + 1) o.1 *
            RqCont dphi L (trueNuisance M L) k (j + 1) o)) := by
  have hm := population_continuous_score_quantile_moment_of_density M h he phi L hL
    cpi hov hpol hd h0
  filter_upwards [observationLaw_covariate_ae M _ hm] with o ho
  have ha := ho k hk j hj.le
  have hb := ho k hk (j + 1) (by omega)
  rw [continuous_band_score_regression_decomposition, ha, hb]
  ring

-- @node: population_continuous_band_component_weighted_mean
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a measurable policy derivative evaluated at baseline propensities](hyp:hdphi),
[covariate-invariant baseline and policy level ordering](hyp:hL),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [a nonfinal bin](hyp:hk),
[a band index below its policy-level count](hyp:hj), [measurable lower](hyp:ha) and
[upper boundaries](hyp:hb), [locally bounded boundary densities](hyp:hd), and
[no lower-endpoint atom](hyp:h0), take [a measurable covariate weight](hyp:hw).
If [the weighted population band mean contrast](hyp:hbase),
[both weighted treated-band residuals](hyp:hJ),
[both lower-boundary-weighted indicator residuals](hyp:hMa),
[both upper-boundary-weighted indicator residuals](hyp:hMb),
[the weighted lower baseline propensity term](hyp:hl),
[the weighted upper baseline propensity term](hyp:hh),
[the weighted lower policy residual term](hyp:hql), and
[the weighted upper policy residual term](hyp:hqh) are integrable,
[the weighted band score is integrable and its expectation equals that of the weighted population band mean contrast](goal). -/
lemma population_continuous_band_component_weighted_mean
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (w : X → ℝ) (hw : Measurable w)
    (hbase : Integrable (fun o : Obs X Z => w o.1 *
      contJ L (trueNuisance M L) k j o.1) (observationLaw M))
    (hJ : ∀ plus, Integrable (fun o : Obs X Z => w o.1 *
      IFJ M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMa : ∀ plus, Integrable (fun o : Obs X Z =>
      (w o.1 * bandBoundary M L k j o.1) *
      IFM M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMb : ∀ plus, Integrable (fun o : Obs X Z =>
      (w o.1 * bandBoundary M L k (j + 1) o.1) *
      IFM M L (trueNuisance M L) plus k (j + 1) o) (observationLaw M))
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
  have hpi a : Measurable ((trueNuisance M L).piLev a) := by
    change Measurable (fun x => ∑ z ∈ L.S a.val, instProb M z x)
    exact population_instrument_set_probability_measurable M (L.S a.val)
  obtain ⟨hr, zr⟩ := population_continuous_band_regression_correction_zero M L
    (trueNuisance M L).piLev hpi k j hk hj ha hb w hw hJ hMa hMb
  obtain ⟨hp, zp⟩ := population_continuous_band_propensity_correction_zero M h.2.2.2.1
    (policyProp phi M.prop) L hL k j hk hj ha hb w hw hl hh
  obtain ⟨hq, zq⟩ := population_continuous_band_policy_correction_zero M h.2.2.2.1
    dphi hdphi L k j hk hj ha hb w hw hql hqh
  have heq' := (population_continuous_band_score_ae_decomposition M h he phi dphi L
    hL cpi hov hpol k j hk hj hd h0)
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
    filter_upwards [heq'] with o ho
    rw [ho]
    ring
  refine ⟨(((hbase.fun_add hr).fun_add hp).fun_add hq).congr hwEq.symm, ?_⟩
  rw [integral_congr_ae hwEq, integral_add ((hbase.fun_add hr).fun_add hp) hq,
    integral_add (hbase.fun_add hr) hp, integral_add hbase hr, zr, zp, zq]
  ring

-- The correction is integrable because the assignment residual is bounded by one.
-- @node: population_continuous_band_product_assignment_zero
/-- Under [threshold crossing](hyp:h) and [covariate-invariant level ordering](hyp:hL),
for [a nonfinal bin](hyp:hk), [a policy index at least one](hyp:hj)
[and at most its bin's policy-level count](hyp:hjK), with
[a measurable lower boundary of the preceding band](hyp:ha),
[a measurable upper boundary](hyp:hb), and [a measurable covariate weight](hyp:hw),
if [the weighted population mean contrast for that band is integrable](hyp:hi),
[its product with the policy-union assignment indicator minus its conditional
probability is integrable and has population expectation zero](goal). -/
lemma population_continuous_band_product_assignment_zero
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (k j : ℕ)
    (hk : k < L.K) (hj : 1 ≤ j) (hjK : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k (j - 1)))
    (hb : Measurable (bandBoundary M L k j))
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      contJ L (trueNuisance M L) k (j - 1) o.1) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * contJ L (trueNuisance M L) k (j - 1) o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) -
        regularValue (trueNuisance M L).gamma k j o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * contJ L (trueNuisance M L) k (j - 1) o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) -
        regularValue (trueNuisance M L).gamma k j o.1) ∂observationLaw M) = 0 := by
  have hm := population_continuous_band_J_measurable M h q L hL k (j - 1)
    hk (by omega) ha (by simpa [Nat.sub_add_cancel hj] using hb)
  have hg x : regularValue (trueNuisance M L).gamma k j x =
      ∑ z ∈ policyUnion L k j, instProb M z x := by
    simp [regularValue, trueNuisance, gamma, hk.le, hj, hjK]
  simp only [hg]
  exact ⟨population_assignment_residual_weighted_integrable M (policyUnion L k j) _ hi,
    population_assignment_weighted_integral_zero M (policyUnion L k j)
      (fun x => w x * contJ L (trueNuisance M L) k (j - 1) x) (hw.mul hm)
      (population_assignment_residual_weighted_integrable M (policyUnion L k j) _ hi)⟩

-- @node: population_continuous_band_product_weighted_mean
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a measurable policy derivative evaluated at baseline propensities](hyp:hdphi),
[covariate-invariant level ordering](hyp:hL), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [a nonfinal bin](hyp:hk), [a policy index at least one](hyp:hj)
[and at most the bin's policy-level count](hyp:hjK), [measurable lower](hyp:ha)
and [upper boundaries of the preceding band](hyp:hb), [locally bounded boundary
densities](hyp:hd), and [no lower-endpoint atom](hyp:h0), take
[a measurable covariate weight](hyp:hw). Suppose that, after weighting also by the
policy-union probability, [the band mean contrast](hyp:hbase),
[both treated-band residuals](hyp:hJ), [both lower-boundary indicator residual terms](hyp:hMa),
[both upper-boundary indicator residual terms](hyp:hMb),
[the lower baseline propensity term](hyp:hl), [the upper baseline propensity term](hyp:hh),
[the lower policy residual term](hyp:hql), and [the upper policy residual term](hyp:hqh)
are integrable, and that [the band mean contrast weighted without the policy-union
probability is integrable](hyp:hunweighted); then [the weighted product score is
integrable and its expectation equals the expectation of the band mean contrast
weighted by the covariate weight and the policy-union probability](goal). -/
lemma population_continuous_band_product_weighted_mean
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j) (hjK : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k (j - 1)))
    (hb : Measurable (bandBoundary M L k j))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (w : X → ℝ) (hw : Measurable w)
    (hbase : Integrable (fun o : Obs X Z => (w o.1 * gamma M L k j o.1) *
      contJ L (trueNuisance M L) k (j - 1) o.1) (observationLaw M))
    (hJ : ∀ plus, Integrable (fun o : Obs X Z => (w o.1 * gamma M L k j o.1) *
      IFJ M L (trueNuisance M L) plus k (j - 1) o) (observationLaw M))
    (hMa : ∀ plus, Integrable (fun o : Obs X Z =>
      ((w o.1 * gamma M L k j o.1) * bandBoundary M L k (j - 1) o.1) *
      IFM M L (trueNuisance M L) plus k (j - 1) o) (observationLaw M))
    (hMb : ∀ plus, Integrable (fun o : Obs X Z =>
      ((w o.1 * gamma M L k j o.1) * bandBoundary M L k j o.1) *
      IFM M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hl : Integrable (fun o : Obs X Z => ((w o.1 * gamma M L k j o.1) *
      alphaLow M L (trueNuisance M L) k (j - 1) o.1) *
      RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => ((w o.1 * gamma M L k j o.1) *
      alphaHigh M L (trueNuisance M L) k (j - 1) o.1) *
      RpCont L (trueNuisance M L) (k + 1) o) (observationLaw M))
    (hql : Integrable (fun o : Obs X Z => ((w o.1 * gamma M L k j o.1) * bandBoundary M L k (j - 1) o.1) *
      RqCont dphi L (trueNuisance M L) k (j - 1) o) (observationLaw M))
    (hqh : Integrable (fun o : Obs X Z => ((w o.1 * gamma M L k j o.1) * bandBoundary M L k j o.1) *
      RqCont dphi L (trueNuisance M L) k j o) (observationLaw M))
    (hunweighted : Integrable (fun o : Obs X Z => w o.1 *
      contJ L (trueNuisance M L) k (j - 1) o.1) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      psiProd M phi dphi L (trueNuisance M L) k j o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      psiProd M phi dphi L (trueNuisance M L) k j o ∂observationLaw M) =
      ∫ o : Obs X Z, (w o.1 * gamma M L k j o.1) *
        contJ L (trueNuisance M L) k (j - 1) o.1 ∂observationLaw M := by
  have hg : Measurable (gamma M L k j) :=
    population_instrument_set_probability_measurable M (policyUnion L k j)
  obtain ⟨hs, hmean⟩ := population_continuous_band_component_weighted_mean M h he
    phi dphi hdphi L hL cpi hov hpol k (j - 1) hk (by omega) ha
    (by simpa [Nat.sub_add_cancel hj] using hb)
    hd h0
    (fun x => w x * gamma M L k j x) (hw.mul hg) hbase hJ hMa
    (by simpa only [Nat.sub_add_cancel hj] using hMb) hl hh hql
    (by simpa only [Nat.sub_add_cancel hj] using hqh)
  obtain ⟨hi, hz⟩ := population_continuous_band_product_assignment_zero M h.2.2.2.1
    (policyProp phi M.prop) L hL k j hk hj hjK ha hb w hw hunweighted
  have hgamma x : regularValue (trueNuisance M L).gamma k j x = gamma M L k j x := by
    simp [regularValue, trueNuisance, hk.le, hj, hjK]
  simp only [hgamma] at hi hz
  simp only [psiProd, hgamma, mul_add, ← mul_assoc]
  refine ⟨hs.fun_add hi, ?_⟩
  rw [integral_add hs hi, hz, add_zero]
  exact hmean

end Papers.TbsPrteOptimalTransport
