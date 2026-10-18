module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandPolicyRegressionAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.QuantilePolicyCancellation
/-! Centering continuous band scores with jointly fitted assignment and pooled denominators. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_fitted_band_propensity_zero
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[invariant level ordering](hyp:hL), let [the fitted assignment denominators be measurable](hyp:hpi)
and [almost surely bounded below by a common constant](hyp:hclip) that [is positive](hyp:hc).
For [a valid treatment interval](hyp:hk) and [a band below its band count](hyp:hj), with
[measurable lower](hyp:ha) and [upper boundaries](hyp:hb) and a [measurable](hyp:hw),
[integrable covariate weight](hyp:iw), [the weighted sum of the propensity corrections with population coefficients and fitted denominators is integrable and has expectation zero, with the lower correction omitted for the first treatment interval](goal). -/
lemma population_continuous_fitted_band_propensity_zero
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1)))
    (w : X → ℝ) (hw : Measurable w) (iw : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
        RpCont L {trueNuisance M L with piLev := pi} k o) +
        alphaHigh M L (trueNuisance M L) k j o.1 *
          RpCont L {trueNuisance M L with piLev := pi} (k+1) o)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
        RpCont L {trueNuisance M L with piLev := pi} k o) +
        alphaHigh M L (trueNuisance M L) k j o.1 *
          RpCont L {trueNuisance M L with piLev := pi} (k+1) o) ∂observationLaw M) = 0 := by
  obtain ⟨il, ih⟩ := population_continuous_alpha_weights_integrable M h he q L hL
    k j hk hj ha hb w iw
  have ml := hw.mul (population_continuous_band_alphaLow_measurable M L k j hk hj ha hb)
  have mh := hw.mul (population_continuous_band_alphaHigh_measurable M L k j hk hj ha hb)
  have irl := population_RpCont_integrable_of_integrable_weight M h.2.2.2.1 q L hL
    pi hpi c hc hclip k _ ml il
  have irh := population_RpCont_integrable_of_integrable_weight M h.2.2.2.1 q L hL
    pi hpi c hc hclip (k+1) _ mh ih
  have zl := population_RpCont_fitted_denominator_weighted_zero M h.2.2.2.1 q L
    pi hpi hL k _ ml irl
  have zh := population_RpCont_fitted_denominator_weighted_zero M h.2.2.2.1 q L
    pi hpi hL (k+1) _ mh irh
  simp only [Pi.mul_apply] at irl irh zl zh
  by_cases hk0 : k = 0
  · simp only [hk0, if_true, zero_add, ← mul_assoc] at *
    exact ⟨irh, zh⟩
  · simp only [hk0, if_false, mul_add, ← mul_assoc]
    exact ⟨irl.fun_add irh, by rw [integral_add irl irh, zl, zh, add_zero]⟩

-- @node: population_continuous_fitted_band_policy_endpoint_zero
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[measurability of the policy derivative evaluated at baseline propensities](hyp:hdphi),
[boundedness and Lipschitz continuity of that derivative](hyp:hDerivative),
[invariant level ordering](hyp:hL), and [policy overlap](hyp:hpol), suppose
[the fitted pooled denominators are measurable](hyp:htau) and [almost surely bounded below by a common constant](hyp:hclip)
that [is positive](hyp:hc). For [a valid treatment interval](hyp:hk) and
[an endpoint index no greater than its band count](hyp:hi) with [a measurable boundary](hyp:ha)
and a [measurable](hyp:hw), [integrable covariate weight](hyp:iw),
[the policy residual multiplied by the weight and population boundary is integrable and has expectation zero](goal). -/
lemma population_continuous_fitted_band_policy_endpoint_zero
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi)
    (tau : RegularIndex L → X → ℝ) (htau : ∀ a, Measurable (tau a))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ tau a x)
    (k i : ℕ) (hk : k < L.K) (hi : i ≤ L.l k)
    (ha : Measurable (bandBoundary M L k i))
    (w : X → ℝ) (hw : Measurable w) (iw : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => (w o.1 * bandBoundary M L k i o.1) *
      RqCont dphi L {trueNuisance M L with tauLev := tau} k i o) (observationLaw M) ∧
    (∫ o : Obs X Z, (w o.1 * bandBoundary M L k i o.1) *
      RqCont dphi L {trueNuisance M L with tauLev := tau} k i o ∂observationLaw M) = 0 := by
  by_cases hi0 : i = 0
  · simp only [hi0, RqCont, true_or, if_true, mul_zero, integral_zero]
    exact ⟨integrable_zero _ _ _, True.intro⟩
  · let a : RegularIndex L := ⟨(k,i), hk.le, by omega, hi⟩
    exact population_RqCont_fitted_pooled_denominator_zero M h.2.2.2.1 dphi hdphi
      hDerivative q L hL cpi hpol tau htau c hc hclip a
      (fun x => w x * bandBoundary M L k i x) (hw.mul ha)
      (population_bandBoundary_weight_integrable M h he q L hL k i hk hi ha w iw)

-- @node: population_continuous_fitted_band_score_ae_decomposition
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[invariant ordering of baseline and policy levels](hyp:hL), [baseline overlap](hyp:hov),
and [policy overlap](hyp:hpol), take [a valid treatment interval](hyp:hk) and
[a band below its band count](hyp:hj), with [bounded boundary densities](hyp:hd) and
[no atom at the lower outcome endpoint](hyp:h0).
Then [the band score with fitted assignment and pooled denominators equals almost surely the population band outcome contrast plus its regression correction, its two propensity corrections, and its signed endpoint policy corrections](goal). -/
lemma population_continuous_fitted_band_score_ae_decomposition
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (pi : PositiveIndex L.K → X → ℝ) (tau : RegularIndex L → X → ℝ)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L) :
    (fun o : Obs X Z => contScoreComponents M phi dphi L
      {trueNuisance M L with piLev := pi, tauLev := tau} k j o)
      =ᵐ[observationLaw M] (fun o =>
        contJ L (trueNuisance M L) k j o.1 +
        continuousBandRegressionCorrection M L {trueNuisance M L with piLev := pi} k j o +
        ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
          RpCont L {trueNuisance M L with piLev := pi} k o) +
          alphaHigh M L (trueNuisance M L) k j o.1 *
            RpCont L {trueNuisance M L with piLev := pi} (k + 1) o) +
        (-(nuValue M (trueNuisance M L) k j o.1 *
          RqCont dphi L {trueNuisance M L with tauLev := tau} k j o) +
          nuValue M (trueNuisance M L) k (j + 1) o.1 *
            RqCont dphi L {trueNuisance M L with tauLev := tau} k (j + 1) o)) := by
  have hm := population_continuous_score_quantile_moment_of_density M h he phi L hL
    cpi hov hpol hd h0
  filter_upwards [observationLaw_covariate_ae M _ hm] with o ho
  have ha := ho k hk j hj.le
  have hb := ho k hk (j + 1) (by omega)
  have hd := continuous_band_score_regression_decomposition M phi dphi L
    {trueNuisance M L with piLev := pi, tauLev := tau} k j o
  change contScoreComponents M phi dphi L _ k j o =
    contJ L (trueNuisance M L) k j o.1 +
    continuousBandRegressionCorrection M L {trueNuisance M L with piLev := pi} k j o +
    nuValue M (trueNuisance M L) k j o.1 *
      (positiveValue (trueNuisance M L).pLev (k+1) o.1 *
        boundaryValue (trueNuisance M L).Mplus k j o.1 -
        positiveValue (trueNuisance M L).pLev k o.1 *
          minusBoundaryValue (trueNuisance M L).Mminus k j o.1 -
        (pooledQ phi L (trueNuisance M L) k j o.1 -
          positiveValue (trueNuisance M L).pLev k o.1)) -
    nuValue M (trueNuisance M L) k (j+1) o.1 *
      (positiveValue (trueNuisance M L).pLev (k+1) o.1 *
        boundaryValue (trueNuisance M L).Mplus k (j+1) o.1 -
        positiveValue (trueNuisance M L).pLev k o.1 *
          minusBoundaryValue (trueNuisance M L).Mminus k (j+1) o.1 -
        (pooledQ phi L (trueNuisance M L) k (j+1) o.1 -
          positiveValue (trueNuisance M L).pLev k o.1)) +
    (if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
      RpCont L {trueNuisance M L with piLev := pi} k o) +
    alphaHigh M L (trueNuisance M L) k j o.1 *
      RpCont L {trueNuisance M L with piLev := pi} (k+1) o -
    nuValue M (trueNuisance M L) k j o.1 *
      RqCont dphi L {trueNuisance M L with tauLev := tau} k j o +
    nuValue M (trueNuisance M L) k (j+1) o.1 *
      RqCont dphi L {trueNuisance M L with tauLev := tau} k (j+1) o at hd
  rw [ha, hb] at hd
  rw [hd]
  ring

-- @node: population_continuous_fitted_band_component_mean
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[measurability of the policy derivative evaluated at baseline propensities](hyp:hdphi),
[boundedness and Lipschitz continuity of that derivative](hyp:hDerivative),
[invariant ordering of baseline and policy levels](hyp:hL), [baseline overlap](hyp:hov),
and [policy overlap](hyp:hpol), suppose [the fitted assignment denominators are measurable](hyp:hpi)
and [bounded below almost surely by the clipping constant](hyp:hclip), while
[the fitted pooled denominators are measurable](hyp:htau) and [bounded below almost surely by the same constant](hyp:htclip),
which [is positive](hyp:hc). For [a valid treatment interval](hyp:hk) and
[a band below its band count](hyp:hj), with [measurable lower](hyp:ha) and
[upper boundaries](hyp:hb), [bounded boundary densities](hyp:hden),
[no atom at the lower outcome endpoint](hyp:h0), and a [measurable](hyp:hw),
[integrable covariate weight](hyp:iw), [the weighted band score with fitted denominators is integrable and its expectation equals the expected weighted population band outcome contrast](goal). -/
lemma population_continuous_fitted_band_component_mean
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (tau : RegularIndex L → X → ℝ) (htau : ∀ a, Measurable (tau a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x)
    (htclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ tau a x)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1)))
    (hden : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (w : X → ℝ) (hw : Measurable w) (iw : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * contScoreComponents M phi dphi L
      {trueNuisance M L with piLev := pi, tauLev := tau} k j o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * contScoreComponents M phi dphi L
      {trueNuisance M L with piLev := pi, tauLev := tau} k j o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * contJ L (trueNuisance M L) k j o.1 ∂observationLaw M := by
  have ib := population_contJ_weighted_integrable M h he (policyProp phi M.prop)
    L hL k j hk hj ha hb w hw iw
  obtain ⟨ir, zr⟩ := population_continuous_band_regression_zero_of_clipped_denominator
    M h he (policyProp phi M.prop) L hL pi hpi c hc hclip k j hk hj ha hb w hw iw
  obtain ⟨ip, zp⟩ := population_continuous_fitted_band_propensity_zero M h he
    (policyProp phi M.prop) L hL pi hpi c hc hclip k j hk hj ha hb w hw iw
  obtain ⟨ia, za⟩ := population_continuous_fitted_band_policy_endpoint_zero M h he
    dphi hdphi hDerivative (policyProp phi M.prop) L hL cpi hpol tau htau c hc
    htclip k j hk hj.le ha w hw iw
  obtain ⟨iz, zz⟩ := population_continuous_fitted_band_policy_endpoint_zero M h he
    dphi hdphi hDerivative (policyProp phi M.prop) L hL cpi hpol tau htau c hc
    htclip k (j+1) hk (by omega) hb w hw iw
  have hnu i (hi : i ≤ L.l k) x : nuValue M (trueNuisance M L) k i x =
      bandBoundary M L k i x := population_nuValue_eq_bandBoundary M L k i hk hi x
  have hae := population_continuous_fitted_band_score_ae_decomposition M h he
    phi dphi L hL cpi hov hpol pi tau k j hk hj hden h0
  have heq : (fun o : Obs X Z => w o.1 * contScoreComponents M phi dphi L
      {trueNuisance M L with piLev := pi, tauLev := tau} k j o) =ᵐ[observationLaw M]
    (fun o => w o.1 * contJ L (trueNuisance M L) k j o.1 +
      w o.1 * continuousBandRegressionCorrection M L {trueNuisance M L with piLev := pi} k j o +
      w o.1 * ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
        RpCont L {trueNuisance M L with piLev := pi} k o) +
        alphaHigh M L (trueNuisance M L) k j o.1 *
          RpCont L {trueNuisance M L with piLev := pi} (k+1) o) -
      (w o.1 * bandBoundary M L k j o.1) *
        RqCont dphi L {trueNuisance M L with tauLev := tau} k j o +
      (w o.1 * bandBoundary M L k (j+1) o.1) *
        RqCont dphi L {trueNuisance M L with tauLev := tau} k (j+1) o) := by
    filter_upwards [hae] with o ho
    rw [ho, hnu j hj.le, hnu (j+1) (by omega)]
    ring
  refine ⟨((((ib.fun_add ir).fun_add ip).sub' ia).fun_add iz).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add (((ib.fun_add ir).fun_add ip).sub' ia) iz,
    integral_sub ((ib.fun_add ir).fun_add ip) ia, integral_add (ib.fun_add ir) ip,
    integral_add ib ir, zr, zp, za, zz]
  ring

-- @node: population_continuous_fitted_band_product_mean
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[measurability of the policy derivative evaluated at baseline propensities](hyp:hdphi),
[boundedness and Lipschitz continuity of that derivative](hyp:hDerivative),
[invariant ordering of baseline and policy levels](hyp:hL), [baseline overlap](hyp:hov),
and [policy overlap](hyp:hpol), suppose [the fitted assignment denominators are measurable](hyp:hpi)
and [bounded below almost surely by the clipping constant](hyp:hclip), while
[the fitted pooled denominators are measurable](hyp:htau) and [bounded below almost surely by the same constant](hyp:htclip),
which [is positive](hyp:hc). For [a valid treatment interval](hyp:hk) and
[a band below its band count](hyp:hj), with [measurable lower](hyp:ha) and
[upper boundaries](hyp:hb), [bounded boundary densities](hyp:hden), and
[no atom at the lower outcome endpoint](hyp:h0), assume [the fitted weight for this band is measurable](hyp:hg)
and [integrable under the covariate distribution](hyp:ig).
Then [the product score with these fitted denominators and weights is integrable, and its expectation equals the expected population band weight times the population band outcome contrast](goal). -/
lemma population_continuous_fitted_band_product_mean
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (tau : RegularIndex L → X → ℝ) (htau : ∀ a, Measurable (tau a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x)
    (htclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ tau a x)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1)))
    (hden : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (g : RegularIndex L → X → ℝ)
    (hg : Measurable (regularValue g k (j+1)))
    (ig : Integrable (regularValue g k (j+1)) (xLaw M)) :
    Integrable (psiProd M phi dphi L
      {trueNuisance M L with piLev := pi, tauLev := tau, gamma := g} k (j+1))
        (observationLaw M) ∧
    (∫ o : Obs X Z, psiProd M phi dphi L
      {trueNuisance M L with piLev := pi, tauLev := tau, gamma := g} k (j+1) o
        ∂observationLaw M) =
      ∫ o : Obs X Z, gamma M L k (j+1) o.1 *
        contJ L (trueNuisance M L) k j o.1 ∂observationLaw M := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let e := {trueNuisance M L with piLev := pi, tauLev := tau, gamma := g}
  let b := {trueNuisance M L with piLev := pi, tauLev := tau}
  let w := regularValue g k (j+1)
  obtain ⟨is, ms⟩ := population_continuous_fitted_band_component_mean M h he phi dphi
    hdphi hDerivative L hL cpi hov hpol pi hpi tau htau c hc hclip htclip
    k j hk hj ha hb hden h0 w hg ig
  have ij := population_contJ_weighted_integrable M h he (policyProp phi M.prop)
    L hL k j hk hj ha hb w hg ig
  have ic : Integrable (fun o : Obs X Z => w o.1 *
      (contScoreComponents M phi dphi L b k j o - contJ L (trueNuisance M L) k j o.1))
      (observationLaw M) := by
    simpa only [mul_sub] using is.sub' ij
  have zc : (∫ o : Obs X Z, w o.1 *
      (contScoreComponents M phi dphi L b k j o - contJ L (trueNuisance M L) k j o.1)
        ∂observationLaw M) = 0 := by
    simp only [mul_sub]
    rw [integral_sub is ij, ms, sub_self]
  have ib := population_contJ_weighted_integrable M h he (policyProp phi M.prop)
    L hL k j hk hj ha hb (fun _ => 1) measurable_const (integrable_const 1)
  simp only [one_mul] at ib
  have im : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k (j+1))) := by
    unfold indicator
    exact Measurable.ite ((policyUnion L k (j+1)).finite_toSet.measurableSet.preimage
      measurable_snd.fst) measurable_const measurable_const
  have bm : ∀ᵐ o : Obs X Z ∂observationLaw M,
      ‖indicator (o.2.1 ∈ policyUnion L k (j+1))‖ ≤ (1 : ℝ) := by
    filter_upwards [] with o
    unfold indicator; split_ifs <;> norm_num
  have ii := ib.bdd_mul im.aestronglyMeasurable bm
  have mi : (∫ o : Obs X Z, indicator (o.2.1 ∈ policyUnion L k (j+1)) *
      contJ L (trueNuisance M L) k j o.1 ∂observationLaw M) =
      ∫ o : Obs X Z, gamma M L k (j+1) o.1 *
        contJ L (trueNuisance M L) k j o.1 ∂observationLaw M := by
    have hi := population_assignment_weighted_integral_zero M (policyUnion L k (j+1))
      (contJ L (trueNuisance M L) k j)
      (population_continuous_band_J_measurable M h.2.2.2.1 (policyProp phi M.prop)
        L hL k j hk hj ha hb)
      (population_assignment_residual_weighted_integrable M (policyUnion L k (j+1)) _ ib)
    have igj := population_contJ_weighted_integrable M h he (policyProp phi M.prop)
      L hL k j hk hj ha hb (gamma M L k (j+1))
      (population_instrument_set_probability_measurable M _) ?_
    · simp only [mul_sub] at hi
      rw [integral_sub (by simpa only [mul_comm] using ii) (by
        simpa only [gamma, mul_comm] using igj)] at hi
      simpa only [gamma, mul_comm] using sub_eq_zero.mp hi
    · have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
      apply Integrable.of_bound
        (population_instrument_set_probability_measurable M _).aestronglyMeasurable 1
      filter_upwards [] with x
      have hx := population_instrument_set_probability_range M (policyUnion L k (j+1)) x
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
  have hid : psiProd M phi dphi L e k (j+1) = fun o : Obs X Z =>
      w o.1 * (contScoreComponents M phi dphi L b k j o -
        contJ L (trueNuisance M L) k j o.1) +
      indicator (o.2.1 ∈ policyUnion L k (j+1)) * contJ L (trueNuisance M L) k j o.1 := by
    funext o
    change w o.1 * contScoreComponents M phi dphi L b k j o +
      contJ L (trueNuisance M L) k j o.1 *
        (indicator (o.2.1 ∈ policyUnion L k (j+1)) - w o.1) = _
    ring
  change Integrable (psiProd M phi dphi L e k (j+1)) _ ∧ _
  rw [hid]
  exact ⟨ic.fun_add ii, by rw [integral_add ic ii, zc, zero_add, mi]⟩

end Papers.TbsPrteOptimalTransport
