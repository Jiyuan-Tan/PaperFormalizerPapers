module
public import Papers.TbsPrteOptimalTransport.Helpers.QuantilePolicyCancellation
/-! Assembly of signed quantile boundary changes for every continuous band. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The first band has a fixed lower endpoint; interior bands use the gap-derived ordering.
-- @node: population_continuous_band_signed_quantile_block_orthogonality
/-- Assume [the model's structural support, consistency, exogeneity, threshold-crossing,
uniform-resistance, and domain conditions](hyp:h), [known outcome endpoints](hyp:he),
[a covariate-invariant baseline and policy level structure](hyp:hL), [interior policy
levels distinct from their lower baseline boundaries](hyp:hOff), [uniform positive
separation of distinct baseline and policy propensity values](hyp:hGap), [baseline
overlap](hyp:hov), [policy overlap with the same constant](hyp:hpol), [bounded treated-outcome
densities near interior quantile boundaries](hyp:hden), and [an admissible continuous
nuisance direction from the population nuisance](hyp:hd). For [a bin before the final
bin](hyp:hk) and [a band index below that bin's policy-level count](hyp:hj), with
[measurable lower](hyp:ha) and [upper quantile boundaries](hyp:hb), [the population mean
of the positive-minus-negative quantile block change, weighted by the moving selected
product weight, has derivative zero at zero when assignment probabilities and quantile
boundaries move along the admissible path, relative to moving assignment probabilities
alone](goal). -/
lemma population_continuous_band_signed_quantile_block_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) (g : RegularIndex L)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    let block := fun plus t (o : Obs X Z) =>
      (IFJ M L (e t) plus k j o + nuValue M (e t) k j o.1 * IFM M L (e t) plus k j o -
        nuValue M (e t) k (j+1) o.1 * IFM M L (e t) plus k (j+1) o) -
      (IFJ M L (b t) plus k j o + bandBoundary M L k j o.1 * IFM M L (b t) plus k j o -
        bandBoundary M L k (j+1) o.1 * IFM M L (b t) plus k (j+1) o)
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      (block true t o - block false t o) ∂observationLaw M) 0 0 := by
  by_cases hj0 : j = 0
  · subst j
    simpa only [bandBoundary, true_or, if_true] using
      population_continuous_first_band_admissible_signed_quantile_block_orthogonality
        M L hden cpi hov del hd k hk (by omega) g hb
  · exact population_continuous_interior_band_signed_quantile_block_orthogonality_of_gap
      M h he phi L hL hOff gap hGap cpi hov hpol hden del hd
      k hk j (by omega) hj g ha hb

-- Both sides are integrable locally, so their derivatives can be assembled under the integral.
-- @node: population_continuous_band_quantile_blocks_integrable
/-- Under [the structural instrumental-variable model assumptions](hyp:h), [known
outcome endpoints](hyp:he), [a covariate-invariant baseline and policy level
structure](hyp:hL), [interior policy levels off their lower baseline boundaries](hyp:hOff),
[uniform positive separation of distinct propensity values](hyp:hGap), [baseline
overlap](hyp:hov), [policy overlap with the same constant](hyp:hpol), [bounded densities
near interior quantile boundaries](hyp:hden), and [an admissible continuous nuisance
direction at the population nuisance](hyp:hd), take [a bin before the final bin](hyp:hk)
and [a band index below its policy-level count](hyp:hj) with [measurable lower](hyp:ha)
and [upper boundaries](hyp:hb). Then [throughout some neighborhood of zero, each signed
quantile block change is integrable after multiplication by the selected moving product
weight, comparing simultaneous assignment-probability and quantile-boundary changes
with assignment-probability changes alone](goal). -/
lemma population_continuous_band_quantile_blocks_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) (g : RegularIndex L)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev}
    let block := fun plus t (o : Obs X Z) =>
      (IFJ M L (e t) plus k j o + nuValue M (e t) k j o.1 * IFM M L (e t) plus k j o -
        nuValue M (e t) k (j+1) o.1 * IFM M L (e t) plus k (j+1) o) -
      (IFJ M L (b t) plus k j o + bandBoundary M L k j o.1 * IFM M L (b t) plus k j o -
        bandBoundary M L k (j+1) o.1 * IFM M L (b t) plus k (j+1) o)
    ∀ᶠ t : ℝ in 𝓝 0, ∀ plus : Bool,
      Integrable (fun o : Obs X Z => (path t).gamma g o.1 * block plus t o)
        (observationLaw M) := by
  by_cases hj0 : j = 0
  · subst j
    have hp := population_continuous_first_band_admissible_quantile_block_integrable
      M L cpi hov del hd k hk (by omega) g true hb
    have hm := population_continuous_first_band_admissible_quantile_block_integrable
      M L cpi hov del hd k hk (by omega) g false hb
    filter_upwards [hp, hm] with t ip im
    intro plus
    cases plus
    · simpa only [bandBoundary, true_or, if_true] using im
    · simpa only [bandBoundary, true_or, if_true] using ip
  · have horder := continuous_admissible_interior_band_ordered_path M h he phi L hL
      hOff gap hGap cpi hov hpol hden del hd k j hk (by omega) hj
    have hp := population_continuous_interior_band_admissible_quantile_block_integrable
      M L cpi hov del hd k hk j (by omega) hj g true ha hb horder
    have hm := population_continuous_interior_band_admissible_quantile_block_integrable
      M L cpi hov del hd k hk j (by omega) hj g false ha hb horder
    filter_upwards [hp, hm] with t ip im
    intro plus
    cases plus
    · exact im
    · exact ip

-- The score's explicit quantile factors are separated from indicator boundaries,
-- propensity representers, and pooled policy residuals before taking expectations.
-- @node: continuous_band_quantile_score_difference_decomposition
/-- If two continuous nuisance specifications have [equal treatment levels](hyp:hp),
[equal baseline assignment probabilities](hyp:hpi), [equal positive and negative
integrated-outcome components](hyp:hJp,hJm), [equal positive and negative distribution
components](hyp:hMp,hMm), [equal instrument propensities](hyp:hprop), [equal pooling
shares](hyp:hshare), and [equal policy-cell probabilities](hyp:htau), then [their band
component-score difference equals the signed quantile block difference plus the lower
and upper quantile displacements times their quantile-equation moments, the changes in
treatment-residual coefficients times the baseline treatment residuals, and the signed
quantile displacements times the baseline policy residuals](goal). -/
lemma continuous_band_quantile_score_difference_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hp : e.pLev = b.pLev) (hpi : e.piLev = b.piLev)
    (hJp : e.Jplus = b.Jplus) (hJm : e.Jminus = b.Jminus)
    (hMp : e.Mplus = b.Mplus) (hMm : e.Mminus = b.Mminus)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share)
    (htau : e.tauLev = b.tauLev) (k j : ℕ) (o : Obs X Z) :
    let block := fun plus =>
      (IFJ M L e plus k j o + nuValue M e k j o.1 * IFM M L e plus k j o -
        nuValue M e k (j+1) o.1 * IFM M L e plus k (j+1) o) -
      (IFJ M L b plus k j o + nuValue M b k j o.1 * IFM M L b plus k j o -
        nuValue M b k (j+1) o.1 * IFM M L b plus k (j+1) o)
    let moment := fun a =>
      positiveValue b.pLev (k+1) o.1 * boundaryValue b.Mplus k a o.1 -
      positiveValue b.pLev k o.1 * minusBoundaryValue b.Mminus k a o.1 -
      (pooledQ phi L b k a o.1 - positiveValue b.pLev k o.1)
    contScoreComponents M phi dphi L e k j o - contScoreComponents M phi dphi L b k j o =
      (block true - block false) +
      ((nuValue M e k j o.1 - nuValue M b k j o.1) * moment j -
        (nuValue M e k (j+1) o.1 - nuValue M b k (j+1) o.1) * moment (j+1)) +
      ((if k = 0 then 0 else (alphaLow M L e k j o.1 - alphaLow M L b k j o.1) *
        RpCont L b k o) +
        (alphaHigh M L e k j o.1 - alphaHigh M L b k j o.1) * RpCont L b (k+1) o) +
      (-(nuValue M e k j o.1 - nuValue M b k j o.1) * RqCont dphi L b k j o +
        (nuValue M e k (j+1) o.1 - nuValue M b k (j+1) o.1) *
          RqCont dphi L b k (j+1) o) := by
  have hq a : pooledQ phi L e k a o.1 = pooledQ phi L b k a o.1 := by
    simp only [pooledQ, shareValue, hp, hprop, hshare]
  have hrp a : RpCont L e a o = RpCont L b a o := by
    simp only [RpCont, hp, hpi]
  have hrq a : RqCont dphi L e k a o = RqCont dphi L b k a o := by
    simp only [RqCont, htau, hprop]
  dsimp only
  simp only [contScoreComponents, contJ, hp, hJp, hJm, hMp, hMm, hq, hrp, hrq]
  split_ifs <;> ring

-- The conditional quantile equation kills the two explicit multiplicative terms.
-- The fitted assignment and pooled denominators do not enter that equation.
-- @node: population_continuous_quantile_score_difference_ae
/-- Assume [the structural instrumental-variable model conditions](hyp:h), [known outcome
endpoints](hyp:he), [a covariate-invariant baseline and policy level structure](hyp:hL),
[baseline overlap](hyp:hov), [policy overlap with the same constant](hyp:hpol), [bounded
densities near interior quantile boundaries](hyp:hden), and [no treated-outcome atom at
the lower outcome endpoint](hyp:h0). For [a bin before the final bin](hyp:hk) and [a band
index below its policy-level count](hyp:hj), [the score change from replacing only the
population quantile boundaries, while holding arbitrary baseline and policy-cell
assignment probabilities fixed, equals almost surely the signed quantile block change
plus the treatment-residual coefficient changes and signed quantile displacements times
policy residuals; the explicit quantile-equation moment terms vanish](goal). -/
lemma population_continuous_quantile_score_difference_ae
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (pi : PositiveIndex L.K → X → ℝ) (tau : RegularIndex L → X → ℝ)
    (nu : BoundaryIndex L → X → ℝ) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    let e := {trueNuisance M L with piLev := pi, tauLev := tau, nu := nu}
    let b := {trueNuisance M L with piLev := pi, tauLev := tau}
    let block := fun plus (o : Obs X Z) =>
      (IFJ M L e plus k j o + nuValue M e k j o.1 * IFM M L e plus k j o -
        nuValue M e k (j+1) o.1 * IFM M L e plus k (j+1) o) -
      (IFJ M L b plus k j o + bandBoundary M L k j o.1 * IFM M L b plus k j o -
        bandBoundary M L k (j+1) o.1 * IFM M L b plus k (j+1) o)
    ∀ᵐ o ∂observationLaw M,
      contScoreComponents M phi dphi L e k j o - contScoreComponents M phi dphi L b k j o =
        (block true o - block false o) +
        ((if k = 0 then 0 else (alphaLow M L e k j o.1 - alphaLow M L b k j o.1) *
          RpCont L b k o) +
          (alphaHigh M L e k j o.1 - alphaHigh M L b k j o.1) * RpCont L b (k+1) o) +
        (-(nuValue M e k j o.1 - bandBoundary M L k j o.1) * RqCont dphi L b k j o +
          (nuValue M e k (j+1) o.1 - bandBoundary M L k (j+1) o.1) *
            RqCont dphi L b k (j+1) o) := by
  dsimp only
  let e := {trueNuisance M L with piLev := pi, tauLev := tau, nu := nu}
  let b := {trueNuisance M L with piLev := pi, tauLev := tau}
  have hm := population_continuous_score_quantile_moment_of_density M h he phi L hL
    cpi hov hpol hden h0
  filter_upwards [observationLaw_covariate_ae M _ hm] with o ho
  have ha : positiveValue b.pLev (k+1) o.1 * boundaryValue b.Mplus k j o.1 -
      positiveValue b.pLev k o.1 * minusBoundaryValue b.Mminus k j o.1 -
      (pooledQ phi L b k j o.1 - positiveValue b.pLev k o.1) = 0 :=
    ho k hk j hj.le
  have hb : positiveValue b.pLev (k+1) o.1 * boundaryValue b.Mplus k (j+1) o.1 -
      positiveValue b.pLev k o.1 * minusBoundaryValue b.Mminus k (j+1) o.1 -
      (pooledQ phi L b k (j+1) o.1 - positiveValue b.pLev k o.1) = 0 :=
    ho k hk (j+1) (by omega)
  have hna : nuValue M b k j o.1 = bandBoundary M L k j o.1 :=
    population_nuValue_eq_bandBoundary M L k j hk hj.le o.1
  have hnb : nuValue M b k (j+1) o.1 = bandBoundary M L k (j+1) o.1 :=
    population_nuValue_eq_bandBoundary M L k (j+1) hk (by omega) o.1
  have hid := continuous_band_quantile_score_difference_decomposition M phi dphi L e b
    rfl rfl rfl rfl rfl rfl rfl rfl rfl k j o
  dsimp only at hid
  rw [ha, hb, hna, hnb] at hid
  simpa only [mul_zero, sub_zero, add_zero] using hid

-- Centering holds throughout the admissible neighborhood, with both denominators moving.
-- @node: population_continuous_quantile_score_residuals_zero
/-- Under [threshold crossing](hyp:h), suppose [the policy derivative evaluated at the
structural propensity is measurable](hyp:hdphi), [that derivative is uniformly bounded
and Lipschitz in unit-interval propensity](hyp:hDerivative), [the baseline and policy
level structure is invariant across covariates](hyp:hL), [baseline overlap holds](hyp:hov),
[policy overlap holds with the same constant](hyp:hpol), and [the continuous nuisance
direction is admissible at the population nuisance](hyp:hd). For [a bin before the final
bin](hyp:hk) and [a band index below its policy-level count](hyp:hj) with [measurable
lower](hyp:ha) and [upper quantile boundaries](hyp:hb), [throughout a neighborhood of
zero the sum of the treatment-residual coefficient changes and the signed quantile
displacements times policy residuals, multiplied by the selected moving product weight,
is integrable and has population mean zero, even as both assignment denominators move
along the nuisance path](goal). -/
lemma population_continuous_quantile_score_residuals_zero
    (h : ThresholdCrossing M) (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) (g : RegularIndex L)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev}
    let P := fun t (o : Obs X Z) =>
      (if k = 0 then 0 else (alphaLow M L (e t) k j o.1 - alphaLow M L (b t) k j o.1) *
        RpCont L (b t) k o) +
      (alphaHigh M L (e t) k j o.1 - alphaHigh M L (b t) k j o.1) * RpCont L (b t) (k+1) o
    let Q := fun t (o : Obs X Z) =>
      -(nuValue M (e t) k j o.1 - bandBoundary M L k j o.1) * RqCont dphi L (b t) k j o +
      (nuValue M (e t) k (j+1) o.1 - bandBoundary M L k (j+1) o.1) *
        RqCont dphi L (b t) k (j+1) o
    ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => (path t).gamma g o.1 * (P t o + Q t o))
        (observationLaw M) ∧
      (∫ o : Obs X Z, (path t).gamma g o.1 * (P t o + Q t o) ∂observationLaw M) = 0 := by
  dsimp only
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
    continuous_admissible_weighted_quantile_displacement_regular M L del hd k j hk hj.le g,
    continuous_admissible_weighted_quantile_displacement_regular M L del hd k (j+1) hk (by omega) g,
    population_continuous_admissible_quantile_policy_zero M h dphi hdphi hDerivative
      q L hL cpi hpol del hd k j hk hj.le g,
    population_continuous_admissible_quantile_policy_zero M h dphi hdphi hDerivative
      q L hL cpi hpol del hd k (j+1) hk (by omega) g,
    continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t hclip hda hdb za zb ht
  have had := hpath t ht
  rcases had with ⟨_, _, _, _, _, hpim, _⟩
  have zp := population_continuous_quantile_propensity_difference_zero M h q L hL
    (trueNuisance M L + t • del).piLev hpim (trueNuisance M L + t • del).nu
    (cpi/2) (div_pos hov.1 (by norm_num)) hclip k j hk hj ha hb
    ((trueNuisance M L + t • del).gamma g)
    (fun x => nuValue M {trueNuisance M L with nu := (trueNuisance M L + t • del).nu}
      k j x - bandBoundary M L k j x)
    (fun x => nuValue M {trueNuisance M L with nu := (trueNuisance M L + t • del).nu}
      k (j+1) x - bandBoundary M L k (j+1) x)
    (fun _ => rfl) (fun _ => rfl) hda.1 hdb.1 hda.2 hdb.2
  dsimp only at zp za zb
  constructor
  · apply (zp.1.fun_add (za.1.neg.fun_add zb.1)).congr
    filter_upwards [] with o
    simp only [Pi.neg_apply, alphaLow, alphaHigh, RpCont, RqCont, nuValue]
    ring
  · have hz := integral_add zp.1 (za.1.neg.fun_add zb.1)
    rw [integral_add za.1.neg zb.1] at hz
    simp only [Pi.neg_apply] at hz
    rw [integral_neg, zp.2, za.2, zb.2, neg_zero, add_zero, add_zero] at hz
    apply Eq.trans ?_ hz
    apply integral_congr_ae
    filter_upwards [] with o
    simp only [Pi.neg_apply, alphaLow, alphaHigh, RpCont, RqCont, nuValue]
    ring

-- This is the actual component-score quantile change, rather than an isolated
-- boundary term. The conditional moment equation and both centered representers
-- reduce its mean to the signed swept-boundary remainder with derivative zero.
-- @node: population_continuous_band_quantile_score_orthogonality
/-- Assume [the structural instrumental-variable model conditions](hyp:h), [known outcome
endpoints](hyp:he), [measurability of the policy derivative at the structural
propensity](hyp:hdphi), [uniform boundedness and Lipschitz continuity of that derivative
in unit-interval propensity](hyp:hDerivative), [a covariate-invariant baseline and policy
level structure](hyp:hL), [interior policy levels off their lower baseline
boundaries](hyp:hOff), [uniform positive separation of distinct propensity values](hyp:hGap),
[baseline overlap](hyp:hov), [policy overlap with the same constant](hyp:hpol), [bounded
densities near interior quantile boundaries](hyp:hden), [no treated-outcome atom at the
lower outcome endpoint](hyp:h0), and [an admissible continuous nuisance direction at the
population nuisance](hyp:hd). For [a bin before the final bin](hyp:hk) and [a band index
below its policy-level count](hyp:hj), with [measurable lower](hyp:ha) and [upper quantile
boundaries](hyp:hb), [the band component-score change caused by moving quantile
boundaries, weighted by the selected moving product weight and with both assignment
denominators moving in both specifications, has population-mean derivative zero at
zero and is integrable throughout a neighborhood of zero](goal). -/
lemma population_continuous_band_quantile_score_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) (g : RegularIndex L)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      (contScoreComponents M phi dphi L (e t) k j o -
        contScoreComponents M phi dphi L (b t) k j o) ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z => (path t).gamma g o.1 *
      (contScoreComponents M phi dphi L (e t) k j o -
        contScoreComponents M phi dphi L (b t) k j o)) (observationLaw M)) := by
  dsimp only
  let path := fun t : ℝ => trueNuisance M L + t • del
  let e := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, nu := (path t).nu}
  let b := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev}
  let block := fun plus t (o : Obs X Z) =>
    (IFJ M L (e t) plus k j o + nuValue M (e t) k j o.1 * IFM M L (e t) plus k j o -
      nuValue M (e t) k (j+1) o.1 * IFM M L (e t) plus k (j+1) o) -
    (IFJ M L (b t) plus k j o + bandBoundary M L k j o.1 * IFM M L (b t) plus k j o -
      bandBoundary M L k (j+1) o.1 * IFM M L (b t) plus k (j+1) o)
  let P := fun t (o : Obs X Z) =>
    (if k = 0 then 0 else (alphaLow M L (e t) k j o.1 - alphaLow M L (b t) k j o.1) *
      RpCont L (b t) k o) +
    (alphaHigh M L (e t) k j o.1 - alphaHigh M L (b t) k j o.1) * RpCont L (b t) (k+1) o
  let Q := fun t (o : Obs X Z) =>
    -(nuValue M (e t) k j o.1 - bandBoundary M L k j o.1) * RqCont dphi L (b t) k j o +
    (nuValue M (e t) k (j+1) o.1 - bandBoundary M L k (j+1) o.1) *
      RqCont dphi L (b t) k (j+1) o
  have zblock : HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      (block true t o - block false t o) ∂observationLaw M) 0 0 :=
    population_continuous_band_signed_quantile_block_orthogonality M h he phi L hL
      hOff gap hGap cpi hov hpol hden del hd k j hk hj g ha hb
  have iblock : ∀ᶠ t : ℝ in 𝓝 0, ∀ plus : Bool,
      Integrable (fun o : Obs X Z => (path t).gamma g o.1 * block plus t o)
        (observationLaw M) :=
    population_continuous_band_quantile_blocks_integrable M h he phi L hL
      hOff gap hGap cpi hov hpol hden del hd k j hk hj g ha hb
  have izero : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => (path t).gamma g o.1 * (P t o + Q t o))
        (observationLaw M) ∧
      (∫ o : Obs X Z, (path t).gamma g o.1 * (P t o + Q t o) ∂observationLaw M) = 0 :=
    population_continuous_quantile_score_residuals_zero M h.2.2.2.1 dphi hdphi
      hDerivative (policyProp phi M.prop) L hL cpi hov hpol del hd k j hk hj g ha hb
  have hmean : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => (path t).gamma g o.1 *
        (contScoreComponents M phi dphi L (e t) k j o -
          contScoreComponents M phi dphi L (b t) k j o)) (observationLaw M) ∧
      (∫ o : Obs X Z, (path t).gamma g o.1 *
        (contScoreComponents M phi dphi L (e t) k j o -
          contScoreComponents M phi dphi L (b t) k j o) ∂observationLaw M) =
      ∫ o : Obs X Z, (path t).gamma g o.1 * (block true t o - block false t o)
        ∂observationLaw M := by
    filter_upwards [iblock, izero] with t it iz
    have ib : Integrable (fun o : Obs X Z => (path t).gamma g o.1 *
        (block true t o - block false t o)) (observationLaw M) := by
      apply ((it true).sub' (it false)).congr
      exact Eventually.of_forall fun o => (mul_sub _ _ _).symm
    have heq : (fun o : Obs X Z => (path t).gamma g o.1 *
        (contScoreComponents M phi dphi L (e t) k j o -
          contScoreComponents M phi dphi L (b t) k j o)) =ᵐ[observationLaw M]
        (fun o => (path t).gamma g o.1 * (block true t o - block false t o) +
          (path t).gamma g o.1 * (P t o + Q t o)) := by
      filter_upwards [population_continuous_quantile_score_difference_ae M h he phi dphi
        L hL cpi hov hpol hden h0 (path t).piLev (path t).tauLev (path t).nu
        k j hk hj] with o ho
      change contScoreComponents M phi dphi L (e t) k j o -
        contScoreComponents M phi dphi L (b t) k j o =
        (block true t o - block false t o) + P t o + Q t o at ho
      rw [ho]
      ring
    refine ⟨(ib.fun_add iz.1).congr heq.symm, ?_⟩
    rw [integral_congr_ae heq, integral_add ib iz.1, iz.2, add_zero]
  refine ⟨?_, hmean.mono fun _ ht => ht.1⟩
  apply zblock.congr_of_eventuallyEq
  exact hmean.mono fun _ ht => ht.2

-- The product-score plug-in term has no quantile dependence. Therefore the
-- preceding weighted component cancellation is exactly its quantile telescope.
-- @node: population_continuous_band_quantile_product_orthogonality
/-- Under [the structural instrumental-variable model assumptions](hyp:h), [known outcome
endpoints](hyp:he), [measurability of the policy derivative at the structural
propensity](hyp:hdphi), [uniform boundedness and Lipschitz continuity of that derivative
in unit-interval propensity](hyp:hDerivative), [a covariate-invariant baseline and policy
level structure](hyp:hL), [interior policy levels distinct from their lower baseline
boundaries](hyp:hOff), [uniform positive separation of distinct propensity values](hyp:hGap),
[baseline overlap](hyp:hov), [policy overlap with the same constant](hyp:hpol), [bounded
densities near interior quantile boundaries](hyp:hden), [no treated-outcome atom at the
lower outcome endpoint](hyp:h0), and [an admissible continuous nuisance direction at the
population nuisance](hyp:hd), choose [a bin before the final bin](hyp:hk) and [a band
index below its policy-level count](hyp:hj) with [measurable lower](hyp:ha) and [upper
quantile boundaries](hyp:hb). Then [the band product-score difference between moving
quantile boundaries and population quantile boundaries, with baseline assignment
probabilities, policy-cell probabilities, and product weights moving identically in
both scores, has population-mean derivative zero at zero and is integrable throughout
a neighborhood of zero](goal). -/
lemma population_continuous_band_quantile_product_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, nu := (path t).nu, gamma := (path t).gamma}
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, gamma := (path t).gamma}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) := by
  dsimp only
  let g : RegularIndex L := ⟨(k,j+1), hk.le, by omega, hj⟩
  let path := fun t : ℝ => trueNuisance M L + t • del
  let e := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, nu := (path t).nu, gamma := (path t).gamma}
  let b := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, gamma := (path t).gamma}
  let e' := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, nu := (path t).nu}
  let b' := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev}
  have hz := population_continuous_band_quantile_score_orthogonality M h he phi dphi
    hdphi hDerivative L hL hOff gap hGap cpi hov hpol hden h0 del hd k j hk hj g ha hb
  have hid (t : ℝ) (o : Obs X Z) :
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o =
      (path t).gamma g o.1 * (contScoreComponents M phi dphi L (e' t) k j o -
        contScoreComponents M phi dphi L (b' t) k j o) := by
    have hJ : contJ L (e t) k j o.1 = contJ L (b t) k j o.1 := rfl
    have hc : contScoreComponents M phi dphi L (e t) k j o =
      contScoreComponents M phi dphi L (e' t) k j o := rfl
    have hd' : contScoreComponents M phi dphi L (b t) k j o =
      contScoreComponents M phi dphi L (b' t) k j o := rfl
    simp only [psiProd, Nat.add_sub_cancel, hJ, hc, hd', regularValue,
      dif_pos (show k ≤ L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k from g.property)]
    change (path t).gamma g o.1 * _ + _ * (_ - (path t).gamma g o.1) -
      ((path t).gamma g o.1 * _ + _ * (_ - (path t).gamma g o.1)) = _
    ring
  have heq : (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) =
      (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
        (contScoreComponents M phi dphi L (e' t) k j o -
          contScoreComponents M phi dphi L (b' t) k j o) ∂observationLaw M) := by
    funext t
    apply integral_congr_ae
    exact Eventually.of_forall (hid t)
  constructor
  · rw [heq]
    exact hz.1
  · filter_upwards [hz.2] with t ht
    exact ht.congr (Eventually.of_forall fun o => (hid t o).symm)

end Papers.TbsPrteOptimalTransport
