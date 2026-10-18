module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBandMean
/-! Assembly of the six centered continuous band regression corrections. -/
@[expose] public section
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

-- @node: continuousBandRegressionCorrection
/-- For [a latent instrumental-variable model](hyp:M), [a level partition](hyp:L),
[continuous nuisance functions](hyp:e), [a treatment level](hyp:k), [a band index](hyp:j),
and [an observation](hyp:o), the [band regression correction](goal) is the difference
between the upper- and lower-level centered outcome corrections, plus the lower-boundary
quantile times the difference of its indicator corrections, minus the upper-boundary
quantile times the difference of its indicator corrections. -/
noncomputable def continuousBandRegressionCorrection (L : LevelData Z X)
    (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) : ℝ :=
  IFJ M L e true k j o - IFJ M L e false k j o +
    nuValue M e k j o.1 * IFM M L e true k j o -
    nuValue M e k j o.1 * IFM M L e false k j o -
    nuValue M e k (j+1) o.1 * IFM M L e true k (j+1) o +
    nuValue M e k (j+1) o.1 * IFM M L e false k (j+1) o

-- Separate the centered regression block from the quantile moment,
-- propensity representers, and pooled policy corrections of the paper.
-- @node: continuous_band_score_regression_decomposition
/-- [The continuous band score equals the band outcome contrast plus its regression
correction, the lower-boundary quantile moment minus the upper-boundary quantile moment,
the two propensity corrections with the lower one omitted at level zero, and the
negative lower plus positive upper policy corrections](goal). -/
lemma continuous_band_score_regression_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) :
    contScoreComponents M phi dphi L e k j o =
      contJ L e k j o.1 + continuousBandRegressionCorrection M L e k j o +
      nuValue M e k j o.1 *
        (positiveValue e.pLev (k+1) o.1 * boundaryValue e.Mplus k j o.1 -
          positiveValue e.pLev k o.1 * minusBoundaryValue e.Mminus k j o.1 -
          (pooledQ phi L e k j o.1 - positiveValue e.pLev k o.1)) -
      nuValue M e k (j+1) o.1 *
        (positiveValue e.pLev (k+1) o.1 * boundaryValue e.Mplus k (j+1) o.1 -
          positiveValue e.pLev k o.1 * minusBoundaryValue e.Mminus k (j+1) o.1 -
          (pooledQ phi L e k (j+1) o.1 - positiveValue e.pLev k o.1)) +
      (if k = 0 then 0 else alphaLow M L e k j o.1 * RpCont L e k o) +
      alphaHigh M L e k j o.1 * RpCont L e (k+1) o -
      nuValue M e k j o.1 * RqCont dphi L e k j o +
      nuValue M e k (j+1) o.1 * RqCont dphi L e k (j+1) o := by
  unfold contScoreComponents continuousBandRegressionCorrection
  ring

-- Each term is centered by its selected conditional law. The integrability
-- assumptions concern residual products, rather than a score moment identity.
-- @node: population_continuous_band_regression_correction_zero
/-- If [the fitted assignment probabilities are measurable](hyp:hpi),
[the treatment level is below the number of levels](hyp:hk), [the band index is below
the number of bands at that level](hyp:hj), [the lower boundary is measurable](hyp:ha),
[the upper boundary is measurable](hyp:hb), and [the covariate weight is measurable](hyp:hw),
and if [both weighted outcome corrections are integrable](hyp:hJ),
[both lower-boundary-weighted indicator corrections are integrable](hyp:hMa), and
[both upper-boundary-weighted indicator corrections are integrable](hyp:hMb), then
[the weighted regression correction at otherwise true nuisances is integrable and has
population mean zero, even with fitted assignment denominators](goal). -/
lemma population_continuous_band_regression_correction_zero
    (L : LevelData Z X) (pi : PositiveIndex L.K → X → ℝ)
    (hpi : ∀ a, Measurable (pi a)) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1)))
    (w : X → ℝ) (hw : Measurable w)
    (hJ : ∀ plus, Integrable (fun o : Obs X Z => w o.1 *
      IFJ M L {trueNuisance M L with piLev := pi} plus k j o) (observationLaw M))
    (hMa : ∀ plus, Integrable (fun o : Obs X Z =>
      (w o.1 * bandBoundary M L k j o.1) *
      IFM M L {trueNuisance M L with piLev := pi} plus k j o) (observationLaw M))
    (hMb : ∀ plus, Integrable (fun o : Obs X Z =>
      (w o.1 * bandBoundary M L k (j+1) o.1) *
      IFM M L {trueNuisance M L with piLev := pi} plus k (j+1) o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * continuousBandRegressionCorrection M L
      {trueNuisance M L with piLev := pi} k j o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * continuousBandRegressionCorrection M L
      {trueNuisance M L with piLev := pi} k j o ∂observationLaw M) = 0 := by
  have hnext : j+1 ≤ L.l k := by omega
  have zJ plus := population_IFJ_fitted_denominator_weighted_zero M L pi hpi
    plus k j hk hj ha hb w hw (hJ plus)
  have zMa plus := population_IFM_fitted_denominator_weighted_zero M L pi hpi
    plus k j hk hj.le ha (fun x => w x * bandBoundary M L k j x)
    (hw.mul ha) (hMa plus)
  have zMb plus := population_IFM_fitted_denominator_weighted_zero M L pi hpi
    plus k (j+1) hk hnext hb (fun x => w x * bandBoundary M L k (j+1) x)
    (hw.mul hb) (hMb plus)
  have hnu b (hbl : b ≤ L.l k) x :
      nuValue M {trueNuisance M L with piLev := pi} k b x = bandBoundary M L k b x :=
    population_nuValue_eq_bandBoundary M L k b hk hbl x
  simp only [continuousBandRegressionCorrection, hnu j hj.le, hnu (j+1) hnext,
    mul_add, mul_sub, ← mul_assoc]
  have hi1 := (hJ true).sub' (hJ false)
  have hi2 := hi1.fun_add (hMa true)
  have hi3 := hi2.sub' (hMa false)
  have hi4 := hi3.sub' (hMb true)
  refine ⟨hi4.fun_add (hMb false), ?_⟩
  rw [integral_add hi4 (hMb false), integral_sub hi3 (hMb true),
    integral_sub hi2 (hMa false), integral_add hi1 (hMa true),
    integral_sub (hJ true) (hJ false), zJ true, zJ false, zMa true,
    zMa false, zMb true, zMb false]
  ring

-- Admissibility only supplies a neighborhood of integrable denominators.
-- The entire centered block is constant there, so no derivative/integral
-- interchange is required.
-- @node: population_continuous_band_regression_denominator_orthogonality
/-- Suppose [the assignment-probability path is measurable at every coordinate and time](hyp:hpi)
and [the neighborhood radius is positive](hyp:hradius). If [the treatment level is valid](hyp:hk),
[the band index is valid](hyp:hj), [the lower boundary is measurable](hyp:ha),
[the upper boundary is measurable](hyp:hb), [the weight is measurable](hyp:hw), and
throughout that neighborhood [both weighted outcome corrections are integrable](hyp:hJ),
[both lower-boundary indicator corrections are integrable](hyp:hMa), and
[both upper-boundary indicator corrections are integrable](hyp:hMb), then
[the population weighted regression correction, with only the assignment denominators
varying, has derivative zero at time zero](goal). -/
lemma population_continuous_band_regression_denominator_orthogonality
    (L : LevelData Z X) (pi : ℝ → PositiveIndex L.K → X → ℝ)
    (hpi : ∀ t a, Measurable (pi t a)) (radius : ℝ) (hradius : 0 < radius)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1)))
    (w : X → ℝ) (hw : Measurable w)
    (hJ : ∀ t, |t| < radius → ∀ plus, Integrable (fun o : Obs X Z => w o.1 *
      IFJ M L {trueNuisance M L with piLev := pi t} plus k j o) (observationLaw M))
    (hMa : ∀ t, |t| < radius → ∀ plus, Integrable (fun o : Obs X Z =>
      (w o.1 * bandBoundary M L k j o.1) *
      IFM M L {trueNuisance M L with piLev := pi t} plus k j o) (observationLaw M))
    (hMb : ∀ t, |t| < radius → ∀ plus, Integrable (fun o : Obs X Z =>
      (w o.1 * bandBoundary M L k (j+1) o.1) *
      IFM M L {trueNuisance M L with piLev := pi t} plus k (j+1) o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w o.1 *
      continuousBandRegressionCorrection M L {trueNuisance M L with piLev := pi t}
        k j o ∂observationLaw M) 0 0 := by
  apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < radius :=
    continuousAt_id.abs.eventually_lt_const (by simpa using hradius)
  filter_upwards [hnear] with t ht
  exact (population_continuous_band_regression_correction_zero M L (pi t) (hpi t)
    k j hk hj ha hb w hw (hJ t ht) (hMa t ht) (hMb t ht)).2

-- The population Riesz coefficients are built from measurable selected means.
-- @node: population_continuous_band_alphaHigh_measurable
/-- If [the treatment level is below the number of levels](hyp:hk),
[the band index is below the number of bands at that level](hyp:hj),
[the lower boundary is measurable](hyp:ha), and [the upper boundary is measurable](hyp:hb),
then [the upper-level propensity coefficient evaluated at the true nuisances is measurable](goal). -/
@[fun_prop] lemma population_continuous_band_alphaHigh_measurable
    (L : LevelData Z X) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    Measurable (alphaHigh M L (trueNuisance M L) k j) := by
  first | fun_prop | skip
  have hJ := population_treated_band_mean_measurable M L true k j ha hb
  have hMa := population_boundary_indicator_mean_measurable M L true k j ha
  have hMb := population_boundary_indicator_mean_measurable M L true k (j+1) hb
  have hnext : j+1 ≤ L.l k := by omega
  have heq : alphaHigh M L (trueNuisance M L) k j = fun x =>
      treatedBandMean M L true false k j x +
        bandBoundary M L k j x * boundaryIndicatorMean M L true k j x -
        bandBoundary M L k (j+1) x * boundaryIndicatorMean M L true k (j+1) x := by
    funext x
    unfold alphaHigh
    rw [population_nuValue_eq_bandBoundary M L k j hk hj.le,
      population_nuValue_eq_bandBoundary M L k (j+1) hk hnext]
    simp [meanValue, boundaryValue, hk, hj.le, hnext, trueNuisance]
  rw [heq]
  fun_prop

-- @node: population_continuous_band_alphaLow_measurable
/-- If [the treatment level is below the number of levels](hyp:hk),
[the band index is below the number of bands at that level](hyp:hj),
[the lower boundary is measurable](hyp:ha), and [the upper boundary is measurable](hyp:hb),
then [the lower-level propensity coefficient evaluated at the true nuisances is measurable](goal). -/
@[fun_prop] lemma population_continuous_band_alphaLow_measurable
    (L : LevelData Z X) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    Measurable (alphaLow M L (trueNuisance M L) k j) := by
  first | fun_prop | skip
  have hJ := population_treated_band_mean_measurable M L false k j ha hb
  have hMa := population_boundary_indicator_mean_measurable M L false k j ha
  have hMb := population_boundary_indicator_mean_measurable M L false k (j+1) hb
  have hnext : j+1 ≤ L.l k := by omega
  unfold alphaLow
  simp only [population_nuValue_eq_bandBoundary M L k j hk hj.le,
    population_nuValue_eq_bandBoundary M L k (j+1) hk hnext]
  by_cases hk0 : k = 0
  · subst k
    simp [minusMeanValue, minusBoundaryValue]
    fun_prop
  · have hk1 : 1 ≤ k := by omega
    simp only [minusMeanValue, minusBoundaryValue, hk1, hk, hj.le, hnext,
      and_self, ↓reduceDIte, trueNuisance]
    fun_prop

-- This is the complete propensity-representer block of the band score,
-- including its structural-zero convention. Its two means vanish separately.
-- @node: population_continuous_band_propensity_correction_zero
/-- Under [threshold crossing](hyp:h) and [a level ordering invariant across covariates
for the baseline propensity and comparison map](hyp:hOrder), suppose
[the treatment level is valid](hyp:hk), [the band index is valid](hyp:hj),
[the lower boundary is measurable](hyp:ha), [the upper boundary is measurable](hyp:hb),
and [the covariate weight is measurable](hyp:hw). If [the weighted lower-level
propensity correction is integrable](hyp:hl) and [the weighted upper-level propensity
correction is integrable](hyp:hh), then [their weighted sum at the true nuisances,
with the lower term set to zero at level zero, is integrable and has population mean zero](goal). -/
lemma population_continuous_band_propensity_correction_zero
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1)))
    (w : X → ℝ) (hw : Measurable w)
    (hl : Integrable (fun o : Obs X Z => (w o.1 *
      alphaLow M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => (w o.1 *
      alphaHigh M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) (k+1) o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
        RpCont L (trueNuisance M L) k o) +
        alphaHigh M L (trueNuisance M L) k j o.1 *
        RpCont L (trueNuisance M L) (k+1) o)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k j o.1 *
        RpCont L (trueNuisance M L) k o) +
        alphaHigh M L (trueNuisance M L) k j o.1 *
        RpCont L (trueNuisance M L) (k+1) o) ∂observationLaw M) = 0 := by
  have zl := population_RpCont_weighted_integral_zero M h q L hOrder k
    (fun x => w x * alphaLow M L (trueNuisance M L) k j x)
    (hw.mul (population_continuous_band_alphaLow_measurable M L k j hk hj ha hb)) hl
  have zh := population_RpCont_weighted_integral_zero M h q L hOrder (k+1)
    (fun x => w x * alphaHigh M L (trueNuisance M L) k j x)
    (hw.mul (population_continuous_band_alphaHigh_measurable M L k j hk hj ha hb)) hh
  by_cases hk0 : k = 0
  · subst k
    simp only [if_true, zero_add, ← mul_assoc]
    exact ⟨hh, zh⟩
  · simp only [hk0, if_false, mul_add, ← mul_assoc]
    exact ⟨hl.fun_add hh, by rw [integral_add hl hh, zl, zh, add_zero]⟩

-- The policy-derivative coefficients multiply instrument-specific treatment
-- residuals; the lower and upper quantile weights preserve their centering.
-- @node: population_continuous_band_policy_correction_zero
/-- Under [threshold crossing](hyp:h), assume [the policy derivative evaluated at the
true propensity is measurable jointly in instrument and covariates](hyp:hdphi),
[the treatment level is valid](hyp:hk), [the band index is valid](hyp:hj),
[the lower boundary is measurable](hyp:ha), [the upper boundary is measurable](hyp:hb),
and [the covariate weight is measurable](hyp:hw). If [the weighted lower-boundary
policy correction is integrable](hyp:hl) and [the weighted upper-boundary policy
correction is integrable](hyp:hh), then [the negative lower plus positive upper
quantile-weighted policy correction at the true nuisances is integrable and has
population mean zero](goal). -/
lemma population_continuous_band_policy_correction_zero
    (h : ThresholdCrossing M) (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1)))
    (w : X → ℝ) (hw : Measurable w)
    (hl : Integrable (fun o : Obs X Z => (w o.1 * bandBoundary M L k j o.1) *
      RqCont dphi L (trueNuisance M L) k j o) (observationLaw M))
    (hh : Integrable (fun o : Obs X Z => (w o.1 * bandBoundary M L k (j+1) o.1) *
      RqCont dphi L (trueNuisance M L) k (j+1) o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (-(nuValue M (trueNuisance M L) k j o.1 *
        RqCont dphi L (trueNuisance M L) k j o) +
        nuValue M (trueNuisance M L) k (j+1) o.1 *
        RqCont dphi L (trueNuisance M L) k (j+1) o)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (-(nuValue M (trueNuisance M L) k j o.1 *
        RqCont dphi L (trueNuisance M L) k j o) +
        nuValue M (trueNuisance M L) k (j+1) o.1 *
        RqCont dphi L (trueNuisance M L) k (j+1) o) ∂observationLaw M) = 0 := by
  have hnext : j+1 ≤ L.l k := by omega
  have zl := population_RqCont_weighted_integral_zero M h dphi hdphi L k j
    (fun x => w x * bandBoundary M L k j x) (hw.mul ha) hl
  have zh := population_RqCont_weighted_integral_zero M h dphi hdphi L k (j+1)
    (fun x => w x * bandBoundary M L k (j+1) x) (hw.mul hb) hh
  simp only [population_nuValue_eq_bandBoundary M L k j hk hj.le,
    population_nuValue_eq_bandBoundary M L k (j+1) hk hnext,
    mul_add, mul_neg, ← mul_assoc]
  have hn : Integrable (fun o : Obs X Z =>
      -((w o.1 * bandBoundary M L k j o.1) *
        RqCont dphi L (trueNuisance M L) k j o)) (observationLaw M) := hl.neg
  refine ⟨hn.fun_add hh, ?_⟩
  rw [integral_add hn hh, integral_neg, zl, zh]
  ring

end Papers.TbsPrteOptimalTransport
