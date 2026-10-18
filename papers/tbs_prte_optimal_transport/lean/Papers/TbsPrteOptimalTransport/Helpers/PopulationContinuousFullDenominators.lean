module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBandMean
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryDenominators
/-! Continuous full-interval score centering and orthogonality along assignment denominator paths. -/
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

-- Selected conditional means center the actual score residual, including W.
-- @node: population_continuous_full_outcome_fitted_denominator_zero
/-- With [measurable fitted assignment probabilities at every positive
level](hyp:hpi), [an interval index below the number of levels](hyp:hk), and
[a measurable covariate weight](hyp:hw), if [the weighted outcome residual
using these fitted denominators and the true outcome means is
integrable](hyp:hi), then [its expectation is zero](goal). -/
lemma population_continuous_full_outcome_fitted_denominator_zero (L : LevelData Z X)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (plus : Bool) (k : ℕ) (hk : k < L.K) (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi} plus k o) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi}
      plus k o ∂observationLaw M) = 0 := by
  have hc i : Measurable (positiveValue pi i) := by
    first | fun_prop | skip
    unfold positiveValue
    split_ifs
    · exact hpi _
    · fun_prop
  cases plus
  · by_cases hk0 : k = 0
    · subst k
      simp [continuousFullOutcomeResidual]
    have hk1 : 1 ≤ k := by omega
    have heq : ∀ o : Obs X Z,
        continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi} false k o =
        indicator (o.2.1 ∈ L.S k) * o.2.2.1 /
          positiveValue {trueNuisance M L with piLev := pi}.piLev k o.1 *
            (o.2.2.2 - ∫ y, y ∂treatedLaw M L k o.1) := by
      intro o
      simp [continuousFullOutcomeResidual, minusFullValue, hk0, hk1, hk,
        trueNuisance, treatedBandMean]
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L k (fun _ y => y)
      measurable_snd _ w (hc k) hw hi
  · have heq : ∀ o : Obs X Z,
        continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi} true k o =
        indicator (o.2.1 ∈ L.S (k+1)) * o.2.2.1 /
          positiveValue {trueNuisance M L with piLev := pi}.piLev (k+1) o.1 *
            (o.2.2.2 - ∫ y, y ∂treatedLaw M L (k+1) o.1) := by
      intro o
      simp [continuousFullOutcomeResidual, fullValue, hk, trueNuisance, treatedBandMean]
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L (k+1) (fun _ y => y)
      measurable_snd _ w (hc (k+1)) hw hi


-- @node: population_RpCont_fitted_denominator_weighted_zero
/-- If [threshold crossing holds](hyp:h), [the fitted assignment probabilities
are measurable at every positive level](hyp:hpi), [baseline propensities and
policy indices share the level ordering](hyp:hOrder), [the covariate weight
is measurable](hyp:hw), and [the weighted propensity residual using fitted
assignment denominators is integrable](hyp:hi), then [that residual has
expectation zero](goal). -/
lemma population_RpCont_fitted_denominator_weighted_zero (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (hOrder : LevelOrderInvariant M.prop q L) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      RpCont L {trueNuisance M L with piLev := pi} k o) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * RpCont L {trueNuisance M L with piLev := pi} k o
      ∂observationLaw M) = 0 := by
  exact population_Rp_denominator_weighted_integral_zero M h q L pi hpi hOrder k w hw hi

-- Each term is centered with its own measurable covariate weight. No
-- conditional moment of the assembled score is assumed here.
-- @node: population_continuous_full_fitted_denominator_correction_zero
/-- Suppose [threshold crossing holds](hyp:h), [baseline propensities and policy
indices share the level ordering](hyp:hOrder), [the fitted assignment
probabilities are measurable](hyp:hpi), [the interval index is below the number
of levels](hyp:hk), and [the covariate weight is measurable](hyp:hw). If, using
the fitted denominators, [the weighted upper outcome residual](hyp:hp), [the
weighted lower outcome residual](hyp:hm), [the upper propensity residual times
the weight and upper mean](hyp:hrp), and [the lower propensity residual times
the weight and lower mean](hyp:hrm) are integrable, then [the weighted score
correction with otherwise true nuisance functions is integrable and has
expectation zero](goal). -/
lemma population_continuous_full_fitted_denominator_correction_zero
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a)) (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w)
    (hp : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi} true k o) (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi} false k o) (observationLaw M))
    (hrp : Integrable (fun o : Obs X Z =>
      (w o.1 * fullValue {trueNuisance M L with piLev := pi}.JfullPlus k o.1) *
        RpCont L {trueNuisance M L with piLev := pi} (k+1) o) (observationLaw M))
    (hrm : Integrable (fun o : Obs X Z =>
      (w o.1 * minusFullValue {trueNuisance M L with piLev := pi} k o.1) *
        RpCont L {trueNuisance M L with piLev := pi} k o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (psiFullJ L {trueNuisance M L with piLev := pi} k o - contFullJ L {trueNuisance M L with piLev := pi} k o.1))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (psiFullJ L {trueNuisance M L with piLev := pi} k o - contFullJ L {trueNuisance M L with piLev := pi} k o.1)
      ∂observationLaw M) = 0 := by
  have hwp := hw.mul (population_continuous_full_mean_measurable M L true k)
  have hwm := hw.mul (population_continuous_full_mean_measurable M L false k)
  simp only [Bool.true_eq, if_true] at hwp
  simp only [Bool.false_eq_true, if_false] at hwm
  have zp := population_continuous_full_outcome_fitted_denominator_zero M L pi hpi true k hk w hw hp
  have zm := population_continuous_full_outcome_fitted_denominator_zero M L pi hpi false k hk w hw hm
  have zrp := population_RpCont_fitted_denominator_weighted_zero M h q L pi hpi hOrder (k+1)
    (fun x => w x * fullValue {trueNuisance M L with piLev := pi}.JfullPlus k x) hwp hrp
  have zrm := population_RpCont_fitted_denominator_weighted_zero M h q L pi hpi hOrder k
    (fun x => w x * minusFullValue {trueNuisance M L with piLev := pi} k x) hwm hrm
  simp_rw [continuous_full_score_correction_decomposition, mul_sub, mul_add, ← mul_assoc]
  refine ⟨((hp.fun_add hrp).sub' hm).sub' hrm, ?_⟩
  rw [integral_sub ((hp.fun_add hrp).sub' hm) hrm, integral_sub (hp.fun_add hrp) hm,
    integral_add hp hrp, zp, zm, zrp, zrm]
  ring

-- @node: population_continuous_full_fitted_denominator_weighted_mean
/-- Suppose [threshold crossing holds](hyp:h), [baseline propensities and policy
indices share the level ordering](hyp:hOrder), [fitted assignment probabilities
are measurable](hyp:hpi), [the interval index is below the number of
levels](hyp:hk), and [the covariate weight is measurable](hyp:hw). If [the
weighted plug-in component](hyp:hJ), [the weighted upper outcome
residual](hyp:hp), [the weighted lower outcome residual](hyp:hm), [the upper
propensity residual times the weight and upper mean](hyp:hrp), and [the lower
propensity residual times the weight and lower mean](hyp:hrm) are integrable
with these denominators, then [the weighted score with otherwise true nuisance
functions is integrable and has the same expectation as its weighted plug-in
component](goal). -/
lemma population_continuous_full_fitted_denominator_weighted_mean
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a)) (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w)
    (hJ : Integrable (fun o : Obs X Z => w o.1 * contFullJ L {trueNuisance M L with piLev := pi} k o.1)
      (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi} true k o) (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi} false k o) (observationLaw M))
    (hrp : Integrable (fun o : Obs X Z =>
      (w o.1 * fullValue {trueNuisance M L with piLev := pi}.JfullPlus k o.1) *
        RpCont L {trueNuisance M L with piLev := pi} (k+1) o) (observationLaw M))
    (hrm : Integrable (fun o : Obs X Z =>
      (w o.1 * minusFullValue {trueNuisance M L with piLev := pi} k o.1) *
        RpCont L {trueNuisance M L with piLev := pi} k o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * psiFullJ L {trueNuisance M L with piLev := pi} k o)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * psiFullJ L {trueNuisance M L with piLev := pi} k o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * contFullJ L {trueNuisance M L with piLev := pi} k o.1 ∂observationLaw M := by
  obtain ⟨hi, hz⟩ := population_continuous_full_fitted_denominator_correction_zero M h q L hOrder
    pi hpi k hk w hw hp hm hrp hrm
  have hid : (fun o : Obs X Z => w o.1 * psiFullJ L {trueNuisance M L with piLev := pi} k o) =
      (fun o => w o.1 * contFullJ L {trueNuisance M L with piLev := pi} k o.1 + w o.1 *
        (psiFullJ L {trueNuisance M L with piLev := pi} k o - contFullJ L {trueNuisance M L with piLev := pi} k o.1)) := by
    funext o
    ring
  rw [hid]
  exact ⟨hJ.fun_add hi, by rw [integral_add hJ hi, hz, add_zero]⟩

-- Only a neighborhood of zero is needed: admissible denominator paths
-- need not have integrable inverse weights for all real parameter values.
-- @node: population_continuous_full_denominator_path_orthogonality
/-- Suppose [threshold crossing holds](hyp:h), [baseline propensities and policy
indices share the level ordering](hyp:hOrder), [every assignment probability
along the denominator path is measurable](hyp:hpi), [the neighborhood radius
is positive](hyp:hradius), [the interval index is below the number of
levels](hyp:hk), and [the covariate weight is measurable](hyp:hw). If [the true
weighted plug-in component is integrable](hyp:hJ) and, throughout this
neighborhood, [the weighted upper outcome residual](hyp:hp), [the weighted
lower outcome residual](hyp:hm), [the upper propensity residual times the
weight and true upper mean](hyp:hrp), and [the lower propensity residual times
the weight and true lower mean](hyp:hrm) are integrable, then [the expected
weighted full-interval score has derivative zero at zero along the denominator
path](goal). -/
lemma population_continuous_full_denominator_path_orthogonality
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (pi : ℝ → PositiveIndex L.K → X → ℝ)
    (hpi : ∀ t a, Measurable (pi t a)) (radius : ℝ) (hradius : 0 < radius)
    (k : ℕ) (hk : k < L.K) (w : X → ℝ) (hw : Measurable w)
    (hJ : Integrable (fun o : Obs X Z => w o.1 * contFullJ L (trueNuisance M L) k o.1)
      (observationLaw M))
    (hp : ∀ t, |t| < radius → Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi t} true k o)
      (observationLaw M))
    (hm : ∀ t, |t| < radius → Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi t} false k o)
      (observationLaw M))
    (hrp : ∀ t, |t| < radius → Integrable (fun o : Obs X Z =>
      (w o.1 * fullValue (trueNuisance M L).JfullPlus k o.1) *
        RpCont L {trueNuisance M L with piLev := pi t} (k+1) o) (observationLaw M))
    (hrm : ∀ t, |t| < radius → Integrable (fun o : Obs X Z =>
      (w o.1 * minusFullValue (trueNuisance M L) k o.1) *
        RpCont L {trueNuisance M L with piLev := pi t} k o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w o.1 *
      psiFullJ L {trueNuisance M L with piLev := pi t} k o ∂observationLaw M) 0 0 := by
  apply (hasDerivAt_const (0 : ℝ)
    (∫ o : Obs X Z, w o.1 * contFullJ L (trueNuisance M L) k o.1
      ∂observationLaw M)).congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < radius :=
    continuousAt_id.abs.eventually_lt_const (by simpa using hradius)
  filter_upwards [hnear] with t ht
  exact (population_continuous_full_fitted_denominator_weighted_mean M h q L hOrder
    (pi t) (hpi t) k hk w hw hJ (hp t ht) (hm t ht) (hrp t ht) (hrm t ht)).2

end Papers.TbsPrteOptimalTransport
