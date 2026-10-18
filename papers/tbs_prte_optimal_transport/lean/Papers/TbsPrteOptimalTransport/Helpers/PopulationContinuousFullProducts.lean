module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullMean
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationAssignmentResidual
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryAdmissibility
/-! Population moments for the signed full-interval continuous product score. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_full_J_measurable
/-- If [threshold crossing holds](hyp:h) and [baseline propensities and policy
indices share the level ordering](hyp:hOrder), then [the population
full-interval plug-in component is measurable in covariates at every interval
index](goal). -/
@[fun_prop] lemma population_continuous_full_J_measurable
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (k : ℕ) :
    Measurable (contFullJ L (trueNuisance M L) k) := by
  first | fun_prop | skip
  have hp i : Measurable (positiveValue (trueNuisance M L).pLev i) := by
    unfold positiveValue
    split_ifs with hi
    · exact ordered_baseline_level_measurable M h q L hOrder i hi
    · fun_prop
  have hjp := population_continuous_full_mean_measurable M L true k
  have hjm := population_continuous_full_mean_measurable M L false k
  simp only [Bool.true_eq, if_true] at hjp
  simp only [Bool.false_eq_true, if_false] at hjm
  exact ((hp (k+1)).mul hjp).sub ((hp k).mul hjm)

-- A set-assignment residual is bounded by one. Thus its integrability is
-- inherited from the plug-in coefficient, without an additional premise.
-- @node: population_assignment_residual_weighted_integrable
/-- If [an observation-level coefficient is integrable](hyp:hf), then [its
product with the residual of membership in any finite instrument set, after
subtracting that set's conditional assignment probability, is integrable](goal). -/
lemma population_assignment_residual_weighted_integrable (C : Finset Z)
    (f : Obs X Z → ℝ) (hf : Integrable f (observationLaw M)) :
    Integrable (fun o : Obs X Z => f o *
      (indicator (o.2.1 ∈ C) - ∑ z ∈ C, instProb M z o.1)) (observationLaw M) := by
  have hr : Measurable (fun o : Obs X Z =>
      indicator (o.2.1 ∈ C) - ∑ z ∈ C, instProb M z o.1) := by
    have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ C)) := by
      unfold indicator
      exact Measurable.ite (C.finite_toSet.measurableSet.preimage measurable_snd.fst)
        measurable_const measurable_const
    exact hi.sub ((population_instrument_set_probability_measurable M C).comp measurable_fst)
  have hb : ∀ᵐ o : Obs X Z ∂observationLaw M,
      ‖indicator (o.2.1 ∈ C) - ∑ z ∈ C, instProb M z o.1‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro o
    have hp := population_instrument_set_probability_range M C o.1
    have hi : indicator (o.2.1 ∈ C) ∈ Icc (0 : ℝ) 1 := by
      unfold indicator
      split_ifs <;> norm_num
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hp.1, hp.2, hi.1, hi.2]
  simpa only [mul_comm] using hf.bdd_mul hr.aestronglyMeasurable hb

-- Center the two assignment indicators separately. The population coefficient
-- gamma_full is signed, so this proof does not use positivity of that weight.
-- @node: population_continuous_full_product_assignment_zero
/-- Suppose [threshold crossing holds](hyp:h), [baseline propensities and policy
indices share the level ordering](hyp:hOrder), [the interval index is below
the number of levels](hyp:hk), and [the covariate weight is measurable](hyp:hw).
If [the higher-policy assignment residual times the weight and population
plug-in component is integrable](hyp:hC) and [the corresponding higher-baseline
assignment term is integrable](hyp:hD), then [the weight times the plug-in
component times the difference of the two assignment indicators minus its
conditional population mean is integrable and has expectation zero](goal). -/
lemma population_continuous_full_product_assignment_zero
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w)
    (hC : Integrable (fun o : Obs X Z =>
      (w o.1 * contFullJ L (trueNuisance M L) k o.1) *
        (indicator (o.2.1 ∈ higherPolicy L k) -
          ∑ z ∈ higherPolicy L k, instProb M z o.1)) (observationLaw M))
    (hD : Integrable (fun o : Obs X Z =>
      (w o.1 * contFullJ L (trueNuisance M L) k o.1) *
        (indicator (o.2.1 ∈ higherBaseline L k) -
          ∑ z ∈ higherBaseline L k, instProb M z o.1)) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * contFullJ L (trueNuisance M L) k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
        fullValue (trueNuisance M L).gammaFull k o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * contFullJ L (trueNuisance M L) k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
        fullValue (trueNuisance M L).gammaFull k o.1) ∂observationLaw M) = 0 := by
  have hz := population_signed_assignment_weighted_integral_zero M
    (higherPolicy L k) (higherBaseline L k)
    (fun x => w x * contFullJ L (trueNuisance M L) k x)
    (hw.mul (population_continuous_full_J_measurable M h q L hOrder k)) hC hD
  have hi := hC.sub' hD
  have heq : ∀ o : Obs X Z,
      (w o.1 * contFullJ L (trueNuisance M L) k o.1) *
        (indicator (o.2.1 ∈ higherPolicy L k) - ∑ z ∈ higherPolicy L k, instProb M z o.1) -
      (w o.1 * contFullJ L (trueNuisance M L) k o.1) *
        (indicator (o.2.1 ∈ higherBaseline L k) - ∑ z ∈ higherBaseline L k, instProb M z o.1) =
      w o.1 * contFullJ L (trueNuisance M L) k o.1 *
        (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
          gammaFull M L k o.1) := by
    intro o
    unfold gammaFull
    ring
  simp_rw [heq] at hi
  simpa only [fullValue, dif_pos hk, trueNuisance, gammaFull] using And.intro hi hz

-- Invoke the component moment with weight w * gamma_full, then remove the
-- signed assignment correction. Only primitive residual integrability is used.
-- @node: population_continuous_full_product_weighted_mean
/-- Suppose [threshold crossing holds](hyp:h), [baseline propensities and policy
indices share the level ordering](hyp:hOrder), [the interval index is below
the number of levels](hyp:hk), and [the covariate weight is measurable](hyp:hw).
If, after weighting by both this weight and the signed population assignment
coefficient, [the plug-in component](hyp:hJ), [the upper outcome
residual](hyp:hp), [the lower outcome residual](hyp:hm), [the upper propensity
residual times the upper mean](hyp:hrp), and [the lower propensity residual
times the lower mean](hyp:hrm) are integrable, and [the plug-in component
weighted by the covariate weight alone is integrable](hyp:hbaseJ), then [the
weighted product score is integrable and its expectation equals that of the
plug-in component weighted by the covariate weight and signed population
assignment coefficient](goal). -/
lemma population_continuous_full_product_weighted_mean
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w)
    (hJ : Integrable (fun o : Obs X Z => (w o.1 * gammaFull M L k o.1) *
      contFullJ L (trueNuisance M L) k o.1) (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => (w o.1 * gammaFull M L k o.1) *
      continuousFullOutcomeResidual L (trueNuisance M L) true k o) (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => (w o.1 * gammaFull M L k o.1) *
      continuousFullOutcomeResidual L (trueNuisance M L) false k o) (observationLaw M))
    (hrp : Integrable (fun o : Obs X Z =>
      ((w o.1 * gammaFull M L k o.1) * fullValue (trueNuisance M L).JfullPlus k o.1) *
        RpCont L (trueNuisance M L) (k+1) o) (observationLaw M))
    (hrm : Integrable (fun o : Obs X Z =>
      ((w o.1 * gammaFull M L k o.1) * minusFullValue (trueNuisance M L) k o.1) *
        RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hbaseJ : Integrable (fun o : Obs X Z =>
      w o.1 * contFullJ L (trueNuisance M L) k o.1) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * psiFullProd L (trueNuisance M L) k o)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * psiFullProd L (trueNuisance M L) k o ∂observationLaw M) =
      ∫ o : Obs X Z, (w o.1 * gammaFull M L k o.1) *
        contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M := by
  have hg : Measurable (gammaFull M L k) := by
    first
    | fun_prop
    | exact (population_instrument_set_probability_measurable M _).sub
        (population_instrument_set_probability_measurable M _)
  obtain ⟨hs, hmean⟩ := population_continuous_full_component_weighted_mean M h q L hOrder
    k hk (fun x => w x * gammaFull M L k x) (hw.mul hg) hJ hp hm hrp hrm
  have hC := population_assignment_residual_weighted_integrable M (higherPolicy L k)
    (fun o : Obs X Z => w o.1 * contFullJ L (trueNuisance M L) k o.1) hbaseJ
  have hD := population_assignment_residual_weighted_integrable M (higherBaseline L k)
    (fun o : Obs X Z => w o.1 * contFullJ L (trueNuisance M L) k o.1) hbaseJ
  obtain ⟨hi, hz⟩ := population_continuous_full_product_assignment_zero M h q L hOrder
    k hk w hw hC hD
  have hgamma x : fullValue (trueNuisance M L).gammaFull k x = gammaFull M L k x := by
    simp only [fullValue, dif_pos hk, trueNuisance]
  simp only [hgamma] at hi hz
  simp only [psiFullProd, hgamma, mul_add, ← mul_assoc]
  refine ⟨hs.fun_add hi, ?_⟩
  rw [integral_add hs hi, hz, add_zero]
  exact hmean

end Papers.TbsPrteOptimalTransport
