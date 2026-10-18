module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleIdentification
/-! # Observed arm moments for the backdoor identification argument

Finite observational support transfers integrability to every equivalent SCM.
Independent selection then identifies potential outcomes using propensity
identities required only almost everywhere on the carrying private-input law.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- If [the model's observational law equals the witness model's law](hyp:hobs)
and [the scalar observable is measurable](hyp:hF), then [that observable is
integrable under the model's observational law](goal). -/
-- @node: counterexample_observable_integrable
lemma counterexample_observable_integrable
    {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (F : Joint backdoorKind → ℝ) (hF : Measurable F) :
    Integrable F (observationalLaw M) := by
  rw [hobs, counterexampleTrueSCM_observationalLaw, counterexampleTrueFiniteObservationLaw_eq]
  apply (integrable_map_measure hF.aestronglyMeasurable
    counterexampleJointOfVector_measurable.aemeasurable).mpr
  unfold counterexampleFiniteObservationLaw
  apply integrable_finsetSum_measure.mpr
  intro i hi
  apply Integrable.smul_measure
  · exact integrable_dirac (by simp)
  · simp [counterexampleAtomWeight]

-- @node: counterexample_observable_eval_integrable
/-- If [the model's observational law equals the witness model's law](hyp:hobs)
and [the scalar observable is measurable](hyp:hF), then [the observable
evaluated on the model's observational simulation is integrable under its
latent law](goal). -/
lemma counterexample_observable_eval_integrable
    {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (F : Joint backdoorKind → ℝ) (hF : Measurable F) :
    Integrable (fun u => F (intervenedEval M (fun _ => none) u)) M.latentLaw := by
  exact (integrable_map_measure hF.aestronglyMeasurable
    (evalSteps_measurable M (fun _ => none) (3*3+3)).aemeasurable).mp
      (counterexample_observable_integrable M hobs F hF)

/-- If [the model's observational law equals the witness model's law](hyp:hobs)
and [the scalar observable is measurable](hyp:hF), then [its observational
expectation is the sum of its values at the six witness observations, each
multiplied by that observation's probability weight](goal). -/
-- @node: counterexample_observable_integral
lemma counterexample_observable_integral
    {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (F : Joint backdoorKind → ℝ) (hF : Measurable F) :
    (∫ v, F v ∂observationalLaw M) = ∑ i : Fin 6,
      (counterexampleAtomWeight i).toReal *
        F (counterexampleJointOfVector (counterexampleObservationAtom 0 i)) := by
  rw [hobs, counterexampleTrueSCM_observationalLaw, counterexampleTrueFiniteObservationLaw_eq,
    integral_map counterexampleJointOfVector_measurable.aemeasurable hF.aestronglyMeasurable]
  have hi : ∀ i : Fin 6,
      Integrable (fun z => F (counterexampleJointOfVector z))
        (counterexampleAtomWeight i • Measure.dirac (counterexampleObservationAtom 0 i)) := by
    intro i
    apply Integrable.smul_measure
    · exact integrable_dirac (by simp)
    · simp [counterexampleAtomWeight]
  rw [counterexampleFiniteObservationLaw, integral_finsetSum_measure (by
    intro i _
    exact hi i)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]

/-- If [the model's observational law equals the witness model's law](hyp:hobs),
then for [a real-valued covariate test function](hyp:h) that [is
measurable](hyp:hh), [the expectation of the test function times the indicator
that treatment equals two is the expectation of the same test function times
the witness treatment propensity](goal). -/
-- @node: counterexample_treatment_propensity_test
lemma counterexample_treatment_propensity_test
    {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (h : ℝ → ℝ) (hh : Measurable h) :
    (∫ v, h (v.ofLp ⟨0, ⟨0, by decide⟩⟩) *
      (if v.ofLp ⟨1, ⟨0, by decide⟩⟩ = 2 then (1 : ℝ) else 0) ∂observationalLaw M) =
    ∫ v, h (v.ofLp ⟨0, ⟨0, by decide⟩⟩) *
      counterexampleTrueTreatmentProbability (v.ofLp ⟨0, ⟨0, by decide⟩⟩)
        ∂observationalLaw M := by
  rw [counterexample_observable_integral M hobs _ (by
    apply Measurable.mul
    · fun_prop
    · apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      <;> fun_prop),
    counterexample_observable_integral M hobs _ (by fun_prop)]
  norm_num [Fin.sum_univ_succ, counterexampleAtomWeight, counterexampleObservationAtom,
    counterexampleJointOfVector, counterexampleTrueTreatmentProbability, counterexampleClamp]
  ring

/-- If [the model's observational law equals the witness model's law](hyp:hobs),
then [the conditional expectation of the indicator that treatment equals two,
given the covariate, equals the witness treatment propensity at that covariate
almost surely under the observational law](goal). -/
-- @node: counterexample_observed_treatment_condExp
lemma counterexample_observed_treatment_condExp
    {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM) :
    (observationalLaw M)[fun v =>
      if v.ofLp ⟨1, ⟨0, by decide⟩⟩ = 2 then (1 : ℝ) else 0 |
      MeasurableSpace.comap (fun v : Joint backdoorKind =>
        v.ofLp ⟨0, ⟨0, by decide⟩⟩) inferInstance] =ᵐ[observationalLaw M]
      fun v => counterexampleTrueTreatmentProbability (v.ofLp ⟨0, ⟨0, by decide⟩⟩) := by
  letI := M.probability
  letI : IsProbabilityMeasure (observationalLaw M) :=
    Measure.isProbabilityMeasure_map
      (evalSteps_measurable M (fun _ => none) (3*3+3)).aemeasurable
  let X : Joint backdoorKind → ℝ := fun v => v.ofLp ⟨0, ⟨0, by decide⟩⟩
  let Y : Joint backdoorKind → ℝ := fun v =>
    if v.ofLp ⟨1, ⟨0, by decide⟩⟩ = 2 then 1 else 0
  let P : Joint backdoorKind → ℝ := fun v => counterexampleTrueTreatmentProbability (X v)
  have hX : Measurable X := by fun_prop
  have hY : Measurable Y := by
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) <;> fun_prop
  have hP : Measurable P := by fun_prop
  apply Causalean.Mathlib.MeasureTheory.condExp_eq_of_integral_preimage_eq
    (observationalLaw M) X hX Y P
    (counterexample_observable_integrable M hobs Y hY)
    (counterexample_observable_integrable M hobs P hP)
    ((counterexampleTrueTreatmentProbability_measurable.comp (comap_measurable X)).aestronglyMeasurable)
  intro S hS
  rw [← integral_indicator (hX hS), ← integral_indicator (hX hS)]
  have ht := counterexample_treatment_propensity_test M hobs
    (S.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hS)
  convert ht using 1 <;> congr 1 <;> funext v <;>
    by_cases hx : X v ∈ S <;> simp [X, Y, P, Set.indicator, Set.preimage, hx] at *

/-- For [a chosen binary treatment arm](hyp:t) and [a joint observation](hyp:v),
[the arm score](goal) first [computes the witness treatment propensity at the
observed covariate](step:1), then [returns the observed outcome divided by the
chosen arm's propensity if the observed treatment matches that arm, and zero
otherwise](step:2). -/
-- @node: counterexampleArmScore
def counterexampleArmScore (t : Bool) (v : Joint backdoorKind) : ℝ :=
  let p := counterexampleTrueTreatmentProbability (v.ofLp ⟨0, ⟨0, by decide⟩⟩)
  if v.ofLp ⟨1, ⟨0, by decide⟩⟩ = (if t then 2 else 1 : ℝ) then
    backdoorOutcome v / (if t then p else 1 - p) else 0

-- @node: counterexampleArmScore_measurable
/-- [The inverse-propensity-weighted score for either treatment arm is a
measurable function of the joint observation](goal). -/
@[fun_prop] lemma counterexampleArmScore_measurable (t : Bool) :
    Measurable (counterexampleArmScore t) := by
  unfold counterexampleArmScore
  apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
  · cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop [backdoorOutcome]
  · fun_prop

-- @node: counterexampleAdjustmentScore_eq_arms
/-- [The adjustment score at any joint observation equals the treated-arm
score minus the control-arm score](goal). -/
lemma counterexampleAdjustmentScore_eq_arms (v : Joint backdoorKind) :
    counterexampleAdjustmentScore v = counterexampleArmScore true v -
      counterexampleArmScore false v := rfl

/-- [The expectation of the arm score under the finite witness observation
law is four fifths for the treated arm and one sixth for the control
arm](goal). -/
-- @node: counterexampleArmScore_finite_integral
lemma counterexampleArmScore_finite_integral (t : Bool) :
    (∫ z, counterexampleArmScore t (counterexampleJointOfVector z)
      ∂counterexampleFiniteObservationLaw 0) = (if t then 4/5 else 1/6 : ℝ) := by
  have hi : ∀ i : Fin 6,
      Integrable (fun z => counterexampleArmScore t (counterexampleJointOfVector z))
        (counterexampleAtomWeight i • Measure.dirac (counterexampleObservationAtom 0 i)) := by
    intro i
    apply Integrable.smul_measure
    · exact integrable_dirac (by simp)
    · simp [counterexampleAtomWeight]
  rw [counterexampleFiniteObservationLaw, integral_finsetSum_measure (by
    intro i _
    exact hi i)]
  simp only [integral_smul_measure, integral_dirac]
  cases t <;>
    norm_num [Fin.sum_univ_succ, counterexampleAtomWeight, counterexampleObservationAtom,
      counterexampleArmScore, counterexampleJointOfVector, backdoorOutcome,
      counterexampleTrueTreatmentProbability, counterexampleClamp, Matrix.cons_val_two,
      Matrix.cons_val_three]

-- @node: counterexampleArmScore_integrable_of_observational_eq
/-- If [the model's observational law equals the witness model's law](hyp:hobs),
then [either arm score evaluated on the observational simulation is integrable
under the model's latent law](goal). -/
lemma counterexampleArmScore_integrable_of_observational_eq
    {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (t : Bool) : Integrable
      (fun u => counterexampleArmScore t (intervenedEval M (fun _ => none) u)) M.latentLaw :=
  counterexample_observable_eval_integrable M hobs _ (by fun_prop)

-- @node: counterexampleArmScore_integral_of_observational_eq
/-- If [the model's observational law equals the witness model's law](hyp:hobs),
then [the expectation of the arm score evaluated on its observational
simulation is four fifths for the treated arm and one sixth for the control
arm](goal). -/
lemma counterexampleArmScore_integral_of_observational_eq
    {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (t : Bool) :
    (∫ u, counterexampleArmScore t (intervenedEval M (fun _ => none) u) ∂M.latentLaw) =
      (if t then 4/5 else 1/6 : ℝ) := by
  calc
    _ = ∫ v, counterexampleArmScore t v ∂observationalLaw M :=
      (integral_map (evalSteps_measurable M (fun _ => none) (3*3+3)).aemeasurable
        (counterexampleArmScore_measurable t).aestronglyMeasurable).symm
    _ = _ := by
      rw [hobs, counterexampleTrueSCM_observationalLaw, counterexampleTrueFiniteObservationLaw_eq,
        integral_map counterexampleJointOfVector_measurable.aemeasurable
          (counterexampleArmScore_measurable t).aestronglyMeasurable]
      exact counterexampleArmScore_finite_integral t

/-- Suppose [the private input is measurable](hyp:hV), [the selection input is
measurable](hyp:hG), [these inputs are independent under the probability
law](hyp:hind), [the selection event is measurable](hyp:hS), [the response is
measurable](hyp:hY), and [the propensity is measurable](hyp:hp). If [the
propensity is nonzero for almost every private input](hyp:hpos), [integrating
the selection indicator over the selection-input law gives that propensity
for almost every private input](hyp:hlaw), and [the selected response divided
by the propensity, set to zero outside selection, is integrable](hyp:hobs),
then [the response is integrable and its expectation equals the expectation
of that selected inverse-propensity-weighted response](goal). -/
-- @node: independent_selection_identification_ae
lemma independent_selection_identification_ae
    {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → X) (G : Ω → Z) (hV : Measurable V) (hG : Measurable G)
    (hind : IndepFun V G μ)
    (S : X × Z → Prop) [DecidablePred S] (hS : MeasurableSet {v | S v})
    (Y p : X → ℝ) (hY : Measurable Y) (hp : Measurable p)
    (hpos : ∀ᵐ x ∂μ.map V, p x ≠ 0)
    (hlaw : ∀ᵐ x ∂μ.map V,
      (∫ z, (if S (x, z) then (1 : ℝ) else 0) ∂μ.map G) = p x)
    (hobs : Integrable (fun u => if S (V u, G u) then Y (V u) / p (V u) else 0) μ) :
    Integrable (fun u => Y (V u)) μ ∧
      (∫ u, (if S (V u, G u) then Y (V u) / p (V u) else 0) ∂μ) =
        ∫ u, Y (V u) ∂μ := by
  let := Measure.isProbabilityMeasure_map (μ := μ) hV.aemeasurable
  let := Measure.isProbabilityMeasure_map (μ := μ) hG.aemeasurable
  let F : X × Z → ℝ := fun v => if S v then Y v.1 / p v.1 else 0
  have hF : Measurable F := by
    apply Measurable.ite hS
    · exact (hY.comp measurable_fst).div (hp.comp measurable_fst)
    · exact measurable_const
  have hI : Integrable F ((μ.map V).prod (μ.map G)) := by
    rw [← hind.map_prod_eq_prod_map_map hV.aemeasurable hG.aemeasurable]
    exact (integrable_map_measure hF.aestronglyMeasurable
      (hV.prodMk hG).aemeasurable).mpr hobs
  have hinner : (fun x => ∫ z, F (x, z) ∂μ.map G) =ᵐ[μ.map V] Y := by
    filter_upwards [hpos, hlaw] with x hx hl
    exact selection_inverse_weighting_inner (μ.map G) (fun z => S (x, z))
      (Y x) (p x) hx hl
  have hYI := hI.integral_prod_left.congr hinner
  refine ⟨hYI.comp_aemeasurable hV.aemeasurable, ?_⟩
  calc
    _ = ∫ v, F v ∂μ.map (fun u => (V u, G u)) :=
      (integral_map (hV.prodMk hG).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ v, F v ∂(μ.map V).prod (μ.map G) := by
      rw [hind.map_prod_eq_prod_map_map hV.aemeasurable hG.aemeasurable]
    _ = ∫ x, ∫ z, F (x, z) ∂μ.map G ∂μ.map V := integral_prod F hI
    _ = ∫ x, Y x ∂μ.map V := integral_congr_ae hinner
    _ = _ := integral_map hV.aemeasurable hY.aestronglyMeasurable

/-- Suppose [the model's observational law equals the witness model's
law](hyp:hobs), [the private input is measurable](hyp:hV), [the selection input
is measurable](hyp:hG), [these inputs are independent under the latent
law](hyp:hind), [the selection event is measurable](hyp:hS), [the response is
measurable](hyp:hY), and [the propensity is measurable](hyp:hp). If [the
propensity is nonzero for almost every private input](hyp:hpos), [integrating
the selection indicator over the selection-input law gives that propensity
for almost every private input](hyp:hlaw), and [the selected response divided
by the propensity, set to zero outside selection, equals the observed score
for the chosen arm almost surely](hyp:hselected), then [the response is
integrable under the latent law and its expectation is four fifths for the
treated arm and one sixth for the control arm](goal). -/
-- @node: counterexample_selected_response_identification
lemma counterexample_selected_response_identification
    {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (t : Bool) {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (V : Exogenous backdoorKind dims → X) (G : Exogenous backdoorKind dims → Z)
    (hV : Measurable V) (hG : Measurable G) (hind : IndepFun V G M.latentLaw)
    (S : X × Z → Prop) [DecidablePred S] (hS : MeasurableSet {v | S v})
    (Y p : X → ℝ) (hY : Measurable Y) (hp : Measurable p)
    (hpos : ∀ᵐ x ∂M.latentLaw.map V, p x ≠ 0)
    (hlaw : ∀ᵐ x ∂M.latentLaw.map V,
      (∫ z, (if S (x, z) then (1 : ℝ) else 0) ∂M.latentLaw.map G) = p x)
    (hselected : (fun u => if S (V u, G u) then Y (V u) / p (V u) else 0)
      =ᵐ[M.latentLaw] fun u =>
        counterexampleArmScore t (intervenedEval M (fun _ => none) u)) :
    Integrable (fun u => Y (V u)) M.latentLaw ∧
      (∫ u, Y (V u) ∂M.latentLaw) = (if t then 4/5 else 1/6 : ℝ) := by
  letI := M.probability
  have hI := (counterexampleArmScore_integrable_of_observational_eq M hobs t).congr
    hselected.symm
  obtain ⟨hYI, heq⟩ := independent_selection_identification_ae
    M.latentLaw V G hV hG hind S hS Y p hY hp hpos hlaw hI
  refine ⟨hYI, ?_⟩
  calc
    _ = ∫ u, (if S (V u, G u) then Y (V u) / p (V u) else 0) ∂M.latentLaw := heq.symm
    _ = ∫ u, counterexampleArmScore t (intervenedEval M (fun _ => none) u)
        ∂M.latentLaw := integral_congr_ae hselected
    _ = _ := counterexampleArmScore_integral_of_observational_eq M hobs t

end
end Papers.TbsNeuralCausalPi
