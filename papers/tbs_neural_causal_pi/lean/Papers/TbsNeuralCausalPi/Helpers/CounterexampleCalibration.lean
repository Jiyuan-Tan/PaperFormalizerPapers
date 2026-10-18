module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexamplePrivateInputs
/-! # Calibration of the actual private treatment kernel

Private-input independence factors each covariate-cell treatment probability.
The finite observational law then determines the kernel on both carrying cells.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {b : ℕ} {dims : Fin b → ℕ}

-- @node: counterexampleCovariateCell
/-- For [a covariate value a](hyp:a) and [an observed joint realization v](hyp:v),
the [covariate-cell indicator](goal) [is one when the covariate equals a](step:1)
and [zero otherwise](step:2). -/
def counterexampleCovariateCell (a : ℝ) (v : Joint backdoorKind) : ℝ :=
  if counterexampleCovariate v = a then 1 else 0

-- @node: counterexampleCovariateCell_measurable
/-- [The indicator that the covariate equals any fixed real value is measurable](goal). -/
@[fun_prop] lemma counterexampleCovariateCell_measurable (a : ℝ) :
    Measurable (counterexampleCovariateCell a) := by
  unfold counterexampleCovariateCell
  apply Measurable.ite (measurableSet_eq_fun counterexampleCovariate_measurable measurable_const)
    <;> fun_prop

-- @node: counterexampleSelectionProbability
/-- For [a causal model M](hyp:M) with [b latent blocks](hyp:b) and
[latent dimensions dims](hyp:dims), [a binary treatment arm t](hyp:t), and
[a fixed covariate value x](hyp:x), the [selection probability](goal)
is the probability that the model's scalar treatment rule selects that arm when x is fixed
and its selection input is drawn from its marginal latent distribution. -/
def counterexampleSelectionProbability (M : EuclideanSCM backdoorKind dims)
    (t : Bool) (x : ℝ) : ℝ :=
  ∫ g, (if counterexampleScalarTreatment M (x,g) = (if t then 2 else 1 : ℝ)
    then (1 : ℝ) else 0) ∂M.latentLaw.map (counterexampleSelectionInput M)

-- @node: counterexample_cell_selection_factorization
/-- If [a model has the backdoor causal graph](hyp:hgraph) and
[independent latent blocks](hyp:hind), then [the observed probability of a given covariate cell and treatment arm equals the covariate-cell probability times the model's selection probability for that arm at that covariate value](goal). -/
lemma counterexample_cell_selection_factorization
    (M : EuclideanSCM backdoorKind dims) (hgraph : causalGraph M = backdoorGraph)
    (hind : LatentBlocksIndependent M) (a : ℝ) (t : Bool) :
    (∫ v, counterexampleCovariateCell a v *
      (if v.ofLp ⟨1, ⟨0, by decide⟩⟩ = (if t then 2 else 1 : ℝ)
        then (1 : ℝ) else 0) ∂observationalLaw M) =
    (∫ v, counterexampleCovariateCell a v ∂observationalLaw M) *
      counterexampleSelectionProbability M t a := by
  let E := intervenedEval M (fun _ => none)
  let V := counterexamplePrivateInput M
  let G := counterexampleSelectionInput M
  let f := fun v => counterexampleCovariateCell a (E v)
  let g := fun u => if counterexampleScalarTreatment M (a,u) = (if t then 2 else 1 : ℝ)
    then (1 : ℝ) else 0
  have hE : Measurable E := evalSteps_measurable M (fun _ => none) (3*3+3)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hg : Measurable g := by
    dsimp [g]
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) <;> fun_prop
  have hT (u) : counterexampleScalarTreatment M (counterexampleCovariate (E u), G u) =
      (E u).ofLp ⟨1, ⟨0, by decide⟩⟩ := by
    have hh := counterexample_treatment_depends_only_on_covariate M hgraph (E (V u)) (G u)
    have hx := counterexample_covariate_private_factorization M hgraph u ⟨0, by decide⟩
    change counterexampleCovariate (E (V u)) = counterexampleCovariate (E u) at hx
    rw [hx] at hh
    exact hh.symm.trans (counterexample_treatment_private_factorization M hgraph u)
  have hfV (u) : f (V u) = counterexampleCovariateCell a (E u) := by
    have hx := counterexample_covariate_private_factorization M hgraph u ⟨0, by decide⟩
    change counterexampleCovariate (E (V u)) = counterexampleCovariate (E u) at hx
    simp only [f, counterexampleCovariateCell, hx]
  have hprod (u) : f (V u) * g (G u) = counterexampleCovariateCell a (E u) *
      (if (E u).ofLp ⟨1, ⟨0, by decide⟩⟩ = (if t then 2 else 1 : ℝ)
        then (1 : ℝ) else 0) := by
    rw [hfV]
    by_cases hx : counterexampleCovariate (E u) = a
    · have ht := hT u
      rw [hx] at ht
      simp only [g, ht]
    · simp [counterexampleCovariateCell, hx]
  have hi := (counterexample_private_inputs_independent M hgraph hind).integral_fun_comp_mul_comp
    (counterexamplePrivateInput_measurable M).aemeasurable
    (counterexampleSelectionInput_measurable M).aemeasurable
    hf.aestronglyMeasurable hg.aestronglyMeasurable
  rw [show (fun u => f (V u) * g (G u)) = _ from funext hprod] at hi
  rw [show (fun u => f (V u)) = _ from funext hfV] at hi
  have hscore : Measurable (fun v : Joint backdoorKind => counterexampleCovariateCell a v *
      (if v.ofLp ⟨1, ⟨0, by decide⟩⟩ = (if t then 2 else 1 : ℝ)
        then (1 : ℝ) else 0)) := by
    apply Measurable.mul (counterexampleCovariateCell_measurable a)
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) <;> fun_prop
  rw [← integral_map hE.aemeasurable hscore.aestronglyMeasurable,
    ← integral_map hE.aemeasurable (counterexampleCovariateCell_measurable a).aestronglyMeasurable,
    ← integral_map (counterexampleSelectionInput_measurable M).aemeasurable
      hg.aestronglyMeasurable] at hi
  exact hi

-- @node: counterexample_covariate_cell_mass
/-- If [a model has the same observational distribution as the true counterexample](hyp:hobs),
then for [a covariate value equal to minus one or zero](hyp:ha),
[the probability of that covariate cell is one half](goal). -/
lemma counterexample_covariate_cell_mass
    (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (a : ℝ) (ha : a = -1 ∨ a = 0) :
    (∫ v, counterexampleCovariateCell a v ∂observationalLaw M) = 1/2 := by
  rw [counterexample_observable_integral M hobs _
    (counterexampleCovariateCell_measurable a)]
  rcases ha with rfl | rfl <;>
    norm_num [Fin.sum_univ_succ, counterexampleAtomWeight, counterexampleObservationAtom,
      counterexampleJointOfVector, counterexampleCovariateCell, counterexampleCovariate]

-- @node: counterexample_covariate_arm_mass
/-- If [a model has the true counterexample's observational distribution](hyp:hobs) and
[the covariate value is minus one or zero](hyp:ha), then
[the joint probability of that covariate value and a chosen treatment arm equals one half times the true treatment probability there for the treated arm, or its complement for the control arm](goal). -/
lemma counterexample_covariate_arm_mass
    (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (a : ℝ) (ha : a = -1 ∨ a = 0) (t : Bool) :
    (∫ v, counterexampleCovariateCell a v *
      (if v.ofLp ⟨1, ⟨0, by decide⟩⟩ = (if t then 2 else 1 : ℝ)
        then (1 : ℝ) else 0) ∂observationalLaw M) =
      (1/2 : ℝ) * (if t then counterexampleTrueTreatmentProbability a
        else 1 - counterexampleTrueTreatmentProbability a) := by
  rw [counterexample_observable_integral M hobs _ (by
    apply Measurable.mul (counterexampleCovariateCell_measurable a)
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) <;> fun_prop)]
  cases t <;> rcases ha with rfl | rfl <;>
    norm_num [Fin.sum_univ_succ, counterexampleAtomWeight, counterexampleObservationAtom,
      counterexampleJointOfVector, counterexampleCovariateCell, counterexampleCovariate,
      counterexampleTrueTreatmentProbability, counterexampleClamp]

-- @node: counterexample_selection_probability_on_cells
/-- If [a model has the backdoor graph](hyp:hgraph), [independent latent blocks](hyp:hind),
and [the true counterexample's observational distribution](hyp:hobs), then at
[a covariate value of minus one or zero](hyp:ha),
[its selection probability equals the true treatment probability for the treated arm and its complement for the control arm](goal). -/
lemma counterexample_selection_probability_on_cells
    (M : EuclideanSCM backdoorKind dims) (hgraph : causalGraph M = backdoorGraph)
    (hind : LatentBlocksIndependent M)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (a : ℝ) (ha : a = -1 ∨ a = 0) (t : Bool) :
    counterexampleSelectionProbability M t a =
      (if t then counterexampleTrueTreatmentProbability a
        else 1 - counterexampleTrueTreatmentProbability a) := by
  have hh := counterexample_cell_selection_factorization M hgraph hind a t
  rw [counterexample_covariate_cell_mass M hobs a ha,
    counterexample_covariate_arm_mass M hobs a ha t] at hh
  linarith

-- @node: counterexample_covariate_ae_cells
/-- If [a model has the true counterexample's observational distribution](hyp:hobs),
then [its observed covariate equals minus one or zero almost surely](goal). -/
lemma counterexample_covariate_ae_cells
    (M : EuclideanSCM backdoorKind dims)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM) :
    ∀ᵐ v ∂observationalLaw M,
      counterexampleCovariate v = -1 ∨ counterexampleCovariate v = 0 := by
  let F : Joint backdoorKind → ℝ := fun v =>
    if counterexampleCovariate v = -1 ∨ counterexampleCovariate v = 0 then 0 else 1
  have hF : Measurable F := by
    dsimp [F]
    apply Measurable.ite ((measurableSet_eq_fun counterexampleCovariate_measurable
      measurable_const).union (measurableSet_eq_fun counterexampleCovariate_measurable
      measurable_const)) <;> fun_prop
  have hi : Integrable F (observationalLaw M) :=
    counterexample_observable_integrable M hobs F hF
  have hz : (∫ v, F v ∂observationalLaw M) = 0 := by
    rw [counterexample_observable_integral M hobs F hF]
    norm_num [F, Fin.sum_univ_succ, counterexampleObservationAtom,
      counterexampleJointOfVector, counterexampleCovariate]
  have hae := (integral_eq_zero_iff_of_nonneg (by
    intro v; dsimp [F]; split_ifs <;> norm_num) hi).mp hz
  filter_upwards [hae] with v hv
  by_contra hn
  simp [F, hn] at hv

-- @node: counterexample_private_covariate_ae_cells
/-- If [a model has the backdoor graph](hyp:hgraph) and
[the true counterexample's observational distribution](hyp:hobs), then
[evaluating the model without intervention on its private input yields a covariate of minus one or zero almost surely under the private input's distribution](goal). -/
lemma counterexample_private_covariate_ae_cells
    (M : EuclideanSCM backdoorKind dims) (hgraph : causalGraph M = backdoorGraph)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM) :
    ∀ᵐ v ∂M.latentLaw.map (counterexamplePrivateInput M),
      counterexampleCovariate (intervenedEval M (fun _ => none) v) = -1 ∨
      counterexampleCovariate (intervenedEval M (fun _ => none) v) = 0 := by
  have hE := evalSteps_measurable M (fun _ => none) (3*3+3)
  apply (ae_map_iff (counterexamplePrivateInput_measurable M).aemeasurable (by
    exact (measurableSet_eq_fun (counterexampleCovariate_measurable.comp hE)
      measurable_const).union
      (measurableSet_eq_fun (counterexampleCovariate_measurable.comp hE)
        measurable_const))).mpr
  have hh := ae_of_ae_map hE.aemeasurable (counterexample_covariate_ae_cells M hobs)
  filter_upwards [hh] with u hu
  have hx := counterexample_covariate_private_factorization M hgraph u ⟨0, by decide⟩
  change counterexampleCovariate (intervenedEval M (fun _ => none) (counterexamplePrivateInput M u)) =
    counterexampleCovariate (intervenedEval M (fun _ => none) u) at hx
  rwa [hx]

-- @node: counterexample_private_selection_calibration
/-- If [a model has the backdoor graph](hyp:hgraph), [independent latent blocks](hyp:hind),
and [the true counterexample's observational distribution](hyp:hobs), then
[for almost every private input, averaging the treatment-arm indicator over the selection input gives the true treatment probability at the private input's covariate for the treated arm, and its complement for the control arm](goal). -/
lemma counterexample_private_selection_calibration
    (M : EuclideanSCM backdoorKind dims) (hgraph : causalGraph M = backdoorGraph)
    (hind : LatentBlocksIndependent M)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (t : Bool) :
    ∀ᵐ v ∂M.latentLaw.map (counterexamplePrivateInput M),
      (∫ g, (if counterexampleTreatmentFromPrivate M (v,g) = (if t then 2 else 1 : ℝ)
        then (1 : ℝ) else 0) ∂M.latentLaw.map (counterexampleSelectionInput M)) =
      (if t then counterexampleTrueTreatmentProbability
        (counterexampleCovariate (intervenedEval M (fun _ => none) v))
      else 1 - counterexampleTrueTreatmentProbability
        (counterexampleCovariate (intervenedEval M (fun _ => none) v))) := by
  filter_upwards [counterexample_private_covariate_ae_cells M hgraph hobs] with v hv
  calc
    _ = counterexampleSelectionProbability M t
        (counterexampleCovariate (intervenedEval M (fun _ => none) v)) := by
      apply integral_congr_ae
      apply ae_of_all
      intro g
      dsimp only [counterexampleTreatmentFromPrivate]
      simp only [counterexample_treatment_depends_only_on_covariate M hgraph]
    _ = _ := counterexample_selection_probability_on_cells M hgraph hind hobs _ hv t

end
end Papers.TbsNeuralCausalPi
