module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleConditional
/-! # The perturbed canonical counterexample SCM and its causal effect -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

-- @node: counterexampleApproxBlockLaw
/-- For [perturbation delta](hyp:delta) and [latent block j](hyp:j), the
[perturbed block distribution](goal) [uses the perturbed finite scalar distribution, embedded as a one-dimensional vector, for the first block](step:1)
and [keeps the original block distribution for either remaining block](step:2). -/
def counterexampleApproxBlockLaw (delta : ℝ) (j : Fin 3) :
    ProbabilityMeasure (L1Vec (counterexampleDims j)) :=
  Fin.cases (let := counterexampleApproxFiniteLatentLaw_probability delta
    ⟨(counterexampleApproxFiniteLatentLaw delta).map (fun x => WithLp.toLp 1 ![x]),
      Measure.isProbabilityMeasure_map (by fun_prop)⟩)
    (fun k => counterexampleBlockLaw k.succ) j

-- @node: counterexampleApproxStructuralWeights
/-- For [perturbation delta](hyp:delta) and [node i](hyp:i), the
[perturbed structural function](goal) [copies the first latent coordinate at the covariate node](step:1),
[uses the perturbed propensity evaluated at the parent covariate at the treatment node](step:2),
and [uses the perturbed outcome function of the covariate and treatment at the outcome node](step:3). -/
def counterexampleApproxStructuralWeights (delta : ℝ) (i : Fin 3) :
    StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) i → L1Vec (outputDim (backdoorKind i)) :=
  Fin.cases (fun x => WithLp.toLp 1 (fun _ =>
      x.ofLp (.inr ⟨⟨0, by simp [canonicalIncidence, counterexampleComponents]⟩, ⟨0, by decide⟩⟩)))
    (Fin.cases (fun x => counterexampleApproxPropensity delta
      (x.ofLp (.inl ⟨⟨0, by exact backdoorDAG.mem_parents.mpr (by decide : (0 : Fin 3) < 1)⟩, ⟨0, by decide⟩⟩)))
      (Fin.cases (fun x => WithLp.toLp 1 (fun _ => counterexampleApproxOutcome delta
        (WithLp.toLp 1 ![(counterexampleOutcomeInput x).ofLp 0,
          (counterexampleOutcomeInput x).ofLp 1]))) (fun k => k.elim0))) i

-- @node: counterexampleApproxStructuralWeights_measurable
/-- [The perturbed structural function at any node is measurable](goal). -/
@[fun_prop] lemma counterexampleApproxStructuralWeights_measurable (delta : ℝ) (i : Fin 3) :
    Measurable (counterexampleApproxStructuralWeights delta i) := by
  fin_cases i
  · change Measurable (fun x : StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) 0 => WithLp.toLp 1 (fun _ : Fin 1 =>
      x.ofLp (.inr ⟨⟨0, by simp [canonicalIncidence, counterexampleComponents]⟩, ⟨0, by decide⟩⟩)))
    fun_prop
  · change Measurable (fun x : StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) 1 => counterexampleApproxPropensity delta
      (x.ofLp (.inl ⟨⟨0, by exact backdoorDAG.mem_parents.mpr (by decide : (0 : Fin 3) < 1)⟩, ⟨0, by decide⟩⟩)))
    fun_prop
  · change Measurable (fun x => WithLp.toLp 1 (fun _ : Fin 1 => counterexampleApproxOutcome delta
      (WithLp.toLp 1 ![(counterexampleOutcomeInput x).ofLp 0,
        (counterexampleOutcomeInput x).ofLp 1])))
    fun_prop

-- @node: counterexampleApproxSCM
/-- For [perturbation delta](hyp:delta), the [perturbed canonical causal model](goal)
uses the original counterexample's graph and latent components, the perturbed structural functions,
and the perturbed block distributions, with valid treatment probabilities. -/
def counterexampleApproxSCM (delta : ℝ) :
    CanonicalSCM backdoorKind counterexampleDims backdoorDAG ⊥ counterexampleComponents where
  categoricalPositive := counterexampleTrueSCM.categoricalPositive
  component := counterexampleTrueSCM.component
  exhaustive := counterexampleTrueSCM.exhaustive
  distinct := counterexampleTrueSCM.distinct
  f := counterexampleApproxStructuralWeights delta
  structuralMeasurable := counterexampleApproxStructuralWeights_measurable delta
  blockLaw := counterexampleApproxBlockLaw delta
  simplex := by
    intro i k h x hx
    fin_cases i <;> simp [backdoorKind] at h
    subst k
    exact counterexampleApproxPropensity_simplex delta _

-- @node: counterexampleApproxSCM_covariate
/-- If [an intervention leaves the covariate untouched](hyp:ht),
[the perturbed model's covariate equals the first coordinate of its first latent block](goal). -/
lemma counterexampleApproxSCM_covariate (delta : ℝ) (t : Intervention backdoorKind)
    (ht : t 0 = none) (u : Exogenous backdoorKind counterexampleDims) :
    (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM t u).ofLp ⟨0,⟨0, by decide⟩⟩ =
      (blockProjection 0 u).ofLp ⟨0, by decide⟩ := by
  rw [counterexample_intervened_coordinate, ht, Option.getD_none]
  rfl

-- @node: counterexampleApproxSCM_treatment
/-- [Under the binary treatment intervention, the perturbed model's treatment coordinate is 2 for the treated arm and 1 for the control arm](goal). -/
lemma counterexampleApproxSCM_treatment (delta : ℝ) (t : Bool)
    (u : Exogenous backdoorKind counterexampleDims) :
    (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (binaryAssignment t) u).ofLp
      ⟨1,⟨0, by decide⟩⟩ = if t then 2 else 1 := by
  rw [counterexample_intervened_coordinate]
  simp [binaryAssignment]

-- @node: counterexampleApproxSCM_outcome
/-- If [an intervention leaves the outcome untouched](hyp:ht),
[the perturbed model's outcome is its perturbed outcome function evaluated at the intervened covariate and treatment](goal). -/
lemma counterexampleApproxSCM_outcome (delta : ℝ) (t : Intervention backdoorKind)
    (ht : t 2 = none) (u : Exogenous backdoorKind counterexampleDims) :
    backdoorOutcome (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM t u) =
      counterexampleApproxOutcome delta (WithLp.toLp 1 ![
        (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM t u).ofLp ⟨0,⟨0, by decide⟩⟩,
        (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM t u).ofLp ⟨1,⟨0, by decide⟩⟩]) := by
  unfold backdoorOutcome
  rw [counterexample_intervened_coordinate, ht, Option.getD_none]
  rfl

-- @node: counterexampleApproxSCM_intervention_outcome
/-- [The perturbed model's outcome under either binary treatment intervention equals the corresponding perturbed intervention outcome function evaluated at the first latent block's scalar coordinate](goal). -/
lemma counterexampleApproxSCM_intervention_outcome (delta : ℝ) (t : Bool)
    (u : Exogenous backdoorKind counterexampleDims) :
    backdoorOutcome (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (binaryAssignment t) u) =
      counterexampleApproxInterventionOutcome delta t ((blockProjection 0 u).ofLp ⟨0, by decide⟩) := by
  rw [counterexampleApproxSCM_outcome delta (binaryAssignment t) (by simp [binaryAssignment]),
    counterexampleApproxSCM_covariate delta (binaryAssignment t) (by simp [binaryAssignment]),
    counterexampleApproxSCM_treatment]
  rfl

-- @node: counterexampleApproxSCM_covariate_law
/-- [The first latent block's scalar coordinate in the perturbed model has the perturbed finite latent distribution](goal). -/
lemma counterexampleApproxSCM_covariate_law (delta : ℝ) :
    (counterexampleApproxSCM delta).latentLaw.map
      (fun u => (blockProjection 0 u).ofLp ⟨0, by decide⟩) =
        counterexampleApproxFiniteLatentLaw delta := by
  let M := counterexampleApproxSCM delta
  let := fun i => canonicalNamedLatentLaw_probability M i
  have hm : Measurable (blockProjection (kind := backdoorKind) (dims := counterexampleDims) 0) := by
    fun_prop [blockProjection]
  have hblock : M.latentLaw.map (blockProjection 0) =
      (M.blockLaw 0 : Measure (L1Vec (counterexampleDims 0))) := by
    rw [canonical_latentLaw_eq_named_product M,
      Measure.map_map hm restoreNamedLatents_measurable]
    change (Measure.pi (canonicalNamedLatentLaw M)).map (fun z => z (.inl 0)) = _
    exact (measurePreserving_eval (canonicalNamedLatentLaw M) (.inl 0)).map_eq
  have he : Measurable (fun x : L1Vec (counterexampleDims 0) => x.ofLp ⟨0, by decide⟩) := by
    fun_prop
  rw [show (fun u : Exogenous backdoorKind counterexampleDims =>
      (blockProjection 0 u).ofLp ⟨0, by decide⟩) =
      (fun x : L1Vec (counterexampleDims 0) => x.ofLp ⟨0, by decide⟩) ∘ blockProjection 0 from rfl,
    ← Measure.map_map he hm, hblock]
  change ((counterexampleApproxFiniteLatentLaw delta).map
    (fun x : ℝ => WithLp.toLp 1 ![x])).map (fun x : L1Vec 1 => x.ofLp 0) = _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

-- @node: counterexampleApproxSCM_intervention_outcome_integrable
/-- [The perturbed model's outcome under either binary treatment intervention is integrable under its latent distribution](goal). -/
lemma counterexampleApproxSCM_intervention_outcome_integrable (delta : ℝ) (t : Bool) :
    Integrable (fun u => backdoorOutcome
      (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (binaryAssignment t) u))
      (counterexampleApproxSCM delta).latentLaw := by
  have h := counterexampleApproxInterventionOutcome_integrable delta t
  rw [← counterexampleApproxSCM_covariate_law delta] at h
  have hm : Measurable (fun u : Exogenous backdoorKind counterexampleDims =>
      (blockProjection 0 u).ofLp ⟨0, by decide⟩) := by fun_prop [blockProjection]
  have hc := (integrable_map_measure
    (counterexampleApproxInterventionOutcome_measurable delta t).aestronglyMeasurable
    hm.aemeasurable).mp h
  simpa only [Function.comp_def, counterexampleApproxSCM_intervention_outcome] using hc

-- @node: counterexampleApproxSCM_effect_integrable
/-- [The difference between treated and control potential outcomes in the perturbed model is integrable under its latent distribution](goal). -/
lemma counterexampleApproxSCM_effect_integrable (delta : ℝ) :
    Integrable (fun u =>
      backdoorOutcome (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (binaryAssignment true) u) -
      backdoorOutcome (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (binaryAssignment false) u))
      (counterexampleApproxSCM delta).latentLaw :=
  (counterexampleApproxSCM_intervention_outcome_integrable delta true).sub
    (counterexampleApproxSCM_intervention_outcome_integrable delta false)

-- @node: counterexampleApproxSCM_ATE
/-- For [a strictly positive perturbation](hyp:hdelta),
[the perturbed model's average treatment effect is one half](goal). -/
lemma counterexampleApproxSCM_ATE (delta : ℝ) (hdelta : 0 < delta) :
    backdoorATE (counterexampleApproxSCM delta).toEuclideanSCM = (1/2 : ℝ) := by
  change (∫ u,
    backdoorOutcome (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (binaryAssignment true) u) -
    backdoorOutcome (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (binaryAssignment false) u)
      ∂(counterexampleApproxSCM delta).latentLaw) = _
  simp only [counterexampleApproxSCM_intervention_outcome]
  have hm : Measurable (fun u : Exogenous backdoorKind counterexampleDims =>
      (blockProjection 0 u).ofLp ⟨0, by decide⟩) := by fun_prop [blockProjection]
  have hf : Measurable (fun x => counterexampleApproxInterventionOutcome delta true x -
      counterexampleApproxInterventionOutcome delta false x) := by fun_prop
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, counterexampleApproxSCM_covariate_law]
  exact counterexampleApproxFiniteATE delta hdelta

end
end Papers.TbsNeuralCausalPi
