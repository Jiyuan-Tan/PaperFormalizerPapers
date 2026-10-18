module
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableEvents
/-! # Causal tables recover the factual categorical labels

The robust race event is taken over every complete label and every node.
On its complement the factual label solves the rounded table equations.
Uniqueness of the causal recursion then identifies its computed output.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: ncm_causalTableEvaluation_agrees_off_ambiguity
/-- With [a measurable latent grid code](hyp:hcode) and [a categorical probability table](hyp:table)
that [depends only on earlier labels in topological order](hyp:hcausal), suppose
[the approximation tolerance is nonnegative](hyp:ha) and [every table propensity approximates the corresponding fixed-label propensity within that tolerance](hyp:herr).
Then [there is a measurable exceptional event with probability at most twice the tolerance times the sum of categorical noise dimensions over all nodes and complete labels, outside which table evaluation equals the model's observed categorical labels](goal). -/
lemma ncm_causalTableEvaluation_agrees_off_ambiguity {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (hcausal : ∀ i k hi c c',
      (∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) →
        table i k hi c = table i k hi c')
    (a : ℝ) (ha : 0 ≤ a)
    (herr : ∀ i k hi z c j,
      |(fixedLabelCategoricalPropensity R.canonical c i k hi
          (jointNonGumbel (ncmSimulationExogenous R z))).val j -
        (table i k hi c (code (jointNonGumbel (ncmSimulationExogenous R z)))).val j| ≤ a) :
    ∃ bad : Set (SimulationInput kind counts), MeasurableSet bad ∧
      (simulationInputLaw kind counts) bad ≤
        ENNReal.ofReal (2 * (∑ i, ∑ _c : CategoricalStratum kind,
          (noiseDim (kind i) : ℝ)) * a) ∧
      ∀ z ∉ bad,
        causalTableEvaluation R.canonical table
          (code (jointNonGumbel (ncmSimulationExogenous R z)))
          (ncmSimulationExogenous R z) = observedCategoricalStratum (ncmEval R z) := by
  exact ⟨ncmCausalTableAmbiguity R code table a,
    ncmCausalTableAmbiguity_measurable R code hcode table a,
    ncmCausalTableAmbiguity_probability_le R code hcode table a ha,
    ncmCausalTableEvaluation_eq_off_ambiguity R code hcode table hcausal a ha herr⟩

-- @node: ncm_causalTableType_measurable
/-- With [a measurable latent grid code](hyp:hcode) and [a categorical probability table](hyp:table),
[the pair consisting of the generated grid cell and the complete label vector evaluated with the original simulation noise is measurable](goal). -/
@[fun_prop] lemma ncm_causalTableType_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k) :
    Measurable (fun z =>
      (code (jointNonGumbel (ncmSimulationExogenous R z)),
        causalTableEvaluation R.canonical table
          (code (jointNonGumbel (ncmSimulationExogenous R z)))
          (ncmSimulationExogenous R z))) := by
  fun_prop

-- @node: ncm_causalTableReadout_measurable
/-- Given [a measurable latent grid code](hyp:hcode) and [a categorical probability table](hyp:table),
[any readout of the table-evaluated complete labels and generated grid cell is measurable in the simulation input](goal). -/
lemma ncm_causalTableReadout_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (v : CategoricalStratum kind → Fin s → Joint kind) :
    Measurable (fun z => v (causalTableEvaluation R.canonical table
      (code (jointNonGumbel (ncmSimulationExogenous R z)))
      (ncmSimulationExogenous R z)) (code (jointNonGumbel (ncmSimulationExogenous R z)))) := by
  fun_prop

-- @node: ncm_causalTableReadout_error_le
/-- With [a measurable grid code](hyp:hcode) and [a categorical probability table](hyp:table)
that [depends only on earlier labels](hyp:hcausal), assume [a nonnegative propensity tolerance](hyp:ha)
and [uniform approximation of all fixed-label propensities within that tolerance](hyp:herr).
If [model outputs have norm at most the given radius](hyp:hbound), [all readout values have norm at most that radius](hyp:hvbound),
and [the readout approximates each fixed-label observation within the given readout error](hyp:hread),
then [there is a measurable exceptional event with probability at most twice the propensity tolerance times the sum of categorical noise dimensions over nodes and complete labels, and the extended distance from each model output to its table readout is at most the readout error plus twice the radius on that event](goal). -/
lemma ncm_causalTableReadout_error_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (hcausal : ∀ i k hi c c',
      (∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) →
        table i k hi c = table i k hi c')
    (a : ℝ) (ha : 0 ≤ a)
    (herr : ∀ i k hi z c j,
      |(fixedLabelCategoricalPropensity R.canonical c i k hi
          (jointNonGumbel (ncmSimulationExogenous R z))).val j -
        (table i k hi c (code (jointNonGumbel (ncmSimulationExogenous R z)))).val j| ≤ a)
    (v : CategoricalStratum kind → Fin s → Joint kind) (e B : ℝ)
    (hbound : ∀ z, ‖ncmEval R z‖ ≤ B) (hvbound : ∀ c j, ‖v c j‖ ≤ B)
    (hread : ∀ z c,
      dist (fixedLabelObservation R.canonical.toEuclideanSCM (categoricalStratumAssignment c)
        (jointNonGumbel (ncmSimulationExogenous R z)))
        (v c (code (jointNonGumbel (ncmSimulationExogenous R z)))) ≤ e) :
    ∃ bad : Set (SimulationInput kind counts), MeasurableSet bad ∧
      (simulationInputLaw kind counts) bad ≤
        ENNReal.ofReal (2 * (∑ i, ∑ _c : CategoricalStratum kind,
          (noiseDim (kind i) : ℝ)) * a) ∧
      ∀ z, edist (ncmEval R z)
        (v (causalTableEvaluation R.canonical table
          (code (jointNonGumbel (ncmSimulationExogenous R z)))
          (ncmSimulationExogenous R z))
          (code (jointNonGumbel (ncmSimulationExogenous R z)))) ≤
        ENNReal.ofReal e + bad.indicator (fun _ => ENNReal.ofReal (2 * B)) z := by
  exact ⟨ncmCausalTableAmbiguity R code table a,
    ncmCausalTableAmbiguity_measurable R code hcode table a,
    ncmCausalTableAmbiguity_probability_le R code hcode table a ha,
    ncmCausalTableReadout_error_le R code hcode table hcausal a ha herr
      v e B hbound hvbound hread⟩

end
end Papers.TbsNeuralCausalPi
