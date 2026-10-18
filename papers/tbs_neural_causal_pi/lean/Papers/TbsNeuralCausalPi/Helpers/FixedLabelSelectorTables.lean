module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelPropensities
public import Papers.TbsNeuralCausalPi.Helpers.SimulationTableAmbiguity
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalTransport
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationCategorical
/-! # Factual categorical labels and their rounded propensity tables

The complete factual label chooses the fixed-label propensity entry used at
an active node. The robustness event is uniform over all such entries, even
though the factual label depends on the same intrinsic Gumbel coordinates.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- If [node i is categorical with k categories](hyp:hi), [each numerical coordinate
of its factual observation equals one plus the category selected using the
propensities for the observed complete stratum and its categorical noise](goal). -/
-- @node: factual_categorical_coordinate_eq_selector
lemma factual_categorical_coordinate_eq_selector
    (M : CanonicalSCM kind dims dag G C) (u : Exogenous kind dims)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (j : Fin (valueDim (kind i))) :
    (intervenedEval M.toEuclideanSCM (fun _ => none) u).ofLp ⟨i,j⟩ =
      ((canonicalSelector (.inr k)
        (fun m hm => M.categoricalPositive i m (hi.trans hm))
        (WithLp.toLp 1 (fixedLabelCategoricalPropensity M
          (observedCategoricalStratum (intervenedEval M.toEuclideanSCM (fun _ => none) u))
          i k hi (jointNonGumbel u)).val)
        (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)))).val + 1 : ℝ) := by
  have hcoord : (intervenedEval M.toEuclideanSCM (fun _ => none) u).ofLp ⟨i,j⟩ =
      (nodeValue M.toEuclideanSCM i
        (evalSteps M.toEuclideanSCM (fun _ => none) u (dag.topoOrder i)) u).ofLp j := by
    change (evalSteps M.toEuclideanSCM (fun _ => none) u (n*n+n)).ofLp ⟨i,j⟩ = _
    rw [evalSteps_coordinate_after_visit M.toEuclideanSCM _ u i _
      (scm_topoOrder_lt_horizon M.toEuclideanSCM i)]
    simp only [evalSteps, WithLp.ofLp_toLp, ite_true, Option.getD_none]
    rfl
  rw [hcoord]
  rw [nodeValue_categorical_coordinate M.toEuclideanSCM i k hi,
    canonical_categoricalLabel_eq_selector M i k hi]
  simp only [fixedLabelCategoricalPropensity, fixedLabelStructuralInput_factual_stratum]
  rfl


/-- If [node i is categorical with k categories](hyp:hi), [its decoded factual
label equals the selector applied to the propensities for the observed complete
stratum and its categorical noise](goal), including at simplex boundaries and ties. -/
-- @node: factual_categorical_stratum_eq_selector
lemma factual_categorical_stratum_eq_selector
    (M : CanonicalSCM kind dims dag G C) (u : Exogenous kind dims)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k) :
    (observedCategoricalStratum
      (intervenedEval M.toEuclideanSCM (fun _ => none) u) i).val =
      (canonicalSelector (.inr k)
        (fun m hm => M.categoricalPositive i m (hi.trans hm))
        (WithLp.toLp 1 (fixedLabelCategoricalPropensity M
          (observedCategoricalStratum (intervenedEval M.toEuclideanSCM (fun _ => none) u))
          i k hi (jointNonGumbel u)).val)
        (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)))).val := by
  apply observedCategoricalStratum_recovers_label _ i k hi
  intro j
  simpa only [Nat.cast_add, Nat.cast_one] using
    factual_categorical_coordinate_eq_selector M u i k hi j

/-- If [node i is categorical with k categories](hyp:hi), [the generated joint
non-Gumbel latent vector and that node's k categorical noise coordinates are
independent under the simulation input law](goal). -/
-- @node: ncm_jointNonGumbel_indep_categorical
lemma ncm_jointNonGumbel_indep_categorical {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k) :
    IndepFun (fun z => jointNonGumbel (ncmSimulationExogenous R z))
      (fun z l => (categoricalNoise i (ncmSimulationExogenous R z)).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l)) (simulationInputLaw kind counts) := by
  let pack : (∀ j, L1Vec (dims j)) → Latent dims :=
    fun x => WithLp.toLp 1 (fun a => (x a.1).ofLp a.2)
  have hp : Measurable pack := by fun_prop
  have hg : Measurable (fun g : Fin (noiseDim (kind i)) → ℝ =>
      fun l : Fin k => g (Fin.cast (congrArg noiseDim hi).symm l)) := by fun_prop
  exact (ncmGeneratedBlocks_indep_categorical R i).comp hp hg

/-- If [node i is categorical with k categories](hyp:hi), [its categorical noise
vector under the simulation input law has the prescribed k-dimensional Gumbel
input distribution](goal). -/
-- @node: ncm_categorical_noise_law
lemma ncm_categorical_noise_law {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k) :
    (simulationInputLaw kind counts).map
      (fun z l => (categoricalNoise i (ncmSimulationExogenous R z)).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l)) = gumbelInputs k := by
  have h := canonical_categorical_noise_law R.canonical i k hi
  rw [← ncmSimulationExogenous_law R, Measure.map_map (by fun_prop [categoricalNoise])
    (ncmSimulationExogenous_measurable R)] at h
  exact h

/-- Suppose [node i has k categories](hyp:hi), [the finite latent code is
measurable](hyp:hcode), [the tolerance a is nonnegative](hyp:ha), and [every table
entry approximates its fixed-stratum propensity within a in every category and
at every simulation input](hyp:herr). Then [there is a measurable exceptional
event of probability at most twice a times k times the number of complete
strata, outside which the factual label equals the selector using the table for
the observed stratum, the latent code, and the same categorical noise](goal). -/
-- @node: ncm_factual_categorical_table_agreement
lemma ncm_factual_categorical_table_agreement {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (ha : 0 ≤ a)
    (herr : ∀ z c j,
      |(fixedLabelCategoricalPropensity R.canonical c i k hi
          (jointNonGumbel (ncmSimulationExogenous R z))).val j -
        (table c (code (jointNonGumbel (ncmSimulationExogenous R z)))).val j| ≤ a) :
    ∃ bad : Set (SimulationInput kind counts), MeasurableSet bad ∧
      (simulationInputLaw kind counts) bad ≤
        ENNReal.ofReal (2 * (∑ _c : CategoricalStratum kind, (k : ℝ)) * a) ∧
      ∀ z ∉ bad,
        (observedCategoricalStratum (ncmEval R z) i).val =
          (canonicalSelector (.inr k)
            (fun m hm => R.canonical.categoricalPositive i m (hi.trans hm))
            (WithLp.toLp 1 (table (observedCategoricalStratum (ncmEval R z))
              (code (jointNonGumbel (ncmSimulationExogenous R z)))).val)
            (WithLp.toLp 1 (fun l => (categoricalNoise i (ncmSimulationExogenous R z)).ofLp
              (Fin.cast (congrArg noiseDim hi).symm l)))).val := by
  letI := simulationInputLaw_probability kind counts
  let U := fun z => jointNonGumbel (ncmSimulationExogenous R z)
  let noise := fun z (l : Fin k) =>
    (categoricalNoise i (ncmSimulationExogenous R z)).ofLp
      (Fin.cast (congrArg noiseDim hi).symm l)
  let q := fun c x => (table c (code x)).val
  have hU : Measurable U := by fun_prop
  have hg : Measurable noise := by fun_prop [categoricalNoise]
  have hq : ∀ c, Measurable (q c) := by intro c; fun_prop
  have hpos : ∀ c x j, 0 ≤ q c x j := fun c x => (table c (code x)).property.1
  have hsum : ∀ c x, ∑ j, q c x j = 1 := fun c x => (table c (code x)).property.2
  let bad := {z | CategoricalTableAmbiguity (fun _ : CategoricalStratum kind => k)
    U (fun _ => noise) q a z}
  refine ⟨bad, measurableSet_categoricalTableAmbiguity _ U _ q hU (fun _ => hg) hq a,
    categoricalTableAmbiguity_probability_le _ _ U _ q hU (fun _ => hg)
      (fun _ => ncm_jointNonGumbel_indep_categorical R i k hi)
      (fun _ => ncm_categorical_noise_law R i k hi) hq hpos hsum a ha, ?_⟩
  intro z hz
  have h := categoricalTable_noAmbiguity_selector_agreement _ U (fun _ => noise) q
    hpos hsum a ha (fun _ m hm => R.canonical.categoricalPositive i m (hi.trans hm))
    z hz (observedCategoricalStratum (ncmEval R z))
    (fixedLabelCategoricalPropensity R.canonical
      (observedCategoricalStratum (ncmEval R z)) i k hi (U z)).val
    (fixedLabelCategoricalPropensity R.canonical _ i k hi (U z)).property.1
    (fixedLabelCategoricalPropensity R.canonical _ i k hi (U z)).property.2
    (herr z _)
  exact (factual_categorical_stratum_eq_selector R.canonical
    (ncmSimulationExogenous R z) i k hi).trans (congrArg Fin.val h)

end
end Papers.TbsNeuralCausalPi
