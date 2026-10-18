module
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableEvaluation
/-! # Explicit ambiguity events for causal tables

The exceptional set used in the transport proof is a fixed Boolean readout
of the joint latent grid code and the original categorical noise. Naming it
allows the very same event to enter the finite-pattern concentration proof.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: causalTableNodeAmbiguity
/-- For [a categorical probability table](hyp:table), [a robustness tolerance](hyp:a),
[a grid cell](hyp:j), [an exogenous realization](hyp:u), and [a node](hyp:i),
[node ambiguity](goal) [never occurs at a continuous node](step:1) and
[occurs at a categorical node when some complete label vector gives table probabilities with no robust winner under that node's private noise](step:2). -/
def causalTableNodeAmbiguity {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (j : Fin s) (u : Exogenous kind dims) (i : Fin n) : Prop :=
  match hi : kind i with
  | .inl _ => False
  | .inr k => ∃ c, ¬ ∃ l, RobustCategoricalWinner (table i k hi c j).val a
      (fun l => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l)) l

-- @node: causalTableNodeAmbiguity_continuous
/-- For [a categorical probability table](hyp:table), if [the chosen node is continuous of the specified dimension](hyp:hi),
[its node ambiguity condition is false](goal). -/
lemma causalTableNodeAmbiguity_continuous {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (j : Fin s) (u : Exogenous kind dims) (i : Fin n)
    (d : ℕ) (hi : kind i = Sum.inl d) :
    causalTableNodeAmbiguity table a j u i = False := by
  unfold causalTableNodeAmbiguity
  split
  · rfl
  · rename_i k hk
    cases hi.symm.trans hk

-- @node: causalTableNodeAmbiguity_categorical
/-- For [a categorical probability table](hyp:table), if [the chosen node is categorical with the specified number of categories](hyp:hi),
[node ambiguity is equivalent to the existence of a complete label vector for which the table probabilities at the chosen cell admit no robust winner under the node's private noise](goal). -/
lemma causalTableNodeAmbiguity_categorical {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (j : Fin s) (u : Exogenous kind dims) (i : Fin n)
    (k : ℕ) (hi : kind i = Sum.inr k) :
    causalTableNodeAmbiguity table a j u i =
      (∃ c, ¬ ∃ l, RobustCategoricalWinner (table i k hi c j).val a
        (fun l => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)) l) := by
  unfold causalTableNodeAmbiguity
  split
  · rename_i d hd
    cases hi.symm.trans hd
  · rename_i k' hk'
    have he : k = k' := Sum.inr.inj (hi.symm.trans hk')
    subst k'
    rfl

-- @node: ncmCausalTableAmbiguity
/-- For [a neural causal model](hyp:R), [a latent grid code](hyp:code),
[a categorical probability table](hyp:table), and [a robustness tolerance](hyp:a),
[the simulation ambiguity event](goal) consists of the simulation inputs at which at least one node is ambiguous,
using the model's generated grid cell and original exogenous noise. -/
def ncmCausalTableAmbiguity {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) : Set (SimulationInput kind counts) :=
  {z | ∃ i, causalTableNodeAmbiguity table a
    (code (jointNonGumbel (ncmSimulationExogenous R z))) (ncmSimulationExogenous R z) i}

-- @node: ncmCausalTableNodeAmbiguity_measurable
/-- Given [a measurable latent grid code](hyp:hcode) and [a categorical probability table](hyp:table),
[the simulation inputs producing ambiguity at any fixed node form a measurable set](goal). -/
lemma ncmCausalTableNodeAmbiguity_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (i : Fin n) :
    MeasurableSet {z | causalTableNodeAmbiguity table a
      (code (jointNonGumbel (ncmSimulationExogenous R z))) (ncmSimulationExogenous R z) i} := by
  cases hi : kind i with
  | inl d => simp only [causalTableNodeAmbiguity_continuous table a _ _ i d hi,
      Set.setOf_false, MeasurableSet.empty]
  | inr k =>
    simp only [causalTableNodeAmbiguity_categorical table a _ _ i k hi]
    change MeasurableSet {z | CategoricalTableAmbiguity
      (fun _ : CategoricalStratum kind => k)
      (fun z => jointNonGumbel (ncmSimulationExogenous R z))
      (fun _ z l => (categoricalNoise i (ncmSimulationExogenous R z)).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l))
      (fun c x => (table i k hi c (code x)).val) a z}
    exact measurableSet_categoricalTableAmbiguity _ _ _ _ (by fun_prop)
      (by intro c; fun_prop [categoricalNoise]) (by intro c; fun_prop) a

-- @node: ncmCausalTableAmbiguity_measurable
/-- Given [a measurable latent grid code](hyp:hcode) and [a categorical probability table](hyp:table),
[the event that at least one node is ambiguous is measurable](goal). -/
lemma ncmCausalTableAmbiguity_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k) (a : ℝ) :
    MeasurableSet (ncmCausalTableAmbiguity R code table a) := by
  simpa only [ncmCausalTableAmbiguity, Set.setOf_exists] using
    MeasurableSet.iUnion (ncmCausalTableNodeAmbiguity_measurable R code hcode table a)

-- @node: ncmCausalTableNodeAmbiguity_probability_le
/-- Given [a measurable latent grid code](hyp:hcode), [a categorical probability table](hyp:table),
and [a nonnegative robustness tolerance](hyp:ha),
[the probability of ambiguity at a fixed node is at most twice the tolerance times that node's categorical noise dimension summed over all complete label vectors](goal). -/
lemma ncmCausalTableNodeAmbiguity_probability_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (ha : 0 ≤ a) (i : Fin n) :
    (simulationInputLaw kind counts) {z | causalTableNodeAmbiguity table a
      (code (jointNonGumbel (ncmSimulationExogenous R z))) (ncmSimulationExogenous R z) i} ≤
      ENNReal.ofReal (2 * (∑ _c : CategoricalStratum kind,
        (noiseDim (kind i) : ℝ)) * a) := by
  letI := simulationInputLaw_probability kind counts
  cases hi : kind i with
  | inl d => simp only [causalTableNodeAmbiguity_continuous table a _ _ i d hi,
      Set.setOf_false, measure_empty, zero_le]
  | inr k =>
    have h := categoricalTableAmbiguity_probability_le (simulationInputLaw kind counts)
      (fun _ : CategoricalStratum kind => k)
      (fun z => jointNonGumbel (ncmSimulationExogenous R z))
      (fun _ z l => (categoricalNoise i (ncmSimulationExogenous R z)).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l))
      (fun c x => (table i k hi c (code x)).val)
      (by fun_prop) (by intro c; fun_prop [categoricalNoise])
      (fun _ => ncm_jointNonGumbel_indep_categorical R i k hi)
      (fun _ => ncm_categorical_noise_law R i k hi)
      (by intro c; fun_prop) (fun c x => (table i k hi c (code x)).property.1)
      (fun c x => (table i k hi c (code x)).property.2) a ha
    simpa only [causalTableNodeAmbiguity_categorical table a _ _ i k hi,
      hi, CategoricalTableAmbiguity, noiseDim] using h

-- @node: ncmCausalTableAmbiguity_probability_le
/-- Given [a measurable latent grid code](hyp:hcode), [a categorical probability table](hyp:table),
and [a nonnegative robustness tolerance](hyp:ha),
[the probability of ambiguity at any node is at most twice the tolerance times the sum of categorical noise dimensions over all nodes and complete label vectors](goal). -/
lemma ncmCausalTableAmbiguity_probability_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (ha : 0 ≤ a) :
    (simulationInputLaw kind counts) (ncmCausalTableAmbiguity R code table a) ≤
      ENNReal.ofReal (2 * (∑ i, ∑ _c : CategoricalStratum kind,
        (noiseDim (kind i) : ℝ)) * a) := by
  classical
  rw [ncmCausalTableAmbiguity, Set.setOf_exists]
  calc
    _ ≤ ∑ i, (simulationInputLaw kind counts) {z | causalTableNodeAmbiguity table a
        (code (jointNonGumbel (ncmSimulationExogenous R z))) (ncmSimulationExogenous R z) i} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (2 * (∑ _c : CategoricalStratum kind,
        (noiseDim (kind i) : ℝ)) * a) :=
      Finset.sum_le_sum (fun i _ => ncmCausalTableNodeAmbiguity_probability_le
        R code hcode table a ha i)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul]

-- @node: ncmCausalTableNodeAmbiguity_selector_agreement
/-- For [a categorical probability table](hyp:table), assume [a nonnegative tolerance](hyp:ha)
and [uniform approximation of fixed-label categorical propensities within that tolerance](hyp:herr).
If [the chosen simulation input is unambiguous at the chosen node](hyp:hz),
[applying the table selector to the model's observed complete labels preserves the observed label at that node](goal). -/
lemma ncmCausalTableNodeAmbiguity_selector_agreement {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : ℝ) (ha : 0 ≤ a)
    (herr : ∀ i k hi z c j,
      |(fixedLabelCategoricalPropensity R.canonical c i k hi
          (jointNonGumbel (ncmSimulationExogenous R z))).val j -
        (table i k hi c (code (jointNonGumbel (ncmSimulationExogenous R z)))).val j| ≤ a)
    (z : SimulationInput kind counts) (i : Fin n)
    (hz : ¬ causalTableNodeAmbiguity table a
      (code (jointNonGumbel (ncmSimulationExogenous R z))) (ncmSimulationExogenous R z) i) :
    causalTableSelector R.canonical table
      (code (jointNonGumbel (ncmSimulationExogenous R z)))
      (ncmSimulationExogenous R z) (observedCategoricalStratum (ncmEval R z)) i =
        observedCategoricalStratum (ncmEval R z) i := by
  have hcases : (∃ d, kind i = Sum.inl d) ∨ (∃ k, kind i = Sum.inr k) := by
    cases kind i with
    | inl d => exact Or.inl ⟨d, rfl⟩
    | inr k => exact Or.inr ⟨k, rfl⟩
  rcases hcases with ⟨d, hi⟩ | ⟨k, hi⟩
  ·
    apply Fin.ext
    have hs : max 1 (noiseDim (kind i)) = 1 := by simp [hi, noiseDim]
    have h1 := (causalTableSelector R.canonical table
      (code (jointNonGumbel (ncmSimulationExogenous R z)))
      (ncmSimulationExogenous R z) (observedCategoricalStratum (ncmEval R z)) i).isLt
    have h2 := (observedCategoricalStratum (ncmEval R z) i).isLt
    omega
  · rw [causalTableNodeAmbiguity_categorical table a _ _ i k hi] at hz
    let U := fun z => jointNonGumbel (ncmSimulationExogenous R z)
    let noise := fun z (l : Fin k) =>
      (categoricalNoise i (ncmSimulationExogenous R z)).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l)
    let q := fun c x => (table i k hi c (code x)).val
    have h := categoricalTable_noAmbiguity_selector_agreement
      (fun _ : CategoricalStratum kind => k) U (fun _ => noise) q
      (fun c x => (table i k hi c (code x)).property.1)
      (fun c x => (table i k hi c (code x)).property.2) a ha
      (fun _ m hm => R.canonical.categoricalPositive i m (hi.trans hm)) z hz
      (observedCategoricalStratum (ncmEval R z))
      (fixedLabelCategoricalPropensity R.canonical
        (observedCategoricalStratum (ncmEval R z)) i k hi (U z)).val
      (fixedLabelCategoricalPropensity R.canonical _ i k hi (U z)).property.1
      (fixedLabelCategoricalPropensity R.canonical _ i k hi (U z)).property.2
      (herr i k hi z _)
    apply Fin.ext
    rw [causalTableSelector_categorical R.canonical table _ _ _ i k hi]
    exact ((factual_categorical_stratum_eq_selector R.canonical
      (ncmSimulationExogenous R z) i k hi).trans (congrArg Fin.val h)).symm

-- @node: ncmCausalTableEvaluation_eq_off_ambiguity
/-- Given [a measurable grid code](hyp:hcode) and [a categorical probability table](hyp:table)
that [depends only on earlier labels in topological order](hyp:hcausal), assume
[a nonnegative tolerance](hyp:ha) and [uniform approximation of fixed-label propensities within that tolerance](hyp:herr).
Then [at every simulation input outside the ambiguity event, table evaluation equals the model's observed complete categorical labels](goal). -/
lemma ncmCausalTableEvaluation_eq_off_ambiguity {counts : Fin b → ℕ}
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
    ∀ z ∉ ncmCausalTableAmbiguity R code table a,
      causalTableEvaluation R.canonical table
        (code (jointNonGumbel (ncmSimulationExogenous R z)))
        (ncmSimulationExogenous R z) = observedCategoricalStratum (ncmEval R z) := by
  intro z hz
  have heq : causalTableSelector R.canonical table
      (code (jointNonGumbel (ncmSimulationExogenous R z)))
      (ncmSimulationExogenous R z) (observedCategoricalStratum (ncmEval R z)) =
        observedCategoricalStratum (ncmEval R z) := by
    funext i
    exact ncmCausalTableNodeAmbiguity_selector_agreement R code table a ha herr z i
      (fun hi => hz ⟨i, hi⟩)
  funext i
  exact causalLabelSteps_eq_solution dag.topoOrder _
    (causalTableSelector_prefix_causal R.canonical table hcausal _ _)
    _ heq _ i (scm_topoOrder_lt_horizon R.canonical.toEuclideanSCM i)


-- @node: ncmCausalTableReadout_error_le
/-- Given [a measurable grid code](hyp:hcode) and [a categorical probability table](hyp:table)
that [depends only on earlier labels](hyp:hcausal), suppose [the propensity tolerance is nonnegative](hyp:ha)
and [the table approximates every fixed-label propensity within that tolerance](hyp:herr).
If [model outputs have norm at most the given radius](hyp:hbound), [readout values have norm at most that radius](hyp:hvbound),
and [each fixed-label observation is approximated by its readout within the given readout error](hyp:hread),
[the extended distance between each model output and its table readout is at most the nonnegative part of the readout error plus twice the radius on the ambiguity event](goal). -/
lemma ncmCausalTableReadout_error_le {counts : Fin b → ℕ}
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
    ∀ z, edist (ncmEval R z)
        (v (causalTableEvaluation R.canonical table
          (code (jointNonGumbel (ncmSimulationExogenous R z)))
          (ncmSimulationExogenous R z))
          (code (jointNonGumbel (ncmSimulationExogenous R z)))) ≤
        ENNReal.ofReal e + (ncmCausalTableAmbiguity R code table a).indicator (fun _ => ENNReal.ofReal (2 * B)) z := by
  classical
  let bad := ncmCausalTableAmbiguity R code table a
  have he := ncmCausalTableEvaluation_eq_off_ambiguity
    R code hcode table hcausal a ha herr
  intro z
  by_cases hz : z ∈ bad
  · rw [Set.indicator_of_mem hz, edist_dist]
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) (le_add_left le_rfl)
    have h1 := hbound z
    have h2 := hvbound (causalTableEvaluation R.canonical table
      (code (jointNonGumbel (ncmSimulationExogenous R z))) (ncmSimulationExogenous R z))
      (code (jointNonGumbel (ncmSimulationExogenous R z)))
    exact (dist_le_norm_add_norm _ _).trans (by linarith only [h1, h2])
  · rw [Set.indicator_of_notMem hz, add_zero, he z hz, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hf := factual_eq_fixedLabelObservation_stratum R.canonical.toEuclideanSCM
      (ncmSimulationExogenous R z)
    change ncmEval R z = _ at hf
    conv_lhs => arg 1; rw [hf]
    exact hread z (observedCategoricalStratum (ncmEval R z))

end
end Papers.TbsNeuralCausalPi
