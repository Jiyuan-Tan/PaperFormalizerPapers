module
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableApproximation
/-! # Sampling transport for the actual causal table

The finite type is the latent grid index paired with the complete categorical
label. Subset and ambiguity estimates imply a complete-observation transport
bound on the original common draws, including zero propensity coordinates.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: simulation_finite_type_empirical_wasserstein_le
/-- Suppose [the sample size is positive](hyp:hm), [the observation map is
measurable](hyp:hf), [the finite type map is measurable](hyp:htype), [a common
observation set is compact](hyp:hS), [all observations lie in it](hyp:hfrange),
[all type representatives lie in it](hyp:hvrange), and [the exceptional event is
measurable](hyp:hE). If [the approximation allowance is nonnegative](hyp:hc),
[the diameter bound is nonnegative](hyp:hB), [the sampling tolerance is
nonnegative](hyp:he), [representatives have pairwise distances bounded by that
diameter](hyp:hdiam), [each observation is within the approximation allowance of
its representative, with an additional diameter allowance on the exceptional
event](hyp:herr), [that event has probability at most the tolerance](hyp:hprob),
[its empirical frequency error is at most the tolerance](hyp:hamb), and [every
type subset has empirical probability error at most the tolerance](hyp:hsub), then
[the Wasserstein distance of order one between the observation law and its
empirical law is at most twice the approximation allowance plus four times the
diameter bound times the sampling tolerance](goal). -/
lemma simulation_finite_type_empirical_wasserstein_le
    {A X T : Type*} [MeasurableSpace A]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [Finite T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (mu : Measure A) [IsProbabilityMeasure mu] {m : ℕ} (hm : 0 < m)
    (f : A → X) (hf : Measurable f)
    (typeOf : A → T) (htype : Measurable typeOf) (draws : Fin m → A)
    (v : T → X) (S : Set X) (hS : IsCompact S)
    (hfrange : ∀ z, f z ∈ S) (hvrange : ∀ i, v i ∈ S)
    (E : Set A) (hE : MeasurableSet E) (c B e : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hdiam : ∀ i j, dist (v i) (v j) ≤ B)
    (herr : ∀ z, edist (f z) (v (typeOf z)) ≤
      ENNReal.ofReal c + E.indicator (fun _ => ENNReal.ofReal B) z)
    (hprob : mu.real E ≤ e)
    (hamb : |mu.real E - (m : ℝ)⁻¹ *
      ∑ i, E.indicator (fun _ => (1 : ℝ)) (draws i)| ≤ e)
    (hsub : ∀ s : Set T,
      |mu.real (typeOf ⁻¹' s) -
        (m : ℝ)⁻¹ * ∑ i, if typeOf (draws i) ∈ s then (1 : ℝ) else 0| ≤ e) :
    wasserstein1 (mu.map f) (empiricalMeasure (fun i => f (draws i))) ≤
      ENNReal.ofReal (2 * c + 4 * B * e) := by
  classical
  letI := Fintype.ofFinite T
  let enc := Fintype.equivFin T
  refine simulation_table_empirical_wasserstein_le mu hm f hf
    (fun z => enc (typeOf z)) (by fun_prop) draws
    (fun i => v (enc.symm i)) S hS hfrange (fun i => hvrange _) E hE
    c B e hc hB he (fun i j => hdiam _ _) ?_ hprob hamb ?_
  · simpa only [Equiv.symm_apply_apply] using herr
  · intro s
    simpa only [Set.preimage_preimage, Function.comp_def, Set.mem_preimage,
      Finset.mem_coe] using hsub (enc ⁻¹' (s : Set (Fin (Fintype.card T))))

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: ncmCausalTableType
/-- For [a neural causal model with its node types, latent block dimensions,
graph, block incidence, generator counts, structural and generator classes, and
optional bound](hyp:R,n,b,kind,dims,dag,G,C,counts,F0,F1,bound), [a latent code with
a finite number of grid indices](hyp:code,s), [a table assigning categorical
probabilities to each node, label stratum, and grid index](hyp:table), and [a
simulation input](hyp:z), [the causal-table type](goal) pairs the coded non-Gumbel
latent output with the categorical label obtained by evaluating the table at
that index using the model's simulated exogenous noise. -/
def ncmCausalTableType {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (z : SimulationInput kind counts) : Fin s × CategoricalStratum kind :=
  (code (jointNonGumbel (ncmSimulationExogenous R z)),
    causalTableEvaluation R.canonical table
      (code (jointNonGumbel (ncmSimulationExogenous R z)))
      (ncmSimulationExogenous R z))

-- @node: ncmCausalTableType_measurable
/-- If [the latent grid code is measurable](hyp:hcode), then [the pair consisting
of the simulated latent grid index and its causal-table categorical label is a
measurable function of the simulation input](goal), for [any categorical
probability table](hyp:table). -/
@[fun_prop] lemma ncmCausalTableType_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k) :
    Measurable (ncmCausalTableType R code table) := by
  first | fun_prop | exact ncm_causalTableType_measurable R code hcode table

-- @node: ncmCausalTable_sampling_transport
/-- Suppose [the latent grid code is measurable](hyp:hcode), [a table assigns
categorical probabilities to node, label, and grid-index combinations](hyp:table),
[its entries depend only on earlier labels](hyp:hcausal), [the propensity error
allowance is nonnegative](hyp:ha), and [all table propensity coordinates
approximate the model's fixed-label propensities within that allowance](hyp:herr).
Assume [the readout error allowance is nonnegative](hyp:hc), [the norm bound is
nonnegative](hyp:hB), [the sampling tolerance is nonnegative](hyp:he), [all simulated
observations satisfy the norm bound](hyp:hbound), [all readouts satisfy the norm
bound](hyp:hvbound), [each fixed-label observation is within the readout allowance
of its coded readout](hyp:hread), and [twice the sum of categorical noise dimensions
over nodes and strata times the propensity allowance is at most the sampling
tolerance](hyp:hevent). Then [the table's ambiguity event is measurable and has
probability at most the tolerance, and, for any positive sample size, empirical
errors at most that tolerance for this event and every causal-table type subset
imply a Wasserstein distance of order one from the observational law to the
empirical simulation law of at most twice the readout allowance plus eight times
the norm bound times the tolerance](goal). -/
lemma ncmCausalTable_sampling_transport {counts : Fin b → ℕ}
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
    (v : CategoricalStratum kind → Fin s → Joint kind) (c B e : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hbound : ∀ z, ‖ncmEval R z‖ ≤ B) (hvbound : ∀ l j, ‖v l j‖ ≤ B)
    (hread : ∀ z l,
      dist (fixedLabelObservation R.canonical.toEuclideanSCM (categoricalStratumAssignment l)
        (jointNonGumbel (ncmSimulationExogenous R z)))
        (v l (code (jointNonGumbel (ncmSimulationExogenous R z)))) ≤ c)
    (hevent : 2 * (∑ i, ∑ _l : CategoricalStratum kind,
      (noiseDim (kind i) : ℝ)) * a ≤ e) :
    let bad := ncmCausalTableAmbiguity R code table a
    MeasurableSet bad ∧
      (simulationInputLaw kind counts).real bad ≤ e ∧
      ∀ (m : ℕ) (_hm : 0 < m) (draws : Fin m → SimulationInput kind counts),
        |(simulationInputLaw kind counts).real bad - (m : ℝ)⁻¹ *
          ∑ i, bad.indicator (fun _ => (1 : ℝ)) (draws i)| ≤ e →
        (∀ t : Set (Fin s × CategoricalStratum kind),
          |(simulationInputLaw kind counts).real (ncmCausalTableType R code table ⁻¹' t) -
            (m : ℝ)⁻¹ * ∑ i,
              if ncmCausalTableType R code table (draws i) ∈ t then (1 : ℝ) else 0| ≤ e) →
        wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (empiricalMeasure (fun i => ncmEval R (draws i))) ≤
            ENNReal.ofReal (2 * c + 8 * B * e) := by
  let bad := ncmCausalTableAmbiguity R code table a
  have hb := ncmCausalTableAmbiguity_measurable R code hcode table a
  have hp := ncmCausalTableAmbiguity_probability_le R code hcode table a ha
  have herr' := ncmCausalTableReadout_error_le R code hcode table
    hcausal a ha herr v c B hbound hvbound hread
  let := simulationInputLaw_probability kind counts
  have hprob : (simulationInputLaw kind counts).real bad ≤ e := by
    apply le_trans (ENNReal.toReal_mono (by simp) (hp.trans
      (ENNReal.ofReal_le_ofReal hevent)))
    exact le_of_eq (ENNReal.toReal_ofReal he)
  refine ⟨hb, hprob, ?_⟩
  intro m hm draws hamb hsub
  rw [← ncmEval_law R]
  have htransport := simulation_finite_type_empirical_wasserstein_le
    (simulationInputLaw kind counts) hm (ncmEval R) (by fun_prop)
    (ncmCausalTableType R code table) (by fun_prop) draws
    (fun t => v t.2 t.1) (Metric.closedBall (0 : Joint kind) B)
    (isCompact_closedBall _ _)
    (fun z => by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound z)
    (fun t => by simpa only [Metric.mem_closedBall, dist_zero_right] using hvbound t.2 t.1)
    bad hb c (2 * B) e hc (by positivity) he
    (fun i j => (dist_le_norm_add_norm _ _).trans
      (by have hi := hvbound i.2 i.1; have hj := hvbound j.2 j.1; linarith))
    herr' hprob hamb hsub
  convert htransport using 1
  congr 1
  ring


-- @node: ncm_causalTable_sampling_transport
/-- Suppose [the latent grid code is measurable](hyp:hcode), [a table assigns
categorical probabilities to node, label, and grid-index combinations](hyp:table),
[its entries depend only on earlier labels](hyp:hcausal), [the propensity error
allowance is nonnegative](hyp:ha), and [all table propensity coordinates approximate
the model's fixed-label propensities within that allowance](hyp:herr). Assume
[the readout error allowance is nonnegative](hyp:hc), [the norm bound is
nonnegative](hyp:hB), [the sampling tolerance is nonnegative](hyp:he), [all simulated
observations satisfy the norm bound](hyp:hbound), [all readouts satisfy the norm
bound](hyp:hvbound), [each fixed-label observation is within the readout allowance
of its coded readout](hyp:hread), and [twice the sum of categorical noise dimensions
over nodes and strata times the propensity allowance is at most the sampling
tolerance](hyp:hevent). Then [there exists a measurable exceptional event of
probability at most the tolerance such that, for any positive sample size,
empirical errors at most that tolerance for the event and every causal-table type
subset imply a Wasserstein distance of order one from the observational law to
the empirical simulation law of at most twice the readout allowance plus eight
times the norm bound times the tolerance](goal). -/
lemma ncm_causalTable_sampling_transport {counts : Fin b → ℕ}
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
    (v : CategoricalStratum kind → Fin s → Joint kind) (c B e : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hbound : ∀ z, ‖ncmEval R z‖ ≤ B) (hvbound : ∀ l j, ‖v l j‖ ≤ B)
    (hread : ∀ z l,
      dist (fixedLabelObservation R.canonical.toEuclideanSCM (categoricalStratumAssignment l)
        (jointNonGumbel (ncmSimulationExogenous R z)))
        (v l (code (jointNonGumbel (ncmSimulationExogenous R z)))) ≤ c)
    (hevent : 2 * (∑ i, ∑ _l : CategoricalStratum kind,
      (noiseDim (kind i) : ℝ)) * a ≤ e) :
    ∃ bad : Set (SimulationInput kind counts), MeasurableSet bad ∧
      (simulationInputLaw kind counts).real bad ≤ e ∧
      ∀ (m : ℕ) (_hm : 0 < m) (draws : Fin m → SimulationInput kind counts),
        |(simulationInputLaw kind counts).real bad - (m : ℝ)⁻¹ *
          ∑ i, bad.indicator (fun _ => (1 : ℝ)) (draws i)| ≤ e →
        (∀ t : Set (Fin s × CategoricalStratum kind),
          |(simulationInputLaw kind counts).real (ncmCausalTableType R code table ⁻¹' t) -
            (m : ℝ)⁻¹ * ∑ i,
              if ncmCausalTableType R code table (draws i) ∈ t then (1 : ℝ) else 0| ≤ e) →
        wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (empiricalMeasure (fun i => ncmEval R (draws i))) ≤
            ENNReal.ofReal (2 * c + 8 * B * e) := by
  obtain ⟨hb, hp, htransport⟩ := ncmCausalTable_sampling_transport R code hcode table
    hcausal a ha herr v c B e hc hB he hbound hvbound hread hevent
  exact ⟨ncmCausalTableAmbiguity R code table a, hb, hp, htransport⟩

-- @node: causalTableEvaluation_host_independent
/-- For [a fixed table of categorical probabilities indexed by node, label
stratum, and grid index](hyp:table), [evaluating the table at the same grid index
and exogenous input gives the same labels under any two canonical host models
with the same graph, incidence structure, and dimensions](goal). -/
lemma causalTableEvaluation_host_independent
    (M M' : CanonicalSCM kind dims dag G C) {s : ℕ}
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (a : Fin s) (u : Exogenous kind dims) :
    causalTableEvaluation M table a u = causalTableEvaluation M' table a u := by
  rfl

-- @node: categoricalNoise_ncmSimulationExogenous
/-- [The categorical noise at each node in the simulated exogenous input is
exactly the categorical noise supplied at that node in the simulation input](goal). -/
lemma categoricalNoise_ncmSimulationExogenous {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    (z : SimulationInput kind counts) (i : Fin n) :
    categoricalNoise i (ncmSimulationExogenous R z) = z.2 i := by
  rfl

-- @node: ncmCausalTableType_reference
/-- For [a fixed table of categorical probabilities indexed by node, label
stratum, and grid index](hyp:table), [a model's causal-table type equals its own
latent grid index paired with the labels obtained by evaluating the table under
a reference model at that index and the reference model's exogenous output on
the same simulation input](goal). -/
lemma ncmCausalTableType_reference {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R R0 : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (z : SimulationInput kind counts) :
    ncmCausalTableType R code table z =
      (code (jointNonGumbel (ncmSimulationExogenous R z)),
        causalTableEvaluation R0.canonical table
          (code (jointNonGumbel (ncmSimulationExogenous R z)))
          (ncmSimulationExogenous R0 z)) := by
  unfold ncmCausalTableType
  apply Prod.ext
  · rfl
  · change causalTableEvaluation R.canonical table _ _ = _
    rw [causalTableEvaluation_host_independent R.canonical R0.canonical]
    apply causalTableEvaluation_eq_of_categoricalNoise
    intro i
    rw [categoricalNoise_ncmSimulationExogenous, categoricalNoise_ncmSimulationExogenous]

-- @node: ncmCausalTableType_patterns_encard_le
/-- For [a fixed table of categorical probabilities indexed by node, label
stratum, and grid index](hyp:table), [the number of distinct causal-table type
patterns produced by a family of model representations on common simulation
inputs is at most the number of distinct latent grid-index patterns produced
by that family](goal). -/
lemma ncmCausalTableType_patterns_encard_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)}
    {A J : Type*} (repr : A → NCMIn kind dims dag G C counts F0 F1 bound)
    (R0 : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k)
    (draws : J → SimulationInput kind counts) :
    (Set.range (fun a j => ncmCausalTableType (repr a) code table (draws j))).encard ≤
      (Set.range (fun a j =>
        code (jointNonGumbel (ncmSimulationExogenous (repr a) (draws j))))).encard := by
  let read : (J → Fin s) → J → Fin s × CategoricalStratum kind := fun p j =>
    (p j, causalTableEvaluation R0.canonical table (p j)
      (ncmSimulationExogenous R0 (draws j)))
  have hsub : Set.range (fun a j => ncmCausalTableType (repr a) code table (draws j)) ⊆
      read '' Set.range (fun a j =>
        code (jointNonGumbel (ncmSimulationExogenous (repr a) (draws j)))) := by
    rintro _ ⟨a, rfl⟩
    refine ⟨_, ⟨a, rfl⟩, ?_⟩
    funext j
    exact (ncmCausalTableType_reference (repr a) R0 code table (draws j)).symm
  exact (Set.encard_mono hsub).trans (Set.encard_image_le _ _)

end
end Papers.TbsNeuralCausalPi
