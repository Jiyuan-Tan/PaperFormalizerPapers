module

public import Papers.TbsNeuralCausalPi.Helpers.RoundedCategoricalTables
public import Papers.TbsNeuralCausalPi.Helpers.NetworkMeasurability
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalLatentIndependence
public import Papers.TbsNeuralCausalPi.Helpers.FiniteTableTransport
/-! # Ambiguity control for the prescribed neural simulation law

The generated non-Gumbel vector is a measurable function of the generator
inputs. Its independence from each intrinsic categorical noise vector follows
from the simulation product law, without an extra model assumption.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

-- @node: NeuralGeneratorRealizable.measurable
/-- If [a generator can be represented by the permitted neural networks](hyp:hg),
then [the generator is measurable](goal). -/
@[fun_prop] lemma NeuralGeneratorRealizable.measurable {N d : ℕ}
    {g : ((Fin N → ℝ) × (Fin N → ℝ)) → L1Vec d}
    (hg : NeuralGeneratorRealizable g) : Measurable g := by
  first | fun_prop | skip
  rcases hg with ⟨W, L, q, hq⟩ | ⟨dC, W1, L1, W2, L2, tau, q, hq⟩
  · have he : g = fun z => q.eval (WithLp.toLp 1 (Fin.addCases z.1 z.2)) := funext hq
    rw [he]
    apply q.eval_measurable.comp
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    intro k
    refine Fin.addCases ?_ ?_ k <;> intro i
    · simpa only [Fin.addCases_left, Function.comp_def] using
        ((measurable_pi_apply i).comp measurable_fst)
    · simpa only [Fin.addCases_right, Function.comp_def] using
        ((measurable_pi_apply i).comp measurable_snd)
  · rcases hq with rfl | ⟨K, rfl⟩
    · fun_prop
    · change Measurable (coordinateClamp (-(K : ℝ)) K ∘ q.eval)
      fun_prop

-- @node: NCMIn.generator_measurable
/-- [Every latent-block generator of a neural causal model is measurable](goal). -/
@[fun_prop] lemma NCMIn.generator_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound) (j : Fin b) :
    Measurable (R.generator j) := by
  first | fun_prop | exact (R.generatorNetworks j).measurable

-- @node: ncmGeneratedBlocks
/-- For [a neural causal model](hyp:R) and [a collection of paired generator inputs](hyp:z),
the [generated latent blocks](goal) are obtained by applying each block's generator
to its own input pair. -/
def ncmGeneratedBlocks {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    (z : ∀ j, (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) : ∀ j, L1Vec (dims j) :=
  fun j => R.generator j (z j)

-- @node: ncmGeneratedBlocks_measurable
/-- [The joint map from generator inputs to all generated latent blocks is measurable](goal). -/
@[fun_prop] lemma ncmGeneratedBlocks_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound) :
    Measurable (ncmGeneratedBlocks R) := by
  first | fun_prop | skip
  unfold ncmGeneratedBlocks
  fun_prop

-- @node: simulationInputLaw_probability
/-- [The prescribed joint simulation-input law is a probability measure](goal)
for any node types and generator input counts. -/
lemma simulationInputLaw_probability (kind : Fin n → NodeKind) (counts : Fin b → ℕ) :
    IsProbabilityMeasure (simulationInputLaw kind counts) := by
  letI : ∀ j, IsProbabilityMeasure (generatorInputLaw (counts j)) :=
    fun j => generatorInputLaw_probability (counts j)
  letI : ∀ i, IsProbabilityMeasure ((gumbelInputs (noiseDim (kind i))).map
      (WithLp.toLp 1)) := fun i => by
    letI := gumbelInputs_probability (noiseDim (kind i))
    exact Measure.isProbabilityMeasure_map scm_toLp_measurable.aemeasurable
  unfold simulationInputLaw
  infer_instance

-- @node: simulationInput_categorical_law
/-- Under the joint simulation-input law, [the intrinsic noise vector at each node
has the product Gumbel distribution of the dimension prescribed by its node type](goal). -/
lemma simulationInput_categorical_law (kind : Fin n → NodeKind) (counts : Fin b → ℕ)
    (i : Fin n) :
    (simulationInputLaw kind counts).map
      (fun z => (z.2 i).ofLp) = gumbelInputs (noiseDim (kind i)) := by
  letI : ∀ j, IsProbabilityMeasure (generatorInputLaw (counts j)) :=
    fun j => generatorInputLaw_probability (counts j)
  letI : ∀ i, IsProbabilityMeasure ((gumbelInputs (noiseDim (kind i))).map
      (WithLp.toLp 1)) := fun i => by
    letI := gumbelInputs_probability (noiseDim (kind i))
    exact Measure.isProbabilityMeasure_map scm_toLp_measurable.aemeasurable
  change ((Measure.pi (fun j => generatorInputLaw (counts j))).prod
    (Measure.pi (fun i => (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1)))).map
      ((fun z => (z i).ofLp) ∘ Prod.snd) = _
  rw [← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  rw [show (fun z : ∀ i, L1Vec (noiseDim (kind i)) => (z i).ofLp) =
      (fun x : L1Vec (noiseDim (kind i)) => x.ofLp) ∘
        (fun z : ∀ j, L1Vec (noiseDim (kind j)) => z i) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_eval _ i).map_eq,
    Measure.map_map (by fun_prop) scm_toLp_measurable]
  simp only [Function.comp_def, WithLp.ofLp_toLp]
  convert (Measure.map_id (μ := gumbelInputs (noiseDim (kind i)))) using 1
  congr 1

-- @node: ncmGeneratedBlocks_indep_categorical
/-- Under the prescribed simulation-input law, [the collection of generated latent
blocks is independent of the intrinsic categorical noise vector at any chosen node](goal). -/
lemma ncmGeneratedBlocks_indep_categorical {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound) (i : Fin n) :
    IndepFun (fun z : SimulationInput kind counts => ncmGeneratedBlocks R z.1)
      (fun z => (z.2 i).ofLp) (simulationInputLaw kind counts) := by
  letI : ∀ j, IsProbabilityMeasure (generatorInputLaw (counts j)) :=
    fun j => generatorInputLaw_probability (counts j)
  letI : ∀ i, IsProbabilityMeasure ((gumbelInputs (noiseDim (kind i))).map
      (WithLp.toLp 1)) := fun i => by
    letI := gumbelInputs_probability (noiseDim (kind i))
    exact Measure.isProbabilityMeasure_map scm_toLp_measurable.aemeasurable
  exact indepFun_prod (ncmGeneratedBlocks_measurable R)
    (by fun_prop : Measurable (fun z : ∀ i, L1Vec (noiseDim (kind i)) => (z i).ofLp))

-- @node: ncm_tableAmbiguity_probability_le
/-- For [category-weight functions of the generated latent blocks](hyp:q) that
are [measurable](hyp:hq), [nonnegative](hyp:hpos), and [sum to one for every
table position and latent input](hyp:hsum), and [a nonnegative ambiguity
tolerance a](hyp:ha), [the probability of categorical table ambiguity is at most
twice a times the sum of the category counts over all table positions](goal).

Positions may repeat a node and therefore share the same Gumbel coordinates. -/
lemma ncm_tableAmbiguity_probability_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {I : Type*} [Fintype I] (node : I → Fin n)
    (q : ∀ p, (∀ j, L1Vec (dims j)) → Fin (noiseDim (kind (node p))) → ℝ)
    (hq : ∀ p, Measurable (q p)) (hpos : ∀ p x j, 0 ≤ q p x j)
    (hsum : ∀ p x, ∑ j, q p x j = 1) (a : ℝ) (ha : 0 ≤ a) :
    (simulationInputLaw kind counts) {z | CategoricalTableAmbiguity
      (fun p => noiseDim (kind (node p))) (fun z => ncmGeneratedBlocks R z.1)
      (fun p z => (z.2 (node p)).ofLp) q a z} ≤
        ENNReal.ofReal (2 * (∑ p, (noiseDim (kind (node p)) : ℝ)) * a) := by
  letI := simulationInputLaw_probability kind counts
  exact categoricalTableAmbiguity_probability_le _ _ _ _ q
    (by fun_prop) (by intro p; fun_prop)
    (fun p => ncmGeneratedBlocks_indep_categorical R (node p))
    (fun p => simulationInput_categorical_law kind counts (node p)) hq hpos hsum a ha

-- @node: ncm_tableAmbiguity_expectation_le
/-- For [category-weight functions of the generated latent blocks](hyp:q) that
are [measurable](hyp:hq), [nonnegative](hyp:hpos), and [sum to one at every
table position and latent input](hyp:hsum), with [nonnegative tolerance a](hyp:ha),
[the expected ambiguity indicator under the simulation law is at most twice a
times the sum of the category counts over all table positions](goal). -/
lemma ncm_tableAmbiguity_expectation_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {I : Type*} [Fintype I] (node : I → Fin n)
    (q : ∀ p, (∀ j, L1Vec (dims j)) → Fin (noiseDim (kind (node p))) → ℝ)
    (hq : ∀ p, Measurable (q p)) (hpos : ∀ p x j, 0 ≤ q p x j)
    (hsum : ∀ p x, ∑ j, q p x j = 1) (a : ℝ) (ha : 0 ≤ a) :
    (∫ z, {z | CategoricalTableAmbiguity (fun p => noiseDim (kind (node p)))
      (fun z => ncmGeneratedBlocks R z.1) (fun p z => (z.2 (node p)).ofLp) q a z}.indicator
        (fun _ => (1 : ℝ)) z ∂simulationInputLaw kind counts) ≤
          2 * (∑ p, (noiseDim (kind (node p)) : ℝ)) * a := by
  letI := simulationInputLaw_probability kind counts
  exact categoricalTableAmbiguity_expectation_le _ _ _ _ q
    (by fun_prop) (by intro p; fun_prop)
    (fun p => ncmGeneratedBlocks_indep_categorical R (node p))
    (fun p => simulationInput_categorical_law kind counts (node p)) hq hpos hsum a ha

-- @node: ncm_tableAmbiguity_draw_probability_le
/-- If [a simulation draw is measurable](hyp:hdraw) and [has the prescribed
simulation-input law under the underlying measure](hyp:hlaw), then for
[category-weight functions of the generated blocks](hyp:q) that are
[measurable](hyp:hq), [nonnegative](hyp:hpos), and [sum to one at every table
position and latent input](hyp:hsum), with [nonnegative tolerance a](hyp:ha),
[the draw's ambiguity event has measure at most twice a times the sum of the
category counts over all table positions](goal). -/
lemma ncm_tableAmbiguity_draw_probability_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (draw : Omega → SimulationInput kind counts) (hdraw : Measurable draw)
    (hlaw : mu.map draw = simulationInputLaw kind counts)
    {I : Type*} [Fintype I] (node : I → Fin n)
    (q : ∀ p, (∀ j, L1Vec (dims j)) → Fin (noiseDim (kind (node p))) → ℝ)
    (hq : ∀ p, Measurable (q p)) (hpos : ∀ p x j, 0 ≤ q p x j)
    (hsum : ∀ p x, ∑ j, q p x j = 1) (a : ℝ) (ha : 0 ≤ a) :
    mu {w | CategoricalTableAmbiguity (fun p => noiseDim (kind (node p)))
      (fun w => ncmGeneratedBlocks R (draw w).1)
      (fun p w => ((draw w).2 (node p)).ofLp) q a w} ≤
        ENNReal.ofReal (2 * (∑ p, (noiseDim (kind (node p)) : ℝ)) * a) := by
  have h := ncm_tableAmbiguity_probability_le R node q hq hpos hsum a ha
  rw [← hlaw, Measure.map_apply hdraw
    (measurableSet_categoricalTableAmbiguity _ _ _ q (by fun_prop)
      (by intro p; fun_prop) hq a)] at h
  exact h

-- @node: canonical_latentLaw_eq_grouped_noise
/-- [The canonical model's exogenous law is obtained by independently drawing
its latent blocks and nodewise product Gumbel noise vectors, then assembling
their coordinates into a single exogenous vector](goal). -/
lemma canonical_latentLaw_eq_grouped_noise (M : CanonicalSCM kind dims dag G C) :
    M.latentLaw =
      ((Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j))))).prod
        (Measure.pi (fun i => (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1)))).map
          (fun z => WithLp.toLp 1 (fun c => match c with
            | .inl ⟨j,k⟩ => (z.1 j).ofLp k
            | .inr ⟨i,k⟩ => (z.2 i).ofLp k)) := by
  letI := gumbelLaw_probability
  let B := Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j))))
  let N := Measure.pi (fun _ : Σ i, Fin (noiseDim (kind i)) => gumbelLaw)
  let group := fun g : (Σ i, Fin (noiseDim (kind i))) → ℝ =>
    fun i => WithLp.toLp 1 (fun k => g ⟨i,k⟩)
  let encode : (∀ j, L1Vec (dims j)) × (∀ i, L1Vec (noiseDim (kind i))) →
      Exogenous kind dims := fun z =>
    WithLp.toLp 1 (fun c => match c with
      | .inl ⟨j,k⟩ => (z.1 j).ofLp k
      | .inr ⟨i,k⟩ => (z.2 i).ofLp k)
  have hg : Measurable group := by fun_prop
  have he : Measurable encode := by
    dsimp only [encode]
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro (⟨j,k⟩ | ⟨i,k⟩) <;> fun_prop
  have hprod := Measure.map_prod_map B N measurable_id hg
  rw [Measure.map_id, canonical_gumbel_family_law] at hprod
  calc
    M.latentLaw = ((B.prod N).map (Prod.map id group)).map encode := by
      rw [Measure.map_map he (measurable_id.prodMap hg)]
      change (B.prod N).map _ = _
      congr 1
      funext z
      apply WithLp.ofLp_injective
      funext c
      rcases c with ⟨j,k⟩ | ⟨i,k⟩ <;> rfl
    _ = _ := congrArg (fun nu => nu.map encode) hprod.symm

-- @node: ncmGeneratedBlocks_law
/-- [Applying the block generators to independent inputs with their prescribed
laws gives exactly the product of the canonical model's latent-block laws](goal). -/
lemma ncmGeneratedBlocks_law {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound) :
    (Measure.pi (fun j => generatorInputLaw (counts j))).map (ncmGeneratedBlocks R) =
      Measure.pi (fun j => (R.canonical.blockLaw j : Measure (L1Vec (dims j)))) := by
  letI : ∀ j, IsProbabilityMeasure (generatorInputLaw (counts j)) :=
    fun j => generatorInputLaw_probability (counts j)
  letI : ∀ j, IsProbabilityMeasure ((generatorInputLaw (counts j)).map (R.generator j)) :=
    fun j => Measure.isProbabilityMeasure_map (R.generator_measurable j).aemeasurable
  change (Measure.pi _).map (fun z j => R.generator j (z j)) = _
  rw [Measure.pi_map_pi (fun j => (R.generator_measurable j).aemeasurable)]
  simp_rw [← R.blockLaw_eq]

-- @node: ncmSimulationExogenous
/-- For [a neural causal model](hyp:R) and [a joint simulation input](hyp:z),
the [simulated exogenous vector](goal) combines [the generated latent-block
coordinates](step:1) with [the input's intrinsic categorical noise coordinates](step:2). -/
def ncmSimulationExogenous {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    (z : SimulationInput kind counts) : Exogenous kind dims :=
  WithLp.toLp 1 (fun c => match c with
    | .inl ⟨j,k⟩ => (R.generator j (z.1 j)).ofLp k
    | .inr ⟨i,k⟩ => (z.2 i).ofLp k)

-- @node: ncmSimulationExogenous_measurable
/-- [The map assembling the model's exogenous vector from a joint simulation
input is measurable](goal). -/
@[fun_prop] lemma ncmSimulationExogenous_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound) :
    Measurable (ncmSimulationExogenous R) := by
  first | fun_prop | skip
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro (⟨j,k⟩ | ⟨i,k⟩) <;> fun_prop [ncmSimulationExogenous]

-- @node: ncmSimulationExogenous_law
/-- [Assembling exogenous vectors from the prescribed simulation-input law
produces exactly the canonical model's exogenous law, including all intrinsic
categorical noise coordinates](goal). -/
lemma ncmSimulationExogenous_law {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound) :
    (simulationInputLaw kind counts).map (ncmSimulationExogenous R) =
      R.canonical.latentLaw := by
  letI : ∀ j, IsProbabilityMeasure (generatorInputLaw (counts j)) :=
    fun j => generatorInputLaw_probability (counts j)
  letI : ∀ i, IsProbabilityMeasure ((gumbelInputs (noiseDim (kind i))).map
      (WithLp.toLp 1)) := fun i => by
    letI := gumbelInputs_probability (noiseDim (kind i))
    exact Measure.isProbabilityMeasure_map scm_toLp_measurable.aemeasurable
  let encode : (∀ j, L1Vec (dims j)) × (∀ i, L1Vec (noiseDim (kind i))) →
      Exogenous kind dims := fun z =>
    WithLp.toLp 1 (fun c => match c with
      | .inl ⟨j,k⟩ => (z.1 j).ofLp k
      | .inr ⟨i,k⟩ => (z.2 i).ofLp k)
  have he : Measurable encode := by
    dsimp only [encode]
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro (⟨j,k⟩ | ⟨i,k⟩) <;> fun_prop
  rw [canonical_latentLaw_eq_grouped_noise]
  have hprod := Measure.map_prod_map
    (Measure.pi (fun j => generatorInputLaw (counts j)))
    (Measure.pi (fun i => (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1)))
    (ncmGeneratedBlocks_measurable R) measurable_id
  rw [ncmGeneratedBlocks_law, Measure.map_id] at hprod
  change ((simulationInputLaw kind counts).map (encode ∘ Prod.map (ncmGeneratedBlocks R) id)) = _
  rw [← Measure.map_map he (by fun_prop), simulationInputLaw, ← hprod]

-- @node: ncmIntervenedEval_measurable
/-- [The model's simulated outcome vector under any fixed intervention is
a measurable function of the joint simulation input](goal). -/
@[fun_prop] lemma ncmIntervenedEval_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    (t : LawIntervention kind) : Measurable (ncmIntervenedEval R t) := by
  first | fun_prop | skip
  exact (evalSteps_measurable R.canonical.toEuclideanSCM t.val (n*n+n)).comp
    (ncmSimulationExogenous_measurable R)

-- @node: ncmIntervenedEval_law
/-- [Evaluating the model under a fixed intervention using the prescribed
simulation-input law produces exactly its canonical interventional distribution](goal). -/
lemma ncmIntervenedEval_law {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    (t : LawIntervention kind) :
    (simulationInputLaw kind counts).map (ncmIntervenedEval R t) =
      interventionalLaw R.canonical.toEuclideanSCM t := by
  change (simulationInputLaw kind counts).map
    ((intervenedEval R.canonical.toEuclideanSCM t.val) ∘ ncmSimulationExogenous R) = _
  have hm : Measurable (intervenedEval R.canonical.toEuclideanSCM t.val) := by
    first | fun_prop | exact evalSteps_measurable R.canonical.toEuclideanSCM t.val (n*n+n)
  rw [← Measure.map_map hm (ncmSimulationExogenous_measurable R), ncmSimulationExogenous_law]
  rfl

-- @node: ncmEval_measurable
/-- [The model's simulated observational outcome vector is a measurable
function of the joint simulation input](goal). -/
@[fun_prop] lemma ncmEval_measurable {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound) :
    Measurable (ncmEval R) := by
  first | fun_prop | exact ncmIntervenedEval_measurable R (noIntervention kind)

-- @node: ncmEval_law
/-- [Evaluating the model without intervention under the prescribed
simulation-input law produces exactly its canonical observational distribution](goal). -/
lemma ncmEval_law {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound) :
    (simulationInputLaw kind counts).map (ncmEval R) =
      observationalLaw R.canonical.toEuclideanSCM :=
  ncmIntervenedEval_law R (noIntervention kind)

-- @node: ncmEval_draw_law
/-- If [a simulation draw is measurable](hyp:hdraw) and [has the prescribed
simulation-input law under the underlying measure](hyp:hlaw), then
[the model's output on that draw has its canonical observational distribution](goal). -/
lemma ncmEval_draw_law {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (draw : Omega → SimulationInput kind counts) (hdraw : Measurable draw)
    (hlaw : mu.map draw = simulationInputLaw kind counts) :
    mu.map (fun w => ncmEval R (draw w)) = observationalLaw R.canonical.toEuclideanSCM := by
  have h := ncmEval_law R
  rw [← hlaw, Measure.map_map (ncmEval_measurable R) hdraw] at h
  exact h

-- @node: ncmEval_draws_iid
/-- If [the simulation draws are mutually independent under the underlying
measure](hyp:hind), [each draw is measurable](hyp:hdraws), and [each has the
prescribed simulation-input law](hyp:hlaw), then [their model output vectors
are mutually independent, each output is measurable, and every output has
the canonical observational distribution](goal). -/
lemma ncmEval_draws_iid {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {Omega J : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (draws : J → Omega → SimulationInput kind counts)
    (hind : iIndepFun draws mu) (hdraws : ∀ j, Measurable (draws j))
    (hlaw : ∀ j, mu.map (draws j) = simulationInputLaw kind counts) :
    iIndepFun (fun j w => ncmEval R (draws j w)) mu ∧
      ∀ j, Measurable (fun w => ncmEval R (draws j w)) ∧
        mu.map (fun w => ncmEval R (draws j w)) =
          observationalLaw R.canonical.toEuclideanSCM := by
  refine ⟨hind.comp (fun _ => ncmEval R) (fun _ => ncmEval_measurable R), ?_⟩
  intro j
  exact ⟨by fun_prop, ncmEval_draw_law R mu (draws j) (hdraws j) (hlaw j)⟩

-- @node: ncmEval_table_empirical_wasserstein_le
/-- Suppose [the sample size m is positive](hyp:hm), [the finite table-type
assignment is measurable](hyp:htype), [the common outcome set is compact](hyp:hS),
[every simulated output belongs to that set](hyp:hfrange), and [every table
representative belongs to that set](hyp:hvrange). If [the exceptional input
set is measurable](hyp:hE), [the baseline approximation error c is nonnegative](hyp:hc),
[the representative diameter bound B is nonnegative](hyp:hB), [the probability
and frequency tolerance e is nonnegative](hyp:he), [all pairs of representatives
are at distance at most B](hyp:hdiam), [each output lies within c of its
representative, with an additional allowance B on the exceptional set](hyp:herr),
[the exceptional set has probability at most e](hyp:hprob), [its empirical
frequency differs from its probability by at most e](hyp:hamb), and [the
empirical frequency of every subset of table types differs from its probability
by at most e](hyp:hsub), then [the Wasserstein distance of order one between
the canonical observational law and the empirical output distribution is at
most twice c plus four times B times e](goal). -/
lemma ncmEval_table_empirical_wasserstein_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {k m : ℕ} (hm : 0 < m)
    (typeOf : SimulationInput kind counts → Fin k) (htype : Measurable typeOf)
    (draws : Fin m → SimulationInput kind counts)
    (v : Fin k → Joint kind) (S : Set (Joint kind)) (hS : IsCompact S)
    (hfrange : ∀ z, ncmEval R z ∈ S) (hvrange : ∀ i, v i ∈ S)
    (E : Set (SimulationInput kind counts)) (hE : MeasurableSet E) (c B e : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hdiam : ∀ i j, dist (v i) (v j) ≤ B)
    (herr : ∀ z, edist (ncmEval R z) (v (typeOf z)) ≤
      ENNReal.ofReal c + E.indicator (fun _ => ENNReal.ofReal B) z)
    (hprob : (simulationInputLaw kind counts).real E ≤ e)
    (hamb : |(simulationInputLaw kind counts).real E - (m : ℝ)⁻¹ *
      ∑ i, E.indicator (fun _ => (1 : ℝ)) (draws i)| ≤ e)
    (hsub : ∀ s : Finset (Fin k),
      |(simulationInputLaw kind counts).real (typeOf ⁻¹' (s : Set (Fin k))) -
        (m : ℝ)⁻¹ * ∑ i, if typeOf (draws i) ∈ s then (1 : ℝ) else 0| ≤ e) :
    wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (empiricalMeasure (fun i => ncmEval R (draws i))) ≤
        ENNReal.ofReal (2 * c + 4 * B * e) := by
  let := simulationInputLaw_probability kind counts
  rw [← ncmEval_law R]
  exact simulation_table_empirical_wasserstein_le (simulationInputLaw kind counts) hm
    (ncmEval R) (by fun_prop) typeOf htype draws v S hS hfrange hvrange E hE
    c B e hc hB he hdiam herr hprob hamb hsub

-- @node: ncmEval_sampling_failure_le_indicator_failure
/-- Suppose [the sample size m is positive](hyp:hm), [the common outcome set
is compact](hyp:hS), [the approximation allowance c is nonnegative](hyp:hc),
[the diameter allowance B is nonnegative](hyp:hB), and [the frequency tolerance
e is nonnegative](hyp:he). Assume that, for every admissible model, [the
table-type assignment is measurable](hyp:htype), [the exceptional input set
is measurable](hyp:hE), [all simulated outputs lie in the common outcome
set](hyp:hfrange), [all table representatives lie in that set](hyp:hvrange),
[pairs of representatives have distance at most B](hyp:hdiam), [each output
is within c of its assigned representative, with an additional allowance B
on the exceptional set](hyp:herr), and [that exceptional set has probability
at most e](hyp:hprob). Then [the measure of samples for which some admissible
model has observational-to-empirical Wasserstein distance greater than twice c
plus four times B times e is at most the measure of samples for which some
admissible model has an exceptional-set or table-type-subset frequency error
greater than e](goal).

This measure comparison does not require measurability of a supremum over models. -/
lemma ncmEval_sampling_failure_le_indicator_failure {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {k m : ℕ} (hm : 0 < m)
    (admissible : NCMIn kind dims dag G C counts F0 F1 → Prop)
    (typeOf : NCMIn kind dims dag G C counts F0 F1 → SimulationInput kind counts → Fin k)
    (v : NCMIn kind dims dag G C counts F0 F1 → Fin k → Joint kind)
    (E : NCMIn kind dims dag G C counts F0 F1 → Set (SimulationInput kind counts))
    (draws : Fin m → Omega → SimulationInput kind counts)
    (S : Set (Joint kind)) (hS : IsCompact S) (c B e : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (he : 0 ≤ e)
    (htype : ∀ R, admissible R → Measurable (typeOf R))
    (hE : ∀ R, admissible R → MeasurableSet (E R))
    (hfrange : ∀ R, admissible R → ∀ z, ncmEval R z ∈ S)
    (hvrange : ∀ R, admissible R → ∀ i, v R i ∈ S)
    (hdiam : ∀ R, admissible R → ∀ i j, dist (v R i) (v R j) ≤ B)
    (herr : ∀ R, admissible R → ∀ z, edist (ncmEval R z) (v R (typeOf R z)) ≤
      ENNReal.ofReal c + (E R).indicator (fun _ => ENNReal.ofReal B) z)
    (hprob : ∀ R, admissible R → (simulationInputLaw kind counts).real (E R) ≤ e) :
    mu {w | ∃ R, admissible R ∧
      ¬ wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (empiricalMeasure (fun i => ncmEval R (draws i w))) ≤
          ENNReal.ofReal (2 * c + 4 * B * e)} ≤
    mu {w | ∃ R, admissible R ∧
      (¬ |(simulationInputLaw kind counts).real (E R) - (m : ℝ)⁻¹ *
          ∑ i, (E R).indicator (fun _ => (1 : ℝ)) (draws i w)| ≤ e ∨
        ∃ s : Finset (Fin k),
          ¬ |(simulationInputLaw kind counts).real (typeOf R ⁻¹' (s : Set (Fin k))) -
            (m : ℝ)⁻¹ * ∑ i, if typeOf R (draws i w) ∈ s then (1 : ℝ) else 0| ≤ e)} := by
  classical
  apply measure_mono
  rintro w ⟨R, hR, hbad⟩
  refine ⟨R, hR, ?_⟩
  by_contra hgood
  push Not at hgood
  exact hbad (ncmEval_table_empirical_wasserstein_le R hm (typeOf R) (htype R hR)
    (fun i => draws i w) (v R) S hS (hfrange R hR) (hvrange R hR)
    (E R) (hE R hR) c B e hc hB he (hdiam R hR) (herr R hR)
    (hprob R hR) hgood.1 hgood.2)

end
end Papers.TbsNeuralCausalPi
