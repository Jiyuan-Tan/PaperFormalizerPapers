module
public import Papers.TbsNeuralCausalPi.Setup.Notation
public import Causalean.Graph.DAG
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Data.EReal.Basic
/-! # Euclidean structural causal models
The general model has one arbitrary joint latent law. The canonical model
instead stores block marginals and forms their product with standard Gumbels.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
/-- A [node kind](goal) specifies either a continuous vector dimension or a categorical variable's number of categories. -/
abbrev NodeKind := ℕ ⊕ ℕ -- @realizes n_i(continuous dimension or categorical cardinality in the two summands) -- @realizes d_i(continuous dimension or categorical cardinality in the two summands)

/-- The [number of observed real coordinates](goal) is [the vector dimension for a continuous node](step:1) and [one for a categorical node](step:2). -/
def valueDim : NodeKind → ℕ
  | .inl d => d
  | .inr _ => 1
/-- The [mechanism output dimension](goal) is [the vector dimension for a continuous node](step:1) and [the number of categories for a categorical node](step:2). -/
def outputDim : NodeKind → ℕ -- @realizes d_i^{\text{out}}(continuous dimension or categorical propensity length) -- @realizes d_{i,\text{out}}^{V}(continuous dimension or categorical propensity length)
  | .inl d => d
  | .inr n => n
/-- For [the assigned node kinds](hyp:kind), the [joint coordinate space](goal) contains all nodes' real coordinates, equipped with the sum norm and one coordinate per categorical node. -/
abbrev Joint {n : ℕ} (kind : Fin n → NodeKind) := -- @realizes V_i(joint finite observed coordinate carrier, categorical labels embedded as integers) -- @realizes \boldsymbol{V}(joint finite observed coordinate carrier, categorical labels embedded as integers) -- @realizes n_V(joint finite observed coordinate carrier, categorical labels embedded as integers) -- @realizes \hat{\boldsymbol{V}}(joint finite observed coordinate carrier, categorical labels embedded as integers) -- @realizes \hat{V}_i(joint finite observed coordinate carrier, categorical labels embedded as integers)
  WithLp 1 ((Σ i, Fin (valueDim (kind i))) → ℝ)
/-- For [the dimensions of the latent blocks](hyp:dims), the [latent coordinate space](goal) collects every block's real coordinates into a vector equipped with the sum norm. -/
abbrev Latent {b : ℕ} (dims : Fin b → ℕ) :=
  WithLp 1 ((Σ j, Fin (dims j)) → ℝ)
/-- The [intrinsic noise dimension](goal) is [zero for a continuous node](step:1) and [the number of categories for a categorical node](step:2). -/
def noiseDim : NodeKind → ℕ
  | .inl _ => 0
  | .inr k => k
/-- For [the node kinds](hyp:kind) and [latent block dimensions](hyp:dims), the [exogenous coordinate space](goal) combines the latent blocks with a separate noise coordinate for every category at every categorical node, using the sum norm. -/
abbrev Exogenous {n b : ℕ} (kind : Fin n → NodeKind) (dims : Fin b → ℕ) := -- @realizes \boldsymbol{U}(flattened product of non-Gumbel block and separate categorical noise coordinates) -- @realizes n_U(flattened product of non-Gumbel block and separate categorical noise coordinates) -- @realizes \hat{\boldsymbol{U}}(flattened product of non-Gumbel block and separate categorical noise coordinates)
  WithLp 1 ((Sum (Σ j, Fin (dims j)) (Σ i, Fin (noiseDim (kind i)))) → ℝ)
/-- For [the node kinds](hyp:kind) and [latent block dimensions](hyp:dims), the [measurable sets in the exogenous coordinate space](goal) are its Borel sets. -/
instance exogenousMeasurable {n b : ℕ} (kind : Fin n → NodeKind) (dims : Fin b → ℕ) :
    MeasurableSpace (Exogenous kind dims) := borel _
/-- For [the node kinds](hyp:kind), the [measurable sets in the joint observed coordinate space](goal) are its Borel sets. -/
instance jointMeasurable {n : ℕ} (kind : Fin n → NodeKind) :
    MeasurableSpace (Joint kind) := borel _
/-- On [a specified number of nodes](hyp:n), a [causal graph](goal) is a directed acyclic graph paired with an undirected simple graph on the same nodes. -/
abbrev CausalGraph (n : ℕ) := Causalean.Graph.DAG (Fin n) × SimpleGraph (Fin n)
/-- Given [node kinds](hyp:kind), [latent block dimensions](hyp:dims), [a parent graph](hyp:dag), and [each node's designated latent blocks](hyp:inc), the [structural input space](goal) for [the selected node](hyp:i) collects exactly its parents' observed coordinates and its designated blocks' coordinates, with the sum norm. -/
abbrev StructuralInput {n b : ℕ} (kind : Fin n → NodeKind) (dims : Fin b → ℕ) -- @realizes \text{Pa}(exact parent and designated-block coordinate product) -- @realizes d_i^{\text{in}}(exact parent and designated-block coordinate product) -- @realizes d_{i,\text{in}}^{V}(exact parent and designated-block coordinate product)
    (dag : Causalean.Graph.DAG (Fin n)) (inc : Fin n → Finset (Fin b)) (i : Fin n) :=
  WithLp 1 ((Sum (Σ p : {p // p ∈ dag.parents i}, Fin (valueDim (kind p)))
    (Σ j : {j // j ∈ inc i}, Fin (dims j))) → ℝ)

/-- The [standard Gumbel law](goal) is the distribution of the negative logarithm of an exponential random variable with rate one. -/
def gumbelLaw : Measure ℝ :=
  (ProbabilityTheory.expMeasure 1).map (fun x => -Real.log x)
/-- The [extended logarithm](goal) of [a real number](hyp:x) is negative infinity at zero and the real logarithm otherwise. -/
def extendedLog (x : ℝ) : EReal := if x = 0 then ⊥ else (Real.log x : EReal)
/-- For [extended real scores on finitely many labels](hyp:score), the [first maximizing label](goal) is the smallest index whose score is at least every other score, or no label if none exists. -/
def firstArgmax {k : ℕ} (score : Fin k → EReal) : Option (Fin k) :=
  (List.finRange k).find? (fun j => ∀ l, score l ≤ score j)

/-- Given [label propensities](hyp:p) and [additive noise scores](hyp:g), the [first positive-propensity maximizer](goal) is the smallest label maximizing log propensity plus noise among labels with strictly positive propensity, or no label if none exists. -/
def firstPositiveArgmax {k : ℕ} (p : Fin k → ℝ) (g : Fin k → ℝ) : Option (Fin k) :=
  (List.finRange k).find? (fun j => 0 < p j ∧
    ∀ l, 0 < p l → Real.log (p l) + g l ≤ Real.log (p j) + g j)

-- @node: firstArgmax_eq_firstPositiveArgmax
/-- If [all label propensities are nonnegative](hyp:hp) and [their sum is positive](hyp:hsum), then [maximizing extended log propensity plus additive noise selects the same first label as maximizing ordinary log propensity plus noise over positive-propensity labels](goal). -/
lemma firstArgmax_eq_firstPositiveArgmax {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : 0 < ∑ j, p j) (g : Fin k → ℝ) :
    firstArgmax (fun j => extendedLog (p j) + (g j : EReal)) =
      firstPositiveArgmax p g := by
  have hex : ∃ l, 0 < p l := by
    by_contra h
    have hz : ∀ l, p l = 0 := by
      intro l
      exact le_antisymm (le_of_not_gt (fun hl => h ⟨l, hl⟩)) (hp l)
    simp only [hz, Finset.sum_const_zero] at hsum
    exact lt_irrefl 0 hsum
  have hscore (j : Fin k) (hj : 0 < p j) :
      extendedLog (p j) + (g j : EReal) = ((Real.log (p j) + g j : ℝ) : EReal) := by
    simp only [extendedLog, if_neg (ne_of_gt hj), EReal.coe_add]
  unfold firstArgmax firstPositiveArgmax
  congr 1
  funext j
  suffices h : (∀ l, extendedLog (p l) + (g l : EReal) ≤
      extendedLog (p j) + (g j : EReal)) ↔
      (0 < p j ∧ ∀ l, 0 < p l → Real.log (p l) + g l ≤ Real.log (p j) + g j) by
    simp only [h]
  constructor
  · intro hmax
    have hj : 0 < p j := by
      by_contra hj
      have hz : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
      obtain ⟨l, hl⟩ := hex
      have h := hmax l
      rw [hscore l hl] at h
      simp [extendedLog, hz] at h
    refine ⟨hj, ?_⟩
    intro l hl
    have h := hmax l
    rw [hscore l hl, hscore j hj] at h
    exact EReal.coe_le_coe_iff.mp h
  · rintro ⟨hj, hmax⟩ l
    by_cases hl : 0 < p l
    · rw [hscore l hl, hscore j hj]
      exact EReal.coe_le_coe_iff.mpr (hmax l hl)
    · have hz : p l = 0 := le_antisymm (le_of_not_gt hl) (hp l)
      simp [extendedLog, hz]

/-- The [structural unit cube](goal) consists of finite real coordinate vectors whose every coordinate lies between zero and one, inclusive. -/
def structuralCube {I : Type*} [Fintype I] : Set (WithLp 1 (I → ℝ)) :=
  {x | ∀ j, x.ofLp j ∈ Set.Icc (0 : ℝ) 1}

/-- For [optional common lower and upper coordinate bounds](hyp:bound), the [structural input domain](goal) is [the full coordinate space when bounds are absent](step:1), or [the set of vectors with every coordinate between the supplied bounds, inclusive](step:2).

Structural maps remain total on the ambient coordinate carrier. -/
def structuralInputDomain {I : Type*} [Fintype I]
    (bound : Option (ℝ × ℝ)) : Set (WithLp 1 (I → ℝ)) :=
  match bound with
  | none => Set.univ
  | some (lo, hi) => {x | ∀ j, x.ofLp j ∈ Set.Icc lo hi}

/-- For [a selected node](hyp:i) and [an exogenous coordinate vector](hyp:u), the [categorical noise vector](goal) extracts that node's intrinsic category noise coordinates, giving an empty vector for a continuous node. -/
def categoricalNoise {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (i : Fin n) (u : Exogenous kind dims) : L1Vec (noiseDim (kind i)) := -- @realizes G_{V_i}(intrinsic projection to the categorical noise vector) -- @realizes g_k^{V_i}(its coordinate projections)
  WithLp.toLp 1 (fun k => u.ofLp (.inr ⟨i,k⟩))
/-- Given [node kinds](hyp:kind), [latent block dimensions](hyp:dims), [a parent graph](hyp:dag), and [designated latent blocks](hyp:inc), the [admissible structural inputs](goal) for [a selected node](hyp:i) require each categorical parent's coordinate to be a valid one-based category label; continuous parent and latent coordinates are unrestricted. -/
def admissibleStructuralInputs {n b : ℕ} (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (inc : Fin n → Finset (Fin b)) (i : Fin n) :
    Set (StructuralInput kind dims dag inc i) :=
  {x | ∀ p : {p // p ∈ dag.parents i}, ∀ k, kind p.val = Sum.inr k →
    ∃ label : Fin k, ∀ j : Fin (valueDim (kind p.val)), -- @realizes \text{Pa}(categorical parent arguments are valid unchanged labels)
      x.ofLp (.inl ⟨p,j⟩) = (label.val + 1 : ℕ)}

/-- A node's [actual value space](goal) is [a real vector space with the sum norm for a continuous node](step:1), or [the finite set of category indices for a categorical node](step:2). -/
def ObservedValue : NodeKind → Type -- @realizes V_i(actual continuous vectors or finite categorical labels)
  | .inl d => L1Vec d
  | .inr k => Fin k
/-- For [a node kind](hyp:k), the [measurable structure on its actual values](goal) is [the usual Borel structure for continuous vectors](step:1) or [the discrete structure for finite category labels](step:2). -/
instance observedValueMeasurable (k : NodeKind) : MeasurableSpace (ObservedValue k) :=
  match k with
  | .inl d => (inferInstance : MeasurableSpace (L1Vec d))
  | .inr k => (inferInstance : MeasurableSpace (Fin k))

/-- A structural model has no mechanism inputs other than the declared parents
and designated members of its finite latent family. Categorical generation
noises, when present, must be members of that family and explicitly designated. -/
-- @node: def:eq-structure-eq
structure StructuralSCM {n : ℕ} (kind : Fin n → NodeKind)
    (J : Type*) [Fintype J] (dims : J → ℕ) where
  dag : Causalean.Graph.DAG (Fin n) -- @realizes \mathcal{G}_0(parent DAG)
  incidence : Fin n → Finset J -- @realizes \boldsymbol{U}_{V_i}(all and only designated latent blocks)
  f : ∀ i, WithLp 1 ((Sum
      (Σ p : {p // p ∈ dag.parents i}, Fin (valueDim (kind p)))
      (Σ j : {j // j ∈ incidence i}, Fin (dims j))) → ℝ) →
    ObservedValue (kind i) -- @realizes f_i(mechanisms depend only on parents and designated latent blocks) -- @realizes F(tuple of those mechanisms)
  structuralMeasurable : ∀ i, Measurable (f i)
  latentLaw : Measure (WithLp 1 ((Σ j, Fin (dims j)) → ℝ)) -- @realizes P(joint law of exactly the declared finite latent family) -- @realizes \boldsymbol{U}(joint coordinates of that family)
  probability : IsProbabilityMeasure latentLaw
  categoricalPositive : ∀ i k, kind i = Sum.inr k → 0 < k

/-- Evaluation carrier separating non-Gumbel blocks from each node's intrinsic
categorical noise. Its general structural-model realization below explicitly
designates the latter too. Existing quantitative proofs use this separation. -/
structure EuclideanSCM {n b : ℕ} (kind : Fin n → NodeKind) (dims : Fin b → ℕ) where -- @realizes \mathcal{M}(SCM tuple with a fixed joint latent probability law) -- @realizes \mathcal{M}^*(SCM tuple with a fixed joint latent probability law)
  dag : Causalean.Graph.DAG (Fin n) -- @realizes \mathcal{G}_0(parent DAG)
  incidence : Fin n → Finset (Fin b) -- @realizes \boldsymbol{U}_{V_i}(designated blocks)
  f : ∀ i, StructuralInput kind dims dag incidence i →
    L1Vec (noiseDim (kind i)) → ObservedValue (kind i) -- @realizes f_i(general structural maps into actual continuous or categorical value spaces) -- @realizes F(tuple of actual structural mechanisms)
  structuralMeasurable : ∀ i, Measurable (fun z :
    StructuralInput kind dims dag incidence i × L1Vec (noiseDim (kind i)) => f i z.1 z.2)
  latentLaw : Measure (Exogenous kind dims) -- @realizes P(joint latent law)
  probability : IsProbabilityMeasure latentLaw -- @realizes P(joint law has total mass one)
  categoricalPositive : ∀ i k, kind i = Sum.inr k → 0 < k -- @realizes n_i(category count)

/-- For [a structural causal model](hyp:M), [a selected node](hyp:i), and [optional common coordinate bounds](hyp:bound), the [node's input domain](goal) consists of admissible parent and latent inputs that also satisfy those bounds when present. -/
def EuclideanSCM.domain {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) (bound : Option (ℝ × ℝ) := none) :
    Set (StructuralInput kind dims M.dag M.incidence i) :=
  admissibleStructuralInputs kind dims M.dag M.incidence i ∩ structuralInputDomain bound

/-- For [a structural causal model](hyp:M) and [a selected node](hyp:i), the [structural input vector](goal) takes [its parents' coordinates](step:1) from [a joint observed vector](hyp:v) and [its designated latent block coordinates](step:2) from [an exogenous vector](hyp:u). -/
def structuralInput {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) (v : Joint kind) (u : Exogenous kind dims) :
    StructuralInput kind dims M.dag M.incidence i :=
  WithLp.toLp 1 (fun c => match c with
    | .inl ⟨p, j⟩ => v.ofLp ⟨p.val, j⟩
    | .inr ⟨k, j⟩ => u.ofLp (.inl ⟨k.val, j⟩))

-- @node: scm_toLp_measurable
/-- [Viewing a finite real coordinate function as a vector equipped with the sum norm is measurable](goal). -/
@[fun_prop] lemma scm_toLp_measurable {I : Type*} [Fintype I] :
    Measurable (WithLp.toLp 1 : (I → ℝ) → WithLp 1 (I → ℝ)) := by
  let : BorelSpace (WithLp 1 (I → ℝ)) := ⟨rfl⟩
  exact (PiLp.continuous_toLp 1 _).measurable

-- @node: scm_ofLp_measurable
/-- [Extracting the coordinate function from a finite real vector equipped with the sum norm is measurable](goal). -/
@[fun_prop] lemma scm_ofLp_measurable {I : Type*} [Fintype I] :
    Measurable (WithLp.ofLp : WithLp 1 (I → ℝ) → (I → ℝ)) := by
  let : BorelSpace (WithLp 1 (I → ℝ)) := ⟨rfl⟩
  exact (PiLp.continuous_ofLp 1 _).measurable

-- @node: structuralInput_measurable
/-- For [a structural causal model](hyp:M) and [a selected node](hyp:i), [extracting that node's parent and designated latent inputs from a joint observed and exogenous vector is measurable](goal). -/
@[fun_prop] lemma structuralInput_measurable {n b : ℕ}
    {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) :
    Measurable (fun z : Joint kind × Exogenous kind dims => structuralInput M i z.1 z.2) := by
  unfold structuralInput
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  intro c
  rcases c with ⟨p, j⟩ | ⟨k, j⟩ <;> fun_prop

-- @node: categoricalNoise_measurable
/-- For [a selected node](hyp:i), [extracting its intrinsic categorical noise vector from the exogenous coordinates is measurable](goal). -/
@[fun_prop] lemma categoricalNoise_measurable {n b : ℕ}
    {kind : Fin n → NodeKind} {dims : Fin b → ℕ} (i : Fin n) :
    Measurable (categoricalNoise (kind := kind) (dims := dims) i) := by
  unfold categoricalNoise
  let : BorelSpace (L1Vec (noiseDim (kind i))) := ⟨rfl⟩
  let : BorelSpace (Exogenous kind dims) := ⟨rfl⟩
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 1 _).comp
  apply continuous_pi
  intro k
  exact (continuous_apply (Sum.inr (⟨i, k⟩ : Σ i, Fin (noiseDim (kind i))) :
    Sum (Σ j, Fin (dims j)) (Σ i, Fin (noiseDim (kind i))))).comp
    (PiLp.continuous_ofLp 1 _)

/-- For [a structural causal model](hyp:M) and [a selected node](hyp:i), the [continuous output map](goal) returns [the structural mechanism's continuous value at zero intrinsic noise when the node is continuous](step:1), and [the zero vector when the node is categorical](step:2). -/
def EuclideanSCM.continuousMap {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) :
    StructuralInput kind dims M.dag M.incidence i → L1Vec (outputDim (kind i)) :=
  fun x => match h : kind i with
    | .inl d => WithLp.toLp 1 (fun j =>
        (cast (congrArg ObservedValue h) (M.f i x 0)).ofLp j)
    | .inr _ => 0

/-- For [a structural causal model](hyp:M), [a selected node](hyp:i), and [a category count](hyp:k) such that [the node is categorical with that many categories](hyp:h), the [categorical label](goal) is the mechanism's finite category index evaluated at [the parent and latent inputs](hyp:x) and [the category noise vector](hyp:g). -/
def EuclideanSCM.categoricalLabel {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) (k : ℕ) (h : kind i = Sum.inr k)
    (x : StructuralInput kind dims M.dag M.incidence i) (g : L1Vec k) : Fin k :=
  cast (congrArg ObservedValue h) (M.f i x
    (WithLp.toLp 1 (fun j => g.ofLp (Fin.cast (congrArg noiseDim h) j))))

/-- For [a structural causal model](hyp:M), a [family of mechanism weights](goal) assigns to each node a function from its parent and designated latent inputs to a real vector with its mechanism output dimension.

Propensity versions are parameters of the Gumbel specialization, not SCM data. -/
abbrev MechanismWeights {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) :=
  ∀ i, StructuralInput kind dims M.dag M.incidence i → L1Vec (outputDim (kind i))

/-- For [a structural causal model](hyp:M), [a selected node](hyp:i), [a joint observed vector](hyp:v), and [an exogenous vector](hyp:u), the [node's embedded value](goal) evaluates its mechanism on the extracted inputs and noise, returning [the continuous vector unchanged](step:1) or [the categorical index plus one as a single real coordinate](step:2). -/
def nodeValue {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) (v : Joint kind) (u : Exogenous kind dims) :
    L1Vec (valueDim (kind i)) :=
  match h : kind i with
  | .inl d => cast (congrArg ObservedValue h) (M.f i (structuralInput M i v u) (categoricalNoise i u))
  | .inr k => WithLp.toLp 1 (fun _ =>
      ((cast (congrArg ObservedValue h) (M.f i (structuralInput M i v u) (categoricalNoise i u))).val + 1 : ℕ))

-- @node: observedValueEmbedding
/-- For [a node kind](hyp:k), the [embedding of actual values into real coordinates](goal) [leaves continuous vectors unchanged](step:1) and [represents a categorical index by its index plus one in a single coordinate](step:2). -/
def observedValueEmbedding (k : NodeKind) : ObservedValue k → L1Vec (valueDim k) :=
  match k with
  | .inl _ => fun y => y
  | .inr _ => fun y => WithLp.toLp 1 (fun _ => (y.val + 1 : ℕ))

-- @node: observedValueEmbedding_measurable
/-- For [any node kind](hyp:k), [embedding its actual values into real observed coordinates is measurable](goal). -/
@[fun_prop] lemma observedValueEmbedding_measurable (k : NodeKind) :
    Measurable (observedValueEmbedding k) := by
  cases k with
  | inl d => exact measurable_id
  | inr k =>
    change Measurable (fun y : Fin k => WithLp.toLp 1 (fun _ : Fin 1 => ((y.val + 1 : ℕ) : ℝ)))
    exact measurable_of_countable _

-- @node: observedValueEmbedding_eq
/-- For [a node kind](hyp:k) and [an actual value of that kind](hyp:y), [the observed coordinate embedding equals the continuous vector itself for a continuous node, or the category index plus one in a single real coordinate for a categorical node](goal). -/
lemma observedValueEmbedding_eq (k : NodeKind) (y : ObservedValue k) :
    observedValueEmbedding k y =
      (show L1Vec (valueDim (id k)) from
        match h : id k with
        | .inl d => cast (congrArg ObservedValue h) y
        | .inr n => WithLp.toLp 1 (fun _ =>
            ((cast (congrArg ObservedValue h) y).val + 1 : ℕ))) := by
  cases k <;> rfl

-- @node: nodeValue_measurable
/-- For [a structural causal model](hyp:M) and [a selected node](hyp:i), [its embedded mechanism value is a measurable function of the joint observed and exogenous vectors](goal). -/
@[fun_prop] lemma nodeValue_measurable {n b : ℕ}
    {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) :
    Measurable (fun z : Joint kind × Exogenous kind dims => nodeValue M i z.1 z.2) := by
  have heq (z : Joint kind × Exogenous kind dims) :
      nodeValue M i z.1 z.2 = observedValueEmbedding (kind i)
        (M.f i (structuralInput M i z.1 z.2) (categoricalNoise i z.2)) := by
    exact (observedValueEmbedding_eq (kind i) _).symm
  simp_rw [heq]
  apply (observedValueEmbedding_measurable (kind i)).comp
  exact (M.structuralMeasurable i).comp
    ((structuralInput_measurable M i).prodMk
      ((categoricalNoise_measurable i).comp measurable_snd))

/-- For [the assigned node kinds](hyp:kind), an [intervention](goal) specifies at each node either no replacement or a replacement vector with that node's observed coordinate dimension. -/
abbrev Intervention {n : ℕ} (kind : Fin n → NodeKind) := -- @realizes \boldsymbol{T}(partial assignments to treatment nodes, with same value carrier as each node) -- @realizes \boldsymbol{t}(partial assignments to treatment nodes, with same value carrier as each node) -- @realizes \boldsymbol{t}_0(partial assignments to treatment nodes, with same value carrier as each node) -- @realizes n_t(partial assignments to treatment nodes, with same value carrier as each node)
  ∀ i, Option (L1Vec (valueDim (kind i)))

/-- For [the assigned node kinds](hyp:kind), [an intervention](hyp:t) is [admissible](goal) when every replacement [is unrestricted at a continuous node](step:1) and [equals a valid one-based category label in every coordinate at a categorical node](step:2). -/
def AdmissibleIntervention {n : ℕ} (kind : Fin n → NodeKind) (t : Intervention kind) : Prop :=
  ∀ i v, t i = some v →
    match h : kind i with
    | .inl _ => True
    | .inr k => ∃ label : Fin k, ∀ j, v.ofLp j = (label.val + 1 : ℕ)

/-- For [the assigned node kinds](hyp:kind), an [intervention suitable for defining an interventional law](goal) is an intervention whose categorical replacements are valid one-based category labels. -/
abbrev LawIntervention {n : ℕ} (kind : Fin n → NodeKind) :=
  {t : Intervention kind // AdmissibleIntervention kind t}
-- @node: noIntervention_admissible
/-- For [any assignment of node kinds](hyp:kind), [the intervention that replaces no node is admissible](goal). -/
lemma noIntervention_admissible {n : ℕ} (kind : Fin n → NodeKind) :
    AdmissibleIntervention kind (fun _ => none) := by
  intro i v hv
  cases hv
/-- For [the assigned node kinds](hyp:kind), the [null intervention](goal) leaves every node's structural mechanism in place and is admissible. -/
def noIntervention {n : ℕ} (kind : Fin n → NodeKind) : LawIntervention kind :=
  ⟨fun _ => none, noIntervention_admissible kind⟩

/-- For [a structural causal model](hyp:M), [an intervention](hyp:t), and [an exogenous realization](hyp:u), the [sequence of partial observed vectors](goal) [starts at zero](step:1) and [at each subsequent step updates the node with that topological rank, using its intervention value if present and its mechanism otherwise, while retaining all other coordinates](step:2). -/
def evalSteps {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (t : Intervention kind) (u : Exogenous kind dims) :
    ℕ → Joint kind
  | 0 => 0
  | r + 1 => WithLp.toLp 1 (fun ⟨i, j⟩ =>
      if M.dag.topoOrder i = r then
        ((t i).getD (nodeValue M i (evalSteps M t u r) u)).ofLp j
      else (evalSteps M t u r).ofLp ⟨i, j⟩)
-- @node: evalSteps_measurable
/-- For a structural causal model and a fixed intervention, [the partial observed vector after any fixed number of evaluation steps is a measurable function of the exogenous realization](goal). -/
@[fun_prop] lemma evalSteps_measurable {n b : ℕ}
    {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (t : Intervention kind) (r : ℕ) :
    Measurable (fun u => evalSteps M t u r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    simp only [evalSteps]
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro ⟨i, j⟩
    by_cases hi : M.dag.topoOrder i = r
    · simp only [hi, if_true]
      cases ht : t i with
      | none =>
        simp only [Option.getD_none]
        have hnode : Measurable (fun u => nodeValue M i (evalSteps M t u r) u) :=
          (nodeValue_measurable M i).comp (ih.prodMk measurable_id)
        exact (measurable_pi_apply j).comp (scm_ofLp_measurable.comp hnode)
      | some v => simp only [Option.getD_some]; exact measurable_const
    · simp only [hi, if_false]
      exact (measurable_pi_apply ⟨i, j⟩).comp (scm_ofLp_measurable.comp ih)

/-- For [a structural causal model](hyp:M), [an intervention](hyp:t), and [an exogenous realization](hyp:u), the [intervened observed vector](goal) is the partial evaluation after the square of the number of nodes plus the number of nodes steps. -/
def intervenedEval {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (t : Intervention kind) (u : Exogenous kind dims) : Joint kind :=
  evalSteps M t u (n * n + n)
-- @node: intervenedEval_aemeasurable
/-- For a structural causal model and an admissible intervention, [the intervened observed vector is an almost everywhere measurable function under the model's exogenous law](goal). -/
@[fun_prop] lemma intervenedEval_aemeasurable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (t : LawIntervention kind) :
    AEMeasurable (intervenedEval M t.val) M.latentLaw := by
  exact (evalSteps_measurable M t.val (n * n + n)).aemeasurable

-- @node: def:intervention
/-- For [a structural causal model](hyp:M) and [an admissible intervention](hyp:t), the [interventional distribution](goal) is the distribution of the intervened observed vector when exogenous realizations follow the model's latent law. -/
def interventionalLaw {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (t : LawIntervention kind) : Measure (Joint kind) :=
  M.latentLaw.map (intervenedEval M t.val)
/-- For [a structural causal model](hyp:M), the [observational distribution](goal) is its interventional distribution when every node retains its original mechanism. -/
def observationalLaw {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ} -- @realizes P^{\mathcal{M}}(observational push-forward law of the SCM)
    (M : EuclideanSCM kind dims) : Measure (Joint kind) :=
  interventionalLaw M (noIntervention kind)

/-- For [a structural causal model](hyp:M) and [an outcome node](hyp:Y) [with exactly one observed coordinate](hyp:hY), the [individual outcome contrast](goal) [extracts that scalar outcome](step:1) and [subtracts its value under the baseline intervention from its value under the comparison intervention](step:2), using [the comparison and baseline interventions](hyp:t,t₀) at [the same exogenous realization](hyp:u). -/
def outcomeContrast {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (Y : Fin n) (hY : valueDim (kind Y) = 1)
    (t t₀ : LawIntervention kind) (u : Exogenous kind dims) : ℝ :=
  let y := fun v : Joint kind => v.ofLp ⟨Y, Fin.cast hY.symm ⟨0, Nat.zero_lt_succ 0⟩⟩
  y (intervenedEval M t.val u) - y (intervenedEval M t₀.val u)

-- @node: def:definition-4
/-- For [a structural causal model](hyp:M) and [an outcome node](hyp:Y) [with exactly one observed coordinate](hyp:hY), given [comparison and baseline interventions](hyp:t,t₀) that [replace the same set of nodes](hyp:_sameTreatment) and [have an integrable scalar outcome contrast under the latent law](hyp:_integrable), the [average treatment effect](goal) is the expectation of the comparison outcome minus the baseline outcome under that law. -/
def ate {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (Y : Fin n) (hY : valueDim (kind Y) = 1)
    (t t₀ : LawIntervention kind)
    (_sameTreatment : ∀ i, (t.val i).isSome = (t₀.val i).isSome)
    (_integrable : Integrable (outcomeContrast M Y hY t t₀) M.latentLaw) : ℝ := -- @realizes \text{ATE}_{\mathcal{M}}(expectation of an integrable contrast of the same scalar outcome on one treatment set)
  ∫ u, outcomeContrast M Y hY t t₀ u ∂M.latentLaw

-- @node: def:definition-2
/-- For [an undirected graph](hyp:G) and [a set of nodes](hyp:C), [being a C2 component](goal) means that the set is a maximal clique: all distinct members are adjacent and no strictly larger set has that property. -/
structure IsC2Component {n : ℕ} (G : SimpleGraph (Fin n)) (C : Set (Fin n)) : Prop where -- @realizes C(maximal bidirected clique)
  maximalClique : Maximal G.IsClique C

/-- For [a latent block index](hyp:j) and [an exogenous realization](hyp:u), the [block projection](goal) extracts that block's real coordinates, excluding intrinsic categorical noise. -/
def blockProjection {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ} -- @realizes U_i(non-Gumbel latent block computed from the full exogenous vector) -- @realizes U_j(projection to a non-Gumbel block of the stated dimension) -- @realizes d_j^U(projection to a non-Gumbel block of the stated dimension)
    (j : Fin b) (u : Exogenous kind dims) : L1Vec (dims j) :=
  WithLp.toLp 1 (fun k => u.ofLp (.inl ⟨j,k⟩))
/-- For [a structural causal model](hyp:M) and [a latent block index](hyp:j), the [latent marginal distribution](goal) is the distribution of that block's coordinates under the model's exogenous law. -/
def latentMarginal {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (j : Fin b) : Measure (L1Vec (dims j)) :=
  M.latentLaw.map (blockProjection j)
/-- Given [the node kinds](hyp:kind) and [the original latent block dimensions](hyp:dims), the [dimension of a named latent block](goal) is [its original dimension for an original block](step:1) or [the node's intrinsic noise dimension for a node noise block](step:2). -/
def fullLatentDim {n b : ℕ} (kind : Fin n → NodeKind) (dims : Fin b → ℕ) : Fin b ⊕ Fin n → ℕ
  | .inl j => dims j
  | .inr i => noiseDim (kind i)
/-- For [a structural causal model](hyp:M), [a name identifying an original latent block or a node's noise block](hyp:j), and [an exogenous realization](hyp:u), the [named latent vector](goal) extracts [the original block coordinates](step:1) or [the node's intrinsic categorical noise coordinates](step:2), respectively. -/
def namedLatent {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (j : Fin b ⊕ Fin n)
    (u : Exogenous kind dims) : L1Vec (fullLatentDim kind dims j) :=
  match j with
  | .inl j => blockProjection j u
  | .inr i => categoricalNoise i u

/-- For [a structural causal model](hyp:M) and [a node](hyp:i), the [expanded set of designated latent blocks](goal) contains [the node's originally designated blocks](step:1) and [its own intrinsic noise block](step:2). -/
def EuclideanSCM.expandedIncidence {n b : ℕ} {kind : Fin n → NodeKind}
    {dims : Fin b → ℕ} (M : EuclideanSCM kind dims) (i : Fin n) :
    Finset (Fin b ⊕ Fin n) :=
  Finset.univ.filter (fun j => match j with
    | .inl j => j ∈ M.incidence i
    | .inr j => j = i)

/-- For [a structural causal model](hyp:M) and [a node](hyp:i), the [expanded input space](goal) collects its parents' observed coordinates, its originally designated latent block coordinates, and its own intrinsic noise coordinates, equipped with the sum norm. -/
abbrev EuclideanSCM.expandedInput {n b : ℕ} {kind : Fin n → NodeKind}
    {dims : Fin b → ℕ} (M : EuclideanSCM kind dims) (i : Fin n) :=
  WithLp 1 ((Sum (Σ p : {p // p ∈ M.dag.parents i}, Fin (valueDim (kind p)))
    (Σ j : {j // j ∈ M.expandedIncidence i}, Fin (fullLatentDim kind dims j))) → ℝ)

/-- For [a structural causal model](hyp:M), [a node](hyp:i), and [an expanded input vector](hyp:x), the [expanded mechanism's output](goal) applies the original mechanism to the parent and designated latent coordinates and to the intrinsic noise coordinates extracted from that vector. -/
def EuclideanSCM.expandedMechanism {n b : ℕ} {kind : Fin n → NodeKind}
    {dims : Fin b → ℕ} (M : EuclideanSCM kind dims) (i : Fin n)
    (x : M.expandedInput i) : ObservedValue (kind i) :=
  M.f i (WithLp.toLp 1 (fun c => match c with
    | .inl p => x.ofLp (.inl p)
    | .inr ⟨j,k⟩ => x.ofLp (.inr ⟨⟨.inl j.val, by
        simp [EuclideanSCM.expandedIncidence, j.property]⟩, k⟩)))
    (WithLp.toLp 1 (fun k => x.ofLp (.inr ⟨⟨.inr i, by
      simp [EuclideanSCM.expandedIncidence]⟩, k⟩)))

/-- For a structural causal model and any node, [the mechanism that receives intrinsic noise as part of its expanded input is measurable](goal). -/
@[fun_prop] lemma EuclideanSCM.expandedMechanism_measurable {n b : ℕ}
    {kind : Fin n → NodeKind} {dims : Fin b → ℕ} (M : EuclideanSCM kind dims)
    (i : Fin n) : Measurable (M.expandedMechanism i) := by
  unfold EuclideanSCM.expandedMechanism
  apply (M.structuralMeasurable i).comp (f := fun x : M.expandedInput i =>
    ((show StructuralInput kind dims M.dag M.incidence i from WithLp.toLp 1 (fun c => match c with
      | .inl p => x.ofLp (.inl p)
      | .inr ⟨j,k⟩ => x.ofLp (.inr ⟨⟨.inl j.val, by
          simp [EuclideanSCM.expandedIncidence, j.property]⟩, k⟩))),
      WithLp.toLp 1 (fun k => x.ofLp (.inr ⟨⟨.inr i, by
        simp [EuclideanSCM.expandedIncidence]⟩, k⟩))))
  apply Measurable.prodMk
  · apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    intro c
    rcases c with p | ⟨j,k⟩ <;> fun_prop
  · apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    intro k
    fun_prop

/-- For [a structural causal model](hyp:_M) and [an exogenous realization](hyp:u), the [expanded latent vector](goal) reindexes [the original latent block coordinates](step:1) and [the intrinsic node noise coordinates](step:2) as coordinates of one named block family. -/
def EuclideanSCM.expandedLatent {n b : ℕ} {kind : Fin n → NodeKind}
    {dims : Fin b → ℕ} (_M : EuclideanSCM kind dims) (u : Exogenous kind dims) :
    WithLp 1 ((Σ j, Fin (fullLatentDim kind dims j)) → ℝ) :=
  WithLp.toLp 1 (fun ⟨j,k⟩ => match j with
    | .inl j => u.ofLp (.inl ⟨j,k⟩)
    | .inr i => u.ofLp (.inr ⟨i,k⟩))

/-- For a structural causal model, [reindexing its exogenous coordinates into the expanded named latent family is measurable](goal). -/
@[fun_prop] lemma EuclideanSCM.expandedLatent_measurable {n b : ℕ}
    {kind : Fin n → NodeKind} {dims : Fin b → ℕ} (M : EuclideanSCM kind dims) :
    Measurable M.expandedLatent := by
  unfold EuclideanSCM.expandedLatent
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro ⟨j,k⟩
  cases j <;> fun_prop

/-- For [a structural causal model with separate intrinsic noise inputs](hyp:M), the [corresponding structural model on the expanded latent family](goal) keeps the parent graph, designates each node's noise block as an input, uses the expanded mechanisms, and transports the latent law to the reindexed coordinates. -/
def EuclideanSCM.toStructuralSCM {n b : ℕ} {kind : Fin n → NodeKind}
    {dims : Fin b → ℕ} (M : EuclideanSCM kind dims) :
    StructuralSCM kind (Fin b ⊕ Fin n) (fullLatentDim kind dims) :=
  { dag := M.dag, incidence := M.expandedIncidence,
    f := M.expandedMechanism, structuralMeasurable := M.expandedMechanism_measurable,
    latentLaw := M.latentLaw.map M.expandedLatent,
    probability := by
      let := M.probability
      exact Measure.isProbabilityMeasure_map M.expandedLatent_measurable.aemeasurable,
    categoricalPositive := M.categoricalPositive }

/-- For [a structural causal model](hyp:M) and [a node](hyp:i), the [mechanism input space](goal) consists of its parents' observed coordinates and exactly its designated latent blocks' coordinates, equipped with the sum norm. -/
abbrev StructuralSCM.Input {n : ℕ} {kind : Fin n → NodeKind}
    {J : Type*} [Fintype J] {dims : J → ℕ} (M : StructuralSCM kind J dims) (i : Fin n) :=
  WithLp 1 ((Sum (Σ p : {p // p ∈ M.dag.parents i}, Fin (valueDim (kind p)))
    (Σ j : {j // j ∈ M.incidence i}, Fin (dims j))) → ℝ)

/-- For [a structural causal model](hyp:M) and [a node](hyp:i), the [mechanism input vector](goal) extracts [the parents' coordinates](step:1) from [a joint observed vector](hyp:v) and [the designated latent coordinates](step:2) from [a joint latent realization](hyp:u). -/
def StructuralSCM.structuralInput {n : ℕ} {kind : Fin n → NodeKind}
    {J : Type*} [Fintype J] {dims : J → ℕ} (M : StructuralSCM kind J dims)
    (i : Fin n) (v : Joint kind) (u : WithLp 1 ((Σ j, Fin (dims j)) → ℝ)) : M.Input i :=
  WithLp.toLp 1 (fun c => match c with
    | .inl ⟨p,k⟩ => v.ofLp ⟨p.val,k⟩
    | .inr ⟨j,k⟩ => u.ofLp ⟨j.val,k⟩)

/-- For [a structural causal model](hyp:M), [a node](hyp:i), [a joint observed vector](hyp:v), and [a joint latent realization](hyp:u), the [node's observed coordinate vector](goal) is its mechanism's output on the extracted parent and designated latent inputs, with categorical outputs encoded as one-based labels. -/
def StructuralSCM.nodeValue {n : ℕ} {kind : Fin n → NodeKind}
    {J : Type*} [Fintype J] {dims : J → ℕ} (M : StructuralSCM kind J dims)
    (i : Fin n) (v : Joint kind) (u : WithLp 1 ((Σ j, Fin (dims j)) → ℝ)) :
    L1Vec (valueDim (kind i)) :=
  observedValueEmbedding (kind i) (M.f i (M.structuralInput i v u))

/-- For [a structural causal model](hyp:M), [an intervention](hyp:t), and [a joint latent realization](hyp:u), the [sequence of partial observed vectors](goal) [starts at zero](step:1) and [at each subsequent step updates the node with that topological rank using its replacement value or, absent a replacement, its mechanism, leaving other coordinates unchanged](step:2). -/
def StructuralSCM.evalSteps {n : ℕ} {kind : Fin n → NodeKind}
    {J : Type*} [Fintype J] {dims : J → ℕ} (M : StructuralSCM kind J dims)
    (t : Intervention kind) (u : WithLp 1 ((Σ j, Fin (dims j)) → ℝ)) : ℕ → Joint kind
  | 0 => 0
  | r + 1 => WithLp.toLp 1 (fun ⟨i,k⟩ =>
      if M.dag.topoOrder i = r then
        ((t i).getD (M.nodeValue i (M.evalSteps t u r) u)).ofLp k
      else (M.evalSteps t u r).ofLp ⟨i,k⟩)

/-- For [a structural causal model](hyp:M), [an intervention](hyp:t), and [a joint latent realization](hyp:u), the [intervened observed vector](goal) is the partial evaluation after the square of the number of nodes plus the number of nodes steps. -/
def StructuralSCM.intervenedEval {n : ℕ} {kind : Fin n → NodeKind}
    {J : Type*} [Fintype J] {dims : J → ℕ} (M : StructuralSCM kind J dims)
    (t : Intervention kind) (u : WithLp 1 ((Σ j, Fin (dims j)) → ℝ)) : Joint kind :=
  M.evalSteps t u (n * n + n)

/-- For [a structural causal model](hyp:M) and [an admissible intervention](hyp:t), the [interventional distribution](goal) is the distribution of the intervened observed vector under the model's joint latent law. -/
def StructuralSCM.interventionalLaw {n : ℕ} {kind : Fin n → NodeKind}
    {J : Type*} [Fintype J] {dims : J → ℕ} (M : StructuralSCM kind J dims)
    (t : LawIntervention kind) : Measure (Joint kind) :=
  M.latentLaw.map (M.intervenedEval t.val)

/-- For [a structural causal model](hyp:_M), [a latent block index](hyp:j), and [a joint latent realization](hyp:u), the [block projection](goal) extracts precisely that block's real coordinates. -/
def StructuralSCM.blockProjection {n : ℕ} {kind : Fin n → NodeKind}
    {J : Type*} [Fintype J] {dims : J → ℕ} (_M : StructuralSCM kind J dims)
    (j : J) (u : WithLp 1 ((Σ j, Fin (dims j)) → ℝ)) : L1Vec (dims j) :=
  WithLp.toLp 1 (fun k => u.ofLp ⟨j,k⟩)

/-- For [a structural causal model](hyp:M), the [causal graph](goal) pairs its parent directed acyclic graph with an undirected graph joining distinct nodes whenever some latent block designated to one and some block designated to the other are statistically dependent under the joint latent law. -/
def StructuralSCM.causalGraph {n : ℕ} {kind : Fin n → NodeKind}
    {J : Type*} [Fintype J] {dims : J → ℕ} (M : StructuralSCM kind J dims) :
    CausalGraph n := -- @realizes \mathcal{G}_{\mathcal{M}}(parent arrows plus dependence between designated latent inputs, allowing the same latent at both nodes)
  (M.dag, SimpleGraph.fromRel (fun i j =>
    ∃ k ∈ M.incidence i, ∃ l ∈ M.incidence j,
      ¬ ProbabilityTheory.IndepFun (M.blockProjection k) (M.blockProjection l) M.latentLaw))

/-- For a structural causal model, any node, any joint observed vector, and any exogenous realization, [the node's observed coordinate vector is unchanged when the model is converted to the expanded latent family and the exogenous coordinates are reindexed accordingly](goal). -/
lemma EuclideanSCM.expanded_nodeValue_eq {n b : ℕ} {kind : Fin n → NodeKind}
    {dims : Fin b → ℕ} (M : EuclideanSCM kind dims) (i : Fin n)
    (v : Joint kind) (u : Exogenous kind dims) :
    M.toStructuralSCM.nodeValue i v (M.expandedLatent u) = nodeValue M i v u := by
  trans observedValueEmbedding (kind i)
    (M.f i (structuralInput M i v u) (categoricalNoise i u))
  · dsimp only [StructuralSCM.nodeValue, EuclideanSCM.toStructuralSCM,
      EuclideanSCM.expandedMechanism, StructuralSCM.structuralInput,
      EuclideanSCM.expandedLatent, structuralInput, categoricalNoise]
    congr 2
    · apply PiLp.ext
      intro c
      cases c <;> rfl
  · exact (observedValueEmbedding_eq (kind i) _)

/-- For a structural causal model, an intervention, an exogenous realization, and any number of evaluation steps, [the partial observed vector is unchanged when evaluation uses the converted structural model with the reindexed latent realization](goal). -/
lemma EuclideanSCM.expanded_evalSteps_eq {n b : ℕ} {kind : Fin n → NodeKind}
    {dims : Fin b → ℕ} (M : EuclideanSCM kind dims) (t : Intervention kind)
    (u : Exogenous kind dims) (r : ℕ) :
    M.toStructuralSCM.evalSteps t (M.expandedLatent u) r = evalSteps M t u r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [StructuralSCM.evalSteps, evalSteps, ih, EuclideanSCM.expanded_nodeValue_eq]
    rfl

/-- For [a structural causal model with separate intrinsic noise inputs](hyp:M), the [causal graph](goal) pairs its parent directed acyclic graph with an undirected graph joining distinct nodes whenever an original latent block designated to one is statistically dependent on an original block designated to the other under the joint latent law. -/
def causalGraph {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ} -- @realizes \mathcal{G}(parent DAG plus statistical dependence-defined bidirected relation) -- @realizes \mathcal{G}_{\mathcal{M}}(parent DAG plus statistical dependence-defined bidirected relation)
    (M : EuclideanSCM kind dims) : CausalGraph n :=
  (M.dag, SimpleGraph.fromRel (fun i j =>
    ∃ k : Fin b, k ∈ M.incidence i ∧ ∃ l : Fin b, l ∈ M.incidence j ∧
      ¬ ProbabilityTheory.IndepFun (blockProjection k) (blockProjection l) M.latentLaw))

-- @node: def:eq-structure-equation
/-- Given [node kinds](hyp:kind), [latent block dimensions](hyp:dims), [a parent directed acyclic graph](hyp:dag), [an undirected graph](hyp:G), and [an indexed family of node sets](hyp:C), a [canonical structural causal model](goal) requires those sets to enumerate the undirected graph's maximal cliques exactly once, assigns each node the blocks for cliques containing it, and provides measurable mechanisms and probability laws for the blocks. Categorical nodes must have positive category counts and their mechanisms must return nonnegative propensities summing to one on admissible inputs. -/
structure CanonicalSCM {n b : ℕ} (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (G : SimpleGraph (Fin n))
    (C : Fin b → Set (Fin n)) where
  categoricalPositive : ∀ i k, kind i = Sum.inr k → 0 < k -- @realizes n_i(positive categorical cardinalities)
  component : ∀ j, IsC2Component G (C j)
  exhaustive : ∀ s, IsC2Component G s → ∃ j, C j = s
  distinct : Function.Injective C
  f : ∀ i, StructuralInput kind dims dag
    (fun i => Finset.univ.filter (fun j => i ∈ C j)) i → L1Vec (outputDim (kind i)) -- @realizes f_i(ambient extensions; paper-facing membership uses restrictions to admissible inputs)
  structuralMeasurable : ∀ i, Measurable (f i)
  blockLaw : ∀ j, ProbabilityMeasure (L1Vec (dims j)) -- @realizes U_C(arbitrary marginal)
  simplex : ∀ i k (h : kind i = Sum.inr k) x, x ∈ admissibleStructuralInputs kind dims dag (fun i => Finset.univ.filter (fun j => i ∈ C j)) i →
    (fun j : Fin k => (f i x).ofLp (Fin.cast (congrArg outputDim h).symm j)) ∈ stdSimplex ℝ (Fin k) -- @realizes f_i(nonnegative normalized categorical values on actual structural inputs)

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}
/-- For [a canonical structural causal model](hyp:_M), [a node](hyp:i), and [one of its observed coordinates](hyp:_j), the [declared coordinate domain](goal) is [all real numbers for a continuous node](step:1) or [the one-based integer labels up to the category count for a categorical node](step:2). -/
def CanonicalSCM.declaredCoordinateDomain (_M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (_j : Fin (valueDim (kind i))) : Set ℝ := -- @realizes V_i(actual real coordinate spaces or one-based categorical labels)
  match kind i with
  | .inl _ => Set.univ
  | .inr k => {x | ∃ label : Fin k, x = (label.val + 1 : ℕ)}

/-- For [an indexed family of node sets](hyp:C) and [a node](hyp:i), the [canonical set of designated latent blocks](goal) contains precisely the indices of sets that contain the node. -/
def canonicalIncidence (C : Fin b → Set (Fin n)) (i : Fin n) : Finset (Fin b) :=
  Finset.univ.filter (fun j => i ∈ C j)
/-- For [a canonical structural causal model](hyp:M), [a node](hyp:i), and [optional common coordinate bounds](hyp:bound), the [mechanism input domain](goal) consists of admissible parent and designated latent inputs satisfying the coordinate bounds when present. -/
def CanonicalSCM.domain (M : CanonicalSCM kind dims dag G C) (i : Fin n) (bound : Option (ℝ × ℝ) := none) :
    Set (StructuralInput kind dims dag (canonicalIncidence C) i) :=
  admissibleStructuralInputs kind dims dag (canonicalIncidence C) i ∩ structuralInputDomain bound
/-- For [a canonical structural causal model](hyp:M), the [joint exogenous law](goal) combines mutually independent latent blocks with their specified marginal laws and independent standard Gumbel coordinates for every category at each categorical node, then collects these coordinates in the exogenous vector. -/
def CanonicalSCM.latentLaw (M : CanonicalSCM kind dims dag G C) :
    Measure (Exogenous kind dims) :=
  ((Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j))))).prod
    (Measure.pi (fun _ : Σ i, Fin (noiseDim (kind i)) => gumbelLaw))).map
      (fun z => WithLp.toLp 1 (fun c => match c with
        | .inl ⟨j,k⟩ => (z.1 j).ofLp k
        | .inr k => z.2 k))
-- @node: gumbelLaw_probability
/-- [The standard Gumbel law has total mass one](goal). -/
lemma gumbelLaw_probability : IsProbabilityMeasure gumbelLaw := by
  let := ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  unfold gumbelLaw
  apply Measure.isProbabilityMeasure_map
  fun_prop

-- @node: CanonicalSCM.latentLaw_probability
/-- For any canonical structural causal model, [its joint exogenous law has total mass one](goal). -/
lemma CanonicalSCM.latentLaw_probability (M : CanonicalSCM kind dims dag G C) :
    IsProbabilityMeasure M.latentLaw := by
  let := gumbelLaw_probability
  unfold CanonicalSCM.latentLaw
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  let (j : Fin b) : BorelSpace (L1Vec (dims j)) := ⟨rfl⟩
  let : BorelSpace (Exogenous kind dims) := ⟨rfl⟩
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 1 _).comp
  apply continuous_pi
  intro c
  rcases c with ⟨j, k⟩ | k
  · exact (continuous_apply k).comp ((PiLp.continuous_ofLp 1 _).comp
      ((continuous_apply j).comp continuous_fst))
  · exact (continuous_apply k).comp continuous_snd
-- @node: CanonicalSCM.positive_categories
/-- For any canonical structural causal model, [every categorical node has a strictly positive number of categories](goal). -/
lemma CanonicalSCM.positive_categories (M : CanonicalSCM kind dims dag G C) :
    ∀ i k, kind i = Sum.inr k → 0 < k := by
  exact M.categoricalPositive
-- @node: firstArgmax_exists
/-- If [the number of labels is positive](hyp:hk), then for any extended real scores on those labels, [the first-maximizer search returns a label](goal). -/
lemma firstArgmax_exists {k : ℕ} (hk : 0 < k) (score : Fin k → EReal) :
    ∃ j, firstArgmax score = some j := by
  classical
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ score
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hsome : (firstArgmax score).isSome := by
    rw [firstArgmax, List.isSome_find?]
    simp only [List.any_eq_true]
    exact ⟨j, by simp, by simpa using fun l => hmax l (Finset.mem_univ l)⟩
  exact Option.isSome_iff_exists.mp hsome

-- @node: firstArgmax_maximizes
/-- If [the first-maximizer search returns a particular label](hyp:hj), then [every label's score is at most that selected label's score](goal). -/
lemma firstArgmax_maximizes {k : ℕ} (score : Fin k → EReal) (j : Fin k)
    (hj : firstArgmax score = some j) : ∀ l, score l ≤ score j := by
  have h := List.find?_some (by simpa only [firstArgmax] using hj)
  simpa using h

-- @node: firstArgmax_getD_measurable
/-- If [each label's extended real score is a measurable function of the input](hyp:hs), then [selecting the first maximizing label, with a fixed default if the search fails, is measurable](goal). -/
@[fun_prop] lemma firstArgmax_getD_measurable {X : Type*} [MeasurableSpace X]
    {k : ℕ} (score : X → Fin k → EReal) (default : Fin k)
    (hs : ∀ j, Measurable (fun x => score x j)) :
    Measurable (fun x => (firstArgmax (score x)).getD default) := by
  have hlist (l : List (Fin k)) :
      Measurable (fun x => (l.find? (fun j => ∀ a, score x a ≤ score x j)).getD default) := by
    induction l with
    | nil => exact measurable_const
    | cons j l ih =>
      have hp : MeasurableSet {x | ∀ a, score x a ≤ score x j} := by
        simpa only [Set.ofPred_forall] using
          MeasurableSet.iInter (fun a => measurableSet_le (hs a) (hs j))
      have heq : (fun x => ((j :: l).find? (fun a => ∀ b, score x b ≤ score x a)).getD default) =
          (fun x => if ∀ a, score x a ≤ score x j then j
            else (l.find? (fun a => ∀ b, score x b ≤ score x a)).getD default) := by
        funext x
        by_cases hx : ∀ a, score x a ≤ score x j <;> simp [hx]
      rw [heq]
      exact Measurable.ite hp measurable_const ih
  exact hlist (List.finRange k)

-- @node: extendedLog_measurable
/-- [The extended logarithm, which equals negative infinity at zero and the real logarithm elsewhere, is measurable](goal). -/
@[fun_prop] lemma extendedLog_measurable : Measurable extendedLog := by
  unfold extendedLog
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    Real.measurable_log.coe_real_ereal

-- @node: canonicalSelector
/-- For [a node kind](hyp:k) with a positive category count whenever categorical, the [canonical observation selector](goal) takes a mechanism output vector and a noise vector and [returns the output vector for a continuous node](step:1), or [returns the first label maximizing extended log propensity plus noise for a categorical node, using the first label as a fallback](step:2). -/
def canonicalSelector : (k : NodeKind) → (∀ m, k = .inr m → 0 < m) →
    L1Vec (outputDim k) → L1Vec (noiseDim k) → ObservedValue k
  | .inl _, _, w, _ => w
  | .inr k, hk, w, g =>
      (firstArgmax (fun j => extendedLog (w.ofLp j) + (g.ofLp j : EReal))).getD
        ⟨0, hk k rfl⟩

-- @node: canonicalSelector_measurable
/-- For any node kind, if [its category count is positive whenever it is categorical](hyp:hk), then [the canonical observation selector is measurable jointly in the mechanism output and noise vectors](goal). -/
@[fun_prop] lemma canonicalSelector_measurable (k : NodeKind)
    (hk : ∀ m, k = .inr m → 0 < m) :
    Measurable (fun z : L1Vec (outputDim k) × L1Vec (noiseDim k) =>
      canonicalSelector k hk z.1 z.2) := by
  cases k with
  | inl d => exact measurable_fst
  | inr m =>
    apply firstArgmax_getD_measurable
    intro j
    fun_prop

-- @node: canonicalSelector_eq
/-- For any node kind with [a positive category count whenever categorical](hyp:hk), any mechanism output vector, and any noise vector, [the canonical selector returns the output coordinates for a continuous node or the first label maximizing extended log propensity plus noise for a categorical node, with the first label as a fallback](goal). -/
lemma canonicalSelector_eq (k : NodeKind) (hk : ∀ m, k = .inr m → 0 < m)
    (w : L1Vec (outputDim k)) (g : L1Vec (noiseDim k)) :
    canonicalSelector k hk w g =
      (show ObservedValue (id k) from
        match h : id k with
        | .inl d => WithLp.toLp 1 (fun j => w.ofLp (Fin.cast (congrArg outputDim h).symm j))
        | .inr m => (firstArgmax (fun j : Fin m =>
            extendedLog (w.ofLp (Fin.cast (congrArg outputDim h).symm j)) +
              (g.ofLp (Fin.cast (congrArg noiseDim h).symm j) : EReal))).getD
                ⟨0, hk m h⟩) := by
  cases k <;> rfl

/-- For [a canonical structural causal model](hyp:M), [a node](hyp:i), [its parent and designated latent inputs](hyp:x), and [its intrinsic noise vector](hyp:g), the [canonical observed-value mechanism](goal) [returns the model's output coordinates for a continuous node](step:1) or [returns the first category maximizing extended log propensity plus noise for a categorical node, with the first category as a fallback](step:2). -/
def canonicalMechanism (M : CanonicalSCM kind dims dag G C) (i : Fin n)
    (x : StructuralInput kind dims dag (canonicalIncidence C) i)
    (g : L1Vec (noiseDim (kind i))) : ObservedValue (kind i) :=
  match h : kind i with
  | .inl d => WithLp.toLp 1 (fun j =>
      (M.f i x).ofLp (Fin.cast (congrArg outputDim h).symm j))
  | .inr k => (firstArgmax (fun j : Fin k =>
      extendedLog ((M.f i x).ofLp (Fin.cast (congrArg outputDim h).symm j)) +
        (g.ofLp (Fin.cast (congrArg noiseDim h).symm j) : EReal))).getD
          ⟨0, M.positive_categories i k h⟩

-- @node: canonicalMechanism_measurable
/-- For any canonical structural causal model, [each node's canonical observed-value mechanism is measurable jointly in its parent and designated latent inputs and its intrinsic noise vector](goal). -/
@[fun_prop] lemma canonicalMechanism_measurable (M : CanonicalSCM kind dims dag G C) :
    ∀ i, Measurable (fun z : StructuralInput kind dims dag (canonicalIncidence C) i ×
      L1Vec (noiseDim (kind i)) => canonicalMechanism M i z.1 z.2) := by
  intro i
  have heq (z : StructuralInput kind dims dag (canonicalIncidence C) i ×
      L1Vec (noiseDim (kind i))) :
      canonicalMechanism M i z.1 z.2 =
        canonicalSelector (kind i) (M.positive_categories i) (M.f i z.1) z.2 := by
    exact (canonicalSelector_eq (kind i) (M.positive_categories i) _ _).symm
  simp_rw [heq]
  exact (canonicalSelector_measurable (kind i) (M.positive_categories i)).comp
    (((M.structuralMeasurable i).comp measurable_fst).prodMk measurable_snd)

/-- For [a canonical structural causal model](hyp:M), the [corresponding Euclidean structural causal model](goal) uses its parent graph, designates the latent blocks of cliques containing each node, applies the canonical observed-value mechanisms, and uses the joint law of independent latent blocks and categorical Gumbel noise. -/
def CanonicalSCM.toEuclideanSCM (M : CanonicalSCM kind dims dag G C) :
    EuclideanSCM kind dims :=
  { dag := dag, incidence := canonicalIncidence C,
    f := canonicalMechanism M, structuralMeasurable := canonicalMechanism_measurable M,
    latentLaw := M.latentLaw, probability := M.latentLaw_probability,
    categoricalPositive := M.positive_categories }

/-- For [a canonical structural causal model](hyp:M), the [corresponding general structural causal model](goal) expresses its canonical equations with the Gumbel noise blocks explicitly included among each node's designated latent inputs. -/
def CanonicalSCM.toStructuralSCM (M : CanonicalSCM kind dims dag G C) :
    StructuralSCM kind (Fin b ⊕ Fin n) (fullLatentDim kind dims) :=
  M.toEuclideanSCM.toStructuralSCM

/-- For [a Euclidean structural causal model](hyp:M) and [a node](hyp:i), the [structural input dimension](goal) is the total number of observed coordinates of its parents and coordinates of its designated latent blocks. -/
def structuralInputSize {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) : ℕ :=
  Fintype.card (Sum (Σ p : {p // p ∈ M.dag.parents i}, Fin (valueDim (kind p)))
    (Σ j : {j // j ∈ M.incidence i}, Fin (dims j)))
/-- For [a Euclidean structural causal model](hyp:M), [a node](hyp:i), and [a real vector of that node's structural input dimension](hyp:x), the [structural input vector](goal) assigns the vector's coordinates to the node's parent and designated latent coordinates using their fixed finite enumeration. -/
def structuralFiniteCoordinates {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) (x : L1Vec (structuralInputSize M i)) :
    StructuralInput kind dims M.dag M.incidence i :=
  WithLp.toLp 1 (fun j => x.ofLp (Fintype.equivFin _ j))

-- @node: def:corollary-deep-nn-dimensions
/-- For [a Euclidean structural causal model](hyp:_M), the [maximum structural input dimension](goal) is the largest total number of parent observed coordinates and designated latent coordinates at any node, or zero if there are no nodes. -/
def maxInDim (_M : EuclideanSCM kind dims) : ℕ := -- @realizes d_{\max}^{\text{in}}(maximum structural input coordinate count)
  Finset.univ.sup (fun i => Fintype.card
    (Sum (Σ p : {p // p ∈ _M.dag.parents i}, Fin (valueDim (kind p)))
      (Σ j : {j // j ∈ _M.incidence i}, Fin (dims j))))
/-- For [a Euclidean structural causal model](hyp:_M), the [maximum mechanism output dimension](goal) is the largest continuous output dimension or categorical propensity vector dimension among its nodes, or zero if there are no nodes. -/
def maxOutDim (_M : EuclideanSCM kind dims) : ℕ := -- @realizes d_{\max}^{\text{out}}(maximum structural output coordinate count)
  Finset.univ.sup (fun i => outputDim (kind i))
/-- For [a Euclidean structural causal model](hyp:_M), the [maximum original latent block dimension](goal) is the largest dimension of its non-Gumbel latent blocks, or zero if there are no such blocks. -/
def maxLatentDim (_M : EuclideanSCM kind dims) : ℕ := Finset.univ.sup dims -- @realizes d_{\max}^U(maximum non-Gumbel block dimension)
/-- For [a Euclidean structural causal model](hyp:_M), the [maximum full latent block dimension](goal) is the largest dimension among its original latent blocks and its nodes' intrinsic noise blocks, including categorical Gumbel vectors, or zero if there are no blocks.

The deep approximation corollary uses this maximum to include categorical Gumbel vectors. -/
def maxFullLatentDim (_M : EuclideanSCM kind dims) : ℕ := -- @realizes d_{\max}^U(deep corollary: maximum over all latent blocks including categorical Gumbels)
  Finset.univ.sup (fullLatentDim kind dims)





end
end Papers.TbsNeuralCausalPi
