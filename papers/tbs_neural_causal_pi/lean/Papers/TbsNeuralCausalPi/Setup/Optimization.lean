module
public import Papers.TbsNeuralCausalPi.Setup.Networks
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Model
public import Papers.TbsNeuralCausalPi.Helpers.ObjectiveExpectationDomain
public import Papers.TbsNeuralCausalPi.Helpers.InterventionDomains
public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.MeasureTheory.Measure.Dirac
/-! # Population parameters and representation-indexed optimization -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.unusedTactic false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

-- @env: S3
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}
/-- For [node types](hyp:kind), [latent block dimensions](hyp:dims), [a causal
DAG](hyp:dag), [latent block memberships](hyp:C), and [a node](hyp:i), the
[structural input space](goal) consists of its parent coordinates and designated
non-Gumbel latent coordinates. -/
abbrev Input (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) (i : Fin n) :=
  StructuralInput kind dims dag (canonicalIncidence C) i
/-- Given [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), [a real bound](hyp:K), and [a node](hyp:i), the
[input cube](goal) contains exactly the structural inputs whose coordinates
all have absolute value at most that bound. -/
def inputCube (K : ℝ) (i : Fin n) : Set (Input kind dims dag C i) :=
  {x | ∀ j, |x.ofLp j| ≤ K}
/-- Given [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), [block memberships](hyp:C), and [admissible structural
function classes](hyp:F), the [canonical model class](goal) contains exactly
the models whose restricted mechanism at every node belongs to its specified class. -/
def canonicalClass (F : AdmissibleStructuralClass kind dims dag C) : Set (CanonicalSCM kind dims dag G C) := -- @realizes \mathcal{M}(\mathcal{G},\mathcal{F},\boldsymbol{U})(membership of restricted canonical mechanisms on the fixed graph)
  {M | ∀ i, M.restrictedMechanism i ∈ F i}
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), and [a nonnegative Lipschitz bound](hyp:L), the
[structural function class](goal) consists at each node of all functions on
admissible inputs with that Lipschitz bound. -/
def lipClass (L : ℝ≥0) : AdmissibleStructuralClass kind dims dag C :=
  fun _ => {f | LipschitzWith L f}
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), [block memberships](hyp:C), [a canonical model](hyp:M),
[a nonnegative Lipschitz bound](hyp:L), and [optional coordinate interval
endpoints](hyp:bound), the [domain-restricted structural class](goal) imposes
that Lipschitz bound between every pair of admissible inputs in the specified domain. -/
def domainLipClass (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0) (bound : Option (ℝ × ℝ) := none) :
    AdmissibleStructuralClass kind dims dag C :=
  fun i => {f | ∀ ⦃x⦄ (hx : x ∈ M.domain i bound) ⦃y⦄ (hy : y ∈ M.domain i bound),
    edist (f ⟨x, hx.1⟩) (f ⟨y, hy.1⟩) ≤ L * edist x y}
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), [an output bound](hyp:K), and [a nonnegative
Lipschitz bound](hyp:L), the [bounded Lipschitz structural class](goal) requires
[the Lipschitz bound between all admissible inputs](step:1) and [an output
one-norm at most the output bound at every admissible input](step:2). -/
def boundedLipClass (K : ℝ) (L : ℝ≥0) : AdmissibleStructuralClass kind dims dag C := -- @realizes \mathcal{F}_L^K(one-norm and Lipschitz bounds on admissible inputs only)
  fun i => {f | (∀ ⦃x⦄ (hx : x ∈ admissibleStructuralInputs kind dims dag (canonicalIncidence C) i)
      ⦃y⦄ (hy : y ∈ admissibleStructuralInputs kind dims dag (canonicalIncidence C) i),
      edist (f ⟨x, hx⟩) (f ⟨y, hy⟩) ≤ L * edist x y) ∧
    ∀ x (hx : x ∈ admissibleStructuralInputs kind dims dag (canonicalIncidence C) i),
      ‖f ⟨x, hx⟩‖ ≤ K}

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a structural
causal model](hyp:M), [an indexed family of interventions](hyp:t),
[a measure on intervention indices](hyp:muT), and [a real outcome functional](hyp:F),
[the intervention objective is defined](goal) when the outcome is integrable
over latent inputs for almost every intervention and the resulting inner
expectations are integrable over intervention indices. -/
def objectiveDefined (M : EuclideanSCM kind dims) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) (F : Joint kind → ℝ) : Prop :=
  iteratedObjectiveDefined muT M.latentLaw
    (fun s u => F (intervenedEval M (t s).val u))

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a structural
causal model](hyp:M), [an indexed intervention family](hyp:t),
[a measure on intervention indices](hyp:muT), and [a real outcome functional](hyp:F),
the [totalized objective integral](goal) integrates the intervened outcome first
over the model's latent law and then over intervention indices.

This integral is used in algebraic identities; finite expectations additionally
require integrability at both levels. -/
def objectiveIntegral (M : EuclideanSCM kind dims) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) (F : Joint kind → ℝ) : ℝ :=
  ∫ s, ∫ u, F (intervenedEval M (t s).val u) ∂M.latentLaw ∂muT

-- @node: def:true-objective
/-- Given [node types](hyp:kind), [latent dimensions](hyp:dims), [a structural
causal model](hyp:M), [an indexed intervention family](hyp:t),
[a probability measure on intervention indices](hyp:muT), [a real outcome
functional](hyp:F), and [integrability at both expectation levels](hyp:hdefined),
the [true objective](goal) is the finite expectation of the intervened outcome,
first over latent inputs and then over interventions. -/
def trueObjective (M : EuclideanSCM kind dims) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : objectiveDefined M t muT F) : ℝ := -- @realizes F_*(finite real iterated expectation on its intrinsic domain)
  finiteIteratedObjective muT M.latentLaw
    (fun s u => F (intervenedEval M (t s).val u)) hdefined

/-- For [node types](hyp:kind) and [a real outcome functional](hyp:Y), the
[rate objective](goal) is that same outcome functional. -/
def rateObjective (Y : Joint kind → ℝ) : Joint kind → ℝ := Y
/-- For [a lower endpoint](hyp:t1), [an upper endpoint](hyp:t2), and [strict
ordering of the endpoints](hyp:_h), the [uniform intervention measure](goal)
is Lebesgue measure restricted to their closed interval and divided by its length. -/
def uniformIntervention (t1 t2 : ℝ) (_h : t1 < t2) : Measure ℝ :=
  ENNReal.ofReal (t2-t1)⁻¹ • volume.restrict (Set.Icc t1 t2)

/-- Given [node types](hyp:kind), [an outcome node](hyp:Y), [its scalar
dimension](hyp:hY), [a lower intervention endpoint](hyp:t1), [an upper
endpoint](hyp:t2), [their strict ordering](hyp:ht12), [a tolerance](hyp:epsilon),
and [its positivity](hyp:hepsilon), the [rate setup](goal) consists of the
outcome-coordinate projection, the uniform law on the intervention interval,
and the positive tolerance. -/
-- @node: def:cor-rate-objective
def rateObjectiveSetup (Y : Fin n) (hY : valueDim (kind Y) = 1)
    (t1 t2 : ℝ) (ht12 : t1 < t2)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) : -- @realizes \epsilon(unused positive scalar in the rate setup)
    (Joint kind → ℝ) × Measure ℝ × {e : ℝ // 0 < e} :=
  (rateObjective (fun v => v.ofLp ⟨Y, Fin.cast hY.symm ⟨0, Nat.zero_lt_succ 0⟩⟩), -- @realizes F(outcome-coordinate projection) -- @realizes Y(designated scalar observed node)
    uniformIntervention t1 t2 ht12, -- @realizes \mu_T(deterministic uniform probability law on the nondegenerate intervention interval)
    ⟨epsilon, hepsilon⟩)

/-- For [a lower endpoint](hyp:t1), [an upper endpoint](hyp:t2), and [strictly
increasing endpoints](hyp:h), the [uniform intervention measure has total mass one](goal). -/
instance uniformIntervention_isProbabilityMeasure (t1 t2 : ℝ) (h : t1 < t2) :
    IsProbabilityMeasure (uniformIntervention t1 t2 h) := by
  constructor
  simp only [uniformIntervention, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_pos.mpr h).le),
    inv_mul_cancel₀ (sub_pos.mpr h).ne', ENNReal.ofReal_one]

/-- For [node types](hyp:kind), [latent block dimensions](hyp:dims), [a DAG](hyp:dag),
and [block memberships](hyp:C), an [ambient canonical parameter](goal) pairs
measurable full structural maps, whose categorical outputs are probability
vectors on admissible inputs, with arbitrary non-Gumbel marginal probability laws. -/
def AmbientCanonicalParam (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) := -- @realizes \theta(full structural maps and arbitrary independent non-Gumbel marginal laws)
  {f : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i)) // -- @realizes f_k(node-indexed structural function coordinate of the complete tuple)
    (∀ i, Measurable (f i)) ∧
    ∀ i k (h : kind i = Sum.inr k) x,
      x ∈ admissibleStructuralInputs kind dims dag (canonicalIncidence C) i →
        (fun j : Fin k => (f i x).ofLp (Fin.cast (congrArg outputDim h).symm j)) ∈
          probabilitySimplex k} × (∀ j, ProbabilityMeasure (L1Vec (dims j)))

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), and [block memberships](hyp:C), from
[a base canonical model supplying the graph and categorical setup](hyp:base)
and [an ambient tuple of structural maps and latent marginal laws](hyp:th),
the [reconstructed canonical model](goal) uses those maps and laws. -/
def ambientCanonicalOfParam (base : CanonicalSCM kind dims dag G C)
    (th : AmbientCanonicalParam kind dims dag C) : CanonicalSCM kind dims dag G C :=
  { categoricalPositive := base.categoricalPositive, component := base.component,
    exhaustive := base.exhaustive, distinct := base.distinct,
    f := th.1.val, structuralMeasurable := th.1.property.1,
    simplex := th.1.property.2, blockLaw := th.2 }

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), [block memberships](hyp:C), [a base canonical model](hyp:base), [a common
nonnegative bound](hyp:K), and [admissible structural classes](hyp:F), the
[canonical parameter space](goal) consists of ambient tuples with [structural
maps in those classes](step:1), [non-Gumbel marginals supported on the bounded
cubes](step:2), [almost surely bounded observed coordinates](step:3), and
[category counts at most the common bound](step:4).

The separately supplied standard Gumbel noises are not bounded. -/
-- @node: def:thm-consistency-model-parameterization
def CanonicalParam (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n))
    (base : CanonicalSCM kind dims dag G C)
    (K : ℝ≥0) (F : AdmissibleStructuralClass kind dims dag C) :=
  {th : AmbientCanonicalParam kind dims dag C //
    (∀ i, (fun x => th.1.val i x.val) ∈ F i) ∧ -- @realizes \theta(structural coordinates belong to the specified population function classes)
    (∀ j, (th.2 j : Measure (L1Vec (dims j))) (boundedCube (dims j) K) = 1) ∧ -- @realizes P(population non-Gumbel marginals supported on the bounded cubes, not required uniform)
    VariablesBoundedAt (ambientCanonicalOfParam base th).toEuclideanSCM K ∧ -- @realizes V_i(almost-sure observed-coordinate bounds by the same K) -- @realizes U_j(almost-sure non-Gumbel coordinate bounds) -- @realizes K(positive common bound on the represented model)
    ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K} -- @realizes n_i(category counts at most the common K)

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), and [block memberships](hyp:C), given
[a common nonnegative bound](hyp:K), [admissible structural classes](hyp:F),
[a canonical model](hyp:M), [membership of its restricted mechanisms in those
classes](hyp:hF), [non-Gumbel marginal support on the bounded cubes](hyp:hsupport),
[almost sure bounds on observed coordinates](hyp:hbounded), and [category
counts at most the common bound](hyp:hcategories), the [associated canonical
parameter](goal) retains the model's full structural maps and latent marginal laws. -/
def canonicalToParam (K : ℝ≥0) (F : AdmissibleStructuralClass kind dims dag C)
    (M : CanonicalSCM kind dims dag G C) (hF : M ∈ canonicalClass F)
    (hsupport : ∀ j, (M.blockLaw j : Measure (L1Vec (dims j))) (boundedCube (dims j) K) = 1)
    (hbounded : VariablesBoundedAt M.toEuclideanSCM K)
    (hcategories : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) :
    CanonicalParam kind dims dag C M K F := -- @realizes \theta_{\mathcal{M}}(bounded model's structural maps and supported non-Gumbel marginals) -- @realizes \theta^*(this tuple for the standing true model)
  ⟨(⟨M.f, M.structuralMeasurable, M.simplex⟩, M.blockLaw), hF, hsupport,
    hbounded, hcategories⟩

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), and [block memberships](hyp:C), from
[a base canonical model supplying the graph and categorical setup](hyp:base)
and [a bounded canonical parameter tuple](hyp:th), the [represented canonical
model](goal) takes its full structural maps and non-Gumbel marginal laws from the tuple. -/
def canonicalOfParam {K : ℝ≥0} {F : AdmissibleStructuralClass kind dims dag C}
    (base : CanonicalSCM kind dims dag G C)
    (th : CanonicalParam kind dims dag C base K F) : CanonicalSCM kind dims dag G C := -- @realizes \mathcal{M}^{\theta}(SCM with exactly the tuple's full structural maps and supported latent marginals) -- @realizes P^\theta(law of this fully represented population SCM)
  { categoricalPositive := base.categoricalPositive, component := base.component, exhaustive := base.exhaustive, distinct := base.distinct,
    f := th.val.1.val, structuralMeasurable := th.val.1.property.1,
    simplex := th.val.1.property.2, blockLaw := th.val.2 }

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), and [a nonnegative cube bound](hyp:K), the
[cube function space](goal) consists of a structural map at each node, defined
on its entire input cube and taking values in its output vector space. -/
abbrev CubeFunctions (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) (K : ℝ≥0) :=
  ∀ i, ↥(inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i) →
    L1Vec (outputDim (kind i))
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), and [a nonnegative cube bound](hyp:K), a
[cube structural class](goal) specifies at each node a set of structural maps
from its entire input cube to its output vector space. -/
abbrev CubeStructuralClass (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) (K : ℝ≥0) :=
  ∀ i, Set (↥(inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i) →
    L1Vec (outputDim (kind i)))
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), [a nonnegative cube and output bound](hyp:K), and
[a nonnegative Lipschitz bound](hyp:L), the [bounded Lipschitz cube class](goal)
requires [the Lipschitz bound on each entire input cube](step:1) and [output
one-norm at most the common bound for continuous nodes](step:2). -/
def cubeBoundedLipClass (K L : ℝ≥0) : CubeStructuralClass kind dims dag C K :=
  fun i => {f | LipschitzWith L f ∧
    ∀ d, kind i = Sum.inl d → ∀ x, ‖f x‖ ≤ K}
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), [a nonnegative cube bound](hyp:K), and [cube
structural classes](hyp:F), a [cube parameter](goal) pairs structural maps
belonging to those classes, with categorical probability-vector outputs and
measurability at every node, with marginal probability laws on the bounded latent cubes. -/
def CubeParam (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) (K : ℝ≥0)
    (F : CubeStructuralClass kind dims dag C K) := -- @realizes M(explicitly cube-defined population function space) -- @realizes \mathcal{P}(all probability measures on the bounded non-Gumbel cubes)
  {f : CubeFunctions kind dims dag C K //
    (∀ i, f i ∈ F i) ∧
    (∀ i k (h : kind i = Sum.inr k) x,
      (fun j : Fin k => (f i x).ofLp (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k) ∧
    (∀ i, Measurable (f i))} ×
    (∀ j, ProbabilityMeasure (boundedCube (dims j) K))

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), [a cube parameter tuple](hyp:th), and [a node](hyp:i), the [extended
structural map](goal) agrees with the tuple's map throughout its input cube
and equals zero for continuous nodes or the uniform probability vector for
categorical nodes outside that cube.

These extensions do not enter the parameter distance. -/
def paramFunction {K : ℝ≥0} {F : CubeStructuralClass kind dims dag C K}
    (th : CubeParam kind dims dag C K F) (i : Fin n) :
    Input kind dims dag C i → L1Vec (outputDim (kind i)) :=
  fun x => if hx : x ∈ inputCube K i then th.1.val i ⟨x,hx⟩ else
    WithLp.toLp 1 (fun _ => if (kind i).isRight then (outputDim (kind i) : ℝ)⁻¹ else 0)
-- @node: paramMarginal_probability
/-- For a cube parameter tuple and a latent block, [pushing the block's
probability law from its bounded cube into the ambient vector space gives
a probability measure](goal). -/
lemma paramMarginal_probability {K : ℝ≥0} {F : CubeStructuralClass kind dims dag C K}
    (th : CubeParam kind dims dag C K F) (j : Fin b) :
    IsProbabilityMeasure ((th.2 j : Measure (boundedCube (dims j) K)).map Subtype.val) := by
  exact Measure.isProbabilityMeasure_map (by fun_prop)

-- @node: paramFunction_simplex
/-- Given a base canonical model and a cube parameter tuple, [at every categorical
node and every admissible structural input, the extended structural map is a
probability vector over that node's categories](goal). -/
lemma paramFunction_simplex {K : ℝ≥0} {F : CubeStructuralClass kind dims dag C K}
    (base : CanonicalSCM kind dims dag G C) (th : CubeParam kind dims dag C K F) : ∀ i k (h : kind i = Sum.inr k) x,
      x ∈ admissibleStructuralInputs kind dims dag (canonicalIncidence C) i →
        (fun j : Fin k => (paramFunction th i x).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k := by
  intro i k h x hx
  by_cases hcube : x ∈ inputCube K i
  · simpa only [paramFunction, dif_pos hcube] using th.1.property.2.1 i k h ⟨x, hcube⟩
  · have hk : 0 < k := base.categoricalPositive i k h
    have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    have hext : paramFunction th i x = WithLp.toLp 1
        (fun _ => if (kind i).isRight then (outputDim (kind i) : ℝ)⁻¹ else 0) :=
      dif_neg hcube
    rw [hext]
    simp only [h, Sum.isRight_inr, outputDim, if_true]
    constructor
    · intro j
      positivity
    · simp [Finset.sum_const, hkreal]
-- @node: paramFunction_measurable
/-- For any cube parameter tuple, [the extended structural map at every node
is measurable on its full ambient input space](goal). -/
@[fun_prop] lemma paramFunction_measurable {K : ℝ≥0} {F : CubeStructuralClass kind dims dag C K}
    (th : CubeParam kind dims dag C K F) : ∀ i, Measurable (paramFunction th i) := by
  intro i
  first | fun_prop | skip
  have hcube : MeasurableSet (inputCube (kind := kind) (dims := dims)
      (dag := dag) (C := C) K i) := by
    change MeasurableSet {x : Input kind dims dag C i | ∀ j, |x.ofLp j| ≤ K}
    exact measurableSet_setOfPred.mpr (by fun_prop)
  exact (th.1.property.2.2 i).dite measurable_const hcube

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), and [block memberships](hyp:C), from
[a base canonical model supplying the graph and categorical setup](hyp:base)
and [a cube parameter tuple](hyp:th), the [represented canonical model](goal)
uses the tuple's extended structural maps and its latent marginal laws pushed
from their bounded cubes into ambient vector spaces. -/
def ofParam (base : CanonicalSCM kind dims dag G C) {K : ℝ≥0}
    {F : CubeStructuralClass kind dims dag C K} (th : CubeParam kind dims dag C K F) :
    CanonicalSCM kind dims dag G C := 
  { categoricalPositive := base.categoricalPositive, component := base.component, exhaustive := base.exhaustive, distinct := base.distinct,
    f := paramFunction th, simplex := paramFunction_simplex base th,
    structuralMeasurable := paramFunction_measurable th,
    blockLaw := fun j => ⟨(th.2 j : Measure (boundedCube (dims j) K)).map Subtype.val,
      paramMarginal_probability th j⟩ }

-- @node: boundedMarginal_comap_probability
/-- For [a nonnegative cube radius K](hyp:K), if [a probability law gives mass one to the coordinate cube of the given
nonnegative bound](hyp:hK), then [pulling that law back to the cube gives a
probability measure on the cube](goal). -/
lemma boundedMarginal_comap_probability (K : ℝ≥0) (d : ℕ)
    (P : ProbabilityMeasure (L1Vec d)) (hK : (P : Measure _) (boundedCube d K) = 1) :
    IsProbabilityMeasure ((P : Measure (L1Vec d)).comap
      (Subtype.val : boundedCube d K → L1Vec d)) := by
  have hmeas : MeasurableSet (boundedCube d K) := by
    change MeasurableSet {x : L1Vec d | ∀ j, |x.ofLp j| ≤ K}
    exact measurableSet_setOfPred.mpr (by fun_prop)
  exact (Toolkit.Foundations.MeasureTheory.probability_comap_subtype
    (P : Measure _) (boundedCube d K) hmeas hK).1
-- @node: canonicalFunction_restrict_measurable
/-- For a canonical model, [a nonnegative cube bound K](hyp:K), and a node, [restricting
the node's structural map to its input cube gives a measurable map](goal). -/
@[fun_prop] lemma canonicalFunction_restrict_measurable
    (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0) (i : Fin n) :
    Measurable (fun x : inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i =>
      M.f i x.val) := by
  first | fun_prop | exact (M.structuralMeasurable i).comp measurable_subtype_coe

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), and [block memberships](hyp:C), given
[a canonical model](hyp:M), [a nonnegative cube bound](hyp:K),
[cube structural classes](hyp:F), [membership of the restricted maps in those
classes](hyp:hF), [categorical probability-vector outputs on every input
cube](hyp:hsimplex), and [latent marginal mass one on every bounded cube](hyp:hK),
the [associated cube parameter](goal) restricts the structural maps to the
input cubes and pulls the latent laws back to their bounded cubes. -/
def toParam (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0)
    (F : CubeStructuralClass kind dims dag C K)
    (hF : ∀ i, (fun x : inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i => M.f i x.val) ∈ F i)
    (hsimplex : ∀ i k (h : kind i = Sum.inr k) (x : inputCube K i),
      (fun j : Fin k => (M.f i x.val).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k)
    (hK : ∀ j, (M.blockLaw j : Measure (L1Vec (dims j))) (boundedCube (dims j) K) = 1) :
    CubeParam kind dims dag C K F := 
  (⟨fun i x => M.f i x.val, hF,
    hsimplex,
    canonicalFunction_restrict_measurable M K⟩,
    fun j => ⟨(M.blockLaw j : Measure (L1Vec (dims j))).comap
      (Subtype.val : boundedCube (dims j) K → L1Vec (dims j)),
        boundedMarginal_comap_probability K (dims j) (M.blockLaw j) (hK j)⟩)

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), and [block memberships](hyp:C), given
[a neural causal representation](hyp:R), [a nonnegative cube
bound](hyp:K), [cube structural classes](hyp:F), [membership of its canonical
maps restricted to the cubes in those classes](hyp:hF), [categorical
probability-vector outputs everywhere on the cubes](hyp:hsimplex), and [latent
marginal support on the bounded cubes](hyp:hK), the [induced cube parameter](goal)
records those restricted maps and the induced latent laws on the cubes. -/
def inducedParam {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts} (R : NCMIn kind dims dag G C counts F0 F1)
    (K : ℝ≥0) (F : CubeStructuralClass kind dims dag C K)
    (hF : ∀ i, (fun x : inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i =>
      R.canonical.f i x.val) ∈ F i)
    (hsimplex : ∀ i k (h : kind i = Sum.inr k) (x : inputCube K i),
      (fun j : Fin k => (R.canonical.f i x.val).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k)
    (hK : ∀ j, (R.canonical.blockLaw j : Measure _) (boundedCube (dims j) K) = 1) :
    CubeParam kind dims dag C K F := -- @realizes \mathcal{P}_n(non-Gumbel population marginal tuple induced by this representation)
  toParam R.canonical K F hF hsimplex hK

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), [a nonnegative cube and output bound](hyp:K), and
[a nonnegative Lipschitz bound](hyp:L), the [population structural class](goal)
requires that Lipschitz bound on each whole input cube and bounds continuous
output one-norms by the common cube bound. -/
def cubePopulationClass (K L : ℝ≥0) : CubeStructuralClass kind dims dag C K :=
  cubeBoundedLipClass K L

-- @node: def:thm-consistency-population-parameter-space
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), [a nonnegative cube and output bound](hyp:K), and
[a nonnegative Lipschitz bound](hyp:L), a [population parameter](goal) stores
cube-defined structural maps with those bounds, categorical probability-vector
outputs, and non-Gumbel marginal probability laws on the bounded cubes. -/
structure PopulationParam (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) (K L : ℝ≥0) where
  parameter : CubeParam kind dims dag C K (cubePopulationClass K L) -- @realizes M(product of bounded Lipschitz cube maps and bounded-cube marginal probability laws) -- @realizes \mathcal{F}_{V_i}(common Lipschitz bound; continuous one-norm bound K and categorical simplex values on the whole cube)

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), [a first population parameter](hyp:th), and [a second population
parameter](hyp:th'), their [cube parameter distance](goal) is the sum of the
uniform distances between corresponding structural maps on their entire input
cubes and the first Wasserstein distances between corresponding latent laws,
with each distance converted to a real number. -/
def cubeParamDist {K L : ℝ≥0} (th th' : PopulationParam kind dims dag C K L) : ℝ :=
  (∑ i, (supDistOn Set.univ (th.parameter.1.val i) (th'.parameter.1.val i)).toReal) +
    ∑ j, (wasserstein1 (th.parameter.2 j : Measure (boundedCube (dims j) K))
      (th'.parameter.2 j : Measure (boundedCube (dims j) K))).toReal

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[block memberships](hyp:C), [a first population parameter](hyp:th), and [a second population
parameter](hyp:th'), the [parameter distance](goal) adds the real-valued
uniform distances of their structural maps on the entire input cubes and the
real-valued first Wasserstein distances of their non-Gumbel marginal laws on
the bounded cubes.

Structural coordinates are cube maps, so ambient extensions do not enter. -/
-- @node: def:thm-consistency-parameter-metric
def paramDist {K L : ℝ≥0}
    (th th' : PopulationParam kind dims dag C K L) : ℝ := -- @realizes \theta'(second cube-domain parameter tuple) -- @realizes d(sum of cube-uniform structural distances and marginal Wasserstein distances)
  cubeParamDist th th'
/-- For [node types](hyp:kind), [a nonnegative common bound](hyp:K), [a domain of intervention indices](hyp:domain),
[an indexed intervention family](hyp:t), and [a measure on intervention indices](hyp:muT),
the [population objective domain condition](goal) requires [all category counts
to be at most the common bound](step:1), [every assigned intervention coordinate
on the domain to have absolute value at most that bound](step:2), and [the
complement of the domain to have measure zero](step:3). -/
def populationObjectiveDomain (K : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (domain : Set I) (t : I → LawIntervention kind) (muT : Measure I) : Prop :=
  (∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) ∧ -- @realizes n_i(category count bounded by the same K)
    (∀ s ∈ domain, ∀ i v, (t s).val i = some v → ∀ j, |v.ofLp j| ≤ K) ∧ -- @realizes \boldsymbol{t}(every objective-domain intervention coordinate belongs to [-K,K])
    muT domainᶜ = 0

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), [block memberships](hyp:C), [a reference canonical model](hyp:base), [a nonnegative support and
output bound](hyp:K), [a nonnegative Lipschitz bound](hyp:L), [an indexed
intervention family](hyp:t), [an intervention-index measure](hyp:muT), and
[a real outcome functional](hyp:F), the [population integrability condition](goal)
requires a finite iterated objective for every canonical model in the bounded
Lipschitz class whose latent marginals are supported on the bounded cubes and
whose observational law has zero first Wasserstein distance from the reference law. -/
def populationObjectivesDefined (base : CanonicalSCM kind dims dag G C) (K L : ℝ≥0)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) (F : Joint kind → ℝ) : Prop :=
  ∀ M : CanonicalSCM kind dims dag G C,
    M ∈ canonicalClass (boundedLipClass K L) →
    (∀ j, (M.blockLaw j : Measure (L1Vec (dims j))) (boundedCube (dims j) K) = 1) →
    wasserstein1 (observationalLaw M.toEuclideanSCM)
      (observationalLaw base.toEuclideanSCM) = 0 →
    objectiveDefined M.toEuclideanSCM t muT F

/-- Given [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), [block memberships](hyp:C), [a reference canonical model](hyp:base), [a nonnegative support and
output bound](hyp:K), [a nonnegative Lipschitz bound](hyp:L), [an indexed
intervention family](hyp:t), [a probability measure on intervention indices](hyp:muT),
[a real outcome functional](hyp:F), and [integrability of every feasible
model's iterated objective](hyp:hdefined), the [population lower bound](goal)
is the extended-real infimum of these objectives over bounded Lipschitz models
with bounded-cube latent support and zero observational first Wasserstein
distance from the reference model. -/
-- @node: def:eq-consistent-limiting
def populationLowerBound (base : CanonicalSCM kind dims dag G C) (K L : ℝ≥0) -- @realizes \underline{F}^L(infimum of finite real objectives over all feasible population models)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind) (muT : Measure I)
    [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : populationObjectivesDefined base K L t muT F) : EReal :=
  ⨅ M : CanonicalSCM kind dims dag G C,
    ⨅ (hF : M ∈ canonicalClass (boundedLipClass K L)),
      ⨅ (hU : ∀ j, (M.blockLaw j : Measure (L1Vec (dims j))) (boundedCube (dims j) K) = 1), -- @realizes U_j(bounded non-Gumbel marginal support in the population class)
      ⨅ (hW : wasserstein1 (observationalLaw M.toEuclideanSCM)
        (observationalLaw base.toEuclideanSCM) = 0),
        (trueObjective M.toEuclideanSCM t muT F (hdefined M hF hU hW) : EReal)

/-- For [a finite list of sample points](hyp:x), the [empirical measure](goal)
is the sum of their point masses divided by the number of points, with the
empty sample giving the zero measure. -/
def empiricalMeasure {X : Type*} [MeasurableSpace X] {m : ℕ} (x : Fin m → X) : Measure X := -- @realizes \mu_n(finite average of Dirac masses at the observed sample points)
  (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a DAG](hyp:dag),
[an observed graph](hyp:G), [block memberships](hyp:C), [a candidate neural causal representation](hyp:R), [a finite sample
of joint observations](hyp:sample), and [a finite list of simulation inputs](hyp:draws),
the [empirical sampling laws](goal) are the empirical measure of the observations
and the empirical measure of the candidate's evaluations on those inputs. -/
-- @node: def:eq-opt-empiri-sampling
def empiricalSamplingLaws {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    (R : NCMIn kind dims dag G C counts F0 F1) {r m : ℕ}
    (sample : Fin r → Joint kind) (draws : Fin m → SimulationInput kind counts) :
    Measure (Joint kind) × Measure (Joint kind) :=
  (empiricalMeasure sample, -- @realizes P_n^{\mathcal{M}^*}(uniform average of Dirac masses at complete observations)
    empiricalMeasure (fun i => ncmEval R (draws i))) -- @realizes P_{m_n}^{\hat{\mathcal{M}}}(uniform average of candidate evaluations on the common exogenous draws)

/-- For [a sample size](hyp:m), the [uniform weights](goal) assign its reciprocal
to each sample index. -/
def uniformWeights (m : ℕ) : Fin m → ℝ := fun _ => (m : ℝ)⁻¹
/-- For [node types](hyp:kind), the [joint coordinate index set](goal) pairs each
node with one of its observed-value coordinates. -/
abbrev JointCoordinates (kind : Fin n → NodeKind) := Σ i, Fin (valueDim (kind i))
/-- For [node types](hyp:kind) and [a joint observation](hyp:v), the [joint
vector](goal) lists all observed coordinates in the finite enumeration of the
joint coordinate index set, using the one-norm. -/
def jointVector (v : Joint kind) : L1Vec (Fintype.card (JointCoordinates kind)) :=
  WithLp.toLp 1 (fun j => v.ofLp ((Fintype.equivFin _).symm j))
/-- For [node types](hyp:kind), [an entropy regularization coefficient](hyp:lam),
[a pair of observed and simulated laws](hyp:laws), [observed data](hyp:sample),
[simulated data](hyp:simulated), [equality of the observed empirical measure
with the first law](hyp:_hobs), and [equality of the simulated empirical measure
with the second law](hyp:_hsim), the [empirical Sinkhorn divergence](goal)
compares the simulated and observed coordinate vectors with uniform weights
and the finite-plan entropy convention. -/
def empiricalLawSinkhorn {r m : ℕ} (lam : ℝ)
    (laws : Measure (Joint kind) × Measure (Joint kind))
    (sample : Fin r → Joint kind) (simulated : Fin m → Joint kind)
    (_hobs : empiricalMeasure sample = laws.1)
    (_hsim : empiricalMeasure simulated = laws.2) : ℝ :=
  sinkhornDivergence lam (fun i => jointVector (simulated i))
    (fun i => jointVector (sample i)) (uniformWeights m) (uniformWeights r)

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
model](hyp:M), and [a nonnegative Lipschitz bound](hyp:Lf), the [adjusted
Lipschitz bound](goal) multiplies that bound by the square root of the product
of the model's maximum input and output dimensions. -/
def LhatF (M : EuclideanSCM kind dims) (Lf : ℝ≥0) : ℝ≥0 := -- @realizes \hat{L}_f(sqrt of the maximum input-output dimension product times the true Lipschitz bound)
  ⟨Real.sqrt (maxInDim M * maxOutDim M) * Lf, mul_nonneg (Real.sqrt_nonneg _) Lf.2⟩
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[a reference model](hyp:base), [a clipping bound](hyp:K), [a Lipschitz
bound](hyp:L), [a width sequence](hyp:W0), [a depth multiplier](hyp:c0), and
[a sample index](hyp:r), the [structural network class](goal) contains maps
represented in finite input coordinates by clipped ReLU networks of the
specified width, with depth equal to the multiplier times the rounded-up
value of one plus the log maximum input dimension, and with the given
Lipschitz bound before clipping. -/
def structuralClassN (base : CanonicalSCM kind dims dag G C) (K L : ℝ≥0) -- @realizes \mathcal{F}_{0,n}(node-specific truncated Lipschitz structural-network class at sample index n) -- @realizes W_{0,n}(node-specific truncated Lipschitz structural-network class at sample index n) -- @realizes \hat{\mathcal{F}}_{V_i,n}(node-specific truncated Lipschitz structural-network class at sample index n)
    (W0 : ℕ → ℕ) (c0 : ℕ) (r : ℕ) : StructuralClass kind dims dag C :=
  fun i => {f | ∃ q : ReLUNet (structuralInputSize base.toEuclideanSCM i)
    (outputDim (kind i)) (W0 r) (c0 * ⌈1+Real.log (maxInDim base.toEuclideanSCM)⌉₊),
    LipschitzWith L q.eval ∧
    ∀ x, f (structuralFiniteCoordinates base.toEuclideanSCM i x) = truncK K (q.eval x)}
/-- For [latent dimensions](hyp:dims), [component counts](hyp:counts),
[component dimensions](hyp:dC), [a clipping bound](hyp:K), [a latent dimension
budget](hyp:dU), [two width multipliers](hyp:c1,c2), [two depth
sequences](hyp:L1,L2), [a temperature sequence](hyp:tau), and [a sample
index](hyp:r), the [generator class](goal) consists of clipped three-part
generators with the specified depths and temperature, whose widths are the
first multiplier times the dimension budget and the second multiplier times
its square. -/
def generatorClassN (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ) -- @realizes \mathcal{NN}^{\infty,K}(generator architecture with final coordinate clipping and no Lipschitz bound) -- @realizes \mathcal{F}_{1,n}(generator architecture with final coordinate clipping and no Lipschitz bound)
    (K : ℝ≥0) (dU c1 c2 : ℕ) (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ) : GeneratorClass dims counts := -- @realizes L_{i,n}(sample-indexed depths of the first and second generator blocks)
  fun j => {g | ∃ q : ThreePartGenerator (counts j) (dims j) (dC j)
    (c1 * dU) (L1 r) (c2 * dU^2) (L2 r) (tau r), g = truncK K ∘ q.eval}

/-- For [three construction thresholds](hyp:a0,a1,a2) and [three chosen
architecture factors](hyp:c0,c1,c2), the [architecture factor condition](goal)
requires [a positive structural threshold](step:1), [a positive first generator
threshold](step:2), [a positive second generator threshold](step:3), [the
structural factor to be at least its threshold](step:4), [the first generator
factor to be at least its threshold](step:5), and [the second generator factor
to be at least its threshold](step:6). -/
def ArchitectureFactorSelection (a0 a1 a2 c0 c1 c2 : ℕ) : Prop :=
  0 < a0 ∧ 0 < a1 ∧ 0 < a2 ∧ a0 ≤ c0 ∧ a1 ≤ c1 ∧ a2 ≤ c2

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[an output bound](hyp:K), [a Lipschitz bound](hyp:L), and [a neural causal
representation](hyp:R), the [candidate restriction](goal) requires at every
node [a Lipschitz canonical map on admissible inputs](step:1), [continuous raw
outputs with one-norm at most the output bound](step:2), and [a Lipschitz raw
map for categorical nodes on admissible inputs](step:3). -/
def restrictedCandidate {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts} (K L : ℝ≥0)
    (R : NCMIn kind dims dag G C counts F0 F1) : Prop :=
  ∀ i, LipschitzOnWith L (R.canonical.f i) (R.canonical.domain i) ∧
    (∀ d, kind i = Sum.inl d → ∀ x ∈ R.canonical.domain i, ‖R.rawStructural i x‖ ≤ K) ∧
    (∀ k, kind i = Sum.inr k → LipschitzOnWith L (R.rawStructural i) (R.canonical.domain i))
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[a reference model](hyp:base), [an output and cube bound](hyp:K), [a Lipschitz
bound](hyp:L), [component counts](hyp:counts), [component dimensions](hyp:dC),
and [three architecture thresholds](hyp:a0,a1,a2), the [construction threshold
condition](goal) requires [positive maximum input dimension](step:1), [positive
maximum latent dimension](step:2), and [uniform approximation constants and
budget and temperature cutoffs](step:3). Above those budget cutoffs and below
the positive temperature cutoff, every choice of factors dominating the
thresholds admits a restricted representation whose summed structural uniform
errors and marginal Wasserstein errors are bounded by a constant times the
sum of the inverse input-dimension power of structural width, the inverse
twice-latent-dimension powers of both depths, and temperature times one minus
its logarithm. -/
def ArchitectureConstructionThresholds (base : CanonicalSCM kind dims dag G C)
    (K L : ℝ≥0) (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
    (a0 a1 a2 : ℕ) : Prop :=
  0 < maxInDim base.toEuclideanSCM ∧ 0 < maxLatentDim base.toEuclideanSCM ∧
  ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, ∃ tau0 : ℝ, 0 < tau0 ∧
    ∀ c0 c1 c2 : ℕ, ArchitectureFactorSelection a0 a1 a2 c0 c1 c2 →
    ∀ W0 L1 L2 : ℕ, B ≤ W0 → B ≤ L1 → B ≤ L2 →
    ∀ tau : ℝ, 0 < tau → tau < min 1 tau0 →
    ∃ R : NCMIn kind dims dag G C counts
      (structuralClassN base K L (fun _ => W0) c0 0)
      (generatorClassN counts dC K (maxLatentDim base.toEuclideanSCM) c1 c2 (fun _ => L1) (fun _ => L2) (fun _ => tau) 0),
      restrictedCandidate K L R ∧
      (∑ i, supDistOn (base.domain i (some (-(K : ℝ), K))) (base.f i) (R.canonical.f i)) +
        (∑ j, wasserstein1 (base.blockLaw j : Measure (L1Vec (dims j)))
          (R.canonical.blockLaw j : Measure (L1Vec (dims j)))) ≤
        ENNReal.ofReal (A * ((W0 : ℝ)^(-(1:ℝ)/maxInDim base.toEuclideanSCM) +
          (L1 : ℝ)^(-(2:ℝ)/maxLatentDim base.toEuclideanSCM) +
          (L2 : ℝ)^(-(2:ℝ)/maxLatentDim base.toEuclideanSCM) + tau * (1-Real.log tau)))

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[structural classes](hyp:F0), [generator classes](hyp:F1), [a criterion for
admitting representations](hyp:admissible), [interventions](hyp:t), [their
index measure](hyp:muT), and [an outcome functional](hyp:F), the [empirical
objective domain condition](goal) requires the iterated outcome expectation
to be defined for every admitted representation. -/
def empiricalObjectivesDefined {counts : Fin b → ℕ} (F0 : StructuralClass kind dims dag C)
    (F1 : GeneratorClass dims counts)
    (admissible : NCMIn kind dims dag G C counts F0 F1 → Prop)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) (F : Joint kind → ℝ) : Prop :=
  ∀ R, admissible R → objectiveDefined R.canonical.toEuclideanSCM t muT F

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[structural classes](hyp:F0), [generator classes](hyp:F1), [an admission
criterion](hyp:admissible), [interventions](hyp:t), [their probability
measure](hyp:muT), [an outcome functional](hyp:F), [observations](hyp:sample),
[common simulation inputs](hyp:draws), [an entropy coefficient](hyp:lam),
[a divergence tolerance](hyp:alpha), and [defined iterated objectives for all
admitted representations](hyp:hdefined), the [restricted empirical partial
identification value](goal) is the extended-real infimum of those objectives
over admitted representations whose empirical Sinkhorn divergence is at most
the tolerance. -/
def empiricalPIValueOn {counts : Fin b → ℕ} (F0 : StructuralClass kind dims dag C) -- @realizes F_n(scalar infimum over representations evaluated on one common observational sample and simulation draws) -- @realizes P_n^{\mathcal{M}^*}(scalar infimum over representations evaluated on one common observational sample and simulation draws) -- @realizes P_{m_n}^{\hat{\mathcal{M}}}(scalar infimum over representations evaluated on one common observational sample and simulation draws)
    (F1 : GeneratorClass dims counts)
    (admissible : NCMIn kind dims dag G C counts F0 F1 → Prop) {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ) {r m : ℕ}
    (sample : Fin r → Joint kind) (draws : Fin m → SimulationInput kind counts)
    (lam alpha : ℝ)
    (hdefined : empiricalObjectivesDefined (G := G) F0 F1 admissible t muT F) : EReal :=
  ⨅ R : NCMIn kind dims dag G C counts F0 F1, ⨅ (hR : admissible R),
    ⨅ (_h : empiricalLawSinkhorn lam (empiricalSamplingLaws R sample draws)
      sample (fun i => ncmEval R (draws i)) rfl rfl ≤ alpha),
        (trueObjective R.canonical.toEuclideanSCM t muT F (hdefined R hR) : EReal)

-- @node: def:eq-opt-empiri
/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[structural classes](hyp:F0), [generator classes](hyp:F1), [interventions](hyp:t),
[their probability measure](hyp:muT), [an outcome functional](hyp:F),
[observations](hyp:sample), [common simulation inputs](hyp:draws), [an entropy
coefficient](hyp:lam), [a divergence tolerance](hyp:alpha), and [defined
iterated objectives for every representation](hyp:hdefined), the [empirical
partial identification value](goal) is the extended-real infimum of the
intervention objective over representations whose empirical Sinkhorn
divergence is at most the tolerance. -/
def empiricalPIValue {counts : Fin b → ℕ} (F0 : StructuralClass kind dims dag C)
    (F1 : GeneratorClass dims counts) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ) {r m : ℕ}
    (sample : Fin r → Joint kind) (draws : Fin m → SimulationInput kind counts)
    (lam alpha : ℝ)
    (hdefined : empiricalObjectivesDefined (G := G) F0 F1 (fun _ => True) t muT F) : EReal :=
  ⨅ R : NCMIn kind dims dag G C counts F0 F1,
    ⨅ (_h : empiricalLawSinkhorn lam (empiricalSamplingLaws R sample draws)
      sample (fun i => ncmEval R (draws i)) rfl rfl ≤ alpha),
        (trueObjective R.canonical.toEuclideanSCM t muT F (hdefined R trivial) : EReal)

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[structural classes](hyp:F0), [generator classes](hyp:F1), [an output
bound](hyp:K), [a Lipschitz bound](hyp:L), [interventions](hyp:t), [their
probability measure](hyp:muT), [an outcome functional](hyp:F),
[observations](hyp:sample), [common simulation inputs](hyp:draws), [an entropy
coefficient](hyp:lam), [a divergence tolerance](hyp:alpha), and [defined
objectives for all candidates satisfying the bounds](hyp:hdefined), the
[bounded empirical partial identification value](goal) is the extended-real
infimum of the intervention objective over those candidates whose empirical
Sinkhorn divergence is at most the tolerance. -/
def restrictedEmpiricalPIValue {counts : Fin b → ℕ} (F0 : StructuralClass kind dims dag C)
    (F1 : GeneratorClass dims counts) (K L : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ) {r m : ℕ}
    (sample : Fin r → Joint kind) (draws : Fin m → SimulationInput kind counts)
    (lam alpha : ℝ)
    (hdefined : empiricalObjectivesDefined (G := G) F0 F1 (restrictedCandidate K L) t muT F) : EReal :=
  empiricalPIValueOn (G := G) F0 F1 (restrictedCandidate (G := G) K L) t muT F sample draws lam alpha hdefined

/-- For [a rate multiplier](hyp:c), [an input dimension](hyp:din), [a latent
dimension](hyp:dU), [positivity of the input dimension](hyp:_hdin), [positivity
of the latent dimension](hyp:_hdU), [a structural width sequence](hyp:W0),
[two generator depth sequences](hyp:L1,L2), [a temperature sequence](hyp:tau),
and [a sample index](hyp:r), the [positive approximation tolerance](goal)
[forms the multiplier times the sum of width to power minus reciprocal input
dimension, both depths to power minus twice reciprocal latent dimension,
and temperature times one minus its logarithm](step:1), then [uses that rate
if positive and one otherwise](step:2). -/
def epsN (c : ℝ) (din dU : ℕ) (_hdin : 0 < din) (_hdU : 0 < dU) (W0 L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ) : ℝ := -- @realizes \epsilon_n(positive extension of the stated constant-multiple approximation rate)
  let rate := c * ((W0 r : ℝ)^(-(1:ℝ)/din) + (L1 r : ℝ)^(-(2:ℝ)/dU) +
    (L2 r : ℝ)^(-(2:ℝ)/dU) + tau r * (1-Real.log (tau r)))
  if 0 < rate then rate else 1
/-- For [a rate multiplier](hyp:c), [a dimension bound](hyp:DU), [simulation
sample sizes](hyp:m), [two generator depth sequences](hyp:L1,L2), [entropy
coefficients](hyp:lam), and [a sample index](hyp:r), the [positive sampling
tolerance](goal) [forms the multiplier times the sum of the simulation rate,
the depth sum times log simulation size divided by its square root, the
observational rate, and the entropy coefficient times log of the product of
the two sample sizes](step:1), then [uses that rate if positive and one
otherwise](step:2). The simulation rate is log simulation size times that size
to power minus one divided by the sum of two and the larger of one and the
dimension bound; the observational rate is squared log observation size times that size
to power minus reciprocal of the larger of two and the dimension bound. -/
def sN (c : ℝ) (DU : ℕ) (m L1 L2 : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) : ℝ := -- @realizes m_n(constant multiple of the simulation, observational and Sinkhorn error rates) -- @realizes s_n(constant multiple of the simulation, observational and Sinkhorn error rates) 
  let rate := c * ((m r : ℝ)^(-(1:ℝ)/(max 1 DU+2)) * Real.log (m r) +
    (L1 r+L2 r : ℕ) * Real.log (m r) / Real.sqrt (m r) +
    (r : ℝ)^(-(1:ℝ)/max 2 DU) * (Real.log r)^2 + Real.log (r*m r) * lam r)
  if 0 < rate then rate else 1
/-- For [approximation and sampling multipliers](hyp:ce,cs), [an input
dimension](hyp:din), [a latent dimension](hyp:dU), [a sampling dimension
bound](hyp:DU), [simulation sample sizes](hyp:m), [structural widths](hyp:W0),
[two generator depth sequences](hyp:L1,L2), [positive input dimension](hyp:hdin),
[positive latent dimension](hyp:hdU), [temperatures](hyp:tau), [entropy
coefficients](hyp:lam), and [a sample index](hyp:r), the [consistency
radius](goal) is the sum of the positive approximation and sampling tolerances
at that index. -/
def consistencyRadius (ce cs : ℝ) (din dU DU : ℕ) (m W0 L1 L2 : ℕ → ℕ) -- @realizes \alpha_n(epsilon_n plus s_n with temperature sequence kept explicit) -- @realizes \tau_n(epsilon_n plus s_n with temperature sequence kept explicit)
    (hdin : 0 < din) (hdU : 0 < dU) (tau lam : ℕ → ℝ) (r : ℕ) : ℝ :=
  epsN ce din dU hdin hdU W0 L1 L2 tau r + sN cs DU m L1 L2 lam r
/-- For a model reconstructed from a cube parameter, [every non-Gumbel latent
coordinate has absolute value at most the cube bound almost surely](goal). -/
-- @node: ofParam_latent_coordinates_bounded
lemma ofParam_latent_coordinates_bounded {K : ℝ≥0}
    {F : CubeStructuralClass kind dims dag C K}
    (base : CanonicalSCM kind dims dag G C) (th : CubeParam kind dims dag C K F) :
    ∀ᵐ u ∂(ofParam base th).latentLaw, ∀ j k, |u.ofLp (.inl ⟨j,k⟩)| ≤ (K : ℝ) := by
  let M := ofParam base th
  letI := gumbelLaw_probability
  have hblock (j : Fin b) : ∀ᵐ x ∂(M.blockLaw j : Measure (L1Vec (dims j))),
      ∀ k, |x.ofLp k| ≤ (K : ℝ) := by
    change ∀ᵐ x ∂(th.2 j : Measure (boundedCube (dims j) K)).map Subtype.val, ∀ k, |x.ofLp k| ≤ (K : ℝ)
    apply (ae_map_iff (by fun_prop) (by exact measurableSet_setOfPred.mpr (by fun_prop))).2
    exact Eventually.of_forall fun x => x.property
  have hpi : ∀ᵐ x ∂Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j)))),
      ∀ j k, |(x j).ofLp k| ≤ (K : ℝ) :=
    eventually_all.2 fun j => (Measure.tendsto_eval_ae_ae (μ := fun j => (M.blockLaw j : Measure (L1Vec (dims j)))) (i := j)).eventually (hblock j)
  change ∀ᵐ u ∂M.latentLaw, _
  unfold CanonicalSCM.latentLaw
  apply (ae_map_iff (by
    apply Measurable.aemeasurable
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro (⟨j,k⟩ | k) <;> fun_prop)
    (by exact measurableSet_setOfPred.mpr (by fun_prop))).2
  apply (Measure.ae_prod_iff_ae_ae (by
    exact measurableSet_setOfPred.mpr (by fun_prop))).2
  filter_upwards [hpi] with z hz
  exact Eventually.of_forall fun _ => hz

/-- If [the node is continuous with the given output dimension](hyp:hi), then
[every coordinate of its extended population structural map has absolute value
at most the cube bound, at every ambient input](goal). -/
-- @node: paramFunction_continuous_coordinate_bound
lemma paramFunction_continuous_coordinate_bound {K L : ℝ≥0}
    (th : CubeParam kind dims dag C K (cubePopulationClass K L))
    (i : Fin n) (d : ℕ) (hi : kind i = .inl d)
    (x : Input kind dims dag C i) (j : Fin (outputDim (kind i))) :
    |(paramFunction th i x).ofLp j| ≤ K := by
  by_cases hx : x ∈ inputCube K i
  · rw [paramFunction, dif_pos hx]
    have hn : |(th.1.val i ⟨x,hx⟩).ofLp j| ≤ ‖th.1.val i ⟨x,hx⟩‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (th.1.val i ⟨x,hx⟩) j
    exact hn.trans ((th.1.property.1 i).2 d hi ⟨x,hx⟩)
  · simp [paramFunction, hx, hi, K.coe_nonneg]

/-- If [categorical nodes have a positive number of labels](hyp:hpos),
[every continuous structural output coordinate has absolute value at most
the bound](hyp:hw), and [every categorical label count is at most the
bound](hyp:hlabels), then [every coordinate of the canonical selector's
embedded observed output has absolute value at most that bound](goal). -/
-- @node: canonicalSelector_embedding_coordinate_bound
lemma canonicalSelector_embedding_coordinate_bound (κ : NodeKind)
    (hpos : ∀ k, κ = .inr k → 0 < k) (K : ℝ)
    (w : L1Vec (outputDim κ)) (g : L1Vec (noiseDim κ))
    (hw : ∀ d, κ = .inl d → ∀ j, |w.ofLp j| ≤ K)
    (hlabels : ∀ k, κ = .inr k → (k : ℝ) ≤ K) :
    ∀ j, |(observedValueEmbedding κ (canonicalSelector κ hpos w g)).ofLp j| ≤ K := by
  cases κ with
  | inl d => exact hw d rfl
  | inr k =>
    intro j
    simp only [canonicalSelector, observedValueEmbedding, WithLp.ofLp_toLp]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    apply le_trans _ (hlabels k rfl)
    exact_mod_cast (Nat.succ_le_of_lt (Fin.isLt _))

/-- If [all category counts are at most the common bound](hyp:hlabels) and
[all coordinates assigned by the intervention have absolute value at most
that bound](hyp:ht), then [every observed coordinate after any given number
of evaluation steps of the reconstructed population model has absolute value
at most the common bound](goal), for every latent input. -/
-- @node: ofParam_evalSteps_coordinate_bounded
lemma ofParam_evalSteps_coordinate_bounded {K L : ℝ≥0}
    (base : CanonicalSCM kind dims dag G C)
    (th : CubeParam kind dims dag C K (cubePopulationClass K L))
    (t : Intervention kind) (u : Exogenous kind dims)
    (hlabels : ∀ i k, kind i = .inr k → (k : ℝ) ≤ K)
    (ht : ∀ i v, t i = some v → ∀ j, |v.ofLp j| ≤ K) (r : ℕ) :
    ∀ i j, |(evalSteps (ofParam base th).toEuclideanSCM t u r).ofLp ⟨i,j⟩| ≤ K := by
  induction r with
  | zero => intro i j; simpa [evalSteps] using K.coe_nonneg
  | succ r ih =>
    intro i j
    simp only [evalSteps, WithLp.ofLp_toLp]
    split_ifs with hslot
    · cases hti : t i with
      | some v => exact ht i v hti j
      | none =>
        simp only [Option.getD_none]
        rw [show nodeValue (ofParam base th).toEuclideanSCM i
            (evalSteps (ofParam base th).toEuclideanSCM t u r) u =
          observedValueEmbedding (kind i)
            (canonicalMechanism (ofParam base th) i
              (structuralInput (ofParam base th).toEuclideanSCM i
                (evalSteps (ofParam base th).toEuclideanSCM t u r) u)
              (categoricalNoise i u)) from (observedValueEmbedding_eq _ _).symm]
        rw [show canonicalMechanism (ofParam base th) i =
            fun x g => canonicalSelector (kind i) ((ofParam base th).positive_categories i)
              ((ofParam base th).f i x) g from by
          funext x g
          exact (canonicalSelector_eq _ _ _ _).symm]
        apply canonicalSelector_embedding_coordinate_bound
        · intro d hd j
          exact paramFunction_continuous_coordinate_bound th i d hd _ j
        · exact hlabels i
    · exact ih i j

/-- If [category counts and assigned intervention coordinates on the specified
domain are bounded by the cube bound, and the domain has full intervention
measure](hyp:hobjective), then [for almost every intervention index and almost
every latent input, every structural input used at its node's evaluation step
belongs to that node's input cube](goal). -/
-- @node: population_intervened_inputs_mem_cube
lemma population_intervened_inputs_mem_cube {K L : ℝ≥0}
    (base : CanonicalSCM kind dims dag G C)
    (th : PopulationParam kind dims dag C K L)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind) (muT : Measure I)
    (domain : Set I) (hobjective : populationObjectiveDomain K domain t muT) :
    ∀ᵐ s ∂muT, ∀ᵐ u ∂(ofParam base th.parameter).latentLaw, ∀ i,
      structuralInput (ofParam base th.parameter).toEuclideanSCM i
        (evalSteps (ofParam base th.parameter).toEuclideanSCM (t s).val u (dag.topoOrder i)) u ∈
          inputCube K i := by
  have hdomain : ∀ᵐ s ∂muT, s ∈ domain := by
    exact ae_iff.mpr hobjective.2.2
  filter_upwards [hdomain] with s hs
  filter_upwards [ofParam_latent_coordinates_bounded base th.parameter] with u hu
  intro i c
  cases c with
  | inl p =>
    exact ofParam_evalSteps_coordinate_bounded base th.parameter (t s).val u
      hobjective.1 (hobjective.2.1 s hs) _ p.1.val p.2
  | inr p => exact hu p.1.val p.2

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[an entropy coefficient](hyp:lam), [observations](hyp:sample), [common
simulation inputs](hyp:draws), and [a neural causal representation](hyp:R),
the [consistency constraint value](goal) is the Sinkhorn divergence between
the uniformly weighted observation vectors and the representation's uniformly
weighted simulated output vectors. -/
def consistencyConstraint {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts} {r m : ℕ} (lam : ℝ) (sample : Fin r → Joint kind)
    (draws : Fin m → SimulationInput kind counts) (R : NCMIn kind dims dag G C counts F0 F1) : ℝ :=
  sinkhornDivergence lam (fun i => jointVector (sample i))
    (fun i => jointVector (ncmEval R (draws i)))
    (uniformWeights r) (uniformWeights m)

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[a base model](hyp:base), [interventions](hyp:t), [their probability
measure](hyp:muT), [an outcome functional](hyp:F), [an intervention-index
domain](hyp:domain), [bounded category counts and intervention assignments
on that full-measure domain](hyp:_hobjective), [a population parameter](hyp:th),
and [integrability of its iterated outcome expectation](hyp:hdefined), the
[consistency objective](goal) is the true intervention objective of the model
reconstructed from the population parameter. -/
def consistencyObjective (base : CanonicalSCM kind dims dag G C) {K L : ℝ≥0}
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (domain : Set I) (_hobjective : populationObjectiveDomain K domain t muT)
    (th : PopulationParam kind dims dag C K L)
    (hdefined : objectiveDefined (ofParam base th.parameter).toEuclideanSCM t muT F) : ℝ := -- @realizes f(population intervention objective determined by the cube parameter)
  trueObjective (ofParam base th.parameter).toEuclideanSCM t muT F hdefined

/-- If [the intervention domain has full measure and bounds category counts
and assigned coordinates by the cube bound](hyp:hobjective), [the model's
structural maps agree with the population maps on admissible cube inputs](hyp:hf),
[its latent marginals equal the population cube laws embedded in the ambient
spaces](hyp:hP), [its iterated outcome expectation is defined](hyp:hM), and
[the reconstructed population model's iterated outcome expectation is
defined](hyp:hth), then [the model's true objective equals the population
parameter's consistency objective](goal). -/
-- @node: consistencyObjective_eq_of_cube_agreement
lemma consistencyObjective_eq_of_cube_agreement {K L : ℝ≥0}
    (base M : CanonicalSCM kind dims dag G C)
    (th : PopulationParam kind dims dag C K L)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (domain : Set I) (hobjective : populationObjectiveDomain K domain t muT)
    (hf : ∀ i (x : inputCube K i), x.val ∈ M.domain i →
      M.f i x.val = th.parameter.1.val i x)
    (hP : ∀ j, (M.blockLaw j : Measure (L1Vec (dims j))) =
      (th.parameter.2 j : Measure (boundedCube (dims j) K)).map Subtype.val)
    (hM : objectiveDefined M.toEuclideanSCM t muT F)
    (hth : objectiveDefined (ofParam base th.parameter).toEuclideanSCM t muT F) :
    trueObjective M.toEuclideanSCM t muT F hM =
      consistencyObjective base t muT F domain hobjective th hth := by
  let N := ofParam base th.parameter
  have hlaw : M.latentLaw = N.latentLaw := by
    unfold CanonicalSCM.latentLaw
    simp_rw [hP]
    rfl
  have hweights (i : Fin n) (x : Input kind dims dag C i)
      (hx : x ∈ inputCube K i) (ha : x ∈ M.domain i) :
      M.f i x = N.f i x := by
    rw [hf i ⟨x,hx⟩ ha]
    simp only [N, ofParam, paramFunction, dif_pos hx]
  have hinputs := population_intervened_inputs_mem_cube base th t muT domain hobjective
  unfold consistencyObjective trueObjective finiteIteratedObjective
  apply integral_congr_ae
  filter_upwards [hinputs] with s hs
  change (∫ u, F (intervenedEval M.toEuclideanSCM (t s).val u) ∂M.latentLaw) =
    ∫ u, F (intervenedEval N.toEuclideanSCM (t s).val u) ∂N.latentLaw
  rw [hlaw]
  apply integral_congr_ae
  filter_upwards [hs] with u hu
  apply congrArg F
  apply canonical_evalSteps_eq_of_weights_eq M N (t s).val u (n*n+n)
  intro r hr i hi
  have hx := hu i
  change structuralInput N.toEuclideanSCM i
    (evalSteps N.toEuclideanSCM (t s).val u (dag.topoOrder i)) u ∈ inputCube K i at hx
  rw [hi] at hx
  apply hweights i _ hx
  have ha := evalSteps_structuralInput_mem_domain N.toEuclideanSCM (t s).val (t s).property
    u i r hi
  exact ha


/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [latent memberships](hyp:C), and [the true population
parameter](hyp:thStar), the [limiting identified parameter set](goal) is the
singleton containing that parameter. -/
def consistencyTildeThetaInf {K L : ℝ≥0}
    (thStar : PopulationParam kind dims dag C K L) :
    Set (PopulationParam kind dims dag C K L) := -- @realizes \tilde{\Theta}_\infty(singleton containing the true cube parameter tuple)
  {thStar}

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[a population parameter](hyp:th), and [a neural causal representation](hyp:R),
the [population representation relation](goal) requires [agreement of their
structural maps on admissible cube inputs](step:1) and [equality of the
representation's latent marginals with the population cube laws embedded in
ambient spaces](step:2). -/
def populationRepresentation {K L : ℝ≥0} {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    (th : PopulationParam kind dims dag C K L)
    (R : NCMIn kind dims dag G C counts F0 F1) : Prop :=
  (∀ i (x : inputCube K i), x.val ∈ R.canonical.domain i →
    R.canonical.f i x.val = th.parameter.1.val i x) ∧
    ∀ j, (R.canonical.blockLaw j : Measure (L1Vec (dims j))) =
      (th.parameter.2 j : Measure (boundedCube (dims j) K)).map Subtype.val

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[an entropy coefficient](hyp:lam), [observations](hyp:sample), [common
simulation inputs](hyp:draws), [a population parameter](hyp:th), [a neural
causal representation](hyp:R), and [agreement of that representation with the
parameter's admissible cube maps and latent laws](hyp:_hRepresentation), the
[constraint at the population parameter](goal) is the empirical Sinkhorn
constraint evaluated using that representation. -/
def consistencyConstraintAt {K L : ℝ≥0} {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {r m : ℕ} (lam : ℝ) (sample : Fin r → Joint kind)
    (draws : Fin m → SimulationInput kind counts)
    (th : PopulationParam kind dims dag C K L)
    (R : NCMIn kind dims dag G C counts F0 F1)
    (_hRepresentation : populationRepresentation th R) : ℝ := -- @realizes g_n(Sinkhorn constraint of the retained representation on common draws)
  consistencyConstraint lam sample draws R

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [latent memberships](hyp:C), [a cube and output bound](hyp:K),
and [a Lipschitz bound](hyp:L), the [proof's population structural class](goal)
consists of maps satisfying the Lipschitz bound on each entire input cube and
the output one-norm bound at continuous nodes. -/
def proofCubePopulationClass (K L : ℝ≥0) : CubeStructuralClass kind dims dag C K :=
  cubePopulationClass K L -- @realizes \mathcal{F}_{V_i}(common Lipschitz bound L and continuous output one-norm bound K on the whole input cube)

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [latent memberships](hyp:C), [a cube and output bound](hyp:K),
and [a Lipschitz bound](hyp:L), a [proof population parameter](goal) consists
of measurable structural maps on the input cubes in the bounded Lipschitz
class, with categorical probability-vector outputs, together with latent
marginal probability laws on the bounded cubes. -/
abbrev ProofPopulationParam (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) (K L : ℝ≥0) := -- @realizes M(proof product with common Lipschitz bound L, continuous output one-norm bound K and bounded-cube marginal laws)
  CubeParam kind dims dag C K (proofCubePopulationClass K L)

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [latent memberships](hyp:C), [a first proof population
parameter](hyp:th), and [a second proof population parameter](hyp:th'), the
[proof parameter distance](goal) adds the uniform distances between their
structural maps on entire input cubes and the first Wasserstein distances
between their latent marginal laws, converting each distance to a real number. -/
def proofParamDist {K L : ℝ≥0}
    (th th' : ProofPopulationParam kind dims dag C K L) : ℝ := -- @realizes d(proof product: cube uniform structural distances plus non-Gumbel marginal Wasserstein distances)
  (∑ i, (supDistOn Set.univ (th.1.val i) (th'.1.val i)).toReal) +
    ∑ j, (wasserstein1 (th.2 j : Measure (boundedCube (dims j) K))
      (th'.2 j : Measure (boundedCube (dims j) K))).toReal

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [latent memberships](hyp:C), and [a sequence of proof population
parameter sets](hyp:Theta), the [positive-index parameter closure](goal)
contains precisely those parameters that can be approximated within every
positive tolerance in proof parameter distance by a member of some set with
index at least one. -/
def proofConsistencyParamClosure {K L : ℝ≥0}
    (Theta : ℕ → Set (ProofPopulationParam kind dims dag C K L)) :
    Set (ProofPopulationParam kind dims dag C K L) :=
  {th | ∀ eps : ℝ, 0 < eps → ∃ r, 1 ≤ r ∧ ∃ th' ∈ Theta r,
    proofParamDist th th' < eps}

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[a proof population parameter](hyp:th), and [a neural causal
representation](hyp:R), the [proof population representation relation](goal)
requires agreement on admissible cube inputs and equality of latent marginals
with the embedded cube laws. -/
def proofPopulationRepresentation {K L : ℝ≥0} {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    (th : ProofPopulationParam kind dims dag C K L)
    (R : NCMIn kind dims dag G C counts F0 F1) : Prop :=
  populationRepresentation ⟨th⟩ R

/-- The bounded population product keeps recursive structural inputs in their cubes. -/
-- @node: proof_population_intervened_inputs_mem_cube
lemma proof_population_intervened_inputs_mem_cube {K L : ℝ≥0}
    (base : CanonicalSCM kind dims dag G C)
    (th : ProofPopulationParam kind dims dag C K L)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind) (muT : Measure I)
    (domain : Set I) (hobjective : populationObjectiveDomain K domain t muT) :
    ∀ᵐ s ∂muT, ∀ᵐ u ∂(ofParam base th).latentLaw, ∀ i,
      structuralInput (ofParam base th).toEuclideanSCM i
        (evalSteps (ofParam base th).toEuclideanSCM (t s).val u (dag.topoOrder i)) u ∈
          inputCube K i := by
  exact population_intervened_inputs_mem_cube base ⟨th⟩ t muT domain hobjective

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[a cube and output bound](hyp:K), [a Lipschitz bound](hyp:L), [a sequence of
structural classes](hyp:F0N), and [a sequence of generator classes](hyp:F1N),
the [neural population parameter sets](goal) contain at each index exactly
the proof population parameters represented by a neural candidate from those
classes satisfying the output and Lipschitz restrictions. -/
def consistencyNeuralParameters (K L : ℝ≥0) {counts : Fin b → ℕ}
    (F0N : ℕ → StructuralClass kind dims dag C)
    (F1N : ℕ → GeneratorClass dims counts) :
    ℕ → Set (ProofPopulationParam kind dims dag C K L) :=
  fun r => {th | ∃ R : NCMIn kind dims dag G C counts (F0N r) (F1N r),
    restrictedCandidate K L R ∧ proofPopulationRepresentation th R}

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[a base model](hyp:base), [a sequence of parameter sets](hyp:Theta),
[interventions](hyp:t), [their index measure](hyp:muT), and [an outcome
functional](hyp:F), the [parameter objective domain condition](goal) requires
the iterated outcome expectation to be defined for every parameter in the
positive-index parameter closure. -/
def parameterObjectivesDefined (base : CanonicalSCM kind dims dag G C) {K L : ℝ≥0}
    (Theta : ℕ → Set (ProofPopulationParam kind dims dag C K L))
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) (F : Joint kind → ℝ) : Prop :=
  ∀ th ∈ proofConsistencyParamClosure Theta,
    objectiveDefined (ofParam base th).toEuclideanSCM t muT F

/-- For [node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
DAG](hyp:dag), [an observed graph](hyp:G), [latent memberships](hyp:C),
[a cube and output bound](hyp:K), [a Lipschitz bound](hyp:L), [parameter
sets at each index](hyp:Theta), [a base model](hyp:base), [the true population
parameter](hyp:thStar), [structural classes at each index](hyp:F0N),
[generator classes at each index](hyp:F1N), [simulation sample sizes](hyp:m),
[entropy coefficients](hyp:lam), [a probability law for the sampling
experiment](hyp:mu), [random observational samples](hyp:sample), [random
simulation inputs](hyp:draws), [positive simulation sample sizes](hyp:hm),
[positive entropy coefficients](hyp:hlam), [measurable independent observations
with the true model's observational law](hyp:hsample), [measurable independent
simulation inputs with the prescribed simulation law](hyp:hsim), [independence
between the observation and simulation arrays at each index](hyp:hsimind),
[interventions](hyp:t), [their probability measure](hyp:muT), [an outcome
functional](hyp:F), [an intervention-index domain](hyp:domain), [bounded
category counts and assigned coordinates on that full-measure domain](hyp:hobjective),
and [defined objectives throughout the parameter closure](hyp:hdefined), the
[consistency optimization data](goal) consist of [the positive-index parameter
closure](step:1), [the empirical Sinkhorn constraint of any retained neural
representation on the common random inputs](step:2), [the population
intervention objective on that closure](step:3), and [the singleton containing
the true parameter](step:4). -/
def consistencyThetaInf (K L : ℝ≥0)
    (Theta : ℕ → Set (ProofPopulationParam kind dims dag C K L)) -- @realizes \Theta_n(positive-index neural cube parameter sets with common Lipschitz bound L)
    (base : CanonicalSCM kind dims dag G C)
    (thStar : ProofPopulationParam kind dims dag C K L) -- @realizes \theta^*(the true cube population parameter with the same common bounds)
    {counts : Fin b → ℕ} (F0N : ℕ → StructuralClass kind dims dag C)
    (F1N : ℕ → GeneratorClass dims counts) (m : ℕ → ℕ) (lam : ℕ → ℝ)
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (hm : ∀ r, 0 < m r) (hlam : ∀ r, 0 < lam r)
    (hsample : ∀ r, ProbabilityTheory.iIndepFun (sample r) mu ∧
      ∀ i, Measurable (sample r i) ∧ mu.map (sample r i) =
        observationalLaw (ofParam base thStar).toEuclideanSCM)
    (hsim : ∀ r, ProbabilityTheory.iIndepFun (draws r) mu ∧
      ∀ i, Measurable (draws r i) ∧ mu.map (draws r i) = simulationInputLaw kind counts)
    (hsimind : ∀ r, ProbabilityTheory.IndepFun (fun w => fun i => sample r i w)
      (fun w => fun i => draws r i w) mu)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ) -- @realizes \mu_T(probability law of intervention values)
    (domain : Set I) (hobjective : populationObjectiveDomain K domain t muT)
    (hdefined : parameterObjectivesDefined base Theta t muT F) :=
  (proofConsistencyParamClosure Theta, -- @realizes \Theta_\infty(positive-index closure using cube-domain paramDist)
    (fun r (th : ProofPopulationParam kind dims dag C K L)
      (R : NCMIn kind dims dag G C counts (F0N r) (F1N r))
      (_hRepresentation : proofPopulationRepresentation th R) (w : Omega) =>
        consistencyConstraint (lam r) (fun i => sample r i w)
          (fun i => draws r i w) R), -- @realizes g_n(chosen representation evaluated on common independent draws)
    (fun th : ↥(proofConsistencyParamClosure Theta) =>
      trueObjective (ofParam base th.val).toEuclideanSCM t muT F (hdefined th.val th.property)), -- @realizes f(population intervention objective of the cube tuple)
    ({thStar} : Set (ProofPopulationParam kind dims dag C K L))) -- @realizes \tilde{\Theta}_\infty(true population parameter singleton)

variable {M : Type*}
/-- For [parameter sets at each index](hyp:Theta), [constraint functions at
each index](hyp:gn), [a nonnegative tolerance multiplier](hyp:Lg), [an
approximation tolerance sequence](hyp:eps), [an additional tolerance
sequence](hyp:delta), and [an index](hyp:r), the [finite-level feasible
set](goal) contains parameters in that index's set whose constraint is at most
the multiplier times the approximation tolerance plus the additional tolerance. -/
def convgOptFeasible (Theta : ℕ → Set M) (gn : ℕ → M → ℝ) -- @realizes g_n(level-n constraint with radius L_g epsilon_n plus delta_n) -- @realizes L_g(level-n constraint with radius L_g epsilon_n plus delta_n)
    (Lg : ℝ≥0) (eps delta : ℕ → ℝ) (r : ℕ) : Set M :=
  {th ∈ Theta r | gn r th ≤ Lg * eps r + delta r}
/-- For [a limiting parameter set](hyp:ThetaInf) and [a constraint
function](hyp:g), the [limiting feasible set](goal) contains exactly the
parameters in that set whose constraint equals zero. -/
def convgOptFeasibleInf (ThetaInf : Set M) (g : M → ℝ) : Set M := {th ∈ ThetaInf | g th = 0} -- @realizes \tilde{\Theta}_\infty(zero-constraint feasible subset of the supplied parameter set) -- @realizes g(zero-constraint feasible subset of the supplied parameter set)
-- @node: def:prop-convg-opt-values
/-- For [an objective function](hyp:f), [parameter sets at each index](hyp:Theta),
[constraint functions at each index](hyp:gn), [a nonnegative tolerance
multiplier](hyp:Lg), [an approximation tolerance sequence](hyp:eps), [an
additional tolerance sequence](hyp:delta), and [an index](hyp:r), the
[finite-level optimal value](goal) is the real infimum of the objective values
over parameters in that index's set whose constraint is at most the multiplier
times the approximation tolerance plus the additional tolerance. -/
def convgOptValue (f : M → ℝ) (Theta : ℕ → Set M) (gn : ℕ → M → ℝ) -- @realizes f_n^*(infimum of the finite-level objective on its feasible set)
    (Lg : ℝ≥0) (eps delta : ℕ → ℝ) (r : ℕ) : ℝ :=
  sInf (f '' convgOptFeasible Theta gn Lg eps delta r)
/-- For [an objective function](hyp:f), [a limiting parameter set](hyp:ThetaInf),
and [a constraint function](hyp:g), the [limiting optimal value](goal) is the
real infimum of objective values over parameters in that set with zero
constraint. -/
def convgOptLimitValue (f : M → ℝ) (ThetaInf : Set M) (g : M → ℝ) : ℝ := -- @realizes f^*(infimum over either supplied limiting feasible region) -- @realizes \tilde{f}^*(infimum over either supplied limiting feasible region)
  sInf (f '' convgOptFeasibleInf ThetaInf g)

/-- Given [a common objective function](hyp:f), [a sequence of parameter
sets](hyp:Theta), [a limiting parameter set](hyp:ThetaInf), [an alternative
limiting parameter set](hyp:tildeTheta), [a sequence of constraint
functions](hyp:gn), [a limiting constraint function](hyp:g), [a nonnegative
tolerance multiplier](hyp:Lg), [an approximation tolerance sequence](hyp:eps),
and [an additional tolerance sequence](hyp:delta), the [collection of
optimization problems](goal) consists of the common objective and each feasible
region paired with the infimum of its objective values: at each finite index,
the constraint is at most the multiplier times the approximation tolerance plus
the additional tolerance; in each limiting parameter set, the limiting
constraint equals zero.

Under attainment these infima are the displayed minima. -/
-- @node: def:prop-convg-opt-problems
def convgOptProblems (f : M → ℝ) (Theta : ℕ → Set M)
    (ThetaInf tildeTheta : Set M) (gn : ℕ → M → ℝ) (g : M → ℝ)
    (Lg : ℝ≥0) (eps delta : ℕ → ℝ) :
    (M → ℝ) × (ℕ → Set M × ℝ) × (Set M × ℝ) × (Set M × ℝ) :=
  (f, (fun r => (convgOptFeasible Theta gn Lg eps delta r,
      convgOptValue f Theta gn Lg eps delta r)),
    (convgOptFeasibleInf ThetaInf g, convgOptLimitValue f ThetaInf g),
    (convgOptFeasibleInf tildeTheta g, convgOptLimitValue f tildeTheta g))

end
end Papers.TbsNeuralCausalPi
