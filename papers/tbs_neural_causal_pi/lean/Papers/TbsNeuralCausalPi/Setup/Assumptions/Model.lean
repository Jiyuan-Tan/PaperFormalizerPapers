module
public import Papers.TbsNeuralCausalPi.Setup.SCM
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.MetricSpace.Lipschitz
/-! # Model assumptions
Independence and mechanism regularity are explicit paper inputs, including when
applied to the Euclidean coercion of a canonical model.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
-- @env: S1
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- Given [the continuous or categorical type of each node](hyp:kind) and [the
dimensions of the non-Gumbel latent blocks](hyp:dims), the [dimension assigned
to an exogenous block index](goal) is [its specified block dimension for a
non-Gumbel index](step:1) and [the node's intrinsic noise dimension for a node
index](step:2). -/
def latentBlockDim (kind : Fin n → NodeKind) (dims : Fin b → ℕ) : Fin b ⊕ Fin n → ℕ
  | .inl j => dims j
  | .inr i => noiseDim (kind i)
/-- Given [the node types](hyp:kind), [the non-Gumbel block dimensions](hyp:dims),
[an index selecting a latent block or a node's noise](hyp:j), and [a full
exogenous vector](hyp:u), the [selected exogenous projection](goal) returns
[the non-Gumbel block at a block index](step:1) or [the categorical noise vector
at a node index](step:2). -/
def exogenousProjection (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (j : Fin b ⊕ Fin n) (u : Exogenous kind dims) : L1Vec (latentBlockDim kind dims j) :=
  match j with
  | .inl j => blockProjection j u
  | .inr i => categoricalNoise i u
-- @node: ass:assump-independence-u
/-- For [a Euclidean structural causal model](hyp:M), [latent-block
independence](goal) means that all named non-Gumbel blocks and node-specific
noise vectors are mutually independent under its exogenous law. -/
def LatentBlocksIndependent (M : EuclideanSCM kind dims) : Prop :=
  iIndepFun (namedLatent M) M.latentLaw

-- @node: ass:assump-categorical-rv-latents
/-- For [a Euclidean structural causal model](hyp:M), the [latent and categorical
noise index decomposition](goal) identifies [the indices of non-Gumbel latent
blocks](step:1) and [the indices of categorical nodes' noise vectors](step:2),
then requires [these two sets to cover the index space and be disjoint](step:3). -/
def LatentGumbelDecomposition (M : EuclideanSCM kind dims) : Prop :=
  let Blocks : Set (Fin b ⊕ {i : Fin n // (kind i).isRight}) :=
    Set.range (Sum.inl : Fin b → Fin b ⊕ {i : Fin n // (kind i).isRight})
  let Noises : Set (Fin b ⊕ {i : Fin n // (kind i).isRight}) :=
    Set.range (Sum.inr : {i : Fin n // (kind i).isRight} → Fin b ⊕ {i : Fin n // (kind i).isRight})
  Set.univ = Blocks ∪ Noises ∧ Disjoint Blocks Noises

/-- For [a Euclidean structural causal model](hyp:M), [category weight
functions](hyp:p), and [optional coordinate bounds on structural inputs](hyp:bound),
the [categorical weight positivity condition](goal) requires every categorical
node's weights to be nonnegative and their sum strictly positive at every input
in its bounded admissible domain. -/
def CategoricalWeightsPositiveOn (M : EuclideanSCM kind dims) (p : MechanismWeights M)
    (bound : Option (ℝ × ℝ) := none) : Prop :=
  ∀ i k, kind i = Sum.inr k → ∀ x ∈ M.domain i bound,
    (∀ j, 0 ≤ (p i x).ofLp j) ∧ 0 < ∑ j, (p i x).ofLp j

-- @node: ass:pin-fix-c0174608
/-- For [a Euclidean structural causal model](hyp:M) and [category weight
functions](hyp:p), [categorical weight positivity](goal) requires nonnegative
weights with strictly positive sum at every admissible categorical input,
without additional coordinate bounds. -/
def CategoricalWeightsPositive (M : EuclideanSCM kind dims) (p : MechanismWeights M) : Prop :=
  CategoricalWeightsPositiveOn M p none

/-- From [a joint vector of observed node values](hyp:v), [a node index](hyp:i),
and [a coordinate index within that node's value](hyp:j), the [node coordinate](goal)
extracts that real-valued entry. -/
def nodeCoordinate (v : Joint kind) (i : Fin n) (j : Fin (valueDim (kind i))) : ℝ :=
  v.ofLp ⟨i,j⟩
/-- For [a Euclidean structural causal model](hyp:M), [a node](hyp:i), and [an
exogenous realization](hyp:u), the [observational structural input](goal)
combines the node's parent values from evaluation without intervention with
its designated latent inputs from that realization. -/
def structuralInputRV (M : EuclideanSCM kind dims) (i : Fin n)
    (u : Exogenous kind dims) := structuralInput M i (intervenedEval M (fun _ => none) u) u

/-- For [a Euclidean structural causal model](hyp:M) and [category weight
functions](hyp:p), the [categorical conditional-law condition](goal) requires,
for every categorical node and category, that the weight divided by the sum of
weights at the observational structural input equal almost surely the conditional
probability of that category given this input, under the model's exogenous law. -/
def categoricalConditionalLaw (M : EuclideanSCM kind dims) (p : MechanismWeights M) : Prop :=
  ∀ i k (h : kind i = Sum.inr k) (j : Fin k),
    (fun u => (p i (structuralInputRV M i u)).ofLp
      (Fin.cast (congrArg outputDim h).symm j) /
        ∑ l, (p i (structuralInputRV M i u)).ofLp l) =ᵐ[M.latentLaw]
      M.latentLaw[fun u => if M.categoricalLabel i k h (structuralInputRV M i u)
      (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim h).symm j))) = j
        then (1:ℝ) else 0 | MeasurableSpace.comap (structuralInputRV M i) (borel _)]
/-- For [a Euclidean structural causal model](hyp:M), [category weight
functions](hyp:p), and [optional structural-input coordinate bounds](hyp:bound),
the [categorical Gumbel-argmax condition](goal) requires [nonnegative weights
with positive sum on each bounded admissible domain](step:1), [normalized
observational weights equal to conditional category probabilities](step:2),
[categorical labels on those domains to select the first maximizer of log weight
plus noise, defaulting to the first category if no maximizer is returned](step:3),
and [each categorical node's noise vector to have a product of standard Gumbel
laws](step:4). -/
def CategoricalGumbelArgmaxOn (M : EuclideanSCM kind dims) (p : MechanismWeights M)
    (bound : Option (ℝ × ℝ) := none) : Prop :=
  CategoricalWeightsPositiveOn M p bound ∧ categoricalConditionalLaw M p ∧
    (∀ i k (h : kind i = Sum.inr k) x, x ∈ M.domain i bound →
      ∀ g : Fin k → ℝ, M.categoricalLabel i k h x (WithLp.toLp 1 g) =
        (firstArgmax (fun j : Fin k =>
          extendedLog ((p i x).ofLp (Fin.cast (congrArg outputDim h).symm j)) +
            (g j : EReal))).getD
              ⟨0, M.categoricalPositive i k h⟩) ∧
    ∀ i k (h : kind i = Sum.inr k),
      M.latentLaw.map (fun u => (categoricalNoise i u).ofLp ∘
        Fin.cast (congrArg noiseDim h).symm) = Measure.pi (fun _ : Fin k => gumbelLaw)

-- @node: ass:assump-categorical-rv-generation
/-- For [a Euclidean structural causal model](hyp:M) and [category weight
functions](hyp:p), the [categorical Gumbel-argmax condition without additional
input bounds](goal) requires positive total nonnegative weights, the normalized
conditional-law identity, first-argmax generation from log weights plus noise,
and product standard Gumbel noise laws on the full admissible domains. -/
def CategoricalGumbelArgmax (M : EuclideanSCM kind dims) (p : MechanismWeights M) : Prop :=
  CategoricalGumbelArgmaxOn M p none

/-- For [a Euclidean structural causal model](hyp:M), [a common nonnegative
Lipschitz bound](hyp:Lf), and [optional structural-input coordinate
bounds](hyp:bound), [continuous-mechanism regularity on these domains](goal)
requires every continuous node's structural map to obey that Lipschitz bound
on its bounded admissible input domain, using the one-norm. -/
def ContinuousMechanismsLipschitzOn (M : EuclideanSCM kind dims) (Lf : ℝ≥0)
    (bound : Option (ℝ × ℝ) := none) : Prop :=
  ∀ i d, kind i = Sum.inl d → LipschitzOnWith Lf (M.continuousMap i) (M.domain i bound) -- @realizes L_f(nonnegative common one-norm Lipschitz bound for continuous structural maps)
-- @node: ass:assump-lip-and-bounded-continuous
/-- For [a Euclidean structural causal model](hyp:M) and [a common nonnegative
Lipschitz bound](hyp:Lf), [continuous-mechanism regularity](goal) requires every
continuous structural map to obey that bound in the one-norm on its full
admissible input domain, without additional coordinate bounds. -/
def ContinuousMechanismsLipschitz (M : EuclideanSCM kind dims) (Lf : ℝ≥0) : Prop :=
  ContinuousMechanismsLipschitzOn M Lf none

/-- For [a Euclidean structural causal model](hyp:M), [category propensity
functions](hyp:p), [a common nonnegative Lipschitz bound](hyp:Lf), and [optional
structural-input coordinate bounds](hyp:bound), [categorical propensity
regularity](goal) requires [each categorical propensity vector to obey the bound
in the one-norm on its bounded admissible domain](step:1) and [each propensity
coordinate at the observational structural input to equal almost surely the
conditional probability of its category given that input](step:2). -/
def CategoricalPropensityLipschitzOn (M : EuclideanSCM kind dims) (p : MechanismWeights M) (Lf : ℝ≥0)
    (bound : Option (ℝ × ℝ) := none) : Prop :=
  (∀ i k, kind i = Sum.inr k → LipschitzOnWith Lf (p i) (M.domain i bound)) ∧ -- @realizes L_f(the same nonnegative one-norm bound for categorical propensity maps)
    ∀ i k (h : kind i = Sum.inr k) (j : Fin k),
      (fun u => (p i (structuralInputRV M i u)).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) =ᵐ[M.latentLaw]
        M.latentLaw[fun u => if M.categoricalLabel i k h (structuralInputRV M i u)
      (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim h).symm j))) = j
          then (1:ℝ) else 0 | MeasurableSpace.comap (structuralInputRV M i) (borel _)]
-- @node: ass:assump-lip-and-bounded-categorical
/-- For [a Euclidean structural causal model](hyp:M), [category propensity
functions](hyp:p), and [a common nonnegative Lipschitz bound](hyp:Lf),
[categorical propensity regularity without additional input bounds](goal)
requires the propensity vectors to obey that bound in the one-norm on full
admissible domains and their observational coordinates to equal conditional
category probabilities almost surely. -/
def CategoricalPropensityLipschitz (M : EuclideanSCM kind dims) (p : MechanismWeights M) (Lf : ℝ≥0) : Prop :=
  CategoricalPropensityLipschitzOn M p Lf none

/-- For [a Euclidean structural causal model](hyp:M) and [a real bound](hyp:K),
the [bounded-variable condition at this bound](goal) requires [the bound to be
strictly positive](step:1) and [almost surely under the exogenous law, every
observed coordinate evaluated without intervention and every non-Gumbel latent
coordinate to have absolute value at most the bound](step:2). -/
def VariablesBoundedAt (M : EuclideanSCM kind dims) (K : ℝ) : Prop :=
  0 < K ∧ ∀ᵐ u ∂M.latentLaw, -- @realizes K(positive deterministic bound; random variables satisfy it almost surely)
    (∀ i j, |nodeCoordinate (intervenedEval M (fun _ => none) u) i j| ≤ K) ∧ -- @realizes V_i(coordinatewise sup-norm observed bound on the joint law)
      ∀ j k, |(blockProjection j u).ofLp k| ≤ K -- @realizes U_j(coordinatewise non-Gumbel block bound)
-- @node: ass:assump-lip-and-bounded-bound
/-- For [a Euclidean structural causal model](hyp:M), [boundedness of the
variables](goal) means that some positive deterministic constant bounds almost
surely the absolute values of all observational node coordinates and all
non-Gumbel latent coordinates. -/
def VariablesBounded (M : EuclideanSCM kind dims) : Prop :=
  ∃ K : ℝ, VariablesBoundedAt M K

/-- For [a Euclidean structural causal model](hyp:M) and [a node](hyp:i), the
[structural approximation domain](goal) is the closed unit cube in that node's
structural-input space. -/
def structuralApproximationDomain (M : EuclideanSCM kind dims) (i : Fin n) :
    Set (StructuralInput kind dims M.dag M.incidence i) := structuralCube -- @realizes f_i(closed unit-cube approximation domain)

/-- For [a Euclidean structural causal model](hyp:M) and [an intervention](hyp:t),
[compatibility with structural cubes](goal) means that every coordinate of an
assigned value at a node that is a parent of another node lies between zero and
one, inclusive. Parent labels are used without rescaling. -/
def InterventionInStructuralCubes (M : EuclideanSCM kind dims)
    (t : LawIntervention kind) : Prop :=
  ∀ i (p : {p // p ∈ M.dag.parents i}) v, (t.val p.val) = some v →
    ∀ j, v.ofLp j ∈ Set.Icc (0 : ℝ) 1 -- @realizes \boldsymbol{t}(assigned parent coordinates lie in the closed unit cubes)

-- @node: ass:relu-approximation-domain
/-- For [a Euclidean structural causal model](hyp:M), the [unit-cube structural
domain condition](goal) says that each node's approximation domain consists
exactly of structural inputs with every coordinate between zero and one, inclusive.

This convention imposes
no condition on the input law or on realized inputs under interventions. -/
def StructuralDomainsUnitCubes (M : EuclideanSCM kind dims) : Sort 0 :=
  ∀ i, structuralApproximationDomain M i =
    {x | ∀ j, x.ofLp j ∈ Set.Icc (0 : ℝ) 1} -- @realizes f_i(approximation domain equals the closed unit cube, independently of input laws)
/-- For [a Euclidean structural causal model](hyp:M), [positivity of the maximum
dimensions](goal) requires [the maximum structural-input dimension to be at
least one](step:1) and [the maximum non-Gumbel latent-block dimension to be at
least one](step:2). -/
def NonGumbelMaxDimsPositive (M : EuclideanSCM kind dims) : Prop :=
  1 ≤ maxInDim M ∧ 1 ≤ maxLatentDim M
end
end Papers.TbsNeuralCausalPi
