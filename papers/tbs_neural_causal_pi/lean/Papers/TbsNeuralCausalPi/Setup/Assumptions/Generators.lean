module
public import Papers.TbsNeuralCausalPi.Setup.SCM
public import Mathlib.Topology.Connected.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.ConditionalProbability
/-! # Support charts and domination of cube Lebesgue measure -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
-- @env: S2
variable {d N : ℕ}
/-- For [a measure on a finite-dimensional vector space](hyp:P), its [support is
the set of points whose every open neighborhood has nonzero measure](goal). -/
def measureSupport (P : Measure (L1Vec d)) : Set (L1Vec d) :=
  {x | ∀ U : Set (L1Vec d), IsOpen U → x ∈ U → P U ≠ 0}
-- @node: ass:assump-support-components
/-- For [a measure](hyp:P) and [a finite indexed family of sets](hyp:C), the
[finite-component support condition](goal) requires that [the support equals
their union](step:1), [distinct indices specify distinct sets](step:2), and
[each set is the connected component of some point in the support](step:3). -/
def SupportFiniteComponents (P : Measure (L1Vec d)) (C : Fin N → Set (L1Vec d)) : Prop := -- @realizes \mathbb{P}(support is the union of the finitely indexed connected components) -- @realizes C_i(support is the union of the finitely indexed connected components)
  measureSupport P = ⋃ i, C i ∧ Function.Injective C ∧
    ∀ i, ∃ x ∈ measureSupport P, C i = connectedComponentIn (measureSupport P) x
-- @node: ass:assump-support-homeomorphisms
/-- For [a finite family of component sets](hyp:C), [their assigned intrinsic
dimensions](hyp:dC), and [a common nonnegative Lipschitz bound](hyp:L), the
[component chart condition](goal) requires a homeomorphism from the unit cube
of each assigned dimension onto its component, Lipschitz with that bound. -/
def ComponentsLipschitzHomeomorphic (C : Fin N → Set (L1Vec d)) -- @realizes g_2^i(component charts between the prescribed unit cubes and support sets)
    (dC : Fin N → ℕ) (L : ℝ≥0) : Prop :=
  ∀ i, ∃ f : homeoClass (unitCube (dC i)) (C i), LipschitzWith L f
/-- For [a measure](hyp:P), [a target set](hyp:K), [a homeomorphism from a unit
cube onto that set](hyp:f), [a Lipschitz bound](hyp:L), and [a real domination
constant](hyp:Cf), the [chart domination condition](goal) requires [compactness
of the target](step:1), [measure one for the target](step:2), [strict positivity
of the constant](step:3), [the distance between chart images to be at most L times the distance between their cube inputs](step:4),
and [the measure of every measurable cube subset's image to be at least the
constant times its cube Lebesgue measure](step:5). -/
def lowerBoundDominationAt {D d : ℕ} (P : Measure (L1Vec D)) -- @realizes C_f(positive cube-Lebesgue domination constant for all measurable cube subsets in the stated ambient dimension) -- @realizes B(positive cube-Lebesgue domination constant for all measurable cube subsets in the stated ambient dimension)
    (K : Set (L1Vec D)) (f : homeoClass (unitCube d) K) (L : ℝ≥0) (Cf : ℝ) : Prop :=
  IsCompact K ∧ P K = 1 ∧ 0 < Cf ∧ LipschitzWith L f ∧ -- @realizes C_f(strictly positive domination constant for the selected chart)
    ∀ B : Set (L1Vec d), MeasurableSet B → B ⊆ unitCube d →
      ENNReal.ofReal Cf *
        ((Measure.pi (fun _ : Fin d => volume)).map (WithLp.toLp 1)) B ≤
          P (Subtype.val '' (f '' (Subtype.val ⁻¹' B)))
-- @node: ass:assumption-lower-bound-domination
/-- For [a measure](hyp:P), [a target set](hyp:K), and [a nonnegative Lipschitz
bound](hyp:L), [lower-bound domination](goal) means that some homeomorphism
from the unit cube onto the target and some positive constant satisfy the chart
domination condition: the target is compact with measure one, the chart obeys
the bound, and image measures dominate the constant times cube Lebesgue measure. -/
def LowerBoundDomination {D d : ℕ} (P : Measure (L1Vec D))
    (K : Set (L1Vec D)) (L : ℝ≥0) : Prop :=
  ∃ f : homeoClass (unitCube d) K, ∃ Cf : ℝ, -- @realizes C_f(positive domination constant for the existentially selected chart, constrained by lowerBoundDominationAt)
    lowerBoundDominationAt P K f L Cf

/-- Given [a homeomorphism from a unit cube onto a target set](hyp:f) and [an
ambient point](hyp:x), the [extended inverse chart](goal) returns the inverse
image of the point when it belongs to the target, and the zero vector otherwise. -/
def chartInverse {D d : ℕ} {K : Set (L1Vec D)}
    (f : homeoClass (unitCube d) K) (x : L1Vec D) : L1Vec d :=
  if hx : x ∈ K then (f.symm ⟨x,hx⟩).val else 0
-- @node: ass:assumption-lower-bound-boundary
/-- For [a measure](hyp:P), [a target set](hyp:K), and [a Lipschitz bound](hyp:L),
the [boundary-vanishing pullback condition](goal) requires a cube homeomorphism
and a constant such that [the chart domination condition holds](step:1) and
[in positive cube dimension the measure transported through the extended inverse
chart assigns zero mass to the cube's boundary](step:2). -/
def PullbackVanishesOnBoundary {D d : ℕ} (P : Measure (L1Vec D))
    (K : Set (L1Vec D)) (L : ℝ≥0) : Prop :=
  ∃ f : homeoClass (unitCube d) K, ∃ Cf : ℝ,
    lowerBoundDominationAt P K f L Cf ∧
      (0 < d → (P.map (chartInverse f)) (frontier (unitCube d)) = 0)


/-- For [a measure](hyp:P), [generator regularity](goal) means that there exist
finitely many component sets, assigned intrinsic dimensions, and a common
Lipschitz bound such that [the sets are exactly the distinct connected components
of the support](step:1), [each admits a unit-cube homeomorphism obeying the
bound](step:2), and [on every component the conditional measure admits cube
Lebesgue lower-bound domination and an inverse chart whose transported measure
vanishes on the cube boundary in positive dimension](step:3). -/
def GeneratorRegular (P : Measure (L1Vec d)) : Prop :=
  ∃ N : ℕ, ∃ C : Fin N → Set (L1Vec d), ∃ dC : Fin N → ℕ, ∃ L : ℝ≥0,
    SupportFiniteComponents P C ∧ ComponentsLipschitzHomeomorphic C dC L ∧
    ∀ i, LowerBoundDomination (d := dC i) (ProbabilityTheory.cond P (C i)) (C i) L ∧
      PullbackVanishesOnBoundary (d := dC i) (ProbabilityTheory.cond P (C i)) (C i) L
/-- For [a canonical structural causal model](hyp:M), [latent-law generator
regularity](goal) requires every non-Gumbel latent block law to satisfy generator
regularity, including finite support components, Lipschitz cube charts,
lower-bound domination, and vanishing transported boundary mass. -/
def LatentLawsGeneratorRegular {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}
    (M : CanonicalSCM kind dims dag G C) : Prop :=
  ∀ j, GeneratorRegular (M.blockLaw j : Measure (L1Vec (dims j)))
end
end Papers.TbsNeuralCausalPi
