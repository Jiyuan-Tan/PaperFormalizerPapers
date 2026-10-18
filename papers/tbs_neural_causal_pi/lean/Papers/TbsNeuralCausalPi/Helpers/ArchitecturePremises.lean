module
public import Papers.TbsNeuralCausalPi.Helpers.CandidateAssembly
public import Papers.TbsNeuralCausalPi.Setup.Optimization
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Model
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Generators
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
/-! # Upstream premises for structural and latent architecture constructions -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped NNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

-- @node: ArchitectureConstructionPremises
/-- For [a canonical causal model M](hyp:M), [nonnegative mechanism regularity
and output bounds L and K](hyp:L,K), [numbers of latent components](hyp:counts),
[component sets](hyp:sets), [their chart dimensions](hyp:dC), and [a nonnegative
chart regularity bound](hyp:Lchart), [the architecture construction
premises](goal) require [independent latent blocks](step:1), [a decomposition
of latent noise into blocks and Gumbel noise](step:2), [categorical mechanisms
given by Gumbel argmax](step:3), [variables bounded at K](step:4), [generator
regularity of the latent laws](step:5), [positive maximum input and latent
dimensions excluding Gumbel noise](step:6), [unit-cube structural
domains](step:7), [L-Lipschitz continuous mechanisms](step:8), [L-Lipschitz
categorical propensities](step:9), [L-Lipschitz full structural maps on their
unrestricted domains](step:10), [continuous outputs with one-norm at most K
on those domains](step:11), [latent laws supported on the specified finite
components](step:12), [Lipschitz homeomorphisms for the component charts](step:13),
[lower-bound domination of each conditional component law](step:14), and
[vanishing of each pulled-back component law on the chart boundary](step:15). -/
def ArchitectureConstructionPremises (M : CanonicalSCM kind dims dag G C)
    (L K : ℝ≥0) (counts : Fin b → ℕ)
    (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0) : Prop :=
  LatentBlocksIndependent M.toEuclideanSCM ∧
    LatentGumbelDecomposition M.toEuclideanSCM ∧
    CategoricalGumbelArgmax M.toEuclideanSCM M.f ∧
    VariablesBoundedAt M.toEuclideanSCM K ∧
    LatentLawsGeneratorRegular M ∧ NonGumbelMaxDimsPositive M.toEuclideanSCM ∧
    StructuralDomainsUnitCubes M.toEuclideanSCM ∧
    ContinuousMechanismsLipschitz M.toEuclideanSCM L ∧
    CategoricalPropensityLipschitz M.toEuclideanSCM M.f L ∧
    (∀ i, LipschitzOnWith L (M.f i) (M.domain i none)) ∧
    (∀ i d, kind i = Sum.inl d → ∀ x ∈ M.domain i none, ‖M.f i x‖ ≤ K) ∧ -- @realizes f_i(continuous uniform one-norm output bound on the full structural input domain)
    (∀ j, SupportFiniteComponents (M.blockLaw j : Measure _) (sets j)) ∧
    (∀ j, ComponentsLipschitzHomeomorphic (sets j) (dC j) Lchart) ∧
    (∀ j i, LowerBoundDomination (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (sets j i)) (sets j i) Lchart) ∧
    (∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (sets j i)) (sets j i) Lchart)

end
end Papers.TbsNeuralCausalPi
