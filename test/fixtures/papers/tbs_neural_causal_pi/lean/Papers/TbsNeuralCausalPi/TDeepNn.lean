module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Conventions
public import Papers.TbsNeuralCausalPi.TApproximation
public import Papers.TbsNeuralCausalPi.TCorFix3c402872
public import Papers.TbsNeuralCausalPi.Helpers.DeepCommonBudgets
public import Papers.TbsNeuralCausalPi.Helpers.DeepModelAssembly
public import Papers.TbsNeuralCausalPi.Helpers.BoxApproximation
public import Papers.TbsNeuralCausalPi.Helpers.StructuralGateCompatibility
public import Papers.TbsNeuralCausalPi.Helpers.CubeDimension
/-! # Existence of one neural approximation for all interventions -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- For [reference and approximating canonical models](hyp:M,Mhat), with
[a nonnegative Lipschitz bound](hyp:L) and [a variable bound](hyp:K), suppose [the reference model
belongs to the canonical class with that bound on the unit interval](hyp:hclass),
[its latent blocks are independent](hyp:hind), [its latent noise admits the
Gumbel decomposition](hyp:hdecomp), [its categorical mechanisms use Gumbel
argmax on the unit interval](hyp:hcat), [its continuous mechanisms are Lipschitz
there](hyp:hcont), [its categorical propensities are Lipschitz there](hyp:hprop), [its variables
are bounded by the given bound](hyp:hbound), [its structural domains are unit
cubes](hyp:hdomain), and [the chosen intervention](hyp:t) [stays within those cubes](hyp:ht).
For [a chosen node](hyp:i),
Then [the expected mechanism error at the chosen node, restricted to structural
inputs in the approximation cube, is at most the output dimension times the
uniform distance between the reference and approximating mechanisms on that
cube](goal). -/
-- @node: deep_ncm_intervened_error_le
lemma deep_ncm_intervened_error_le
    (M Mhat : CanonicalSCM kind dims dag G C) (L : ℝ≥0) (K : ℝ)
    (hclass : M ∈ canonicalClass (domainLipClass M L (some (0, 1))))
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hdecomp : LatentGumbelDecomposition M.toEuclideanSCM)
    (hcat : CategoricalGumbelArgmaxOn M.toEuclideanSCM M.f (some (0, 1)))
    (hcont : ContinuousMechanismsLipschitzOn M.toEuclideanSCM L (some (0, 1)))
    (hprop : CategoricalPropensityLipschitzOn M.toEuclideanSCM M.f L (some (0, 1)))
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hdomain : StructuralDomainsUnitCubes M.toEuclideanSCM)
    (t : LawIntervention kind) (ht : InterventionInStructuralCubes M.toEuclideanSCM t) (i : Fin n) :
    (∫⁻ u in {u | structuralInput M.toEuclideanSCM i
        (intervenedEval M.toEuclideanSCM t.val u) u ∈ structuralApproximationDomain M.toEuclideanSCM i},
      ENNReal.ofReal ‖M.f i (structuralInput M.toEuclideanSCM i
        (intervenedEval M.toEuclideanSCM t.val u) u) -
      Mhat.f i (structuralInput M.toEuclideanSCM i
        (intervenedEval M.toEuclideanSCM t.val u) u)‖ ∂M.latentLaw) ≤
      (outputDim (kind i) : ℝ≥0∞) * supDistOn structuralCube (M.f i) (Mhat.f i) := by
  let := M.latentLaw_probability
  let E := (outputDim (kind i) : ℝ≥0∞) *
    supDistOn structuralCube (M.f i) (Mhat.f i)
  calc
    _ ≤ ∫⁻ u in {u | structuralInput M.toEuclideanSCM i
        (intervenedEval M.toEuclideanSCM t.val u) u ∈
          structuralApproximationDomain M.toEuclideanSCM i}, E ∂M.latentLaw := by
      apply setLIntegral_mono measurable_const
      intro u hu
      have herr := approximation_edist_le_dim_supDistOn structuralCube (M.f i) (Mhat.f i) hu
      simpa only [edist_dist, dist_eq_norm] using herr
    _ ≤ E := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact mul_le_of_le_one_right' prob_le_one

/-- For [a canonical model](hyp:M), [latent component counts](hyp:counts),
[latent support components](hyp:sets), [their intrinsic dimensions](hyp:dC),
and [a common chart Lipschitz bound](hyp:Lchart), suppose [each block law has
those finitely many support components](hyp:hsupp), [the components have
Lipschitz homeomorphisms from cubes of those dimensions](hyp:hhomeo),
[the conditional component laws satisfy lower-bound domination](hyp:hdom),
and [their pullbacks vanish on cube boundaries](hyp:hboundary); assume also
[the structural neural approximation theorem](hyp:hgate). For [a chosen
latent block](hyp:j), [that
latent block admits positive architecture and error constants, minimum depths,
and a temperature ceiling below one, such that all sufficiently large depths
and smaller positive temperatures admit a three-part generator with the exact
component masses, first blocks mapping into component cubes, second blocks
mapping zero-dimensional cubes into their components, and Wasserstein error
bounded by a constant times the sum of both depths to power minus two divided
by the maximum positive component dimension, plus temperature minus temperature
times its logarithm; the depth terms vanish when every component has dimension
zero](goal). -/
-- @node: deep_ncm_latent_component_approximation
lemma deep_ncm_latent_component_approximation
    (M : CanonicalSCM kind dims dag G C)
    (counts : Fin b → ℕ) (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hsupp : ∀ j, SupportFiniteComponents (M.blockLaw j : Measure _) (sets j))
    (hhomeo : ∀ j, ComponentsLipschitzHomeomorphic (sets j) (dC j) Lchart)
    (hdom : ∀ j i, LowerBoundDomination (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (sets j i)) (sets j i) Lchart)
    (hboundary : ∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (sets j i)) (sets j i) Lchart)
    (hgate : YarotskyStructuralApprox) (j : Fin b) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧ ∃ A : ℝ, 0 < A ∧
      ∃ B : ℕ, 1 ≤ B ∧ ∃ tauBar : ℝ, 0 < tauBar ∧ tauBar < 1 ∧
      ∀ L1 L2 : ℕ, B ≤ L1 → B ≤ L2 → ∀ tau : ℝ, 0 < tau → tau < tauBar →
        ∃ q : ThreePartGenerator (counts j) (dims j) (dC j)
          (c1 * max 1 (Finset.univ.sup (dC j))) L1
          (c2 * dims j * max 1 (Finset.univ.sup (dC j))) L2 tau,
          (∀ i, q.p i = ((M.blockLaw j : Measure _) (sets j i)).toReal) ∧
          (∀ i, Set.MapsTo (q.g1 i).eval (unitCube 1) (unitCube (dC j i))) ∧
          (∀ i, dC j i = 0 → Set.MapsTo (q.g2 i).eval (unitCube (dC j i)) (sets j i)) ∧
          wasserstein1 (generatorLaw q) (M.blockLaw j : Measure _) ≤
            ENNReal.ofReal (A * ((if 0 < Finset.univ.sup (dC j) then
              (L1 : ℝ)^(-(2 : ℝ)/max 1 (Finset.univ.sup (dC j))) +
              (L2 : ℝ)^(-(2 : ℝ)/max 1 (Finset.univ.sup (dC j))) else 0) +
              tau - tau * Real.log tau)) := by
  exact deep_generator_approximation_exists_factors (M.blockLaw j) (sets j) (dC j) Lchart
    (hsupp j) (hhomeo j) (hdom j) (hboundary j)
    (yarotskyCoordinate_of_structural hgate)

/-- For [a canonical model](hyp:M), [a variable bound](hyp:K), and [an intervention
radius](hyp:R), with [a nonnegative Lipschitz bound](hyp:L), suppose [the model belongs to
the corresponding canonical Lipschitz class](hyp:hclass), [its latent blocks
are independent](hyp:hind), [its noise admits the Gumbel decomposition](hyp:hdecomp),
[categorical mechanisms use Gumbel argmax](hyp:hcat), [continuous mechanisms
are globally Lipschitz](hyp:hcont), [categorical propensities are globally
Lipschitz](hyp:hprop), [variables
are bounded by the given bound](hyp:hbound), [the intervention radius is
positive](hyp:hR), and [the maximum structural input dimension is positive](hyp:hdin).
Assuming [the structural neural approximation theorem](hyp:hgate), [there exist
a nonnegative transport constant, positive structural-error and width constants,
and a minimum depth such that every larger structural depth and every family
of three-part latent generators in a chosen generator class admit one neural
causal model in that class, with structural width equal to the width constant
times the maximum input and output dimensions, whose Wasserstein error for
every intervention bounded by the radius is at most the transport constant
times the sum of the number of nodes times the structural-error constant times
depth to power minus two divided by maximum input dimension, and the sum of
latent marginal Wasserstein errors](goal). -/
-- @node: deep_ncm_structural_transport
lemma deep_ncm_structural_transport
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0) (K R : ℝ)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hdecomp : LatentGumbelDecomposition M.toEuclideanSCM)
    (hcat : CategoricalGumbelArgmax M.toEuclideanSCM M.f)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hR : 0 < R) (hdin : 0 < maxInDim M.toEuclideanSCM)
    (hgate : YarotskyStructuralApprox) :
    ∃ A : ℝ≥0, ∃ E : ℝ, 0 < E ∧ ∃ c0 B0 : ℕ, 0 < c0 ∧ 1 ≤ B0 ∧
      ∀ L0 : ℕ, B0 ≤ L0 →
      ∀ (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
        (W1 L1 W2 L2 : ℕ) (tau : ℝ)
        (Q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau)
        (F1 : GeneratorClass dims counts),
        (∀ j, (Q j).eval ∈ F1 j) →
        ∃ N : NCMIn kind dims dag G C counts
          (fun i => {f | ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
            (outputDim (kind i))
            (c0 * maxInDim M.toEuclideanSCM * maxOutDim M.toEuclideanSCM) L0,
            ∀ x, f (structuralFiniteCoordinates M.toEuclideanSCM i x) = q.eval x}) F1,
          ∀ t : LawIntervention kind,
            (∀ i d, kind i = Sum.inl d → ∀ v, t.val i = some v → ‖v.ofLp‖ ≤ R) →
            wasserstein1 (interventionalLaw M.toEuclideanSCM t)
              (interventionalLaw N.canonical.toEuclideanSCM t) ≤
              (A : ℝ≥0∞) * ((n : ℝ≥0∞) *
                ENNReal.ofReal (E * (L0 : ℝ)^(-(2 : ℝ)/maxInDim M.toEuclideanSCM)) +
                ∑ j, wasserstein1 (M.blockLaw j : Measure _) (generatorLaw (Q j))) := by
  obtain ⟨B, hB, hKB, hRB, hlabels, htrunc, hobs, hbounded⟩ :=
    truncate_interventionalLaw_eq M L K R hclass hbound hR
  let MB := boxTruncatedSCM M B hlabels
  obtain ⟨hindB, hdecompB, hcatB, hcontB, hpropB, hboundB, hlawB⟩ :=
    boxTruncatedSCM_atoms M L B K hlabels hKB hclass hind hdecomp hcat hcont hprop hbound
  have hclassB := boxTruncatedSCM_regular M L B hlabels hclass
  obtain ⟨A, hcomparison⟩ := approximation_wasserstein_bound
    (kind := kind) (dag := dag) (G := G) L K hbound.1
  obtain ⟨E, hE, c0, B0, hc0, hB0, happ⟩ :=
    deep_ncm_structural_networks M L B hlabels hclass hdin hgate
  refine ⟨A, E, hE, c0, B0, hc0, hB0, ?_⟩
  intro L0 hL0 counts dC W1 L1 W2 L2 tau Q F1 hF1
  obtain ⟨N, herr, hlatent⟩ := happ L0 hL0 counts dC W1 L1 W2 L2 tau Q F1 hF1
  refine ⟨N, ?_⟩
  intro t ht
  rw [(htrunc t ht).2]
  refine (hcomparison b dims C (fun _ => Set.univ) MB N.canonical hclassB
    (fun _ => Set.mem_univ _) hindB hdecompB hcatB hcontB hpropB hboundB t).trans ?_
  apply mul_le_mul' le_rfl
  apply add_le_add
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => herr i)
    simpa only [MB, CanonicalSCM.domain, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hs
  · exact hlatent

/-- For [a canonical model](hyp:M), [a variable bound](hyp:K), and [an intervention
radius](hyp:R), with [a nonnegative Lipschitz bound](hyp:L), suppose [the model belongs to
the corresponding canonical Lipschitz class](hyp:hclass), [its latent blocks
are independent](hyp:hind), [its noise admits the Gumbel decomposition](hyp:hdecomp),
[categorical mechanisms use Gumbel argmax](hyp:hcat), [continuous mechanisms
are globally Lipschitz](hyp:hcont), [categorical propensities are globally
Lipschitz](hyp:hprop), [variables
are bounded by the given bound](hyp:hbound), [the intervention radius is
positive](hyp:hR), and [the maximum structural input dimension is positive](hyp:hdin).
Assuming [the structural neural approximation theorem](hyp:hgate), [there exist
a nonnegative transport constant, a positive structural-error constant, and a
minimum depth such that every larger structural depth and every family of
three-part latent generators in a chosen generator class admit one neural
causal model in that class, with structural width equal to the fixed universal
width factor times the maximum input and output dimensions, whose Wasserstein
error for every intervention bounded by the radius is at most the transport
constant times the sum of the number of nodes times the structural-error
constant times depth to power minus two divided by maximum input dimension,
and the sum of latent marginal Wasserstein errors](goal). -/
lemma deep_ncm_structural_transport_explicit
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0) (K R : ℝ)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hdecomp : LatentGumbelDecomposition M.toEuclideanSCM)
    (hcat : CategoricalGumbelArgmax M.toEuclideanSCM M.f)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hR : 0 < R) (hdin : 0 < maxInDim M.toEuclideanSCM)
    (hgate : YarotskyStructuralApprox) :
    ∃ A : ℝ≥0, ∃ E : ℝ, 0 < E ∧ ∃ B0 : ℕ, 1 ≤ B0 ∧
      ∀ L0 : ℕ, B0 ≤ L0 →
      ∀ (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
        (W1 L1 W2 L2 : ℕ) (tau : ℝ)
        (Q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau)
        (F1 : GeneratorClass dims counts),
        (∀ j, (Q j).eval ∈ F1 j) →
        ∃ N : NCMIn kind dims dag G C counts
          (fun i => {f | ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
            (outputDim (kind i))
            (deepStructuralWidthFactor * maxInDim M.toEuclideanSCM * maxOutDim M.toEuclideanSCM) L0,
            ∀ x, f (structuralFiniteCoordinates M.toEuclideanSCM i x) = q.eval x}) F1,
          ∀ t : LawIntervention kind,
            (∀ i d, kind i = Sum.inl d → ∀ v, t.val i = some v → ‖v.ofLp‖ ≤ R) →
            wasserstein1 (interventionalLaw M.toEuclideanSCM t)
              (interventionalLaw N.canonical.toEuclideanSCM t) ≤
              (A : ℝ≥0∞) * ((n : ℝ≥0∞) *
                ENNReal.ofReal (E * (L0 : ℝ)^(-(2 : ℝ)/maxInDim M.toEuclideanSCM)) +
                ∑ j, wasserstein1 (M.blockLaw j : Measure _) (generatorLaw (Q j))) := by
  obtain ⟨B, hB, hKB, hRB, hlabels, htrunc, hobs, hbounded⟩ :=
    truncate_interventionalLaw_eq M L K R hclass hbound hR
  let MB := boxTruncatedSCM M B hlabels
  obtain ⟨hindB, hdecompB, hcatB, hcontB, hpropB, hboundB, hlawB⟩ :=
    boxTruncatedSCM_atoms M L B K hlabels hKB hclass hind hdecomp hcat hcont hprop hbound
  have hclassB := boxTruncatedSCM_regular M L B hlabels hclass
  obtain ⟨A, hcomparison⟩ := approximation_wasserstein_bound
    (kind := kind) (dag := dag) (G := G) L K hbound.1
  obtain ⟨E, hE, B0, hB0, happ⟩ :=
    deep_ncm_structural_networks_explicit M L B hlabels hclass hdin hgate
  refine ⟨A, E, hE, B0, hB0, ?_⟩
  intro L0 hL0 counts dC W1 L1 W2 L2 tau Q F1 hF1
  obtain ⟨N, herr, hlatent⟩ := happ L0 hL0 counts dC W1 L1 W2 L2 tau Q F1 hF1
  refine ⟨N, ?_⟩
  intro t ht
  rw [(htrunc t ht).2]
  refine (hcomparison b dims C (fun _ => Set.univ) MB N.canonical hclassB
    (fun _ => Set.mem_univ _) hindB hdecompB hcatB hcontB hpropB hboundB t).trans ?_
  apply mul_le_mul' le_rfl
  apply add_le_add
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => herr i)
    simpa only [MB, CanonicalSCM.domain, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hs
  · exact hlatent

/-- For [a canonical model](hyp:M), [a variable bound](hyp:K), and [an intervention
radius](hyp:R), with [a nonnegative Lipschitz bound](hyp:L), suppose [the model belongs to
the corresponding canonical Lipschitz class](hyp:hclass), [its latent blocks
are independent](hyp:hind), [its noise admits the Gumbel decomposition](hyp:hdecomp),
[categorical mechanisms use Gumbel argmax](hyp:hcat), [continuous mechanisms
are globally Lipschitz](hyp:hcont), [categorical propensities are globally
Lipschitz](hyp:hprop), and [its
variables are bounded by the given bound](hyp:hbound). For [latent component
counts](hyp:counts), [latent support
components](hyp:sets), [their intrinsic dimensions](hyp:dC), and [a common
chart Lipschitz bound](hyp:Lchart), assume [finite-component support](hyp:hsupp),
[Lipschitz cube homeomorphisms](hyp:hhomeo), [lower-bound domination of
conditional component laws](hyp:hdom), [vanishing of their pullbacks on cube
boundaries](hyp:hboundary), [unit-cube structural domains](hyp:hdomain),
[positive maximum structural input and latent dimensions](hyp:hdims),
[a positive intervention radius](hyp:hR), and [the structural neural
approximation theorem](hyp:hYarotskyStructural_of_gate). Then [there exist a
positive error constant, three minimum depths, and a temperature ceiling below
one, such that every larger triple of depths and smaller positive temperature
admits one neural causal model with the prescribed fixed structural and generator
widths, cube-preserving first generator blocks and component-preserving
zero-dimensional second blocks, whose Wasserstein error uniformly over all
interventions within the radius is at most that constant times the sum of
structural depth to power minus two divided by maximum structural input
dimension, both generator depths to power minus two divided by maximum latent
dimension, and temperature minus temperature times its logarithm](goal).

The cited input is `YarotskyStructuralApprox`: D. Yarotsky (2018),
Theorem 2(b), arXiv:1802.03620, Section 2, equations (1) and (2),
citation handle `yarotsky2018optimal`. Any chart approximation needed
for the latent generators remains a local proof obligation. -/
-- @node: thm:deep-nn
theorem deep_ncm_approximation (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0) (K : ℝ)
    (hclass : M ∈ canonicalClass (domainLipClass M L))
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hdecomp : LatentGumbelDecomposition M.toEuclideanSCM)
    (hcat : CategoricalGumbelArgmax M.toEuclideanSCM M.f)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (counts : Fin b → ℕ) (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hsupp : ∀ j, SupportFiniteComponents (M.blockLaw j : Measure _) (sets j))
    (hhomeo : ∀ j, ComponentsLipschitzHomeomorphic (sets j) (dC j) Lchart)
    (hdom : ∀ j i, LowerBoundDomination (d := dC j i) (ProbabilityTheory.cond (M.blockLaw j : Measure _)
      (sets j i)) (sets j i) Lchart)
    (hboundary : ∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (sets j i)) (sets j i) Lchart)
    (hdomain : StructuralDomainsUnitCubes M.toEuclideanSCM)
    (hdims : 0 < maxInDim M.toEuclideanSCM ∧ 0 < maxLatentDim M.toEuclideanSCM)
    (R : ℝ) (hR : 0 < R) -- @realizes R(fixed positive intervention bound before constants and the neural model)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox) :
    ∃ A : ℝ, 0 < A ∧ ∃ B0 B1 B2 : ℕ, 1 ≤ B0 ∧ 1 ≤ B1 ∧ 1 ≤ B2 ∧
      ∃ taubar : ℝ, 0 < taubar ∧ taubar < 1 ∧
      ∀ L0 L1 L2 : ℕ, B0 ≤ L0 → B1 ≤ L1 → B2 ≤ L2 →
      ∀ tau : ℝ, 0 < tau → tau < taubar →
        ∃ N : NCMIn kind dims dag G C counts
          (fun i => {f | ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
            (outputDim (kind i)) (deepStructuralWidthFactor * maxInDim M.toEuclideanSCM * maxOutDim M.toEuclideanSCM) L0,
              ∀ x, f (structuralFiniteCoordinates M.toEuclideanSCM i x) = q.eval x})
          (fun j => {g | ∃ q : ThreePartGenerator (counts j) (dims j) (dC j)
            (deepFirstWidthFactor * maxLatentDim M.toEuclideanSCM) L1
            (deepSecondWidthFactor * (maxLatentDim M.toEuclideanSCM)^2) L2 tau, g = q.eval ∧
              (∀ i, Set.MapsTo (q.g1 i).eval (unitCube 1) (unitCube (dC j i))) ∧
              (∀ i, dC j i = 0 → Set.MapsTo (q.g2 i).eval (unitCube (dC j i)) (sets j i))}),
          ∀ t : LawIntervention kind,
            (∀ i d, kind i = Sum.inl d → ∀ v, t.val i = some v → ‖v.ofLp‖ ≤ R) → -- @realizes \boldsymbol{t}(continuous coordinates bounded by fixed R; categorical labels legal by LawIntervention)
            wasserstein1 (interventionalLaw M.toEuclideanSCM t)
              (interventionalLaw N.canonical.toEuclideanSCM t) ≤
                ENNReal.ofReal (A * ((L0 : ℝ)^(-(2:ℝ)/maxInDim M.toEuclideanSCM) +
                  (L1 : ℝ)^(-(2:ℝ)/maxLatentDim M.toEuclideanSCM) +
                  (L2 : ℝ)^(-(2:ℝ)/maxLatentDim M.toEuclideanSCM) + tau-tau*Real.log tau)) := by
  obtain ⟨T, E, hE, B0, hB0, hstruct⟩ :=
    deep_ncm_structural_transport_explicit M L K R hclass hind hdecomp hcat hcont hprop
      hbound hR hdims.1 hYarotskyStructural_of_gate
  have hchartdim : ∀ j i, dC j i ≤ maxLatentDim M.toEuclideanSCM := by
    intro j i
    obtain ⟨chart, hchart⟩ := hhomeo j i
    refine le_trans ?_ (Finset.le_sup (f := dims) (Finset.mem_univ j))
    exact cube_chart_dimension_le_ambient chart
  obtain ⟨A, hA, B, hB, tb, htb, htb1, hlatent⟩ :=
    deep_generators_common_budgets_explicit dims M.blockLaw counts sets dC Lchart hsupp hhomeo
      hdom hboundary (yarotskyCoordinate_of_structural hYarotskyStructural_of_gate)
      (maxLatentDim M.toEuclideanSCM) hdims.2
      (fun j => Finset.le_sup (f := dims) (Finset.mem_univ j)) hchartdim
  let Ctotal : ℝ := 1 + (T : ℝ) * ((n : ℝ) * E + (b : ℝ) * A)
  have hCtotal : 0 < Ctotal := by
    have : 0 ≤ (T : ℝ) * ((n : ℝ) * E + (b : ℝ) * A) := by positivity
    dsimp [Ctotal]
    linarith
  refine ⟨Ctotal, hCtotal, B0, B, B, hB0, hB, hB, tb, htb, htb1, ?_⟩
  intro L0 L1 L2 hL0 hL1 hL2 tau htau htaub
  obtain ⟨Q, hp, hcube, hzero, herr⟩ := hlatent L1 L2 hL1 hL2 tau htau htaub
  obtain ⟨N, hN⟩ := hstruct L0 hL0 counts dC _ L1 _ L2 tau Q
    (fun j => {g | ∃ q : ThreePartGenerator (counts j) (dims j) (dC j)
      (deepFirstWidthFactor * maxLatentDim M.toEuclideanSCM) L1
      (deepSecondWidthFactor * (maxLatentDim M.toEuclideanSCM)^2) L2 tau, g = q.eval ∧
        (∀ i, Set.MapsTo (q.g1 i).eval (unitCube 1) (unitCube (dC j i))) ∧
        (∀ i, dC j i = 0 → Set.MapsTo (q.g2 i).eval (unitCube (dC j i)) (sets j i))})
    (fun j => ⟨Q j, rfl, hcube j, hzero j⟩)
  refine ⟨N, ?_⟩
  intro t ht
  let r0 : ℝ := (L0 : ℝ) ^ (-(2 : ℝ) / maxInDim M.toEuclideanSCM)
  let rU : ℝ := (L1 : ℝ) ^ (-(2 : ℝ) / maxLatentDim M.toEuclideanSCM) +
    (L2 : ℝ) ^ (-(2 : ℝ) / maxLatentDim M.toEuclideanSCM) + tau - tau * Real.log tau
  have hr0 : 0 ≤ r0 := Real.rpow_nonneg (Nat.cast_nonneg L0) _
  have hrU : 0 ≤ rU := by
    have hlog := Real.log_nonpos htau.le (htaub.trans htb1).le
    have := Real.rpow_nonneg (Nat.cast_nonneg L1)
      (-(2 : ℝ) / maxLatentDim M.toEuclideanSCM)
    have := Real.rpow_nonneg (Nat.cast_nonneg L2)
      (-(2 : ℝ) / maxLatentDim M.toEuclideanSCM)
    have := mul_nonpos_of_nonneg_of_nonpos htau.le hlog
    dsimp [rU]
    linarith
  have hsum : (∑ j, wasserstein1 (M.blockLaw j : Measure _) (generatorLaw (Q j))) ≤
      (b : ℝ≥0∞) * ENNReal.ofReal (A * rU) := by
    have h (j : Fin b) : wasserstein1 (M.blockLaw j : Measure _) (generatorLaw (Q j)) ≤
        ENNReal.ofReal (A * rU) := by
      let := generatorInputLaw_probability (counts j)
      let nu : ProbabilityMeasure (L1Vec (dims j)) :=
        ⟨generatorLaw (Q j), Measure.isProbabilityMeasure_map (by fun_prop)⟩
      rw [show generatorLaw (Q j) = (nu : Measure _) from rfl,
        wasserstein1_symm]
      exact herr j
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hs
  calc
    _ ≤ (T : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal (E * r0) +
        ∑ j, wasserstein1 (M.blockLaw j : Measure _) (generatorLaw (Q j))) := hN t ht
    _ ≤ (T : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal (E * r0) +
        (b : ℝ≥0∞) * ENNReal.ofReal (A * rU)) :=
      mul_le_mul' le_rfl (add_le_add le_rfl hsum)
    _ = ENNReal.ofReal ((T : ℝ) * ((n : ℝ) * (E * r0) + (b : ℝ) * (A * rU))) := by
      rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_natCast b,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg b),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul T.coe_nonneg]
    _ ≤ ENNReal.ofReal (Ctotal * (r0 + rU)) := by
      apply ENNReal.ofReal_le_ofReal
      have hcross0 : 0 ≤ (T : ℝ) * (n : ℝ) * E * rU := by positivity
      have hcrossU : 0 ≤ (T : ℝ) * (b : ℝ) * A * r0 := by positivity
      dsimp [Ctotal]
      nlinarith only [hr0, hrU, hcross0, hcrossU]
    _ = _ := by
      congr 1
      dsimp [r0, rU]
      ring

end
end Papers.TbsNeuralCausalPi
