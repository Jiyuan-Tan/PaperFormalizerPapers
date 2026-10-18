module
public import Papers.TbsNeuralCausalPi.TCounterexampleForal
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleCalibration
/-! # Identifiability in the class with jointly independent latents -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: ass:pin-owner-2
/-- For [a reference canonical backdoor model with no bidirected edges](hyp:Mstar),
[identification among models with independent latent blocks](goal) means that
[the reference individual treatment contrast is integrable](step:1) and
[every Euclidean model with the same causal graph, independent latent blocks,
the same observational distribution, and an integrable treatment contrast has
the same average treatment effect as the reference model](step:2). -/
def IdentifiabilityIndependentLatentsReading {b : ℕ} {dims : Fin b → ℕ}
    {C : Fin b → Set (Fin 3)}
    (Mstar : CanonicalSCM backdoorKind dims backdoorDAG (⊥ : SimpleGraph (Fin 3)) C) : Prop :=
  Integrable (fun u =>
    backdoorOutcome (intervenedEval Mstar.toEuclideanSCM (binaryAssignment true) u) -
    backdoorOutcome (intervenedEval Mstar.toEuclideanSCM (binaryAssignment false) u))
      Mstar.toEuclideanSCM.latentLaw ∧
  ∀ (b' : ℕ) (dims' : Fin b' → ℕ) (M : EuclideanSCM backdoorKind dims'),
    causalGraph M = backdoorGraph → LatentBlocksIndependent M →
    observationalLaw M = observationalLaw Mstar.toEuclideanSCM →
    Integrable (fun u =>
      backdoorOutcome (intervenedEval M (binaryAssignment true) u) -
      backdoorOutcome (intervenedEval M (binaryAssignment false) u)) M.latentLaw →
      backdoorATE M = backdoorATE Mstar.toEuclideanSCM
/-- For [a reference canonical backdoor model with no bidirected edges](hyp:Mstar),
[identification of its average treatment effect](goal) means identification among
observationally equivalent models with independent latent blocks and integrable
treatment contrasts, including integrability of the reference contrast. -/
abbrev ATEIdentified {b : ℕ} {dims : Fin b → ℕ} {C : Fin b → Set (Fin 3)}
    (Mstar : CanonicalSCM backdoorKind dims backdoorDAG (⊥ : SimpleGraph (Fin 3)) C) :=
  IdentifiabilityIndependentLatentsReading Mstar
/-- [There exist a positive effect-gap constant and a canonical backdoor model
with no bidirected edges, independent latent blocks, a Gumbel noise decomposition,
Gumbel-argmax categorical mechanisms, Lipschitz continuous mechanisms and
categorical propensities, bounded observed and non-Gumbel latent coordinates,
regular latent laws, and an identified average treatment effect, such that for every positive
observational tolerance another canonical model with the same latent dimensions
and component structure has an integrable treatment contrast and an observational
distribution within that tolerance in Wasserstein distance, while its average
treatment effect differs by more than the fixed constant](goal). -/
-- @node: prop:counterexample
theorem counterexample_identifiable :
    ∃ c : ℝ, 0 < c ∧ ∃ b : ℕ, ∃ dims : Fin b → ℕ, ∃ C : Fin b → Set (Fin 3),
      ∃ M : CanonicalSCM backdoorKind dims backdoorDAG (⊥ : SimpleGraph (Fin 3)) C,
        counterexampleAtoms M ∧ ATEIdentified M ∧
        (∀ eps : ℝ, 0 < eps → ∃ Mep : CanonicalSCM backdoorKind dims backdoorDAG ⊥ C,
          Integrable (fun u =>
            backdoorOutcome (intervenedEval Mep.toEuclideanSCM (binaryAssignment true) u) -
            backdoorOutcome (intervenedEval Mep.toEuclideanSCM (binaryAssignment false) u))
              Mep.toEuclideanSCM.latentLaw ∧
          wasserstein1 (observationalLaw M.toEuclideanSCM)
            (observationalLaw Mep.toEuclideanSCM) ≤ ENNReal.ofReal eps ∧
          c < |backdoorATE M.toEuclideanSCM-backdoorATE Mep.toEuclideanSCM|) := by
  refine ⟨1/10, by norm_num, 3, counterexampleDims, counterexampleComponents,
    counterexampleTrueSCM, counterexampleTrueSCM_atoms, ?_, ?_⟩
  · refine ⟨counterexampleTrueSCM_effect_integrable, ?_⟩
    intro b' dims' M hgraph hind hobs hintegrable
    calc
      backdoorATE M = ∫ v, counterexampleAdjustmentScore v ∂observationalLaw M := by
        apply counterexample_adjustment_of_private_calibration M hgraph hind hobs
        exact counterexample_private_selection_calibration M hgraph hind hobs
      _ = 19/30 := counterexample_adjustment_integral_of_observational_eq M hobs
      _ = backdoorATE counterexampleTrueSCM.toEuclideanSCM := counterexampleTrueSCM_ATE.symm
  · intro eps heps
    refine ⟨counterexampleApproxSCM eps, counterexampleApproxSCM_effect_integrable eps, ?_, ?_⟩
    · exact (counterexampleSCM_observational_wasserstein_le eps heps).trans
        (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [counterexampleTrueSCM_ATE, counterexampleApproxSCM_ATE eps heps]
      norm_num

end
end Papers.TbsNeuralCausalPi
