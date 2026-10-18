module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleConditional
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleInterventions
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleObservations
/-! # Backdoor observational convergence with an ATE gap -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- [There exists a canonical backdoor model with no bidirected edges and
independent latent blocks, a Gumbel noise decomposition, Gumbel-argmax categorical
mechanisms, Lipschitz continuous mechanisms and categorical propensities,
bounded observed and non-Gumbel latent coordinates, and regular latent laws,
with two distinct independent Bernoulli coordinates of success probabilities
three fifths and one third in an outcome-associated latent block, and a measurable, integrable, mean-zero
outcome disturbance, such that under either binary treatment intervention,
whenever the first observed coordinate is zero, the outcome almost surely equals
the first selected latent coordinate if the second observed coordinate is two,
and the other selected latent coordinate otherwise, plus that disturbance](goal). -/
-- @node: exists_backdoor_outcome_witness
lemma exists_backdoor_outcome_witness :
    ∃ b : ℕ, ∃ dims : Fin b → ℕ, ∃ C : Fin b → Set (Fin 3),
      ∃ M : CanonicalSCM backdoorKind dims backdoorDAG (⊥ : SimpleGraph (Fin 3)) C,
        counterexampleAtoms M ∧ ∃ j : Fin b, ∃ a a' : Fin (dims j),
          counterexampleBernoulliCoordinates M j a a' ∧ LatentLawsGeneratorRegular M ∧
          ∃ Uy : Exogenous backdoorKind dims → ℝ,
            Measurable Uy ∧ Integrable Uy M.latentLaw ∧ (∫ u, Uy u ∂M.latentLaw) = 0 ∧
            ∀ᵐ u ∂M.latentLaw, ∀ t : Bool,
              let v := intervenedEval M.toEuclideanSCM (binaryAssignment t) u
              v.ofLp ⟨0, ⟨0, Nat.zero_lt_succ 0⟩⟩ = 0 →
              backdoorOutcome v =
                (if v.ofLp ⟨1, ⟨0, Nat.zero_lt_succ 0⟩⟩ = 2 then
                  (blockProjection j u).ofLp a else (blockProjection j u).ofLp a') + Uy u := by
  exact ⟨3, counterexampleDims, counterexampleComponents, counterexampleTrueSCM,
    counterexampleTrueSCM_atoms, 2, ⟨0, by decide⟩, ⟨1, by decide⟩,
    counterexampleTrueSCM_bernoulli_coordinates, counterexampleTrueSCM_regular,
    counterexampleTrueSCM_outcome_connection⟩

-- @node: prop:counterexample-foral
/-- [There exist a positive effect-gap constant and a canonical backdoor model
with no bidirected edges, independent latent blocks, a Gumbel noise decomposition,
Gumbel-argmax categorical mechanisms, Lipschitz continuous mechanisms and
categorical propensities, bounded observed and non-Gumbel latent coordinates,
and regular latent laws, with two distinct independent Bernoulli coordinates
of success probabilities three fifths and one third in an outcome-associated
latent block and a measurable integrable mean-zero disturbance such that, under
either binary treatment intervention, a zero covariate makes the outcome
almost surely equal the first latent coordinate for treatment category two
and the second otherwise, plus the disturbance, such that for
every positive tolerance another canonical model with the same latent dimensions
and component structure has an integrable treatment contrast and an observational
distribution within that tolerance in Wasserstein distance, while its average
treatment effect differs by more than the fixed constant](goal). -/
theorem counterexample_backdoor :
    ∃ c : ℝ, 0 < c ∧ ∃ b : ℕ, ∃ dims : Fin b → ℕ, ∃ C : Fin b → Set (Fin 3), -- @realizes \mathcal{M}_\epsilon(positive effect-gap constant before the arbitrary positive observational tolerance) -- @realizes c(positive effect-gap constant before the arbitrary positive observational tolerance)
      ∃ M : CanonicalSCM backdoorKind dims backdoorDAG (⊥ : SimpleGraph (Fin 3)) C,
        counterexampleAtoms M ∧ ∃ j : Fin b, ∃ a a' : Fin (dims j),
        counterexampleBernoulliCoordinates M j a a' ∧ counterexampleOutcomeConnection M j a a' ∧
        (∀ eps : ℝ, 0 < eps → ∃ Mep : CanonicalSCM backdoorKind dims backdoorDAG ⊥ C,
          Integrable (fun u =>
            backdoorOutcome (intervenedEval Mep.toEuclideanSCM (binaryAssignment true) u) -
            backdoorOutcome (intervenedEval Mep.toEuclideanSCM (binaryAssignment false) u))
              Mep.toEuclideanSCM.latentLaw ∧
          wasserstein1 (observationalLaw M.toEuclideanSCM)
            (observationalLaw Mep.toEuclideanSCM) ≤ ENNReal.ofReal eps ∧
          c < |backdoorATE M.toEuclideanSCM-backdoorATE Mep.toEuclideanSCM|) := by
  refine ⟨1/10, by norm_num, 3, counterexampleDims, counterexampleComponents,
    counterexampleTrueSCM, counterexampleTrueSCM_atoms, 2, ⟨0, by decide⟩, ⟨1, by decide⟩,
    counterexampleTrueSCM_bernoulli_coordinates, counterexampleTrueSCM_outcome_connection, ?_⟩
  intro eps heps
  refine ⟨counterexampleApproxSCM eps, counterexampleApproxSCM_effect_integrable eps, ?_, ?_⟩
  · exact (counterexampleSCM_observational_wasserstein_le eps heps).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  · rw [counterexampleTrueSCM_ATE, counterexampleApproxSCM_ATE eps heps]
    norm_num

end
end Papers.TbsNeuralCausalPi
