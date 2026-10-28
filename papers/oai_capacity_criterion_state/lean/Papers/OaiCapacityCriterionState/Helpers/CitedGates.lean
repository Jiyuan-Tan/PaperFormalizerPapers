module

public import Papers.OaiCapacityCriterionState.Helpers.PosteriorLaws

/-! # Disclosed companion-paper input

This file states the exact borrowed logical claim as a proposition carrier.
Consumers must accept it as an explicit hypothesis; it is not proved here.
-/

@[expose] public section

open MeasureTheory

namespace OaiCapacityCriterionState

-- @node: prop:companion
/-- The [companion moment-saving proposition](goal) asserts that there exists a class of
probability laws for four-state posterior beliefs such that [every member is a symmetric
posterior law](step:1), [the fully revealing law belongs to the class](step:2),
[the uninformative law belongs to the class](step:3), [channel updates with parameters
between zero and one inclusive preserve membership](step:4), [combining two members as conditionally
independent experiments preserves membership](step:5), and [the combined quadratic information
is at most the sum of the two quadratic informations minus one thousandth of the sum of
each law's fourth moment times the other law's quadratic information](step:6).

OpenAI (2026), *The Reconstruction Threshold for the Ferromagnetic Four-State Potts Model*,
Proposition 3.2 and Equations (3.8)--(3.9), citation handle `OpenAI26Potts`.
The owner-provided TeX attested in `discovery/cited_sources/OpenAI26Potts.txt` states
closure and the displayed moment-saving inequality; no mixture closure is needed here.
-/
def CompanionMomentSaving : Sort 0 :=
  ∃ C : Set (Measure (Fin 4 → ℝ)), -- @realizes \calC(class of symmetric posterior laws)
    (∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu) ∧
    revealingLaw ∈ C ∧ uninformativeLaw ∈ C ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C) ∧
    (∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C) ∧
    ∀ mu ∈ C, ∀ nu ∈ C,
      quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu -
        (1 / 1000 : ℝ) * -- @realizes c(the fixed positive constant 1/1000)
          ((∫ p, quadStat p ^ 2 ∂mu) * quadInfo nu +
            quadInfo mu * ∫ p, quadStat p ^ 2 ∂nu)

end OaiCapacityCriterionState
