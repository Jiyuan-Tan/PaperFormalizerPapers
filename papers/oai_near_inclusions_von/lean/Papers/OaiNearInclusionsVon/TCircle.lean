module

public import Papers.OaiNearInclusionsVon.Helpers.CircleSummability
public import Papers.OaiNearInclusionsVon.Helpers.CircleCoefficientSums

/-! Existence of the circle of free-group representations. -/

public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon


/-- [There exist a circle-indexed family of free-group unitary representations
and operator-valued Laurent coefficients satisfying the circle-family
conditions: the Laurent expansions converge in norm with the prescribed
coefficient bounds, the generators have the prescribed weak limit, the
weights and their first absolute moments are summable, and the expansions
are absolutely convergent with uniformly small tails](goal). -/
-- @node: prop:circle
theorem circle_family_exists :
    ∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A := by
  -- The finite path expansion supplies explicit coefficients and their exact sum.
  refine ⟨circleTreeRep, circleLaurentCoefficients,
    circle_family_of_coefficients circleTreeRep circleLaurentCoefficients
      circleLaurentCoefficients_hasSum circleLaurentCoefficients_norm_le
      circleTreeRep_gen_tendsto_wot⟩

end Papers.OaiNearInclusionsVon
