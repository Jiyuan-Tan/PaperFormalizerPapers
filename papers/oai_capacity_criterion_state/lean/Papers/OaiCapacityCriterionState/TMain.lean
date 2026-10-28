module

public import Papers.OaiCapacityCriterionState.Helpers

/-! # Reconstruction is equivalent to positive nonlinear capacity

The companion moment-saving result is an explicit disclosed hypothesis. All
remaining steps from the deterministic tree and channel setup are proof obligations.
-/

public section

namespace OaiCapacityCriterionState

-- @node: thm:main
/-- Assume [the companion proposition giving a symmetric posterior class closed
under channels and conditional products with a quantitative moment saving](hyp:hCompanion_of_gate),
[the identity equating the squared Euclidean norm in three dimensions with the
sum of squared coordinates](hyp:hpin1), and [invariance of the conditional-product
posterior law under measurable probability-vector extensions of the normalized
product rule on its zero-density set](hyp:hpin2). If [the bounded tree has a
strictly positive branching bound and infinitely many vertices](hyp:hT) and
[the channel parameter is strictly between zero and one](hyp:hlam), then
[the limiting reconstruction information is positive if and only if the tree's
nonlinear capacity of order three is positive](goal). -/
theorem reconstructs_iff_capacity_pos (hCompanion_of_gate : CompanionMomentSaving)
    (hpin1 : EuclideanNormPin) (hpin2 : ProductRulePin)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hT : MainTree T) (hlam : MainLambda lam) :
    0 < limitInfo T lam ↔ 0 < capacity3 T lam := by
  constructor
  · exact capacity_pos_of_reconstructs hCompanion_of_gate T lam hT hlam
  · intro hcap
    obtain ⟨c, hc, hbound⟩ := capacity_pos_implies_treeExperiment_uniform_pos
      hCompanion_of_gate T lam hlam hcap
    apply (reconstructs_iff_broadcastPosteriorLaw_uniform_pos T lam hlam).mpr
    refine ⟨c, hc, fun n => (hbound n).trans ?_⟩
    exact le_of_eq (congrArg quadInfo
      (treeExperimentLaw_root_eq_broadcastPosteriorLaw T lam hlam n))

end OaiCapacityCriterionState
