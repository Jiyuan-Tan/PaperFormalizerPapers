module

public import Papers.OaiCloseSeparableCstar.Helpers.TreeNorm
public import Papers.OaiCloseSeparableCstar.Helpers.TreePathOperators

/-! # Lemma 5: the tree deformation of the regular representation -/

public section

open Filter Topology

namespace Papers.OaiCloseSeparableCstar

-- @node: cBound_tendsto_zero
/-- [The uniform perturbation bound tends to zero as the deformation parameter approaches zero from above within the open unit interval](goal). -/
lemma cBound_tendsto_zero :
    Tendsto (fun t : {t : ℝ // DeformationRange t} => cBound t.val t.property)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  have hv : Tendsto (fun t : {t : ℝ // DeformationRange t} => t.val)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hc : ContinuousAt
      (fun t : ℝ => 2 * (1 - Real.sqrt (1 - t ^ 2)) + t / (1 - t) + t) 0 := by
    fun_prop (disch := norm_num)
  simpa [Function.comp_def, cBound, rValue] using hc.tendsto.comp hv

-- @node: lem:tree
/-- [For every real deformation parameter strictly between zero and one, there is a unitary representation of the free group whose matrix coefficient at the identity coordinate vector equals that parameter for every free generator, and whose operator-norm distance from the left regular representation at every group element is at most the uniform perturbation bound; this bound tends to zero as the parameter approaches zero from above](goal). -/
lemma exists_treeRep :
    (∀ (t : ℝ) (ht : DeformationRange t),
      ∃ π : FG →* unitary (Op KSp), IsTreeRep t ht π) ∧
    Tendsto (fun t : {t : ℝ // DeformationRange t} => cBound t.val t.property)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  constructor
  · intro t ht
    refine ⟨treeUnitaryRep t ht, treeUnitaryRep_coefficient t ht, ?_⟩
    intro g
    rw [← treePerturbation_norm_eq t ht g]
    -- Extend the finite-path operators by X = 1 and S = 0 off the path.
    -- The diagonal construction and all analytic estimates are already proved.
    suffices hpath : ∃ X S : Op KSp, ‖S‖ ≤ 1 ∧
        X * (1 - (t : ℂ) • star S) = treePathDiagonal t ht g 1 ∧
        treePerturbation t ht g = X * treePathDiagonal t ht g g - (t : ℂ) • S by
      obtain ⟨X, S, hS, hrec, hT⟩ := hpath
      exact tree_pathOperator_norm_of_recursion t ht _ X
        (treePathDiagonal t ht g 1) (treePathDiagonal t ht g g) S hS
        (treePathDiagonal_norm_le t ht g 1) (treePathDiagonal_norm_le t ht g g)
        (treePathDiagonal_sub_one_norm_le t ht g 1)
        (treePathDiagonal_sub_one_norm_le t ht g g) hrec hT
    exact ⟨treePathColumnOperator t ht g, treePathShift g, treePathShift_norm_le g,
      treePathColumnOperator_recursion t ht g, treePerturbation_eq_pathOperators t ht g⟩
  · exact cBound_tendsto_zero

end Papers.OaiCloseSeparableCstar
