module

public import Papers.OaiNearInclusionsVon.ReusedTree.Helpers.TreeGram
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # Unitary extension of translations of the root-path vectors

The finite Gram identities give norm preservation on finite linear combinations.
The dense extension then supplies the representation before its perturbation estimate.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Papers.OaiNearInclusionsVon.ReusedTree
/-- For [a real deformation parameter t](hyp:t) [strictly between zero and one](hyp:ht)
and [a group element g](hyp:g), [the translated linear-combination map](goal) sends
finitely supported complex coefficients to the sum of those coefficients times the
root-path vectors indexed by the left translates gx. -/
noncomputable def treeCombination (t : ℝ) (ht : DeformationRange t) (g : FG) :
    (FG →₀ ℂ) →ₗ[ℂ] KSp :=
  Finsupp.linearCombination ℂ (fun x => treeVector t ht (g * x))
/-- If [t lies strictly between zero and one](hyp:ht), [left translating the indices
of two finite linear combinations of root-path vectors by the same group element
preserves their inner product](goal). -/
lemma treeCombination_inner (t : ℝ) (ht : DeformationRange t) (g : FG)
    (a b : FG →₀ ℂ) :
    ⟪treeCombination t ht g a, treeCombination t ht g b⟫_ℂ =
      ⟪treeCombination t ht 1 a, treeCombination t ht 1 b⟫_ℂ := by
  classical
  simp only [treeCombination, Finsupp.linearCombination_apply, Finsupp.sum,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    treeVector_inner_left_translate, one_mul]
/-- If [t lies strictly between zero and one](hyp:ht), [left translating the indices
of a finite linear combination of root-path vectors preserves its norm](goal). -/
lemma treeCombination_norm (t : ℝ) (ht : DeformationRange t) (g : FG)
    (a : FG →₀ ℂ) :
    ‖treeCombination t ht g a‖ = ‖treeCombination t ht 1 a‖ := by
  have h := treeCombination_inner t ht g a a
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hsq : ‖treeCombination t ht g a‖ ^ 2 = ‖treeCombination t ht 1 a‖ ^ 2 := by
    exact_mod_cast h
  nlinarith [norm_nonneg (treeCombination t ht g a),
    norm_nonneg (treeCombination t ht 1 a)]
/-- If [t lies strictly between zero and one](hyp:ht), [the finite linear
combinations of root-path vectors translated by any fixed group element are dense
in the square-summable Hilbert space on the group](goal). -/
lemma treeCombination_dense (t : ℝ) (ht : DeformationRange t) (g : FG) :
    DenseRange (treeCombination t ht g) := by
  have hr : Set.range (fun x => treeVector t ht (g * x)) =
      Set.range (treeVector t ht) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨g * x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨g⁻¹ * x, by simp⟩
  have h := treeVector_dense_span t ht
  rw [← hr, ← Finsupp.range_linearCombination] at h
  change Dense (Set.range (treeCombination t ht g))
  rw [← LinearMap.coe_range]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr h
/-- For [a real deformation parameter t](hyp:t) [strictly between zero and one](hyp:ht)
and [a group element g](hyp:g), [the tree translation by g](goal) is the complex
linear isometric bijection extending the assignment of the root-path vector at x
to the root-path vector at gx. -/
noncomputable def treeTranslation (t : ℝ) (ht : DeformationRange t) (g : FG) :
    KSp ≃ₗᵢ[ℂ] KSp :=
  (LinearEquiv.refl ℂ (FG →₀ ℂ)).extendOfIsometry
    (treeCombination t ht 1) (treeCombination t ht g)
    (treeCombination_dense t ht 1) (treeCombination_dense t ht g)
    (treeCombination_norm t ht g)
/-- If [t lies strictly between zero and one](hyp:ht), [tree translation by g sends
the root-path vector at x to the root-path vector at gx](goal). -/
lemma treeTranslation_treeVector (t : ℝ) (ht : DeformationRange t) (g x : FG) :
    treeTranslation t ht g (treeVector t ht x) = treeVector t ht (g * x) := by
  have h := LinearEquiv.extendOfIsometry_eq
    (LinearEquiv.refl ℂ (FG →₀ ℂ)) (treeCombination t ht 1) (treeCombination t ht g)
    (treeCombination_dense t ht 1) (treeCombination_dense t ht g)
    (treeCombination_norm t ht g) (Finsupp.single x 1)
  simpa [treeTranslation, treeCombination, Finsupp.linearCombination_single] using h
/-- If [t lies strictly between zero and one](hyp:ht) and [two bounded operators
agree on every root-path vector](hyp:h), [the operators are equal](goal). -/
lemma treeTranslation_ext (t : ℝ) (ht : DeformationRange t)
    {A B : Op KSp} (h : ∀ x, A (treeVector t ht x) = B (treeVector t ht x)) : A = B := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (treeVector_dense_span t ht))
  rintro _ ⟨x, rfl⟩
  exact h x
/-- If [t lies strictly between zero and one](hyp:ht), [tree translation by the
group identity is the identity operator](goal). -/
lemma treeTranslation_one (t : ℝ) (ht : DeformationRange t) :
    treeTranslation t ht 1 = 1 := by
  apply LinearIsometryEquiv.toLinearIsometry_injective
  apply LinearIsometry.toContinuousLinearMap_injective
  apply treeTranslation_ext t ht
  intro x
  simp [treeTranslation_treeVector]
/-- If [t lies strictly between zero and one](hyp:ht), [tree translation by gh
equals tree translation by g composed with tree translation by h](goal). -/
lemma treeTranslation_mul (t : ℝ) (ht : DeformationRange t) (g h : FG) :
    treeTranslation t ht (g * h) = treeTranslation t ht g * treeTranslation t ht h := by
  apply LinearIsometryEquiv.toLinearIsometry_injective
  apply LinearIsometry.toContinuousLinearMap_injective
  apply treeTranslation_ext t ht
  intro x
  simp [treeTranslation_treeVector, mul_assoc]
/-- For [a real deformation parameter t](hyp:t) [strictly between zero and one](hyp:ht),
[the tree unitary representation](goal) assigns to each group element its tree
translation as a unitary operator on the square-summable Hilbert space on the group. -/
noncomputable def treeUnitaryRep (t : ℝ) (ht : DeformationRange t) :
    FG →* unitary (Op KSp) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    { toFun := treeTranslation t ht
      map_one' := treeTranslation_one t ht
      map_mul' := treeTranslation_mul t ht }
/-- If [t lies strictly between zero and one](hyp:ht), [the tree representation of g
sends the root-path vector at x to the root-path vector at gx](goal). -/
lemma treeUnitaryRep_treeVector (t : ℝ) (ht : DeformationRange t) (g x : FG) :
    (treeUnitaryRep t ht g : Op KSp) (treeVector t ht x) = treeVector t ht (g * x) :=
  treeTranslation_treeVector t ht g x
/-- If [t lies strictly between zero and one](hyp:ht), [the inner product of the
image of the identity coordinate vector under any free generator in the tree
representation with that same coordinate vector equals t](goal). -/
lemma treeUnitaryRep_coefficient (t : ℝ) (ht : DeformationRange t) (i : ℕ) :
    ⟪(treeUnitaryRep t ht (gen i) : Op KSp) (delta 1), delta 1⟫_ℂ = (t : ℂ) := by
  rw [← treeVector_one t ht, treeUnitaryRep_treeVector, mul_one, treeVector_one]
  exact treeVector_gen_coefficient t ht i

end Papers.OaiNearInclusionsVon.ReusedTree
