module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.LinearAlgebra.Complex.Module
import Toolkit.Foundations.Analysis.Normed.FiniteDimensionalOperators

/-! Eigenspaces of finite-dimensional unitaries, indexed by the unit circle. -/

public section

namespace Papers.OaiNearInclusionsVon

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
  [CompleteSpace D]

/-- If [U is unitary](hyp:hU), [v is nonzero](hyp:hv), and
[U sends v to z times v](hyp:he), then [the absolute value of z is one](goal). -/
-- @node: unitary_eigenvalue_norm
lemma unitary_eigenvalue_norm (U : D →L[ℂ] D) (hU : U ∈ unitary _)
    {z : ℂ} {v : D} (hv : v ≠ 0) (he : U v = z • v) : ‖z‖ = 1 := by
  have hn := (Unitary.linearIsometryEquiv (⟨U, hU⟩ : unitary _)).norm_map v
  change ‖U v‖ = ‖v‖ at hn
  rw [he, norm_smul] at hn
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hv) (hn.trans (one_mul ‖v‖).symm)

/-- If [U is unitary](hyp:hU) on a finite-dimensional complex Hilbert space,
then [its eigenspaces with eigenvalues on the unit circle span the whole space](goal). -/
-- @node: unitary_iSup_circle_eigenspace_eq_top
lemma unitary_iSup_circle_eigenspace_eq_top [FiniteDimensional ℂ D]
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) :
    (⨆ z : Circle, Module.End.eigenspace U.toLinearMap (z : ℂ)) = ⊤ := by
  haveI : IsStarNormal U := isStarNormal_of_mem_unitary hU
  apply top_unique
  rw [← Toolkit.Foundations.Analysis.Normed.iSup_eigenspace_eq_top_of_isStarNormal U]
  refine iSup_le fun z => ?_
  intro v hv
  by_cases hv0 : v = 0
  · simpa [hv0] using (Submodule.zero_mem
      (⨆ z : Circle, Module.End.eigenspace U.toLinearMap (z : ℂ)))
  · have hz := unitary_eigenvalue_norm U hU hv0 (Module.End.mem_eigenspace_iff.mp hv)
    exact (le_iSup (fun z : Circle => Module.End.eigenspace U.toLinearMap (z : ℂ))
      ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩) hv

/-- If [U is unitary](hyp:hU) on a finite-dimensional complex Hilbert space
and [the continuous linear maps S and T agree on every vector that U
multiplies by a scalar on the unit circle](hyp:h), then [S and T are equal](goal). -/
-- @node: unitary_ext_on_eigenvectors
lemma unitary_ext_on_eigenvectors [FiniteDimensional ℂ D]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) (S T : D →L[ℂ] E)
    (h : ∀ (z : Circle) (v : D), U v = (z : ℂ) • v → S v = T v) : S = T := by
  ext v
  have hv : v ∈ ⨆ z : Circle, Module.End.eigenspace U.toLinearMap (z : ℂ) := by
    rw [unitary_iSup_circle_eigenspace_eq_top U hU]
    trivial
  exact Submodule.iSup_induction (motive := fun v => S v = T v) _ hv
    (fun z v hv => h z v (Module.End.mem_eigenspace_iff.mp hv))
    (by simp only [map_zero])
    (fun x y hx hy => by simp only [map_add, hx, hy])

/-- If [U is unitary](hyp:hU) and [U sends v to z times v, with z on the
unit circle](hyp:hv), then [the adjoint of U sends v to the complex
conjugate of z times v](goal). -/
-- @node: unitary_star_apply_eigen
lemma unitary_star_apply_eigen (U : D →L[ℂ] D) (hU : U ∈ unitary _)
    (z : Circle) (v : D) (hv : U v = (z : ℂ) • v) :
    star U v = star (z : ℂ) • v := by
  have h := congrArg (fun w => star U w) hv
  have hz : star (z : ℂ) * (z : ℂ) = 1 := by
    rw [show star (z : ℂ) = (z : ℂ)⁻¹ from
      (Circle.coe_inv_eq_conj z).symm.trans (Circle.coe_inv z),
      inv_mul_cancel₀ z.coe_ne_zero]
  have hu : star U (U v) = v := by
    change (star U * U) v = v
    rw [Unitary.star_mul_self_of_mem hU, one_apply_eq_self]
  rw [hu, map_smul] at h
  calc
    star U v = (star (z : ℂ) * (z : ℂ)) • star U v := by rw [hz, one_smul]
    _ = star (z : ℂ) • v := by rw [mul_smul, ← h]

end Papers.OaiNearInclusionsVon
