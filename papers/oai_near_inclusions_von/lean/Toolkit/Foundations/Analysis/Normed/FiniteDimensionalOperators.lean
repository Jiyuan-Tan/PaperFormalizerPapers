module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Separation.Lemmas

/-!
# Toolkit.Foundations.Analysis.Normed.FiniteDimensionalOperators

Spectral and unitarity facts for operators on finite-dimensional complex Hilbert spaces
-/

public section

namespace Toolkit.Foundations.Analysis.Normed

section

open Filter
open scoped Topology Matrix.Norms.Operator

-- @node: finite_norm_preserving_mem_unitary
/-- On [a finite-dimensional complex Hilbert space E](hyp:E), if [a continuous linear operator T](hyp:T)
[preserves the norm of every vector](hyp:hT), then [T is unitary](goal). -/
lemma mem_unitary_of_forall_norm_apply_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] (T : E →L[ℂ] E)
    (hT : ∀ x, ‖T x‖ = ‖x‖) : T ∈ unitary (E →L[ℂ] E) := by
  let f : E →ₗᵢ[ℂ] E := { T.toLinearMap with norm_map' := hT }
  let e := LinearIsometryEquiv.ofSurjective f
    (LinearMap.injective_iff_surjective.mp f.injective)
  exact (Unitary.linearIsometryEquiv.symm e).property

end

end Toolkit.Foundations.Analysis.Normed

namespace Toolkit.Foundations.Analysis.Normed

section

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

/-- For a normal operator on a finite-dimensional complex Hilbert space,
[its eigenspaces, taken over all complex eigenvalues, span the whole space](goal). -/
-- @node: normal_iSup_eigenspace_eq_top
lemma iSup_eigenspace_eq_top_of_isStarNormal [FiniteDimensional ℂ D]
    (U : D →L[ℂ] D) [IsStarNormal U] :
    (⨆ z : ℂ, Module.End.eigenspace U.toLinearMap z) = ⊤ := by
  let R : D →L[ℂ] D := realPart U
  let J : D →L[ℂ] D := imaginaryPart U
  have hR : R.toLinearMap.IsSymmetric := (realPart U).property.isSymmetric
  have hJ : J.toLinearMap.IsSymmetric := (imaginaryPart U).property.isSymmetric
  have hc : Commute R.toLinearMap J.toLinearMap := by
    exact congrArg ContinuousLinearMap.toLinearMap (Commute.realPart_imaginaryPart U).eq
  have hspan := hR.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hJ hc
  apply top_unique
  rw [← hspan]
  refine iSup_le fun a => iSup_le fun b => ?_
  apply le_trans _ (le_iSup (fun z : ℂ => Module.End.eigenspace U.toLinearMap z)
    (a + Complex.I * b))
  intro v hv
  have ha := Module.End.mem_eigenspace_iff.mp hv.1
  have hb := Module.End.mem_eigenspace_iff.mp hv.2
  change R v = a • v at ha
  change J v = b • v at hb
  apply Module.End.mem_eigenspace_iff.mpr
  change U v = (a + Complex.I * b) • v
  rw [← realPart_add_I_smul_imaginaryPart U]
  change R v + Complex.I • J v = _
  rw [ha, hb, add_smul, mul_smul]

end

end Toolkit.Foundations.Analysis.Normed
