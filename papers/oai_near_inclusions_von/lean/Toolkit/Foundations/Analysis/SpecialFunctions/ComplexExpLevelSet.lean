module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Separation.Lemmas

/-!
# Toolkit.Foundations.Analysis.SpecialFunctions.ComplexExpLevelSet

Continuous functions with values in the level set exp⁻¹(1) = 2πiℤ
-/

public section

namespace Toolkit.Foundations.Analysis.SpecialFunctions

section

open Filter
open scoped Topology Matrix.Norms.Operator

-- @node: exponential_one_continuousOn_constant
/-- In [a topological space X](hyp:X), suppose [a set S is connected in the sense that it cannot
be separated into two nonempty relatively open pieces](hyp:S,hS), [a complex-valued function L](hyp:L)
[is continuous on S](hyp:hL), and [the exponential of L equals one everywhere on S](hyp:hexp).
For [points x and y](hyp:x,y) with [x in S](hyp:hx) and [y in S](hyp:hy), [L has the same value at x and y](goal). -/
lemma eq_of_cexp_eq_one_of_isPreconnected {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsPreconnected S) {L : X → ℂ} (hL : ContinuousOn L S)
    (hexp : ∀ x ∈ S, Complex.exp (L x) = 1) {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    L x = L y := by
  have hc : (Complex.exp ⁻¹' ({1} : Set ℂ)).Countable :=
    (Set.countable_singleton (1 : ℂ)).preimage_cexp
  have himage : L '' S ⊆ Complex.exp ⁻¹' ({1} : Set ℂ) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hexp z hz
  exact hc.isTotallyDisconnected _ himage (hS.image L hL)
    (Set.mem_image_of_mem L hx) (Set.mem_image_of_mem L hy)

end

end Toolkit.Foundations.Analysis.SpecialFunctions
