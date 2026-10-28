module

public import Papers.OaiExactSemidefiniteLift.Helpers.LiftCertificate

/-!
# Equivalence with the finite moment lift

The basis and complex-polynomial conventions are fixed by their definitions.
There are no pin assumptions and no certificate assumptions in the equivalence.
-/

public section

namespace Papers.OaiExactSemidefiniteLift

open Matrix

-- @node: prop:lift
/-- [A pair of symmetric four-by-four matrices and a real three-vector belongs
to the closed hyperbolicity cone exactly when there exists a lift functional
satisfying their output equations with a positive semidefinite moment matrix](goal). -/
lemma lift_equivalence (X Z : Sym4) (y : Fin 3 → ℝ) :
    (X, Z, y) ∈ coneK ↔
      ∃ Λ : LiftFunctional, OutputEquations Λ X Z y ∧ (momentMatrixH Λ).PosSemidef := by
  obtain ⟨θ, η, ξ, rfl⟩ := angular_plane_surjective y
  constructor
  · intro hK
    have hL := (slice_equivalence.1 θ η ξ X Z).mp hK
    refine ⟨evaluationFunctional θ X Z η ξ, ?_, ?_⟩
    · exact ⟨fun i j => eval_coordXElem i j θ X Z η ξ,
        fun i j => eval_coordZElem i j θ X Z η ξ,
        fun l => eval_YplaneElem l θ X Z η ξ⟩
    · apply (momentMatrixH_posSemidef_iff _).mpr
      intro q hq
      change 0 ≤ evalLift (quadraticFunctionElem q) θ X Z η ξ
      rw [eval_quadraticFunctionElem q hq]
      have h := hL.dotProduct_mulVec_nonneg
        (fun i => q (sliceIndexEquiv i) θ)
      rw [← sliceIndexEquiv.sum_comp]
      simp_rw [← sliceIndexEquiv.sum_comp]
      simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum,
        slicePencil20, Equiv.symm_apply_apply, mul_assoc] using h
  · rintro ⟨Λ, hout, hH⟩
    have hm := (momentMatrixH_posSemidef_iff Λ).mp hH
    have hX := feasible_X_posSemidef Λ X Z (Yplane θ η ξ) hout hm
    have hc := feasible_certificate Λ X Z (Yplane θ η ξ) hout hm
    exact (slice_equivalence.1 θ η ξ X Z).mpr
      (certificate_slice_posSemidef X Z θ η ξ hX hc)

end Papers.OaiExactSemidefiniteLift
