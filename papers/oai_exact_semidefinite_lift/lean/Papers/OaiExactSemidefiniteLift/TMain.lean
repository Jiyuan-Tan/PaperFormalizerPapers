module

public import Papers.OaiExactSemidefiniteLift.Helpers.Lift
public import Papers.OaiExactSemidefiniteLift.Helpers.Coordinates

/-!
# A homogeneous semidefinite lift of size 100 with 307 auxiliary variables

The equivalence is over every symmetric output triple, including the singular
boundary. The output order is the paper's upper-triangular lexicographic order.
-/

public section

namespace Papers.OaiExactSemidefiniteLift

open Matrix
open scoped BigOperators

-- @node: thm:main
/-- [There exist 23 fixed real symmetric 100-by-100 matrices A and 307 fixed real
symmetric 100-by-100 matrices B such that, for every triple x consisting of two
real symmetric 4-by-4 matrices and a real three-vector, x belongs to the closed
hyperbolicity cone K if and only if some choice of 307 real auxiliary coefficients
makes the sum of the A matrices weighted by the 23 output coordinates of x and
the B matrices weighted by those auxiliary coefficients positive semidefinite](goal).
The output coordinates list the upper-triangular entries of the first matrix,
then those of the second matrix, both in lexicographic order, followed by the
three vector entries. -/
theorem exact_semidefinite_lift :
    ∃ (A : Fin 23 → Mat 100) (B : Fin 307 → Mat 100),
    -- @realizes N(matrix size 100)
    -- @realizes m(auxiliary count 307)
      (∀ ν, (A ν).IsSymm) ∧ -- @realizes A_\nu(fixed real symmetric matrices of size 100)
      (∀ j, (B j).IsSymm) ∧ -- @realizes B_j(fixed real symmetric matrices of size 100)
      ∀ x : V, x ∈ coneK ↔
        ∃ v : Fin 307 → ℝ, -- @realizes v(real auxiliary vector chosen for each output)
          (∑ ν : Fin 23, outputCoords x ν • A ν +
            ∑ j : Fin 307, v j • B j).PosSemidef := by
  refine ⟨outputMatrix, auxiliaryMatrix, outputMatrix_isSymm, auxiliaryMatrix_isSymm, ?_⟩
  intro x
  rcases x with ⟨X, Z, y⟩
  rw [lift_equivalence]
  constructor
  · rintro ⟨Λ, hOut, hPSD⟩
    refine ⟨fun j => Λ (coeffUnit (freeSlot j)), ?_⟩
    have hCoords := (outputEquations_iff Λ X Z y).mp hOut
    have hRec := functional_reconstruction Λ
    simp only [hCoords] at hRec
    have h100 := (momentMatrix100_posSemidef_iff Λ).mpr hPSD
    rw [hRec, momentMatrix100_fromCoords] at h100
    exact h100
  · rintro ⟨v, hPSD⟩
    refine ⟨functionalFromCoords (outputCoords (X, Z, y)) v, ?_, ?_⟩
    · apply (outputEquations_iff _ X Z y).mpr
      intro ν
      exact functionalFromCoords_outputs _ _ ν
    · apply (momentMatrix100_posSemidef_iff _).mp
      rw [momentMatrix100_fromCoords]
      exact hPSD

end Papers.OaiExactSemidefiniteLift
