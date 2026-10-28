module

public import Papers.OaiExactSemidefiniteLift.Helpers.Slice

/-!
# Matrix algebra for the scalar certificate tests
-/

public section

namespace Papers.OaiExactSemidefiniteLift

open Matrix
open scoped BigOperators

-- @node: slice_quadratic_expansion
/-- For [symmetric four-by-four matrices X and Z](hyp:X,Z), [real parameters θ, η, and ξ](hyp:θ,η,ξ),
[four arbitrary four-dimensional top-block vectors](hyp:a), and [a four-dimensional bottom-block vector](hyp:u),
[the pencil's quadratic form is the sum of the four X quadratic forms, twice the sum of
the skew-block cross terms, and the Z quadratic form](goal). -/
lemma slice_quadratic_expansion (X Z : Sym4) (θ η ξ : ℝ)
    (a : Fin 4 → Fin 4 → ℝ) -- @realizes a_j(arbitrary four real top-block vectors)
    (u : Fin 4 → ℝ) :
    let v : SliceIndex → ℝ := Sum.elim (fun ji => a ji.1 ji.2) u
    dotProduct v ((slicePencil θ X Z η ξ).mulVec v) =
      (∑ j : Fin 4, dotProduct (a j) ((X : Mat 4).mulVec (a j))) +
      2 * (∑ j : Fin 4, dotProduct (a j) ((Bskew (factorColumn θ η ξ j)).mulVec u)) +
      dotProduct u ((Z : Mat 4).mulVec u) := by
  dsimp only
  let atop : Fin 4 × Fin 4 → ℝ := fun ji => a ji.1 ji.2
  have htop : (Matrix.kronecker (1 : Mat 4) (X : Mat 4)).mulVec atop =
      fun ji => (X : Mat 4).mulVec (a ji.1) ji.2 := by
    ext ⟨j, i⟩
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
      Matrix.one_apply, atop]
  have hcross : dotProduct atop ((sliceB θ η ξ).mulVec u) =
      ∑ j : Fin 4, dotProduct (a j) ((Bskew (factorColumn θ η ξ j)).mulVec u) := by
    simp [dotProduct, Fintype.sum_prod_type, atop, sliceB, Matrix.mulVec]
  change dotProduct (Sum.elim atop u)
    ((Matrix.fromBlocks _ _ _ _).mulVec (Sum.elim atop u)) = _
  rw [Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  rw [sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_add,
    Matrix.dotProduct_transpose_mulVec, hcross, htop]
  have hdiag : dotProduct atop (fun ji => (X : Mat 4).mulVec (a ji.1) ji.2) =
      ∑ j : Fin 4, dotProduct (a j) ((X : Mat 4).mulVec (a j)) := by
    simp [dotProduct, Fintype.sum_prod_type, atop]
  rw [hdiag]
  ring

-- @node: Bskew_mulVec_Ju
/-- For [a three-dimensional vector r](hyp:r) and [a four-dimensional vector u](hyp:u),
[the skew matrix associated with r applied to u equals the transpose of the matrix J
associated with u applied to r](goal). -/
lemma Bskew_mulVec_Ju (r : Fin 3 → ℝ) (u : Fin 4 → ℝ) :
    (Bskew r).mulVec u = (Ju u)ᵀ.mulVec r := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Bskew, Ju, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Bskew, Ju,
      Matrix.transpose_apply, Fin.cases_succ, Fin.cases_zero]
    fin_cases j <;> simp [Matrix.one_apply] <;> ring

-- @node: trace_columns_quadratic
/-- For [a three-by-three matrix A](hyp:A) and [a three-by-four matrix C](hyp:C),
[the sum of the A quadratic forms of C's columns equals the trace of A times C times
the transpose of C](goal). -/
lemma trace_columns_quadratic (A : Mat 3) (C : Matrix (Fin 3) (Fin 4) ℝ) :
    (∑ j : Fin 4, dotProduct (fun i => C i j) (A.mulVec (fun i => C i j))) =
      (A * (C * Cᵀ)).trace := by
  rw [Matrix.trace_mul_cycle' A C Cᵀ]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

-- @node: certificate_top_column
/-- For [symmetric four-by-four matrices X and D](hyp:X,D), [a four-dimensional vector u](hyp:u),
and [a three-dimensional vector b](hyp:b), [the X quadratic form at minus D times the
transpose of J(u) times b equals the quadratic form at b with matrix
J(u) D X D J(u) transpose](goal). -/
lemma certificate_top_column (X D : Sym4) (u : Fin 4 → ℝ) (b : Fin 3 → ℝ) :
    dotProduct (-((D : Mat 4) * (Ju u)ᵀ).mulVec b)
      ((X : Mat 4).mulVec (-((D : Mat 4) * (Ju u)ᵀ).mulVec b)) =
    dotProduct b ((Ju u * (D : Mat 4) * (X : Mat 4) * (D : Mat 4) *
      (Ju u)ᵀ).mulVec b) := by
  have hD : (D : Mat 4)ᵀ = (D : Mat 4) :=
    (Matrix.isHermitian_iff_isSymm.mp D.property).eq
  simp only [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [dotProduct_comm _ ((X : Mat 4).mulVec _),
    ← Matrix.dotProduct_transpose_mulVec ((D : Mat 4) * (Ju u)ᵀ)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hD,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

-- @node: certificate_cross_column
/-- For [a symmetric four-by-four matrix D](hyp:D), [a four-dimensional vector u](hyp:u),
and [three-dimensional vectors b and r](hyp:b,r), [the inner product of minus D times
the transpose of J(u) times b with the skew matrix of r applied to u equals minus
the inner product of r with J(u) D J(u) transpose applied to b](goal). -/
lemma certificate_cross_column (D : Sym4) (u : Fin 4 → ℝ)
    (b r : Fin 3 → ℝ) :
    dotProduct (-((D : Mat 4) * (Ju u)ᵀ).mulVec b) ((Bskew r).mulVec u) =
      -dotProduct r ((Ju u * (D : Mat 4) * (Ju u)ᵀ).mulVec b) := by
  rw [Bskew_mulVec_Ju, neg_dotProduct, Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

-- @node: trace_sandwich_entries
/-- For [a three-by-four matrix A](hyp:A), [a four-by-four matrix X](hyp:X), and
[a four-by-three matrix B](hyp:B), [the trace of A X B equals the sum over all entries
of X of that entry times the transposed-position entry of B A](goal). -/
lemma trace_sandwich_entries (A : Matrix (Fin 3) (Fin 4) ℝ)
    (X : Mat 4) (B : Matrix (Fin 4) (Fin 3) ℝ) :
    (A * X * B).trace = ∑ i : Fin 4, ∑ j : Fin 4, (B * A) j i * X i j := by
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  simp [Matrix.trace, Matrix.mul_apply, mul_comm]

-- @node: Qpol_left_coordinates
/-- For [three-dimensional vectors y and z](hyp:y,z), [the polarized matrix Q(y,z)
is the sum of the polarized matrices obtained by replacing y with each standard
basis vector, weighted by the corresponding coordinate of y](goal). -/
lemma Qpol_left_coordinates (y z : Fin 3 → ℝ) :
    Qpol y z = ∑ l : Fin 3, y l • Qpol (Pi.single l 1) z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qpol, Qmat, QuadraticMap.polar, Fin.sum_univ_succ, Pi.single_apply] <;> ring

-- @node: trace_columns_pairing
/-- For [a three-by-three matrix S](hyp:S) and [three-by-four matrices F and C](hyp:F,C),
[the sum of the inner products of each column of F with S applied to the matching
column of C equals the trace of F transpose times S times C](goal). -/
lemma trace_columns_pairing (S : Mat 3) (F C : Matrix (Fin 3) (Fin 4) ℝ) :
    (∑ j : Fin 4, dotProduct (fun i => F i j) (S.mulVec (fun i => C i j))) =
      (Fᵀ * S * C).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

end Papers.OaiExactSemidefiniteLift
