module

public import Papers.OaiBoundDyadicTriangular.Basic

/-!
# Cubic traces on the common vertex space

The six closed walks of length three split into two orientations. Rectangular
trace cyclicity identifies the three starting vertices in each orientation.
-/

@[expose] public section

open Matrix

namespace Papers.OaiBoundDyadicTriangular

variable {H₀ H₁ H₂ : Type*} [Fintype H₀] [Fintype H₁] [Fintype H₂]

-- @node: offDiagonalBlocks
/-- Given blocks [A in position zero-one](hyp:A), [B in position zero-two](hyp:B),
[C in position one-zero](hyp:C), [D in position two-zero](hyp:D),
[E in position one-two](hyp:E), and [F in position two-one](hyp:F),
[the off-diagonal block matrix places these six blocks in their designated
positions and has zero blocks on its three diagonal positions](goal). -/
def offDiagonalBlocks
    (A : Matrix H₀ H₁ ℝ) (B : Matrix H₀ H₂ ℝ)
    (C : Matrix H₁ H₀ ℝ) (D : Matrix H₂ H₀ ℝ)
    (E : Matrix H₁ H₂ ℝ) (F : Matrix H₂ H₁ ℝ) :
    Matrix (H₀ ⊕ (H₁ ⊕ H₂)) (H₀ ⊕ (H₁ ⊕ H₂)) ℝ :=
  Matrix.fromBlocks 0 (Matrix.fromCols A B) (Matrix.fromRows C D)
    (Matrix.fromBlocks 0 E F 0)

-- @node: trace_vertexBlocks
/-- [The trace of a two-by-two block matrix with diagonal blocks A and D and
off-diagonal blocks B and C equals the trace of A plus the trace of D](goal). -/
lemma trace_vertexBlocks (A : Matrix H₀ H₀ ℝ) (B : Matrix H₀ H₁ ℝ)
    (C : Matrix H₁ H₀ ℝ) (D : Matrix H₁ H₁ ℝ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

-- @node: trace_offDiagonalBlocks_cube
/-- [The trace of the cube of the three-vertex matrix with zero diagonal blocks
and off-diagonal blocks A, B, C, D, E, F equals three times the trace of A times
E times D plus three times the trace of B times F times C](goal). -/
lemma trace_offDiagonalBlocks_cube
    (A : Matrix H₀ H₁ ℝ) (B : Matrix H₀ H₂ ℝ)
    (C : Matrix H₁ H₀ ℝ) (D : Matrix H₂ H₀ ℝ)
    (E : Matrix H₁ H₂ ℝ) (F : Matrix H₂ H₁ ℝ) :
    ((offDiagonalBlocks A B C D E F * offDiagonalBlocks A B C D E F) *
      offDiagonalBlocks A B C D E F).trace =
      3 * (A * E * D).trace + 3 * (B * F * C).trace := by
  simp only [offDiagonalBlocks, Matrix.fromBlocks_multiply, Matrix.zero_mul,
    Matrix.mul_zero, zero_add, add_zero, Matrix.fromCols_mul_fromRows,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromBlocks_mul_fromRows,
    Matrix.fromRows_mul_fromCols, Matrix.add_mul,
    trace_vertexBlocks, Matrix.trace_add]
  rw [Matrix.trace_mul_cycle E D A, Matrix.trace_mul_cycle F C B,
    ← Matrix.trace_mul_cycle B F C, ← Matrix.trace_mul_cycle A E D,
    Matrix.trace_zero]
  simp only [Matrix.trace_zero]
  ring

-- @node: vertexDiagonal
/-- For [a square block at vertex zero](hyp:D₀), [a square block at vertex
one](hyp:D₁), and [a square block at vertex two](hyp:D₂), [the vertex diagonal
matrix places these three blocks on its diagonal and zero blocks everywhere
else](goal). -/
def vertexDiagonal (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ)
    (D₂ : Matrix H₂ H₂ ℝ) :
    Matrix (H₀ ⊕ (H₁ ⊕ H₂)) (H₀ ⊕ (H₁ ⊕ H₂)) ℝ :=
  Matrix.fromBlocks D₀ 0 0 (Matrix.fromBlocks D₁ 0 0 D₂)

omit [Fintype H₀] [Fintype H₁] [Fintype H₂] in
-- @node: vertexDiagonal_isSymm
/-- If [the three vertex blocks are symmetric](hyp:hSymmetry), [the block
diagonal matrix formed from them is symmetric](goal). -/
lemma vertexDiagonal_isSymm
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ)
    (hSymmetry : TraceSymmetry D₀ D₁ D₂) :
    (vertexDiagonal D₀ D₁ D₂).IsSymm := by
  exact hSymmetry.1.fromBlocks (Matrix.transpose_zero)
    (hSymmetry.2.1.fromBlocks (Matrix.transpose_zero) hSymmetry.2.2)

omit [Fintype H₀] [Fintype H₁] [Fintype H₂] in
-- @node: triangleBlocks_isSymm
/-- [The three-vertex matrix with zero diagonal blocks, edge blocks W₀, W₁,
and W₂ around the triangle, and their transposes in the reverse positions is
symmetric](goal). -/
lemma triangleBlocks_isSymm
    (W₀ : Matrix H₀ H₁ ℝ) (W₁ : Matrix H₁ H₂ ℝ) (W₂ : Matrix H₂ H₀ ℝ) :
    (offDiagonalBlocks W₀ W₂.transpose W₀.transpose W₂ W₁ W₁.transpose).IsSymm := by
  apply Matrix.IsSymm.fromBlocks (Matrix.isSymm_zero)
  · simp only [Matrix.transpose_fromCols, Matrix.transpose_transpose]
  · exact (Matrix.isSymm_zero).fromBlocks rfl (Matrix.isSymm_zero)

-- @node: vertexDiagonal_mul_offDiagonalBlocks
/-- [Multiplying the off-diagonal block matrix on the left by the vertex diagonal
matrix multiplies blocks A and B on the left by D₀, blocks C and E by D₁, and
blocks D and F by D₂, while leaving the diagonal blocks zero](goal). -/
lemma vertexDiagonal_mul_offDiagonalBlocks
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ)
    (A : Matrix H₀ H₁ ℝ) (B : Matrix H₀ H₂ ℝ)
    (C : Matrix H₁ H₀ ℝ) (D : Matrix H₂ H₀ ℝ)
    (E : Matrix H₁ H₂ ℝ) (F : Matrix H₂ H₁ ℝ) :
    vertexDiagonal D₀ D₁ D₂ * offDiagonalBlocks A B C D E F =
      offDiagonalBlocks (D₀ * A) (D₀ * B) (D₁ * C) (D₂ * D) (D₁ * E) (D₂ * F) := by
  simp only [vertexDiagonal, offDiagonalBlocks, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_fromCols,
    Matrix.fromBlocks_mul_fromRows]

-- @node: weighted_triangle_cube_trace
/-- If [the vertex weights D₀, D₁, and D₂ are symmetric](hyp:hSymmetry),
[the trace of the cube of the vertex diagonal matrix times the symmetric
triangle matrix equals six times the trace of the ordered product D₀, W₀,
D₁, W₁, D₂, W₂](goal). -/
lemma weighted_triangle_cube_trace
    (W₀ : Matrix H₀ H₁ ℝ) (W₁ : Matrix H₁ H₂ ℝ) (W₂ : Matrix H₂ H₀ ℝ)
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ)
    (hSymmetry : TraceSymmetry D₀ D₁ D₂) :
    let M := offDiagonalBlocks W₀ W₂.transpose W₀.transpose W₂ W₁ W₁.transpose
    let D := vertexDiagonal D₀ D₁ D₂
    ((D * M * (D * M)) * (D * M)).trace =
      6 * (D₀ * W₀ * D₁ * W₁ * D₂ * W₂).trace := by
  dsimp only
  rw [vertexDiagonal_mul_offDiagonalBlocks, trace_offDiagonalBlocks_cube]
  have hReverse : ((D₀ * W₂.transpose) * (D₂ * W₁.transpose) *
      (D₁ * W₀.transpose)).trace = (D₀ * W₀ * D₁ * W₁ * D₂ * W₂).trace := by
    rw [← Matrix.trace_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      hSymmetry.1.eq,
      hSymmetry.2.1.eq,
      hSymmetry.2.2.eq]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm _ D₀]
    simp only [← Matrix.mul_assoc]
  rw [hReverse]
  simp only [← Matrix.mul_assoc]
  ring

-- @node: posSemidef_two_vertex_blocks
/-- If [A is positive semidefinite](hyp:hA) and [B is positive
semidefinite](hyp:hB), [the block diagonal matrix with blocks A and B is
positive semidefinite](goal). -/
lemma posSemidef_two_vertex_blocks {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr
      ((Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).fromBlocks
        Matrix.transpose_zero (Matrix.isHermitian_iff_isSymm.mp hB.isHermitian))
  · intro x
    simpa [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks,
      Finset.mul_sum, Finset.sum_add_distrib] using
      add_nonneg (hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
        (hB.dotProduct_mulVec_nonneg (x ∘ Sum.inr))

-- @node: vertexDiagonal_contraction
/-- If [the identity minus each vertex block and the identity plus each vertex
block are positive semidefinite](hyp:hContraction), [both the identity minus
the vertex diagonal matrix and the identity plus the vertex diagonal matrix
are positive semidefinite](goal). -/
lemma vertexDiagonal_contraction
    [DecidableEq H₀] [DecidableEq H₁] [DecidableEq H₂]
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ)
    (hContraction : TraceContraction D₀ D₁ D₂) :
    (1 - vertexDiagonal D₀ D₁ D₂).PosSemidef ∧
      (1 + vertexDiagonal D₀ D₁ D₂).PosSemidef := by
  rcases hContraction with ⟨h₀m, h₀p, h₁m, h₁p, h₂m, h₂p⟩
  constructor
  · convert posSemidef_two_vertex_blocks (1 - D₀)
      (Matrix.fromBlocks (1 - D₁) 0 0 (1 - D₂)) h₀m
      (posSemidef_two_vertex_blocks _ _ h₁m h₂m) using 1
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [vertexDiagonal, Matrix.one_apply]
  · convert posSemidef_two_vertex_blocks (1 + D₀)
      (Matrix.fromBlocks (1 + D₁) 0 0 (1 + D₂)) h₀p
      (posSemidef_two_vertex_blocks _ _ h₁p h₂p) using 1
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [vertexDiagonal, Matrix.one_apply]

end Papers.OaiBoundDyadicTriangular
