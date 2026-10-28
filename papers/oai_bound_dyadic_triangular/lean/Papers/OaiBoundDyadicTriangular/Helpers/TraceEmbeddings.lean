module

public import Papers.OaiBoundDyadicTriangular.Helpers.HessianTransport
public import Papers.OaiBoundDyadicTriangular.Helpers.TraceBlocks

/-!
# Vertex projections and row-star embeddings

The three neighbor spaces embed isometrically in vertex order. These embeddings
identify each common-space Hessian with its original row-star Hessian.
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

variable {H₀ H₁ H₂ : Type*} [Fintype H₀] [DecidableEq H₀]
  [Fintype H₁] [DecidableEq H₁] [Fintype H₂] [DecidableEq H₂]

-- @node: vertexDiagonal_mul
/-- [Multiplying two block diagonal matrices on the three vertex spaces multiplies
their corresponding diagonal blocks](goal). -/
lemma vertexDiagonal_mul (A₀ B₀ : Matrix H₀ H₀ ℝ)
    (A₁ B₁ : Matrix H₁ H₁ ℝ) (A₂ B₂ : Matrix H₂ H₂ ℝ) :
    vertexDiagonal A₀ A₁ A₂ * vertexDiagonal B₀ B₁ B₂ =
      vertexDiagonal (A₀ * B₀) (A₁ * B₁) (A₂ * B₂) := by
  simp [vertexDiagonal, Matrix.fromBlocks_multiply]

-- @node: vertexDiagonal_one
/-- [The block diagonal matrix with identity blocks on all three vertex spaces
is the identity on their direct sum](goal). -/
lemma vertexDiagonal_one :
    vertexDiagonal (1 : Matrix H₀ H₀ ℝ) (1 : Matrix H₁ H₁ ℝ)
      (1 : Matrix H₂ H₂ ℝ) = 1 := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [vertexDiagonal, Matrix.one_apply]

-- @node: vertexProjection
/-- On the direct sum of [the first vertex space](hyp:H₀), [the second vertex
space](hyp:H₁), and [the third vertex space](hyp:H₂), the [projection onto the
vertex selected by v](goal), for [a vertex index v between zero and two](hyp:v),
keeps that vertex's coordinates and sets the other coordinates to zero. -/
def vertexProjection (v : Fin 3) :
    Matrix (H₀ ⊕ (H₁ ⊕ H₂)) (H₀ ⊕ (H₁ ⊕ H₂)) ℝ :=
  ![vertexDiagonal 1 0 0, vertexDiagonal 0 1 0, vertexDiagonal 0 0 1] v

-- @node: vertexProjection_posSemidef
/-- [The coordinate projection onto any one of the three vertex spaces is positive
semidefinite](goal). -/
lemma vertexProjection_posSemidef (v : Fin 3) :
    (vertexProjection (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) v).PosSemidef := by
  fin_cases v <;> dsimp [vertexProjection, vertexDiagonal]
  all_goals apply posSemidef_two_vertex_blocks
  all_goals first | exact Matrix.PosSemidef.one | exact Matrix.PosSemidef.zero |
    exact posSemidef_two_vertex_blocks _ _ Matrix.PosSemidef.one Matrix.PosSemidef.zero |
    exact posSemidef_two_vertex_blocks _ _ Matrix.PosSemidef.zero Matrix.PosSemidef.one |
    exact posSemidef_two_vertex_blocks _ _ Matrix.PosSemidef.zero Matrix.PosSemidef.zero

-- @node: vertexProjection_complement_posSemidef
/-- [The identity minus the coordinate projection onto any selected vertex space
is positive semidefinite](goal). -/
lemma vertexProjection_complement_posSemidef (v : Fin 3) :
    (1 - vertexProjection (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) v).PosSemidef := by
  have he : 1 - vertexProjection (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) v =
      ![vertexDiagonal 0 1 1, vertexDiagonal 1 0 1, vertexDiagonal 1 1 0] v := by
    fin_cases v <;> ext i j <;>
      rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [vertexProjection, vertexDiagonal, Matrix.one_apply]
  rw [he]
  fin_cases v <;> dsimp [vertexDiagonal]
  all_goals apply posSemidef_two_vertex_blocks
  all_goals first | exact Matrix.PosSemidef.one | exact Matrix.PosSemidef.zero |
    exact posSemidef_two_vertex_blocks _ _ Matrix.PosSemidef.one Matrix.PosSemidef.one |
    exact posSemidef_two_vertex_blocks _ _ Matrix.PosSemidef.zero Matrix.PosSemidef.one |
    exact posSemidef_two_vertex_blocks _ _ Matrix.PosSemidef.one Matrix.PosSemidef.zero

-- @node: vertexProjection_idempotent
/-- [Applying the coordinate projection onto a selected vertex space twice gives
the same matrix as applying it once](goal). -/
lemma vertexProjection_idempotent (v : Fin 3) :
    vertexProjection (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) v * vertexProjection v =
      vertexProjection v := by
  fin_cases v <;> simp [vertexProjection, vertexDiagonal_mul]

-- @node: vertexProjection_commute
/-- [The coordinate projection onto a selected vertex space commutes with the
block diagonal matrix whose vertex blocks are D₀, D₁, and D₂](goal). -/
lemma vertexProjection_commute (v : Fin 3)
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ) :
    vertexProjection v * vertexDiagonal D₀ D₁ D₂ =
      vertexDiagonal D₀ D₁ D₂ * vertexProjection v := by
  fin_cases v <;> simp [vertexProjection, vertexDiagonal_mul]

-- @node: vertexProjection_sum
/-- [The three coordinate projections onto the vertex spaces sum to the identity
on their direct sum](goal). -/
lemma vertexProjection_sum :
    vertexProjection (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) 0 +
      vertexProjection 1 + vertexProjection 2 = 1 := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [vertexProjection, vertexDiagonal, Matrix.one_apply]

-- @node: vertexInclusion0
/-- For [vertex space H₀](hyp:H₀) and the other vertex spaces [H₁](hyp:H₁) and
[H₂](hyp:H₂), the [inclusion of vertex zero into the common space](goal) places
an H₀ vector in the first coordinate block and fills the other blocks with zeros. -/
def vertexInclusion0 : Matrix (H₀ ⊕ (H₁ ⊕ H₂)) H₀ ℝ := Matrix.fromRows 1 0

-- @node: vertexInclusion1
/-- For [vertex space H₁](hyp:H₁) and the other vertex spaces [H₀](hyp:H₀) and
[H₂](hyp:H₂), the [inclusion of vertex one into the common space](goal) places
an H₁ vector in the second coordinate block and fills the other blocks with zeros. -/
def vertexInclusion1 : Matrix (H₀ ⊕ (H₁ ⊕ H₂)) H₁ ℝ :=
  Matrix.fromRows 0 (Matrix.fromRows 1 0)

-- @node: vertexInclusion2
/-- For [vertex space H₂](hyp:H₂) and the other vertex spaces [H₀](hyp:H₀) and
[H₁](hyp:H₁), the [inclusion of vertex two into the common space](goal) places
an H₂ vector in the third coordinate block and fills the other blocks with zeros. -/
def vertexInclusion2 : Matrix (H₀ ⊕ (H₁ ⊕ H₂)) H₂ ℝ :=
  Matrix.fromRows 0 (Matrix.fromRows 0 1)

-- @node: neighborInclusion0
/-- For [vertex space H₀](hyp:H₀) and its neighbor spaces [H₁](hyp:H₁) and
[H₂](hyp:H₂), the [neighbor inclusion at vertex zero](goal) embeds a pair of
neighbor vectors into the common space as zero followed by the H₁ and H₂ vectors. -/
def neighborInclusion0 : Matrix (H₀ ⊕ (H₁ ⊕ H₂)) (H₁ ⊕ H₂) ℝ :=
  Matrix.fromRows 0 1

-- @node: neighborInclusion1
/-- For [vertex space H₁](hyp:H₁) and its neighbor spaces [H₂](hyp:H₂) and
[H₀](hyp:H₀), the [neighbor inclusion at vertex one](goal) takes a pair ordered
as H₂ then H₀ and embeds it into the common space as the H₀ vector, zero, and
the H₂ vector. -/
def neighborInclusion1 : Matrix (H₀ ⊕ (H₁ ⊕ H₂)) (H₂ ⊕ H₀) ℝ :=
  Matrix.fromRows (Matrix.fromCols 0 1) (Matrix.fromRows 0 (Matrix.fromCols 1 0))

-- @node: neighborInclusion2
/-- For [vertex space H₂](hyp:H₂) and its neighbor spaces [H₀](hyp:H₀) and
[H₁](hyp:H₁), the [neighbor inclusion at vertex two](goal) embeds a pair ordered
as H₀ then H₁ into the common space as those two vectors followed by zero. -/
def neighborInclusion2 : Matrix (H₀ ⊕ (H₁ ⊕ H₂)) (H₀ ⊕ H₁) ℝ :=
  Matrix.fromRows (Matrix.fromCols 1 0) (Matrix.fromRows (Matrix.fromCols 0 1) 0)

-- @node: neighborInclusion0_isometry
/-- [The transpose of the neighbor inclusion at vertex zero times that inclusion
is the identity on the combined H₁ and H₂ neighbor space](goal). -/
lemma neighborInclusion0_isometry :
    (neighborInclusion0 (H₀ := H₀) (H₁ := H₁) (H₂ := H₂)).transpose *
      neighborInclusion0 (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) = 1 := by
  simp [neighborInclusion0, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]

-- @node: neighborInclusion1_isometry
/-- [The transpose of the neighbor inclusion at vertex one times that inclusion
is the identity on the combined H₂ and H₀ neighbor space](goal). -/
lemma neighborInclusion1_isometry :
    (neighborInclusion1 (H₀ := H₀) (H₁ := H₁) (H₂ := H₂)).transpose *
      neighborInclusion1 (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) = 1 := by
  simp only [neighborInclusion1, Matrix.transpose_fromRows, Matrix.transpose_fromCols,
    Matrix.transpose_zero, Matrix.transpose_one, Matrix.fromCols_mul_fromRows,
    Matrix.fromRows_mul_fromCols, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
    Matrix.mul_one, zero_add, add_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

-- @node: neighborInclusion2_isometry
/-- [The transpose of the neighbor inclusion at vertex two times that inclusion
is the identity on the combined H₀ and H₁ neighbor space](goal). -/
lemma neighborInclusion2_isometry :
    (neighborInclusion2 (H₀ := H₀) (H₁ := H₁) (H₂ := H₂)).transpose *
      neighborInclusion2 (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) = 1 := by
  simp only [neighborInclusion2, Matrix.transpose_fromRows, Matrix.transpose_fromCols,
    Matrix.transpose_zero, Matrix.transpose_one, Matrix.fromCols_mul_fromRows,
    Matrix.fromRows_mul_fromCols, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
    Matrix.mul_one, zero_add, add_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

-- @node: hessForm_row_isometric_extension
/-- If [D is symmetric](hyp:hD) and [the transpose of F times F is the identity,
so F preserves inner products](hyp:hF), then [the Hessian form associated with
the Gram matrix and D-weighted perturbation of R times the transpose of F equals
the corresponding Hessian form for R](goal). -/
lemma hessForm_row_isometric_extension {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (R : Matrix α β ℝ) (D : Matrix α α ℝ) (hD : D.IsSymm)
    (F : Matrix γ β ℝ) (hF : F.transpose * F = 1) :
    hessForm (rowGram (R * F.transpose)) (rowGram_isHermitian _)
      (rowPerturbation (R * F.transpose) D) =
    hessForm (rowGram R) (rowGram_isHermitian R) (rowPerturbation R D) := by
  have hP : (rowGram R).PosSemidef := by
    simpa only [rowGram, conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self R
  have hK : (rowPerturbation R D).IsSymm := by
    change (R.transpose * D * R).transpose = _
    simp only [rowPerturbation, Matrix.transpose_mul, Matrix.transpose_transpose, hD.eq, Matrix.mul_assoc]
  have hSupported : SupportedOn (rowGram R) (rowPerturbation R D) := by
    constructor
    intro x hx
    have hr : R *ᵥ x = 0 := (Matrix.conjTranspose_mul_self_mulVec_eq_zero R x).mp
      (by simpa only [rowGram, conjTranspose_eq_transpose_of_trivial] using hx)
    simp only [rowPerturbation, ← Matrix.mulVec_mulVec, hr, Matrix.mulVec_zero]
  have hGram : rowGram (R * F.transpose) = F * rowGram R * F.transpose := by
    simp only [rowGram, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hPert : rowPerturbation (R * F.transpose) D = F * rowPerturbation R D * F.transpose := by
    simp only [rowPerturbation, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  simpa only [hGram, hPert] using hessForm_isometric_extension F hF
    (rowGram R) (rowPerturbation R D) hP hK hSupported

-- @node: hessForm_common_row
/-- Suppose [M is symmetric](hyp:hM), [MPM is Hermitian](hyp:hA), [the vertex
perturbation Dv is symmetric](hyp:hDv), and [F preserves inner products, with
its transpose times itself equal to the identity](hyp:hF). If [P equals G times
its transpose](hyp:hProjection), [PD equals G Dv times the transpose of G](hyp:hPerturbation),
and [the transpose of G times M equals R times the transpose of F](hyp:hRow),
then [the Hessian form at MPM in direction MPDM equals the Hessian form at the
Gram matrix of R in the direction of its Dv-weighted perturbation](goal). -/
lemma hessForm_common_row {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (M P D : Matrix γ γ ℝ) (hM : M.IsSymm) (hA : (M * P * M).IsHermitian)
    (G : Matrix γ α ℝ) (R : Matrix α β ℝ) (Dv : Matrix α α ℝ) (hDv : Dv.IsSymm)
    (F : Matrix γ β ℝ) (hF : F.transpose * F = 1)
    (hProjection : P = G * G.transpose)
    (hPerturbation : P * D = G * Dv * G.transpose)
    (hRow : G.transpose * M = R * F.transpose) :
    hessForm (M * P * M) hA (M * P * D * M) =
      hessForm (rowGram R) (rowGram_isHermitian R) (rowPerturbation R Dv) := by
  have hGram : rowGram (R * F.transpose) = M * P * M := by
    rw [← hRow, hProjection]
    simp only [rowGram, Matrix.transpose_mul, Matrix.transpose_transpose,
      hM.eq, Matrix.mul_assoc]
  have hPert : rowPerturbation (R * F.transpose) Dv = M * P * D * M := by
    rw [← hRow, Matrix.mul_assoc M P D, hPerturbation]
    simp only [rowPerturbation, Matrix.transpose_mul, Matrix.transpose_transpose,
      hM.eq, Matrix.mul_assoc]
  simpa only [hGram, hPert] using hessForm_row_isometric_extension R Dv hDv F hF

-- @node: hessForm_vertex0
/-- If [the three vertex perturbation matrices are symmetric](hyp:hSymmetry),
then [for any verification that M times the vertex-zero projection times M is
Hermitian, the common-space Hessian form at vertex zero equals the
Hessian form of its row matrix, formed by adjoining W₀ and the transpose of W₂,
with vertex perturbation D₀](goal). Here M is the symmetric triangle block matrix
and the common-space perturbation direction is M times the vertex-zero projection
times the block diagonal vertex perturbation times M. -/
lemma hessForm_vertex0
    (W₀ : Matrix H₀ H₁ ℝ) (W₁ : Matrix H₁ H₂ ℝ) (W₂ : Matrix H₂ H₀ ℝ)
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ)
    (hSymmetry : TraceSymmetry D₀ D₁ D₂) :
    let M := offDiagonalBlocks W₀ W₂.transpose W₀.transpose W₂ W₁ W₁.transpose
    let D := vertexDiagonal D₀ D₁ D₂
    ∀ hA : (M * vertexProjection 0 * M).IsHermitian,
    hessForm (M * vertexProjection 0 * M) hA (M * vertexProjection 0 * D * M) =
      hessForm (rowGram (rowStar W₀ W₂)) (rowGram_isHermitian _)
        (rowPerturbation (rowStar W₀ W₂) D₀) := by
  dsimp only
  intro hA
  apply hessForm_common_row _ _ _ (triangleBlocks_isSymm W₀ W₁ W₂) hA
    vertexInclusion0 (rowStar W₀ W₂) D₀ hSymmetry.1
    neighborInclusion0 neighborInclusion0_isometry
  · simp [vertexProjection, vertexInclusion0, vertexDiagonal,
      Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols]
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> simp
  · simp [vertexProjection, vertexInclusion0, vertexDiagonal_mul, vertexDiagonal,
      Matrix.transpose_fromRows, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      Matrix.fromBlocks_multiply]
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> simp
  · simp [vertexInclusion0, neighborInclusion0, offDiagonalBlocks, rowStar,
      Matrix.transpose_fromRows, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows, Matrix.mul_fromCols]

-- @node: hessForm_vertex1
/-- If [the three vertex perturbation matrices are symmetric](hyp:hSymmetry),
then [for any verification that M times the vertex-one projection times M is
Hermitian, the common-space Hessian form at vertex one equals the
Hessian form of its row matrix, formed by adjoining W₁ and the transpose of W₀,
with vertex perturbation D₁](goal). Here M is the symmetric triangle block matrix
and the common-space perturbation direction is M times the vertex-one projection
times the block diagonal vertex perturbation times M. -/
lemma hessForm_vertex1
    (W₀ : Matrix H₀ H₁ ℝ) (W₁ : Matrix H₁ H₂ ℝ) (W₂ : Matrix H₂ H₀ ℝ)
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ)
    (hSymmetry : TraceSymmetry D₀ D₁ D₂) :
    let M := offDiagonalBlocks W₀ W₂.transpose W₀.transpose W₂ W₁ W₁.transpose
    let D := vertexDiagonal D₀ D₁ D₂
    ∀ hA : (M * vertexProjection 1 * M).IsHermitian,
    hessForm (M * vertexProjection 1 * M) hA (M * vertexProjection 1 * D * M) =
      hessForm (rowGram (rowStar W₁ W₀)) (rowGram_isHermitian _)
        (rowPerturbation (rowStar W₁ W₀) D₁) := by
  dsimp only
  intro hA
  apply hessForm_common_row _ _ _ (triangleBlocks_isSymm W₀ W₁ W₂) hA
    vertexInclusion1 (rowStar W₁ W₀) D₁ hSymmetry.2.1
    neighborInclusion1 neighborInclusion1_isometry
  · simp [vertexProjection, vertexInclusion1, vertexDiagonal,
      Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols]
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> simp
  · simp [vertexProjection, vertexInclusion1, vertexDiagonal_mul, vertexDiagonal,
      Matrix.transpose_fromRows, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      Matrix.fromBlocks_multiply]
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> simp
  · simp [vertexInclusion1, neighborInclusion1, offDiagonalBlocks, rowStar,
      Matrix.transpose_fromRows, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows, Matrix.mul_fromCols]

-- @node: hessForm_vertex2
/-- If [the three vertex perturbation matrices are symmetric](hyp:hSymmetry),
then [for any verification that M times the vertex-two projection times M is
Hermitian, the common-space Hessian form at vertex two equals the
Hessian form of its row matrix, formed by adjoining W₂ and the transpose of W₁,
with vertex perturbation D₂](goal). Here M is the symmetric triangle block matrix
and the common-space perturbation direction is M times the vertex-two projection
times the block diagonal vertex perturbation times M. -/
lemma hessForm_vertex2
    (W₀ : Matrix H₀ H₁ ℝ) (W₁ : Matrix H₁ H₂ ℝ) (W₂ : Matrix H₂ H₀ ℝ)
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ)
    (hSymmetry : TraceSymmetry D₀ D₁ D₂) :
    let M := offDiagonalBlocks W₀ W₂.transpose W₀.transpose W₂ W₁ W₁.transpose
    let D := vertexDiagonal D₀ D₁ D₂
    ∀ hA : (M * vertexProjection 2 * M).IsHermitian,
    hessForm (M * vertexProjection 2 * M) hA (M * vertexProjection 2 * D * M) =
      hessForm (rowGram (rowStar W₂ W₁)) (rowGram_isHermitian _)
        (rowPerturbation (rowStar W₂ W₁) D₂) := by
  dsimp only
  intro hA
  apply hessForm_common_row _ _ _ (triangleBlocks_isSymm W₀ W₁ W₂) hA
    vertexInclusion2 (rowStar W₂ W₁) D₂ hSymmetry.2.2
    neighborInclusion2 neighborInclusion2_isometry
  · simp [vertexProjection, vertexInclusion2, vertexDiagonal,
      Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols]
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> simp
  · simp [vertexProjection, vertexInclusion2, vertexDiagonal_mul, vertexDiagonal,
      Matrix.transpose_fromRows, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      Matrix.fromBlocks_multiply]
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> simp
  · simp [vertexInclusion2, neighborInclusion2, offDiagonalBlocks, rowStar,
      Matrix.transpose_fromRows, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows, Matrix.mul_fromCols]

end Papers.OaiBoundDyadicTriangular
