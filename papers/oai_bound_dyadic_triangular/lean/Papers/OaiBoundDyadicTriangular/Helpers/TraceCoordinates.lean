module

public import Papers.OaiBoundDyadicTriangular.Helpers.TraceSpectral
public import Papers.OaiBoundDyadicTriangular.Helpers.TraceBlocks
public import Mathlib.Data.Prod.Lex

/-!
# The cubic estimate in matrix coordinates

Order the eigenvalues by absolute value, expand the cubic trace in an
orthonormal eigenbasis, and transfer the contraction to those coordinates.
-/

public section

open Matrix
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: spectral_cubic_le_five_Q_unordered
/-- If [D is symmetric](hyp:hD), [the identity minus D is positive semidefinite](hyp:hMinus),
and [the identity plus D is positive semidefinite](hyp:hPlus), then [the absolute cyclic
sum of mᵢ mⱼ mₖ Dᵢⱼ Dⱼₖ Dₖᵢ is at most five times the sum of
|mᵢ|² |mⱼ|² Dᵢⱼ² / (|mᵢ| + |mⱼ|) over all pairs of indices](goal). -/
lemma spectral_cubic_le_five_Q_unordered {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (D : Matrix ι ι ℝ) (hD : D.IsSymm)
    (hMinus : (1 - D).PosSemidef) (hPlus : (1 + D).PosSemidef) :
    |∑ i, ∑ j, ∑ k, m i * m j * m k * D i j * D j k * D k i| ≤
      5 * ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 / (|m i| + |m j|) * D i j ^ 2 := by
  classical
  let key (i : ι) : ℝ ×ₗ Fin (Fintype.card ι) :=
    toLex (-|m i|, Fintype.equivFin ι i)
  have hKey : Function.Injective key := by
    intro i j h
    exact (Fintype.equivFin ι).injective (congrArg (fun x => (ofLex x).2) h)
  let : LinearOrder ι := LinearOrder.lift' key hKey
  have hOrder : Antitone (fun i => |m i|) := by
    intro i j hij
    have h := (Prod.Lex.le_iff'.mp (show key i ≤ key j from hij)).1
    exact neg_le_neg_iff.mp h
  convert spectral_cubic_le_five_Q m D hD
    (by convert hMinus using 1; ext i j; simp [Matrix.one_apply])
    (by convert hPlus using 1; ext i j; simp [Matrix.one_apply]) hOrder using 1

-- @node: trace_diagonal_cubic_eq_sum
/-- [The trace of the cube of D times the diagonal matrix with entries m equals
the sum of mᵢ mⱼ mₖ Dᵢⱼ Dⱼₖ Dₖᵢ over all triples of indices](goal). -/
lemma trace_diagonal_cubic_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (D : Matrix ι ι ℝ) :
    ((D * diagonal m) * (D * diagonal m) * (D * diagonal m)).trace =
      ∑ i, ∑ j, ∑ k, m i * m j * m k * D i j * D j k * D k i := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

-- @node: trace_unitary_coordinate_change
/-- [Conjugating A by the orthogonal matrix U preserves its trace](goal). -/
lemma trace_unitary_coordinate_change {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul]

-- @node: unitary_coordinate_change_contraction
/-- If [the identity minus D is positive semidefinite](hyp:hMinus) and
[the identity plus D is positive semidefinite](hyp:hPlus), then [both the identity
minus and the identity plus the orthogonal conjugate of D by U are positive
semidefinite](goal). -/
lemma unitary_coordinate_change_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (D : Matrix ι ι ℝ)
    (hMinus : (1 - D).PosSemidef) (hPlus : (1 + D).PosSemidef) :
    (1 - Unitary.conjStarAlgAut ℝ _ U D).PosSemidef ∧
      (1 + Unitary.conjStarAlgAut ℝ _ U D).PosSemidef := by
  constructor
  · simpa only [Unitary.conjStarAlgAut_apply, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star,
      Unitary.coe_mul_star_self] using
      hMinus.mul_mul_conjTranspose_same (U : Matrix ι ι ℝ)
  · simpa only [Unitary.conjStarAlgAut_apply, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star,
      Unitary.coe_mul_star_self] using
      hPlus.mul_mul_conjTranspose_same (U : Matrix ι ι ℝ)

-- @node: unitary_coordinate_change_isSymm
/-- If [D is symmetric](hyp:hD), then [its orthogonal conjugate by U is symmetric](goal). -/
lemma unitary_coordinate_change_isSymm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (D : Matrix ι ι ℝ) (hD : D.IsSymm) :
    (Unitary.conjStarAlgAut ℝ _ U D).IsSymm := by
  change ((U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ)).transpose = _
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_mul, Matrix.transpose_transpose, hD.eq, Matrix.mul_assoc]

-- @node: matrix_cubic_le_five_spectral_Q
/-- Suppose [M is a real Hermitian matrix](hyp:hM), [D is symmetric](hyp:hD),
[the identity minus D is positive semidefinite](hyp:hMinus), and [the identity plus D
is positive semidefinite](hyp:hPlus). Then [the absolute trace of the cube of DM
is at most five times the sum of |mᵢ|² |mⱼ|² Eᵢⱼ² / (|mᵢ| + |mⱼ|), where m are
the eigenvalues of M and E represents D in the orthonormal eigenbasis of M](goal). -/
lemma matrix_cubic_le_five_spectral_Q {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M D : Matrix ι ι ℝ) (hM : M.IsHermitian) (hD : D.IsSymm)
    (hMinus : (1 - D).PosSemidef) (hPlus : (1 + D).PosSemidef) :
    let E := Unitary.conjStarAlgAut ℝ _ (star hM.eigenvectorUnitary) D
    let m := hM.eigenvalues
    |((D * M) * (D * M) * (D * M)).trace| ≤
      5 * ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 / (|m i| + |m j|) * E i j ^ 2 := by
  let U := star hM.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hDiag : C M = diagonal hM.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hM.conjStarAlgAut_star_eigenvectorUnitary
  have hTrace : ((D * M) * (D * M) * (D * M)).trace =
      ((C D * diagonal hM.eigenvalues) * (C D * diagonal hM.eigenvalues) *
        (C D * diagonal hM.eigenvalues)).trace := by
    rw [← trace_unitary_coordinate_change U ((D * M) * (D * M) * (D * M))]
    change (C ((D * M) * (D * M) * (D * M))).trace = _
    simp only [map_mul, hDiag]
  dsimp only
  rw [hTrace, trace_diagonal_cubic_eq_sum]
  have hContraction := unitary_coordinate_change_contraction U D hMinus hPlus
  exact spectral_cubic_le_five_Q_unordered hM.eigenvalues (C D)
    (unitary_coordinate_change_isSymm U D hD) hContraction.1 hContraction.2

-- @node: triangle_trace_le_spectral_Q
/-- If [the three vertex matrices are symmetric](hyp:hSymmetry) and [each vertex
matrix lies between minus the identity and the identity in positive semidefinite
order](hyp:hContraction), then [six times the absolute trace of D₀W₀D₁W₁D₂W₂
is at most five times the sum of |mᵢ|² |mⱼ|² Eᵢⱼ² / (|mᵢ| + |mⱼ|), where m are
the eigenvalues of the symmetric triangle block matrix and E represents the
block diagonal vertex matrix in its orthonormal eigenbasis](goal). -/
lemma triangle_trace_le_spectral_Q
    {H₀ H₁ H₂ : Type*} [Fintype H₀] [DecidableEq H₀]
    [Fintype H₁] [DecidableEq H₁] [Fintype H₂] [DecidableEq H₂]
    (W₀ : Matrix H₀ H₁ ℝ) (W₁ : Matrix H₁ H₂ ℝ) (W₂ : Matrix H₂ H₀ ℝ)
    (D₀ : Matrix H₀ H₀ ℝ) (D₁ : Matrix H₁ H₁ ℝ) (D₂ : Matrix H₂ H₂ ℝ)
    (hSymmetry : TraceSymmetry D₀ D₁ D₂) (hContraction : TraceContraction D₀ D₁ D₂) :
    let M := offDiagonalBlocks W₀ W₂.transpose W₀.transpose W₂ W₁ W₁.transpose
    let D := vertexDiagonal D₀ D₁ D₂
    let hM : M.IsHermitian :=
      Matrix.isHermitian_iff_isSymm.mpr (triangleBlocks_isSymm W₀ W₁ W₂)
    let E := Unitary.conjStarAlgAut ℝ _ (star hM.eigenvectorUnitary) D
    let m := hM.eigenvalues
    6 * |(D₀ * W₀ * D₁ * W₁ * D₂ * W₂).trace| ≤
      5 * ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 / (|m i| + |m j|) * E i j ^ 2 := by
  dsimp only
  have hCon := vertexDiagonal_contraction D₀ D₁ D₂ hContraction
  have hBound := matrix_cubic_le_five_spectral_Q
    (offDiagonalBlocks W₀ W₂.transpose W₀.transpose W₂ W₁ W₁.transpose)
    (vertexDiagonal D₀ D₁ D₂)
    (Matrix.isHermitian_iff_isSymm.mpr (triangleBlocks_isSymm W₀ W₁ W₂))
    (vertexDiagonal_isSymm D₀ D₁ D₂ hSymmetry) hCon.1 hCon.2
  dsimp only at hBound
  rw [weighted_triangle_cube_trace W₀ W₁ W₂ D₀ D₁ D₂ hSymmetry,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] at hBound
  exact hBound

end Papers.OaiBoundDyadicTriangular
