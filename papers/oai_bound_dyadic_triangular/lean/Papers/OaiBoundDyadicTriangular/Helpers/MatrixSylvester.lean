module

public import Papers.OaiBoundDyadicTriangular.Helpers.TraceCoordinates

/-!
# A basis-independent trace formula for the supported Hessian

The Sylvester equation for the square-root derivative identifies the spectral
quadratic form with a Hilbert--Schmidt pairing, including singular matrices.
-/

public section

open Matrix
open scoped BigOperators MatrixOrder

namespace Papers.OaiBoundDyadicTriangular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If [P is real symmetric](hyp:hP), [K annihilates the kernel of P](hyp:hK),
and [the j-th eigenvalue of P is zero](hyp:hj), then [the j-th column of K times
the orthonormal eigenvector matrix of P is zero](goal). -/
-- @node: supported_eigenvector_column_zero
lemma supported_eigenvector_column_zero (P K : Matrix ι ι ℝ)
    (hP : P.IsHermitian) (hK : SupportedOn P K) (j : ι)
    (hj : hP.eigenvalues j = 0) :
    (K * (hP.eigenvectorUnitary : Matrix ι ι ℝ))ᵀ j = 0 := by
  have hzero := hK.annihilates (hP.eigenvectorBasis j)
    (by rw [hP.mulVec_eigenvectorBasis, hj, zero_smul])
  ext i
  exact congrFun hzero i

/-- If [P is real symmetric](hyp:hP), [K annihilates the kernel of P](hyp:hK),
[K is symmetric](hyp:hSymm), and [at least one of the i-th and j-th eigenvalues
of P is zero](hyp:hij), then [the corresponding entry of K in the orthonormal
eigenbasis of P is zero](goal). -/
-- @node: supported_eigenvector_entry_zero
lemma supported_eigenvector_entry_zero (P K : Matrix ι ι ℝ)
    (hP : P.IsHermitian) (hK : SupportedOn P K) (hSymm : K.IsSymm)
    (i j : ι) (hij : hP.eigenvalues i = 0 ∨ hP.eigenvalues j = 0) :
    ((hP.eigenvectorUnitary : Matrix ι ι ℝ).transpose * K *
      (hP.eigenvectorUnitary : Matrix ι ι ℝ)) i j = 0 := by
  have hcol (j : ι) (hj : hP.eigenvalues j = 0) (i : ι) :
      ((hP.eigenvectorUnitary : Matrix ι ι ℝ).transpose * K *
        (hP.eigenvectorUnitary : Matrix ι ι ℝ)) i j = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have hz := supported_eigenvector_column_zero P K hP hK j hj
    simp only [Matrix.transpose_apply, funext_iff] at hz
    simp [hz]
  rcases hij with hi | hj
  · have hs : ((hP.eigenvectorUnitary : Matrix ι ι ℝ).transpose * K *
        (hP.eigenvectorUnitary : Matrix ι ι ℝ)).IsSymm := by
      change (_ * K * _).transpose = _
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hSymm.eq,
        Matrix.mul_assoc]
    rw [← hs.apply i j]
    exact hcol i hi j
  · exact hcol j hj i

/-- If [P is positive semidefinite](hyp:hP), then [its positive square root,
expressed in P's orthonormal eigenbasis, is diagonal with entries equal to the
square roots of P's eigenvalues](goal). -/
-- @node: sqrt_eigenvector_coordinates
lemma sqrt_eigenvector_coordinates (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    Unitary.conjStarAlgAut ℝ _ (star hP.isHermitian.eigenvectorUnitary) (CFC.sqrt P) =
      diagonal (fun i => Real.sqrt (hP.isHermitian.eigenvalues i)) := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ P, hP.isHermitian.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, ← Unitary.conjStarAlgAut_mul_apply,
    Unitary.star_mul_self]
  rw [map_one]
  simp only [StarAlgEquiv.one_apply, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
  simp only [Real.sqrt]

/-- [The trace of the transpose of K times X equals the sum of the products of
their corresponding entries after conjugating both matrices by the same
orthogonal matrix](goal). -/
-- @node: trace_pairing_unitary_coordinates
lemma trace_pairing_unitary_coordinates (U : Matrix.unitaryGroup ι ℝ)
    (K X : Matrix ι ι ℝ) :
    (K.transpose * X).trace = ∑ i, ∑ j,
      (Unitary.conjStarAlgAut ℝ _ U K) i j *
      (Unitary.conjStarAlgAut ℝ _ U X) i j := by
  rw [← trace_unitary_coordinate_change U (K.transpose * X), map_mul]
  have ht : Unitary.conjStarAlgAut ℝ _ U K.transpose =
      (Unitary.conjStarAlgAut ℝ _ U K).transpose := by
    simpa only [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      map_star (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U) K
  rw [ht]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- If [P is positive semidefinite](hyp:hP), [K is symmetric](hyp:hK),
[K annihilates the kernel of P](hyp:hSupported), and [the square root of P times
X plus X times the square root of P equals K](hyp:hEquation), then [the supported
Hessian form at P in direction K equals three halves times the trace of the
transpose of K times X](goal).

The identity holds for singular matrices and any solution of the Sylvester equation. -/
-- @node: hessForm_eq_trace_of_sylvester
lemma hessForm_eq_trace_of_sylvester (P K X : Matrix ι ι ℝ)
    (hP : P.PosSemidef) (hK : K.IsSymm) (hSupported : SupportedOn P K)
    (hEquation : CFC.sqrt P * X + X * CFC.sqrt P = K) :
    hessForm P hP.isHermitian K = (3 / 2 : ℝ) * (K.transpose * X).trace := by
  let C := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ)
    (star hP.isHermitian.eigenvectorUnitary)
  have hC (A : Matrix ι ι ℝ) : C A =
      (hP.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ).transpose * A *
      (hP.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
    simp only [C, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial]
  have hEq := congrArg C hEquation
  change C (CFC.sqrt P * X + X * CFC.sqrt P) = C K at hEq
  simp only [map_add, map_mul, show C (CFC.sqrt P) =
    diagonal (fun i => Real.sqrt (hP.isHermitian.eigenvalues i)) from
      sqrt_eigenvector_coordinates P hP] at hEq
  rw [trace_pairing_unitary_coordinates (star hP.isHermitian.eigenvectorUnitary)]
  unfold hessForm
  change (3 / 2 : ℝ) * (∑ i, ∑ j, if 0 < hP.isHermitian.eigenvalues i ∧
      0 < hP.isHermitian.eigenvalues j then
      (C K) i j ^ 2 / (Real.sqrt (hP.isHermitian.eigenvalues i) +
        Real.sqrt (hP.isHermitian.eigenvalues j)) else 0) =
    (3 / 2 : ℝ) * ∑ i, ∑ j, (C K) i j * (C X) i j
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · have hd : Real.sqrt (hP.isHermitian.eigenvalues i) +
        Real.sqrt (hP.isHermitian.eigenvalues j) ≠ 0 :=
      ne_of_gt (add_pos (Real.sqrt_pos.mpr hij.1) (Real.sqrt_pos.mpr hij.2))
    have he := congrFun (congrFun hEq i) j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    apply (div_eq_iff hd).mpr
    rw [← he]
    ring
  · have hz : hP.isHermitian.eigenvalues i = 0 ∨ hP.isHermitian.eigenvalues j = 0 := by
      have hi := hP.eigenvalues_nonneg i
      have hj := hP.eigenvalues_nonneg j
      by_cases h : 0 < hP.isHermitian.eigenvalues i
      · exact Or.inr (le_antisymm (le_of_not_gt (fun hj => hij ⟨h, hj⟩)) hj)
      · exact Or.inl (le_antisymm (le_of_not_gt h) hi)
    have hzero : C K i j = 0 := by
      rw [hC]
      exact supported_eigenvector_entry_zero P K hP.isHermitian hSupported hK i j hz
    rw [hzero, zero_mul]

omit [DecidableEq ι] in
/-- If [M is a real symmetric matrix](hyp:hM), then [M squared is positive
semidefinite](goal). -/
-- @node: hermitian_square_posSemidef
lemma hermitian_square_posSemidef (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    (M * M).PosSemidef := by
  simpa only [hM.eq] using Matrix.posSemidef_conjTranspose_mul_self M

/-- If [M is a real symmetric matrix](hyp:hM), then [the positive square root
of M squared, expressed in M's orthonormal eigenbasis, is diagonal with entries
equal to the absolute values of M's eigenvalues](goal). -/
-- @node: sqrt_square_eigenvector_coordinates
lemma sqrt_square_eigenvector_coordinates (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    Unitary.conjStarAlgAut ℝ _ (star hM.eigenvectorUnitary) (CFC.sqrt (M * M)) =
      diagonal (fun i => |hM.eigenvalues i|) := by
  let C := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hM.eigenvectorUnitary)
  have hDiag : C M = diagonal hM.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hM.conjStarAlgAut_star_eigenvectorUnitary
  let B := C.symm (diagonal (fun i => |hM.eigenvalues i|))
  have hB : B.PosSemidef := by
    have hd : (diagonal (fun i => |hM.eigenvalues i|)).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun i => abs_nonneg _)
    simpa only [B, C, Unitary.conjStarAlgAut_symm_apply, Unitary.coe_star,
      star_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      hd.mul_mul_conjTranspose_same (hM.eigenvectorUnitary : Matrix ι ι ℝ)
  have hs : M * M = B ^ 2 := by
    apply C.injective
    change C (M * M) = C (B ^ 2)
    simp only [map_mul, map_pow, hDiag, B, C.apply_symm_apply]
    rw [sq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    nlinarith [sq_abs (hM.eigenvalues i)]
  have hr : CFC.sqrt (M * M) = B :=
    (CFC.sqrt_eq_iff (M * M) B (hermitian_square_posSemidef M hM).nonneg hB.nonneg).mpr
      (by simpa only [sq] using hs.symm)
  change C (CFC.sqrt (M * M)) = _
  rw [hr]
  exact C.apply_symm_apply _

omit [DecidableEq ι] in
/-- If [M is a real symmetric matrix](hyp:hM), then [multiplying any matrix D
on both sides by M produces a matrix that annihilates the kernel of M squared](goal). -/
-- @node: sandwich_supportedOn_square
lemma sandwich_supportedOn_square (M D : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    SupportedOn (M * M) (M * D * M) := by
  constructor
  intro x hx
  have hm : M *ᵥ x = 0 :=
    (Matrix.conjTranspose_mul_self_mulVec_eq_zero M x).mp (by simpa only [hM.eq] using hx)
  simp only [← Matrix.mulVec_mulVec, hm, Matrix.mulVec_zero]

/-- If [M is real symmetric](hyp:hM) and [D is symmetric](hyp:hD), then [the
supported Hessian form at M squared in direction M times D times M equals three
halves times the sum over eigenvalue pairs of the product of their squared
absolute values, divided by the sum of their absolute values, times the squared
corresponding entry of D in M's orthonormal eigenbasis](goal).

A pair of zero eigenvalues contributes zero. The Sylvester equation makes this
expression independent of the eigenbasis chosen for M squared. -/
-- @node: hessForm_square_sandwich_eq_spectral
lemma hessForm_square_sandwich_eq_spectral (M D : Matrix ι ι ℝ)
    (hM : M.IsHermitian) (hD : D.IsSymm) :
    let E := Unitary.conjStarAlgAut ℝ _ (star hM.eigenvectorUnitary) D
    let m := hM.eigenvalues
    hessForm (M * M) (hermitian_square_posSemidef M hM).isHermitian (M * D * M) =
      (3 / 2 : ℝ) * ∑ i, ∑ j,
        |m i| ^ 2 * |m j| ^ 2 / (|m i| + |m j|) * E i j ^ 2 := by
  let C := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hM.eigenvectorUnitary)
  let m := hM.eigenvalues
  let E := C D
  let Y : Matrix ι ι ℝ := fun i j => m i * m j * E i j / (|m i| + |m j|)
  let X := C.symm Y
  have hDiag : C M = diagonal m := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hM.conjStarAlgAut_star_eigenvectorUnitary
  have hK (i j : ι) : C (M * D * M) i j = m i * m j * E i j := by
    simp only [map_mul, hDiag, Matrix.diagonal_mul, Matrix.mul_diagonal]
    change m i * E i j * m j = _
    ring
  have hEquation : CFC.sqrt (M * M) * X + X * CFC.sqrt (M * M) = M * D * M := by
    apply C.injective
    change C (CFC.sqrt (M * M) * X + X * CFC.sqrt (M * M)) = C (M * D * M)
    simp only [map_add, map_mul, show C (CFC.sqrt (M * M)) = diagonal (fun i => |m i|)
      from sqrt_square_eigenvector_coordinates M hM, X, C.apply_symm_apply]
    ext i j
    rw [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [← map_mul, ← map_mul, hK]
    change |m i| * (m i * m j * E i j / (|m i| + |m j|)) +
      (m i * m j * E i j / (|m i| + |m j|)) * |m j| = m i * m j * E i j
    by_cases hden : |m i| + |m j| = 0
    · have hi : m i = 0 := abs_eq_zero.mp (by
        have := abs_nonneg (m j)
        have := abs_nonneg (m i)
        linarith)
      simp [hi]
    · field_simp
  have hSymm : (M * D * M).IsSymm := by
    have hm := Matrix.isHermitian_iff_isSymm.mp hM
    change (M * D * M).transpose = _
    simp only [Matrix.transpose_mul, hm.eq, hD.eq, Matrix.mul_assoc]
  rw [hessForm_eq_trace_of_sylvester (M * M) (M * D * M) X
    (hermitian_square_posSemidef M hM) hSymm (sandwich_supportedOn_square M D hM) hEquation,
    trace_pairing_unitary_coordinates (star hM.eigenvectorUnitary)]
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change C (M * D * M) i j * C X i j = _
  rw [hK, show C X = Y from C.apply_symm_apply Y]
  change (m i * m j * E i j) * (m i * m j * E i j / (|m i| + |m j|)) =
    |m i| ^ 2 * |m j| ^ 2 / (|m i| + |m j|) * E i j ^ 2
  rw [sq_abs, sq_abs]
  ring

end Papers.OaiBoundDyadicTriangular
