module

public import Papers.OaiBoundDyadicTriangular.Helpers.MatrixSylvester

/-!
# Transport of the supported Hessian

The Sylvester equation makes invariance under an isometric embedding independent
of the eigenbases chosen on the original space and its extension by zero.
-/

public section

open Matrix
open scoped BigOperators MatrixOrder

namespace Papers.OaiBoundDyadicTriangular

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

-- @node: exists_sqrt_sylvester_solution
/-- If [P is positive semidefinite](hyp:hP), [K is symmetric](hyp:hK), and
[K annihilates the kernel of P](hyp:hSupported), then [there is a matrix X
such that √P X + X √P = K](goal), even when P is singular. -/
lemma exists_sqrt_sylvester_solution (P K : Matrix ι ι ℝ)
    (hP : P.PosSemidef) (hK : K.IsSymm) (hSupported : SupportedOn P K) :
    ∃ X : Matrix ι ι ℝ, CFC.sqrt P * X + X * CFC.sqrt P = K := by
  let C := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ)
    (star hP.isHermitian.eigenvectorUnitary)
  let p := hP.isHermitian.eigenvalues
  let Y : Matrix ι ι ℝ := fun i j => C K i j / (Real.sqrt (p i) + Real.sqrt (p j))
  refine ⟨C.symm Y, C.injective ?_⟩
  change C (CFC.sqrt P * C.symm Y + C.symm Y * CFC.sqrt P) = C K
  simp only [map_add, map_mul, show C (CFC.sqrt P) =
    diagonal (fun i => Real.sqrt (p i)) from sqrt_eigenvector_coordinates P hP,
    C.apply_symm_apply]
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  change Real.sqrt (p i) * (C K i j / (Real.sqrt (p i) + Real.sqrt (p j))) +
    (C K i j / (Real.sqrt (p i) + Real.sqrt (p j))) * Real.sqrt (p j) = C K i j
  by_cases hd : Real.sqrt (p i) + Real.sqrt (p j) = 0
  · have hi : p i = 0 := by
      have hs : Real.sqrt (p i) = 0 := le_antisymm
        (by linarith [Real.sqrt_nonneg (p j)]) (Real.sqrt_nonneg (p i))
      exact le_antisymm (Real.sqrt_eq_zero'.mp hs) (hP.eigenvalues_nonneg i)
    have hz : C K i j = 0 := by
      change ((hP.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ).transpose * K *
        (hP.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)) i j = 0
      exact supported_eigenvector_entry_zero P K hP.isHermitian hSupported hK i j
        (Or.inl hi)
    rw [hz]
    simp
  · field_simp

-- @node: posSemidef_isometric_extension
/-- If [P is positive semidefinite](hyp:hP), then [F P Fᵀ is positive
semidefinite](goal) for any rectangular matrix F. -/
lemma posSemidef_isometric_extension (F : Matrix κ ι ℝ) (P : Matrix ι ι ℝ)
    (hP : P.PosSemidef) : (F * P * F.transpose).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    hP.mul_mul_conjTranspose_same F

-- @node: isometric_extension_mul
/-- If [the columns of F are orthonormal](hyp:hF), then [the product of
F A Fᵀ and F B Fᵀ equals F (AB) Fᵀ](goal). -/
lemma isometric_extension_mul (F : Matrix κ ι ℝ) (hF : F.transpose * F = 1)
    (A B : Matrix ι ι ℝ) :
    (F * A * F.transpose) * (F * B * F.transpose) = F * (A * B) * F.transpose := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.transpose F, hF, Matrix.one_mul]

-- @node: sqrt_isometric_extension
/-- If [the columns of F are orthonormal](hyp:hF) and [P is positive
semidefinite](hyp:hP), then [the positive square root of F P Fᵀ equals
F √P Fᵀ](goal). -/
lemma sqrt_isometric_extension (F : Matrix κ ι ℝ) (hF : F.transpose * F = 1)
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    CFC.sqrt (F * P * F.transpose) = F * CFC.sqrt P * F.transpose := by
  apply (CFC.sqrt_eq_iff (F * P * F.transpose) (F * CFC.sqrt P * F.transpose)
    (posSemidef_isometric_extension F P hP).nonneg
    (posSemidef_isometric_extension F (CFC.sqrt P)
      (CFC.sqrt_nonneg P).posSemidef).nonneg).mpr
  rw [isometric_extension_mul F hF]
  congr 2
  exact CFC.sqrt_mul_sqrt_self P hP.nonneg

-- @node: supportedOn_isometric_extension
/-- If [the columns of F are orthonormal](hyp:hF) and [K annihilates the
kernel of P](hyp:hSupported), then [F K Fᵀ annihilates the kernel of
F P Fᵀ](goal). -/
lemma supportedOn_isometric_extension (F : Matrix κ ι ℝ) (hF : F.transpose * F = 1)
    (P K : Matrix ι ι ℝ) (hSupported : SupportedOn P K) :
    SupportedOn (F * P * F.transpose) (F * K * F.transpose) := by
  constructor
  intro x hx
  have hp : P *ᵥ (F.transpose *ᵥ x) = 0 := by
    have he := congrArg (fun y => F.transpose *ᵥ y) hx
    simpa only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      hF, Matrix.one_mul] using he
  simp only [← Matrix.mulVec_mulVec, hSupported.annihilates _ hp, Matrix.mulVec_zero]

-- @node: trace_pairing_isometric_extension
/-- If [the columns of F are orthonormal](hyp:hF), then [the trace of
(F K Fᵀ)ᵀ (F X Fᵀ) equals the trace of Kᵀ X](goal). -/
lemma trace_pairing_isometric_extension (F : Matrix κ ι ℝ) (hF : F.transpose * F = 1)
    (K X : Matrix ι ι ℝ) :
    ((F * K * F.transpose).transpose * (F * X * F.transpose)).trace =
      (K.transpose * X).trace := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc F K.transpose F.transpose, isometric_extension_mul F hF]
  rw [Matrix.trace_mul_cycle, hF, Matrix.one_mul]

-- @node: hessForm_isometric_extension
/-- If [the columns of F are orthonormal](hyp:hF), [P is positive
semidefinite](hyp:hP), [K is symmetric](hyp:hK), and [K annihilates the
kernel of P](hyp:hSupported), then [the supported Hessian quadratic form at
F P Fᵀ in direction F K Fᵀ equals its value at P in direction K](goal). -/
lemma hessForm_isometric_extension (F : Matrix κ ι ℝ) (hF : F.transpose * F = 1)
    (P K : Matrix ι ι ℝ) (hP : P.PosSemidef) (hK : K.IsSymm)
    (hSupported : SupportedOn P K) :
    hessForm (F * P * F.transpose) (posSemidef_isometric_extension F P hP).isHermitian
      (F * K * F.transpose) = hessForm P hP.isHermitian K := by
  obtain ⟨X, hX⟩ := exists_sqrt_sylvester_solution P K hP hK hSupported
  have hSymm : (F * K * F.transpose).IsSymm := by
    change (F * K * F.transpose).transpose = _
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hK.eq, Matrix.mul_assoc]
  have hEq : CFC.sqrt (F * P * F.transpose) * (F * X * F.transpose) +
      (F * X * F.transpose) * CFC.sqrt (F * P * F.transpose) = F * K * F.transpose := by
    rw [sqrt_isometric_extension F hF P hP, isometric_extension_mul F hF,
      isometric_extension_mul F hF, ← Matrix.add_mul, ← Matrix.mul_add, hX]
  rw [hessForm_eq_trace_of_sylvester _ _ _ (posSemidef_isometric_extension F P hP)
    hSymm (supportedOn_isometric_extension F hF P K hSupported) hEq,
    hessForm_eq_trace_of_sylvester P K X hP hK hSupported hX,
    trace_pairing_isometric_extension F hF]

end Papers.OaiBoundDyadicTriangular
