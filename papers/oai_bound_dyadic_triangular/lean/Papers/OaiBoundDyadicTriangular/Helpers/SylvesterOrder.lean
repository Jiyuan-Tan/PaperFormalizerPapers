module

public import Papers.OaiBoundDyadicTriangular.Helpers.HessianTransport
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! # Order comparison on the Hilbert--Schmidt matrix space

The positive Sylvester operator reverses order on its supported inverse
quadratic forms. Completing a square proves this also for singular operators.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace Papers.OaiBoundDyadicTriangular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @node: realMatrixComplexification
/-- [Real matrix complexification embeds real square matrices into complex
square matrices by treating each real entry as a complex number, preserving
addition, multiplication, real scalar multiplication, and adjoints](goal). -/
noncomputable def realMatrixComplexification :
    Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℂ where
  __ := (Algebra.ofId ℝ ℂ).mapMatrix
  map_star' A := by
    ext i j
    simp [Matrix.star_apply, Matrix.map_apply]

-- @node: realMatrixComplexification_posSemidef_iff
/-- [The complexification of a real matrix A is positive semidefinite if and
only if A is positive semidefinite](goal). -/
lemma realMatrixComplexification_posSemidef_iff (A : Matrix ι ι ℝ) :
    (realMatrixComplexification A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.isHermitian_iff_isSymm.mpr
      ext i j
      have he := congrArg Complex.re (h.isHermitian.apply i j)
      simpa [realMatrixComplexification, Matrix.map_apply] using he
    · intro x
      have hp := h.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
      simpa [realMatrixComplexification, Matrix.mulVec, dotProduct,
        Matrix.map_apply, ← Complex.ofReal_mul, ← Complex.ofReal_sum] using hp
  · intro h
    exact (map_nonneg realMatrixComplexification h.nonneg).posSemidef

-- @node: realMatrixComplexification_sqrt
/-- If [A is positive semidefinite](hyp:hA), [complexifying its positive square
root gives the positive square root of its complexification](goal). -/
lemma realMatrixComplexification_sqrt (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    realMatrixComplexification (CFC.sqrt A) =
      CFC.sqrt (realMatrixComplexification A) := by
  symm
  apply (CFC.sqrt_eq_iff _ _
    ((realMatrixComplexification_posSemidef_iff A).mpr hA).nonneg
    ((realMatrixComplexification_posSemidef_iff (CFC.sqrt A)).mpr
      (CFC.sqrt_nonneg A).posSemidef).nonneg).mpr
  rw [← map_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]

-- @node: sqrt_nonneg_smul
/-- If [Q is positive semidefinite](hyp:hQ) and [a is nonnegative](hyp:ha),
[the positive square root of a times Q equals the square root of a times the
positive square root of Q](goal). -/
lemma sqrt_nonneg_smul (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef)
    (a : ℝ) (ha : 0 ≤ a) :
    CFC.sqrt (a • Q) = Real.sqrt a • CFC.sqrt Q := by
  apply (CFC.sqrt_eq_iff _ _ (hQ.smul ha).nonneg
    ((CFC.sqrt_nonneg Q).posSemidef.smul (Real.sqrt_nonneg a)).nonneg).mpr
  rw [smul_mul_smul_comm, CFC.sqrt_mul_sqrt_self Q hQ.nonneg,
    ← sq, Real.sq_sqrt ha]

-- @node: sqrt_orderComparison
/-- If [P is positive semidefinite](hyp:hP), [Q is positive semidefinite](hyp:hQ),
[a is nonnegative](hyp:ha), and [a times Q minus P is positive semidefinite](hyp:hPQ),
[the square root of a times the positive square root of Q minus the positive
square root of P is positive semidefinite](goal). -/
lemma sqrt_orderComparison (P Q : Matrix ι ι ℝ) (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (a : ℝ) (ha : 0 ≤ a) (hPQ : (a • Q - P).PosSemidef) :
    (Real.sqrt a • CFC.sqrt Q - CFC.sqrt P).PosSemidef := by
  have hle : P ≤ a • Q := sub_nonneg.mp hPQ.nonneg
  have hs := CFC.sqrt_le_sqrt (realMatrixComplexification P)
    (realMatrixComplexification (a • Q))
    (OrderHomClass.mono realMatrixComplexification hle)
  rw [← realMatrixComplexification_sqrt P hP,
    ← realMatrixComplexification_sqrt (a • Q) (hQ.smul ha),
    sqrt_nonneg_smul Q hQ a ha] at hs
  apply (realMatrixComplexification_posSemidef_iff _).mp
  exact (by simpa only [map_sub] using (sub_nonneg.mpr hs).posSemidef)

-- @node: trace_pairing_comm
/-- [The trace of the transpose of X times Y equals the trace of the transpose
of Y times X](goal). -/
lemma trace_pairing_comm (X Y : Matrix ι ι ℝ) :
    (X.transpose * Y).trace = (Y.transpose * X).trace := by
  rw [← Matrix.trace_transpose (X.transpose * Y), Matrix.transpose_mul,
    Matrix.transpose_transpose]

-- @node: sylvester_pairing_nonneg
/-- If [A is positive semidefinite](hyp:hA), [the trace of the transpose of X
times the sum of A times X and X times A is nonnegative for every real matrix
X](goal). -/
lemma sylvester_pairing_nonneg (A X : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    0 ≤ (X.transpose * (A * X + X * A)).trace := by
  have h₁ := (hA.conjTranspose_mul_mul_same X).trace_nonneg
  have h₂ := (hA.mul_mul_conjTranspose_same X).trace_nonneg
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h₁ h₂
  rw [Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm X.transpose (X * A)]
  exact add_nonneg h₁ h₂

-- @node: sylvester_pairing_selfAdjoint
/-- If [A is symmetric](hyp:hA), [the trace pairing of X with A times Y plus
Y times A equals the trace pairing of A times X plus X times A with Y](goal).

The trace pairing of two real matrices is the trace of the transpose of the
first times the second. -/
lemma sylvester_pairing_selfAdjoint (A X Y : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    (X.transpose * (A * Y + Y * A)).trace =
      ((A * X + X * A).transpose * Y).trace := by
  have hAt : A.transpose = A := Matrix.isHermitian_iff_isSymm.mp hA
  simp only [Matrix.transpose_add, Matrix.transpose_mul, hAt, Matrix.mul_add,
    Matrix.add_mul, Matrix.trace_add]
  congr 1
  · rw [Matrix.mul_assoc]
  · rw [Matrix.trace_mul_comm X.transpose (Y * A),
      Matrix.trace_mul_comm (A * X.transpose) Y, Matrix.mul_assoc]

-- @node: sylvester_inverse_pairing_order
/-- If [A is positive semidefinite](hyp:hA), [B minus A is positive
semidefinite](hyp:hAB), [A times X plus X times A equals K](hyp:hX), and
[B times Y plus Y times B equals K](hyp:hY), [the trace of the transpose of K
times Y is at most the trace of the transpose of K times X](goal). -/
lemma sylvester_inverse_pairing_order (A B K X Y : Matrix ι ι ℝ)
    (hA : A.PosSemidef) (hAB : (B - A).PosSemidef)
    (hX : A * X + X * A = K) (hY : B * Y + Y * B = K) :
    (K.transpose * Y).trace ≤ (K.transpose * X).trace := by
  have hpos := sylvester_pairing_nonneg A (X - Y) hA
  have hdiff := sylvester_pairing_nonneg (B - A) Y hAB
  have hcross : (Y.transpose * (A * X + X * A)).trace = (K.transpose * Y).trace := by
    rw [hX, trace_pairing_comm]
  have hcross' : (X.transpose * (A * Y + Y * A)).trace = (K.transpose * Y).trace := by
    rw [sylvester_pairing_selfAdjoint A X Y hA.isHermitian, hX]
  have hxx : (X.transpose * (A * X + X * A)).trace = (K.transpose * X).trace := by
    rw [hX, trace_pairing_comm]
  have hyy : (Y.transpose * (B * Y + Y * B)).trace = (K.transpose * Y).trace := by
    rw [hY, trace_pairing_comm]
  have he : ((X - Y).transpose * (A * (X - Y) + (X - Y) * A)).trace =
      (X.transpose * (A * X + X * A)).trace -
      (X.transpose * (A * Y + Y * A)).trace -
      (Y.transpose * (A * X + X * A)).trace +
      (Y.transpose * (A * Y + Y * A)).trace := by
    simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.trace_add, Matrix.trace_sub]
    ring
  have hd : (Y.transpose * ((B - A) * Y + Y * (B - A))).trace =
      (Y.transpose * (B * Y + Y * B)).trace -
      (Y.transpose * (A * Y + Y * A)).trace := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.trace_add, Matrix.trace_sub]
    ring
  rw [he, hcross, hcross', hxx] at hpos
  rw [hd, hyy] at hdiff
  linarith

end Papers.OaiBoundDyadicTriangular
