module

public import Papers.OaiBoundDyadicTriangular.Helpers.SupportedDerivatives
public import Mathlib.Analysis.Convex.Mul

/-! # Smoothness and order of the supported matrix Hessian -/

public section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder

namespace Papers.OaiBoundDyadicTriangular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @node: annihilatesKernel_of_orderComparison
/-- If [P is positive semidefinite](hyp:hP) and [P is bounded above by a times Q
in the positive semidefinite order](hyp:hComparison), then [every vector in the
kernel of Q is also in the kernel of P](goal). -/
lemma annihilatesKernel_of_orderComparison (P Q : Matrix ι ι ℝ) (a : ℝ)
    (hP : P.PosSemidef) (hComparison : OrderComparison P Q a) :
    AnnihilatesKernel Q P := by
  intro x hx
  apply (hP.dotProduct_mulVec_zero_iff x).mp
  have hLower := hP.dotProduct_mulVec_nonneg x
  have hUpper := hComparison.dotProduct_mulVec_nonneg x
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, hx, smul_zero,
    zero_sub, dotProduct_neg] at hUpper
  exact le_antisymm (neg_nonneg.mp hUpper) hLower

-- @node: supportedOn_of_orderComparison
/-- If [P is positive semidefinite](hyp:hP), [P is bounded above by a times Q
in the positive semidefinite order](hyp:hComparison), and [K annihilates the
kernel of P](hyp:hK), then [K also annihilates the kernel of Q](goal). -/
lemma supportedOn_of_orderComparison (P Q K : Matrix ι ι ℝ) (a : ℝ)
    (hP : P.PosSemidef) (hComparison : OrderComparison P Q a)
    (hK : SupportedOn P K) : SupportedOn Q K := by
  refine ⟨?_⟩
  intro x hx
  exact hK.annihilates x (annihilatesKernel_of_orderComparison P Q a hP hComparison x hx)

/-- If [P is a real symmetric matrix](hyp:hP), then [its supported Hessian form
at the sum of three direction matrices is at most three times the sum of its
values at those direction matrices separately](goal). -/
-- @node: hessForm_add_three_le
lemma hessForm_add_three_le (P : Matrix ι ι ℝ) (hP : P.IsHermitian)
    (K₀ K₁ K₂ : Matrix ι ι ℝ) :
    hessForm P hP (K₀ + K₁ + K₂) ≤
      3 * (hessForm P hP K₀ + hessForm P hP K₁ + hessForm P hP K₂) := by
  have hsq (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  unfold hessForm
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  rw [← mul_add, ← mul_add]
  rw [mul_left_comm (3 : ℝ) (3 / 2 : ℝ)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs with h
  · rw [← add_div, ← add_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hsq _ _ _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · simp

-- @node: orderComparison_add_identity
/-- If [the comparison factor is at least one](hyp:hFactor), [P is bounded above
by that factor times Q in the positive semidefinite order](hyp:hComparison), and
[the regularization parameter is nonnegative](hyp:hη), then [adding that parameter
times the identity to both matrices preserves the same order comparison](goal). -/
lemma orderComparison_add_identity (P Q : Matrix ι ι ℝ) (a η : ℝ)
    (hFactor : OrderFactor a) (hComparison : OrderComparison P Q a) (hη : 0 ≤ η) :
    OrderComparison (P + η • 1) (Q + η • 1) a := by
  have hExtra : (((a - 1) * η) • (1 : Matrix ι ι ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (mul_nonneg (sub_nonneg.mpr hFactor) hη)
  have he : a • (Q + η • 1) - (P + η • 1) =
      (a • Q - P) + ((a - 1) * η) • 1 := by
    simp only [smul_add, smul_smul, sub_mul, one_mul, sub_smul]
    abel
  unfold OrderComparison
  rw [he]
  exact hComparison.add hExtra

-- @node: posDef_add_identity
/-- If [P is positive semidefinite](hyp:hP) and [the regularization parameter is
strictly positive](hyp:hη), then [adding that parameter times the identity to P
produces a positive definite matrix](goal). -/
lemma posDef_add_identity (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    (η : ℝ) (hη : 0 < η) : (P + η • 1).PosDef := by
  exact Matrix.PosDef.posSemidef_add hP (Matrix.PosDef.one.smul hη)

-- @node: lem:hessian
/-- If [P is positive semidefinite](hyp:hP) and [K is symmetric and annihilates
the kernel of P](hyp:hK), then [on the space of symmetric matrices annihilating
that kernel, P lies in an open positive-support locus where the matrix energy
is infinitely differentiable: its first derivative in any direction is three
halves times the trace of the square root of the base matrix times that direction,
and its second derivative repeated in that direction is the supported Hessian
form; these formulas hold in particular at P in direction K, and the energy is
convex on the positive semidefinite cone](goal). -/
lemma matrixEnergy_hessian (P K : Matrix ι ι ℝ)
    (hP : HessianPositiveSupport P) (hK : HessianDirection P K) :
    let E := supportedTangent P
    let Φ : E → ℝ := fun Q => matrixEnergy Q.val
    let p : E := ⟨P, base_mem_supportedTangent P hP⟩
    let d : E := ⟨K, (mem_supportedTangent P K).mpr hK⟩
    p ∈ positiveSupportLocus P ∧
    IsOpen (positiveSupportLocus P) ∧
    ContDiffOn ℝ ⊤ Φ (positiveSupportLocus P) ∧
    (∀ Q ∈ positiveSupportLocus P, ∀ L : E,
      fderiv ℝ Φ Q L = (3 / 2 : ℝ) * (CFC.sqrt Q.val * L.val).trace ∧
      fderiv ℝ (fderiv ℝ Φ) Q L L =
        hessForm Q.val (supportedTangent_isHermitian P Q) L.val) ∧
    fderiv ℝ Φ p d = (3 / 2 : ℝ) * (CFC.sqrt P * K).trace ∧
    fderiv ℝ (fderiv ℝ Φ) p d d = hessForm P hP.isHermitian K ∧
    ConvexOn ℝ {A : Matrix ι ι ℝ | A.PosSemidef} matrixEnergy := by
  refine ⟨base_mem_positiveSupportLocus P hP, isOpen_positiveSupportLocus P,
    contDiffOn_supported_matrixEnergy P, ?_, ?_, ?_, convexOn_matrixEnergy⟩
  · intro Q hQ L
    exact ⟨fderiv_supported_matrixEnergy P Q L hQ,
      fderiv_two_supported_matrixEnergy P Q L hQ⟩
  · exact fderiv_supported_matrixEnergy P _ _ (base_mem_positiveSupportLocus P hP)
  · exact fderiv_two_supported_matrixEnergy P _ _ (base_mem_positiveSupportLocus P hP)

-- @node: lem:order
/-- If [P and Q are positive semidefinite](hyp:hMatrices), [a is at least
one](hyp:hFactor), [P is bounded above by a times Q in the positive semidefinite
order](hyp:hComparison), and [K is symmetric and annihilates the kernel of
P](hyp:hDirection), then [K annihilates the kernel of Q, and the supported Hessian
form at Q, multiplied by the inverse square root of a, is at most the supported
Hessian form at P in direction K](goal). -/
lemma hessForm_order (P Q K : Matrix ι ι ℝ) (a : ℝ)
    (hMatrices : OrderMatrices P Q) (hFactor : OrderFactor a)
    (hComparison : OrderComparison P Q a) (hDirection : OrderDirection P K) :
    SupportedOn Q K ∧
    a ^ (-1 / 2 : ℝ) * hessForm Q hMatrices.2.isHermitian K ≤
      hessForm P hMatrices.1.isHermitian K := by
  refine ⟨supportedOn_of_orderComparison P Q K a hMatrices.1 hComparison ⟨hDirection.2⟩, ?_⟩
  have ha : 0 < a := lt_of_lt_of_le (by norm_num) hFactor
  have hc : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hPK : SupportedOn P K := ⟨hDirection.2⟩
  have hQK := supportedOn_of_orderComparison P Q K a hMatrices.1 hComparison hPK
  obtain ⟨X, hX⟩ := exists_sqrt_sylvester_solution P K hMatrices.1 hDirection.1 hPK
  obtain ⟨Z, hZ⟩ := exists_sqrt_sylvester_solution Q K hMatrices.2 hDirection.1 hQK
  let Y := (Real.sqrt a)⁻¹ • Z
  have hY : (Real.sqrt a • CFC.sqrt Q) * Y +
      Y * (Real.sqrt a • CFC.sqrt Q) = K := by
    simp only [Y, smul_mul_smul_comm, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc, one_smul]
    exact hZ
  have hInv := sylvester_inverse_pairing_order (CFC.sqrt P)
    (Real.sqrt a • CFC.sqrt Q) K X Y (CFC.sqrt_nonneg P).posSemidef
    (sqrt_orderComparison P Q hMatrices.1 hMatrices.2 a ha.le hComparison) hX hY
  rw [hessForm_eq_trace_of_sylvester P K X hMatrices.1 hDirection.1 hPK hX,
    hessForm_eq_trace_of_sylvester Q K Z hMatrices.2 hDirection.1 hQK hZ]
  have hpower : a ^ (-1 / 2 : ℝ) = (Real.sqrt a)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ha.le]
    congr 1
    norm_num
  rw [hpower]
  have hPair : (K.transpose * Y).trace =
      (Real.sqrt a)⁻¹ * (K.transpose * Z).trace := by
    simp only [Y, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [hPair] at hInv
  nlinarith

end Papers.OaiBoundDyadicTriangular
