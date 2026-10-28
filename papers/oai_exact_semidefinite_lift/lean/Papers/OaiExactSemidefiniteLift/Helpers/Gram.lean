module

public import Papers.OaiExactSemidefiniteLift.Basic

/-!
# Angular Gram identity
-/

public section

namespace Papers.OaiExactSemidefiniteLift

open Matrix

-- @node: angular_plane_surjective
/-- [Every real three-vector can be represented by an angle, a planar coefficient,
and a vertical coefficient in the angular-plane parametrization](goal). -/
lemma angular_plane_surjective (y : Fin 3 → ℝ) :
    ∃ θ η ξ : ℝ, y = Yplane θ η ξ := by
  let z : ℂ := ⟨y 0, y 1⟩
  refine ⟨z.arg, ‖z‖, y 2, ?_⟩
  ext i
  fin_cases i
  · simpa [Yplane, dVec, kVec, z] using (Complex.norm_mul_cos_arg z).symm
  · simpa [Yplane, dVec, kVec, z] using (Complex.norm_mul_sin_arg z).symm
  · simp [Yplane, dVec, kVec]

-- @node: angular_bounds
/-- [At every real angle, both cosine and sine lie between minus one and one,
and the associated complex phase has modulus one](goal). -/
lemma angular_bounds (θ : ℝ) :
    (-1 ≤ cosine θ ∧ cosine θ ≤ 1) ∧ -- @realizes c(range [-1,1])
    (-1 ≤ sine θ ∧ sine θ ≤ 1) ∧ -- @realizes s(range [-1,1])
    ‖wPhase θ‖ = 1 := by -- @realizes w(unit modulus)
  exact ⟨⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩,
    ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩,
    Complex.norm_exp_ofReal_mul_I θ⟩

-- @node: wPhase_inv_trig
/-- [The inverse of the complex phase at an angle equals its cosine minus the
imaginary unit times its sine](goal). -/
lemma wPhase_inv_trig (θ : ℝ) :
    (wPhase θ)⁻¹ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  rw [wPhase, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I]
  simp [sub_eq_add_neg]

-- @node: realify_Umat_gram
/-- [The row Gram matrix of the realified angular factor has diagonal entries
one, sine squared, and cosine squared; its first two off-diagonal entries are
minus sine times cosine, and its other off-diagonal entries are zero](goal). -/
lemma realify_Umat_gram (θ : ℝ) :
    realify (Umat θ) * (realify (Umat θ))ᵀ =
      !![1, -Real.sin θ * Real.cos θ, 0;
         -Real.sin θ * Real.cos θ, (Real.sin θ)^2, 0;
         0, 0, (Real.cos θ)^2] := by
  simp only [Umat, wPhase_inv_trig θ]
  have hc3 : Real.cos θ ^ 3 = Real.cos θ * (1 - Real.sin θ ^ 2) := by
    rw [← Real.cos_sq']; ring
  have hc4 : Real.cos θ ^ 4 = (1 - Real.sin θ ^ 2) ^ 2 := by
    rw [← Real.cos_sq']; ring
  have hc6 : Real.cos θ ^ 6 = (1 - Real.sin θ ^ 2) ^ 3 := by
    rw [← Real.cos_sq']; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Matrix.mul_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring_nf <;>
    simp only [show Real.sqrt 2 ^ 2 = 2 by norm_num, hc3, hc4, hc6, Real.cos_sq'] <;>
    ring

-- @node: realify_V0_gram
/-- [The row Gram matrix of the realified constant factor is diagonal, with
entries zero, one, and one](goal). -/
lemma realify_V0_gram :
    realify V0 * (realify V0)ᵀ = !![0, 0, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realify, V0, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> ring_nf <;> norm_num

-- @node: realify_Umat_V0_cross
/-- [The symmetric cross product of the realified angular and constant factors
has zero diagonal, zero entries between the first two coordinates, minus cosine
between the first and third coordinates, and minus sine between the second and
third coordinates](goal). -/
lemma realify_Umat_V0_cross (θ : ℝ) :
    realify (Umat θ) * (realify V0)ᵀ + realify V0 * (realify (Umat θ))ᵀ =
      !![0, 0, -Real.cos θ;
         0, 0, -Real.sin θ;
         -Real.cos θ, -Real.sin θ, 0] := by
  simp only [Umat, wPhase_inv_trig θ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realify, V0, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring_nf <;>
    simp only [show Real.sqrt 2 ^ 2 = 2 by norm_num, Real.cos_sq'] <;>
    ring

-- @node: realify_Fθ_linear
/-- [Realifying the angular Gram factor gives the planar coefficient times the
realified angular factor plus the vertical coefficient times the realified
constant factor](goal). -/
lemma realify_Fθ_linear (θ η ξ : ℝ) :
    realify (Fθ θ η ξ) = η • realify (Umat θ) + ξ • realify V0 := by
  ext i j
  fin_cases j <;> simp [realify, Fθ, Complex.mul_re, Complex.mul_im]

-- @node: realify_Fθ_gram_expansion
/-- [The row Gram matrix of the realified combined factor equals the sum of the
two component Gram matrices weighted by the squared planar and vertical
coefficients, plus their symmetric cross product weighted by the product of
those coefficients](goal). -/
lemma realify_Fθ_gram_expansion (θ η ξ : ℝ) :
    realify (Fθ θ η ξ) * (realify (Fθ θ η ξ))ᵀ =
      η ^ 2 • (realify (Umat θ) * (realify (Umat θ))ᵀ) +
      ξ ^ 2 • (realify V0 * (realify V0)ᵀ) +
      (η * ξ) • (realify (Umat θ) * (realify V0)ᵀ +
        realify V0 * (realify (Umat θ))ᵀ) := by
  rw [realify_Fθ_linear]
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ]
  ring

-- @node: lem:gram
/-- [For every angle and pair of plane coefficients, the realified angular
factor has row Gram matrix equal to the quadratic matrix at the corresponding
three-vector; consequently, the quadratic matrix is positive semidefinite at
every real three-vector](goal). -/
lemma gram_identity :
    (∀ θ η ξ : ℝ, realify (Fθ θ η ξ) * (realify (Fθ θ η ξ))ᵀ =
      Qmat (Yplane θ η ξ)) ∧
    (∀ y : Fin 3 → ℝ, (Qmat y).PosSemidef) := by
  have hgram (θ η ξ : ℝ) :
      realify (Fθ θ η ξ) * (realify (Fθ θ η ξ))ᵀ = Qmat (Yplane θ η ξ) := by
    rw [realify_Fθ_gram_expansion, realify_Umat_gram, realify_V0_gram,
      realify_Umat_V0_cross]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Qmat, Yplane, dVec, kVec] <;>
      ring_nf <;> simp only [Real.cos_sq'] <;> ring
  refine ⟨hgram, ?_⟩
  intro y
  obtain ⟨θ, η, ξ, rfl⟩ := angular_plane_surjective y
  rw [← hgram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (realify (Fθ θ η ξ))

end Papers.OaiExactSemidefiniteLift
