module
public import Mathlib.Algebra.QuadraticDiscriminant
public import Papers.TsAdaptiveEstimationInference.Helpers.RKHS
public import Toolkit.Foundations.LinearAlgebra.Matrix.PosSemidef
/-! Normal equations and minimum norm solutions for the RKHS quadratic program. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open scoped BigOperators

-- @node: rkhs_symmetric_pairing
/-- If [the matrix is symmetric](hyp:hA), [pairing a vector with the matrix applied to
another vector is unchanged when the two vectors are exchanged](goal). -/
lemma rkhs_symmetric_pairing {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsSymm) (x z : Fin N → ℝ) :
    dotProduct x (A.mulVec z) = dotProduct z (A.mulVec x) := by
  simpa only [hA.eq] using Matrix.dotProduct_transpose_mulVec A x z

-- @node: rkhs_quadratic_increment
/-- For [a symmetric matrix](hyp:hA), [moving from a coefficient vector in a direction
by a scalar step changes the quadratic objective by the squared step times the
direction's quadratic form, plus twice the step times the direction's inner product
with the normal-equation residual](goal). -/
lemma rkhs_quadratic_increment {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsSymm) (b x d : Fin N → ℝ) (t : ℝ) :
    (dotProduct (x + t • d) (A.mulVec (x + t • d)) - 2 * dotProduct (x + t • d) b) -
      (dotProduct x (A.mulVec x) - 2 * dotProduct x b) =
      t ^ 2 * dotProduct d (A.mulVec d) + 2 * t * dotProduct d (A.mulVec x - b) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
    add_dotProduct, smul_dotProduct, dotProduct_sub, smul_eq_mul]
  rw [rkhs_symmetric_pairing hA x d]
  ring

-- @node: rkhs_quadratic_normal_equation
/-- For [a symmetric matrix](hyp:hA), if [a coefficient vector globally minimizes the
quadratic form minus twice its inner product with the response vector](hyp:hx),
then [the matrix applied to that coefficient vector equals the response vector](goal). -/
lemma rkhs_quadratic_normal_equation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsSymm) (b x : Fin N → ℝ)
    (hx : ∀ z, dotProduct x (A.mulVec x) - 2 * dotProduct x b ≤
      dotProduct z (A.mulVec z) - 2 * dotProduct z b) : A.mulVec x = b := by
  exact Toolkit.Foundations.LinearAlgebra.Matrix.mulVec_eq_of_forall_dotProduct_mulVec_sub_le
    A hA b x hx

-- @node: rkhs_quadratic_minimum_of_normal
/-- If [the matrix is positive semidefinite](hyp:hA) and [a coefficient vector solves
the normal equation](hyp:hx), then [its quadratic objective, the quadratic form minus
twice its inner product with the response, is no larger than that of any other vector](goal). -/
lemma rkhs_quadratic_minimum_of_normal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosSemidef) (b x : Fin N → ℝ) (hx : A.mulVec x = b) :
    ∀ z, dotProduct x (A.mulVec x) - 2 * dotProduct x b ≤
      dotProduct z (A.mulVec z) - 2 * dotProduct z b := by
  exact Toolkit.Foundations.LinearAlgebra.Matrix.dotProduct_mulVec_sub_le_of_posSemidef_of_mulVec_eq
    A hA b x hx

-- @node: rkhs_penrose_solution
/-- If [a vector solves the linear system with the given matrix and response](hyp:hx),
then [applying the matrix's Moore–Penrose inverse to the response also solves that
linear system](goal). -/
lemma rkhs_penrose_solution {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (b x : Fin N → ℝ) (hx : A.mulVec x = b) :
    A.mulVec ((Causalean.Mathlib.Analysis.moorePenroseInverse A).mulVec b) = b := by
  rw [← hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (Causalean.Mathlib.Analysis.moorePenroseInverse_spec A).1]

-- @node: rkhs_penrose_minimum_norm
/-- If [a vector solves the linear system with the given matrix and response](hyp:hx),
then [the squared Euclidean norm of the Moore–Penrose solution is no larger than
the squared Euclidean norm of that vector](goal). -/
lemma rkhs_penrose_minimum_norm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (b x : Fin N → ℝ) (hx : A.mulVec x = b) :
    dotProduct ((Causalean.Mathlib.Analysis.moorePenroseInverse A).mulVec b)
      ((Causalean.Mathlib.Analysis.moorePenroseInverse A).mulVec b) ≤ dotProduct x x := by
  let Q := Causalean.Mathlib.Analysis.moorePenroseInverse A * A
  have hQ := Causalean.Mathlib.Analysis.rowProjection_penrose A
  have hsym : Q.IsSymm := hQ.2
  have hidem : Q * Q = Q := hQ.1
  have hpair : dotProduct (Q.mulVec x) (Q.mulVec x) = dotProduct x (Q.mulVec x) := by
    rw [rkhs_symmetric_pairing hsym, Matrix.mulVec_mulVec, hidem]
  have hn : 0 ≤ dotProduct (x - Q.mulVec x) (x - Q.mulVec x) := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  simp only [sub_dotProduct, dotProduct_sub] at hn
  rw [dotProduct_comm (Q.mulVec x) x, hpair] at hn
  rw [← hx, Matrix.mulVec_mulVec]
  change dotProduct (Q.mulVec x) (Q.mulVec x) ≤ dotProduct x x
  linarith only [hn, hpair]

variable {𝒳 𝒵 H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H 𝒳 ℝ] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [RKHS ℝ F 𝒵 ℝ]
variable (H F) (N : ℕ) (X : Fin N → 𝒳) (Z : Fin N → 𝒵) (y : Fin N → ℝ)

-- @node: rkhs_criticSmoother_symmetric
/-- With [a positive sample size](hyp:hN) and [a positive critic ridge penalty](hyp:hη),
[the critic smoothing matrix is symmetric](goal). -/
lemma rkhs_criticSmoother_symmetric (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    (criticSmoother F N Z η).IsSymm := by
  let A := gramF F N Z + (N * η) • (1 : Matrix (Fin N) (Fin N) ℝ)
  have hA : A.PosDef := rkhs_critic_ridge_posDef F N Z hN η hη
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)
  have he : criticSmoother F N Z η = 1 - (N * η) • A⁻¹ := by
    change gramF F N Z * A⁻¹ = _
    have hex : gramF F N Z = A - (N * η) • 1 := by dsimp [A]; abel
    rw [hex, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hmul]
  rw [he]
  exact Matrix.isHermitian_iff_isSymm.mp
    (Matrix.isHermitian_one.sub (hA.inv.isHermitian.smul (by rfl : IsSelfAdjoint ((N : ℝ) * η))))

-- @node: rkhs_criticSmoother_posSemidef
/-- With [a positive sample size](hyp:hN) and [a positive critic ridge penalty](hyp:hη),
[the critic smoothing matrix is positive semidefinite](goal). -/
lemma rkhs_criticSmoother_posSemidef (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    (criticSmoother F N Z η).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (rkhs_criticSmoother_symmetric F N Z hN η hη))
  intro r
  have hb := (rkhsEvaluationLoss_bounds F N Z r hN η hη.le 0).1
  rw [rkhs_profiled_loss F N Z r hN η hη 0] at hb
  simp only [sub_zero] at hb
  simpa only [star_trivial] using nonneg_of_mul_nonneg_right hb (by positivity : (0 : ℝ) < 1 / N)

-- @node: rkhs_empirical_coefficient_penalty
/-- [The empirical mean squared value of a kernel expansion equals the quadratic
form in its coefficients with the squared sample Gram matrix, divided by the
sample size](goal). -/
lemma rkhs_empirical_coefficient_penalty (α : Fin N → ℝ) :
    rkhsEmpSq H N X (∑ i, α i • kernelRepresenter H (X i)) =
      (N : ℝ)⁻¹ * dotProduct α ((gramH H N X * gramH H N X).mulVec α) := by
  have hsym := Matrix.isHermitian_iff_isSymm.mp (rkhs_gram_posSemidef H N X).1
  have he := rkhs_symmetric_pairing hsym α ((gramH H N X).mulVec α)
  rw [Matrix.mulVec_mulVec] at he
  simp only [rkhsEmpSq, rkhs_representer_evaluation]
  congr 1
  rw [he]
  simp only [dotProduct, sq]

-- @node: rkhs_coefficient_objective_identity
/-- With [a positive sample size](hyp:hN) and [a positive critic ridge penalty](hyp:hη),
[the adversarial loss of a kernel expansion plus its empirical squared-value penalty
equals the coefficient objective divided by the sample size](goal). -/
lemma rkhs_coefficient_objective_identity (hN : 0 < N) (η lam : ℝ) (hη : 0 < η)
    (α : Fin N → ℝ) :
    rkhsAdversarialLoss H F N X Z y η (∑ i, α i • kernelRepresenter H (X i)) +
      lam * rkhsEmpSq H N X (∑ i, α i • kernelRepresenter H (X i)) =
      (N : ℝ)⁻¹ * rkhsCoefficientObjective H F N X Z y η lam α := by
  change rkhsEvaluationLoss F N Z y η (fun j => (∑ i, α i • kernelRepresenter H (X i)) (X j)) + _ = _
  simp only [rkhs_representer_evaluation]
  rw [rkhs_profiled_loss F N Z y hN η hη, rkhs_empirical_coefficient_penalty]
  simp only [rkhsCoefficientObjective, one_div]
  ring

-- @node: rkhs_fit_coefficients
/-- With [a positive sample size](hyp:hN) and [a positive critic ridge penalty](hyp:hη),
consider [a candidate RKHS function](hyp:h) that [minimizes the penalized adversarial
loss](hyp:hFit) and [has minimum RKHS norm among functions with the same sample
evaluations](hyp:hRepresentative). Then [the function has a sample kernel expansion
whose coefficients minimize the coefficient objective](goal). -/
lemma rkhs_fit_coefficients (hN : 0 < N) (η lam : ℝ) (hη : 0 < η)
    (h : H) (hFit : IsRKHSFit H F N X Z y η lam h)
    (hRepresentative : MinNormRepresentative H N X h) :
    ∃ α : Fin N → ℝ, h = ∑ i, α i • kernelRepresenter H (X i) ∧
      IsRKHSCoefficientMinimizer H F N X Z y η lam α := by
  obtain ⟨α, rfl⟩ := rkhs_minNorm_representer H N X h hRepresentative
  refine ⟨α, rfl, fun α' => ?_⟩
  have hi := hFit (∑ i, α' i • kernelRepresenter H (X i))
  rw [rkhs_coefficient_objective_identity H F N X Z y hN η lam hη,
    rkhs_coefficient_objective_identity H F N X Z y hN η lam hη] at hi
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (N : ℝ)⁻¹)).mp hi

-- @node: rkhs_gram_pairing
/-- [The inner product of the sample Gram matrix applied to one vector with a second
vector equals the inner product of the first vector with the Gram matrix applied
to the second](goal). -/
lemma rkhs_gram_pairing (x z : Fin N → ℝ) :
    dotProduct ((gramH H N X).mulVec x) z = dotProduct x ((gramH H N X).mulVec z) := by
  rw [dotProduct_comm, rkhs_symmetric_pairing
    (Matrix.isHermitian_iff_isSymm.mp (rkhs_gram_posSemidef H N X).1)]

-- @node: rkhs_normal_matrix_posSemidef
/-- With [a positive sample size](hyp:hN), [a positive critic ridge penalty](hyp:hη),
and [a nonnegative empirical penalty](hyp:hlam), [the coefficient normal matrix,
formed by sandwiching the critic smoother between sample Gram matrices and adding
the empirical penalty times the squared Gram matrix, is positive semidefinite](goal). -/
lemma rkhs_normal_matrix_posSemidef (hN : 0 < N) (η lam : ℝ) (hη : 0 < η) (hlam : 0 ≤ lam) :
    (gramH H N X * criticSmoother F N Z η * gramH H N X +
      lam • (gramH H N X * gramH H N X)).PosSemidef := by
  have hK := rkhs_gram_posSemidef H N X
  have hP := rkhs_criticSmoother_posSemidef F N Z hN η hη
  have hmain := hP.conjTranspose_mul_mul_same (gramH H N X)
  rw [hK.1.eq] at hmain
  exact hmain.add (by simpa only [pow_two] using (hK.pow 2).smul hlam)

-- @node: rkhs_coefficient_expansion
/-- With [a positive sample size](hyp:hN) and [a positive critic ridge penalty](hyp:hη),
[the coefficient objective equals the response's quadratic form under the critic
smoother plus the coefficients' quadratic form under the normal matrix, minus
twice their inner product with the Gram matrix times the smoothed response](goal). -/
lemma rkhs_coefficient_expansion (hN : 0 < N) (η lam : ℝ) (hη : 0 < η)
    (α : Fin N → ℝ) :
    rkhsCoefficientObjective H F N X Z y η lam α =
      dotProduct y ((criticSmoother F N Z η).mulVec y) +
        (dotProduct α ((gramH H N X * criticSmoother F N Z η * gramH H N X +
            lam • (gramH H N X * gramH H N X)).mulVec α) -
          2 * dotProduct α ((gramH H N X * criticSmoother F N Z η).mulVec y)) := by
  let K := gramH H N X
  let P := criticSmoother F N Z η
  have hc : dotProduct y (P.mulVec (K.mulVec α)) = dotProduct α (K.mulVec (P.mulVec y)) := by
    rw [rkhs_symmetric_pairing (rkhs_criticSmoother_symmetric F N Z hN η hη),
      rkhs_gram_pairing H N X]
  have hq : dotProduct (K.mulVec α) (P.mulVec (K.mulVec α)) =
      dotProduct α (K.mulVec (P.mulVec (K.mulVec α))) := rkhs_gram_pairing H N X _ _
  change dotProduct (y - K.mulVec α) (P.mulVec (y - K.mulVec α)) +
    lam * dotProduct α ((K * K).mulVec α) = _
  change _ = dotProduct y (P.mulVec y) +
    (dotProduct α ((K * P * K + lam • (K * K)).mulVec α) -
      2 * dotProduct α ((K * P).mulVec y))
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct,
    Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  rw [hc, hq, rkhs_gram_pairing H N X]
  ring

-- @node: rkhs_coefficient_normal_iff
/-- With [a positive sample size](hyp:hN), [a positive critic ridge penalty](hyp:hη),
and [a nonnegative empirical penalty](hyp:hlam), [coefficients minimize the objective
if and only if the coefficient normal matrix applied to them equals the sample Gram
matrix applied to the smoothed response](goal). -/
lemma rkhs_coefficient_normal_iff (hN : 0 < N) (η lam : ℝ) (hη : 0 < η) (hlam : 0 ≤ lam)
    (α : Fin N → ℝ) :
    IsRKHSCoefficientMinimizer H F N X Z y η lam α ↔
      (gramH H N X * criticSmoother F N Z η * gramH H N X +
        lam • (gramH H N X * gramH H N X)).mulVec α =
        (gramH H N X * criticSmoother F N Z η).mulVec y := by
  have hA := rkhs_normal_matrix_posSemidef H F N X Z hN η lam hη hlam
  constructor
  · intro hmin
    apply rkhs_quadratic_normal_equation _ (Matrix.isHermitian_iff_isSymm.mp hA.1) _ α
    intro z
    have hi := hmin z
    rw [rkhs_coefficient_expansion H F N X Z y hN η lam hη,
      rkhs_coefficient_expansion H F N X Z y hN η lam hη] at hi
    linarith only [hi]
  · intro hn z
    have hi := rkhs_quadratic_minimum_of_normal _ hA _ α hn z
    simp only [rkhs_coefficient_expansion H F N X Z y hN η lam hη]
    linarith only [hi]

-- @node: rkhs_minimum_coefficients_spec
/-- With [a positive sample size](hyp:hN), [a positive critic ridge penalty](hyp:hη),
and [a nonnegative empirical penalty](hyp:hlam), if [a coefficient vector minimizes
the objective](hyp:hα), then [the Moore–Penrose coefficient choice also minimizes
the objective and has squared Euclidean norm no larger than that vector's](goal). -/
lemma rkhs_minimum_coefficients_spec (hN : 0 < N) (η lam : ℝ) (hη : 0 < η) (hlam : 0 ≤ lam)
    (α : Fin N → ℝ) (hα : IsRKHSCoefficientMinimizer H F N X Z y η lam α) :
    IsRKHSCoefficientMinimizer H F N X Z y η lam
      (rkhsMinimumCoefficients H F N X Z y η lam) ∧
      (∑ i, rkhsMinimumCoefficients H F N X Z y η lam i ^ 2) ≤ ∑ i, α i ^ 2 := by
  have hn := (rkhs_coefficient_normal_iff H F N X Z y hN η lam hη hlam α).mp hα
  constructor
  · apply (rkhs_coefficient_normal_iff H F N X Z y hN η lam hη hlam _).mpr
    exact rkhs_penrose_solution _ _ α hn
  · simpa only [rkhsMinimumCoefficients, dotProduct, sq] using rkhs_penrose_minimum_norm _ _ α hn

-- @node: rkhs_coefficient_minimizers_same_function
/-- With [a positive sample size](hyp:hN), [a positive critic ridge penalty](hyp:hη),
and [a strictly positive empirical penalty](hyp:hlam), if [the first coefficient
vector minimizes the objective](hyp:hα) and [the second coefficient vector also
minimizes it](hyp:ha), then [their sample kernel expansions define the same RKHS
function](goal). -/
lemma rkhs_coefficient_minimizers_same_function (hN : 0 < N) (η lam : ℝ)
    (hη : 0 < η) (hlam : 0 < lam) (α a : Fin N → ℝ)
    (hα : IsRKHSCoefficientMinimizer H F N X Z y η lam α)
    (ha : IsRKHSCoefficientMinimizer H F N X Z y η lam a) :
    (∑ i, α i • kernelRepresenter H (X i)) = ∑ i, a i • kernelRepresenter H (X i) := by
  let K := gramH H N X
  let P := criticSmoother F N Z η
  let u := α - a
  have hnα := (rkhs_coefficient_normal_iff H F N X Z y hN η lam hη hlam.le α).mp hα
  have hna := (rkhs_coefficient_normal_iff H F N X Z y hN η lam hη hlam.le a).mp ha
  have hzero : (K * P * K + lam • (K * K)).mulVec u = 0 := by
    dsimp [u, K, P]
    rw [Matrix.mulVec_sub, hnα, hna, sub_self]
  have he : dotProduct (K.mulVec u) (P.mulVec (K.mulVec u)) +
      lam * dotProduct (K.mulVec u) (K.mulVec u) = 0 := by
    have hz := congrArg (dotProduct u) hzero
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_zero, smul_eq_mul] at hz
    rw [← rkhs_gram_pairing H N X, ← rkhs_gram_pairing H N X] at hz
    exact hz
  have hP := (rkhs_criticSmoother_posSemidef F N Z hN η hη).dotProduct_mulVec_nonneg (K.mulVec u)
  simp only [star_trivial] at hP
  have hKu : dotProduct (K.mulVec u) (K.mulVec u) = 0 := by
    have hnn : 0 ≤ dotProduct (K.mulVec u) (K.mulVec u) :=
      Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
    nlinarith only [he, hP, hnn, hlam]
  have hKu0 : K.mulVec u = 0 := dotProduct_self_eq_zero.mp hKu
  have hg : ‖∑ i, u i • kernelRepresenter H (X i)‖ ^ 2 = 0 := by
    rw [rkhs_representer_norm_sq]
    change dotProduct u (K.mulVec u) = 0
    rw [hKu0, dotProduct_zero]
  have hfun : (∑ i, u i • kernelRepresenter H (X i)) = 0 :=
    norm_eq_zero.mp (by nlinarith only [hg, norm_nonneg (∑ i, u i • kernelRepresenter H (X i))])
  have heq : (∑ i, u i • kernelRepresenter H (X i)) =
      (∑ i, α i • kernelRepresenter H (X i)) - ∑ i, a i • kernelRepresenter H (X i) := by
    simp only [u, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [heq] at hfun
  exact sub_eq_zero.mp hfun

end Papers.TsAdaptiveEstimationInference
