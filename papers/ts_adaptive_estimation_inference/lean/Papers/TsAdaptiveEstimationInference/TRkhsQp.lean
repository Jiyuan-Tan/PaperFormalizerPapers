module
public import Papers.TsAdaptiveEstimationInference.Helpers.RKHSQuadratic
/-! Representer and Moore--Penrose formulas without spectral truncation. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open scoped BigOperators
variable {𝒳 𝒵 H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H 𝒳 ℝ] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [RKHS ℝ F 𝒵 ℝ]
-- @node: prop:rkhs-qp
/-- For [a positive fitting-sample size](hyp:hN), [positive critic ridge](hyp:hη)
and [positive regularization penalty](hyp:hlam), suppose [the two function spaces
have the specified reproducing kernels](hyp:hSpaces), [h is an RKHS minimax fit](hyp:hFit),
and [h is the minimum-norm representative of its fitted values](hyp:hRepresentative).
Then [h has a kernel expansion with minimizing coefficients, the canonical
coefficients also minimize the coefficient objective and have the smallest
Euclidean norm among its minimizers, and those canonical coefficients represent h](goal). -/
theorem rkhs_qp (N : ℕ) (hN : 0 < N) (X : Fin N → 𝒳) (Z : Fin N → 𝒵) -- @realizes N(positive natural fitting-sample size)
    (y : Fin N → ℝ) (kH : 𝒳 → 𝒳 → ℝ) (kF : 𝒵 → 𝒵 → ℝ)
    (η lam : ℝ) (hη : 0 < η) (hlam : 0 < lam) -- @realizes \eta(strictly positive critic ridge)
    (hSpaces : RKHSSpaces H F kH kF)
    (h : H) (hFit : IsRKHSFit H F N X Z y η lam h)
    (hRepresentative : MinNormRepresentative H N X h) :
    (∃ α : Fin N → ℝ, h = ∑ i, α i • kernelRepresenter H (X i) ∧
      IsRKHSCoefficientMinimizer H F N X Z y η lam α) ∧
    IsRKHSCoefficientMinimizer H F N X Z y η lam
      (rkhsMinimumCoefficients H F N X Z y η lam) ∧
    (∀ α : Fin N → ℝ, IsRKHSCoefficientMinimizer H F N X Z y η lam α →
      (∑ i, rkhsMinimumCoefficients H F N X Z y η lam i ^ 2) ≤ ∑ i, α i ^ 2) ∧
    h = ∑ i, rkhsMinimumCoefficients H F N X Z y η lam i • kernelRepresenter H (X i) := by
  obtain ⟨α, hα, hmin⟩ := rkhs_fit_coefficients H F N X Z y hN η lam hη h hFit hRepresentative
  have hspec := rkhs_minimum_coefficients_spec H F N X Z y hN η lam hη hlam.le α hmin
  refine ⟨⟨α, hα, hmin⟩, hspec.1, ?_, ?_⟩
  · intro a ha
    exact (rkhs_minimum_coefficients_spec H F N X Z y hN η lam hη hlam.le a ha).2
  · exact hα.trans (rkhs_coefficient_minimizers_same_function H F N X Z y hN η lam
      hη hlam α (rkhsMinimumCoefficients H F N X Z y η lam) hmin hspec.1)
end Papers.TsAdaptiveEstimationInference
