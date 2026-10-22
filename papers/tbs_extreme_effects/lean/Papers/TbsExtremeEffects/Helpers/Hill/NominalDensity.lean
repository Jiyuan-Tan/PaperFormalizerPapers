module
public import Papers.TbsExtremeEffects.Helpers.Hill.RadialTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

/-! The nominal component-density error in the radial Hill expansion.
The mean value estimate retains the original Pareto type-II support. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped BigOperators

/-- [A nonnegative exponent](hyp:hb) and [a nonnegative shift](hyp:hy) ensure that the absolute change in the corresponding negative power is at most the exponent times the shift; [this bound](goal) holds. -/
-- @node: hill_negative_power_shift_bound
lemma hill_negative_power_shift_bound {b y : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) :
    |(1 + y) ^ (-b) - 1| ≤ b * y := by
  have hderiv : ∀ x ∈ Set.Icc 1 (1 + y),
      HasDerivWithinAt (fun x : ℝ => x ^ (-b))
        ((-b) * x ^ (-b - 1)) (Set.Icc 1 (1 + y)) x := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico 1 (1 + y), ‖(-b) * x ^ (-b - 1)‖ ≤ b := by
    intro x hx
    have hp : 0 ≤ x ^ (-b - 1) := Real.rpow_nonneg (by linarith [hx.1]) _
    have hpone : x ^ (-b - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hb, abs_of_nonneg hp]
    exact (mul_le_mul_of_nonneg_left hpone hb).trans_eq (mul_one b)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
    (1 + y) (Set.right_mem_Icc.mpr (by linarith))
  simpa only [Real.norm_eq_abs, Real.one_rpow, add_sub_cancel_left] using h

/-- [A positive tail index](hyp:hb), [a positive component scale](hyp:ha), and [a positive radius](hyp:hr) imply that [the error from replacing the shifted type-II density factor by its unshifted version](goal) is bounded by its leading density times `(beta + 1) a / r`. -/
-- @node: hill_component_density_error
lemma hill_component_density_error {beta a r : ℝ}
    (hb : 0 < beta) (ha : 0 < a) (hr : 0 < r) :
    |beta * a ^ beta * (a + r) ^ (-beta - 1) -
      beta * a ^ beta * r ^ (-beta - 1)| ≤
      (beta * a ^ beta * r ^ (-beta - 1)) * ((beta + 1) * a / r) := by
  have heq : (a + r) ^ (-beta - 1) =
      r ^ (-beta - 1) * (1 + a / r) ^ (-(beta + 1)) := by
    rw [show a + r = r * (1 + a / r) by field_simp; ring,
      Real.mul_rpow hr.le (by positivity)]
    rw [show -beta - 1 = -(beta + 1) by ring]
  have hmain : 0 ≤ beta * a ^ beta * r ^ (-beta - 1) := by positivity
  rw [heq, show beta * a ^ beta *
      (r ^ (-beta - 1) * (1 + a / r) ^ (-(beta + 1))) -
      beta * a ^ beta * r ^ (-beta - 1) =
      (beta * a ^ beta * r ^ (-beta - 1)) *
        ((1 + a / r) ^ (-(beta + 1)) - 1) by ring,
    abs_mul, abs_of_nonneg hmain]
  have h := hill_negative_power_shift_bound (by linarith : 0 ≤ beta + 1)
    (div_nonneg ha.le hr.le)
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left h hmain

/-- Given [a positive tail index](hyp:hb), [a positive radius](hyp:hr), [positive component scales](hyp:ha), and [a common upper bound on those scales](hyp:hu), [the total shifted-density error](goal) is at most the nominal leading density times `(beta + 1) u / r`. -/
-- @node: hill_nominal_density_error
lemma hill_nominal_density_error {m : ℕ} (a : Fin m → ℝ) {beta r u : ℝ}
    (hb : 0 < beta) (hr : 0 < r) (ha : ∀ i, 0 < a i) (hu : ∀ i, a i ≤ u) :
    |(∑ i, beta * (a i) ^ beta * (a i + r) ^ (-beta - 1)) -
      beta * (∑ i, (a i) ^ beta) * r ^ (-beta - 1)| ≤
      (beta * (∑ i, (a i) ^ beta) * r ^ (-beta - 1)) * ((beta + 1) * u / r) := by
  have hsum : (∑ i, beta * (a i) ^ beta * r ^ (-beta - 1)) =
      beta * (∑ i, (a i) ^ beta) * r ^ (-beta - 1) := by
    rw [← Finset.sum_mul, Finset.mul_sum]
  rw [← hsum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |beta * (a i) ^ beta * (a i + r) ^ (-beta - 1) -
        beta * (a i) ^ beta * r ^ (-beta - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (beta * (a i) ^ beta * r ^ (-beta - 1)) *
        ((beta + 1) * u / r) := by
      apply Finset.sum_le_sum
      intro i _
      apply (hill_component_density_error hb (ha i) hr).trans
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hb.le (Real.rpow_nonneg (ha i).le _))
          (Real.rpow_nonneg hr.le _))
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hu i) (by linarith)) hr.le
    _ = _ := by rw [Finset.sum_mul]

/-- Given [a positive tail index](hyp:hb), [a positive radius](hyp:hr), [positive component scales](hyp:ha), [their upper bound](hyp:hu), [a positive convolution multiplier](hyp:hkappa), and [a positive sum of scale powers](hyp:hsum), if [the convolution approximation has half the error budget](hyp:hconv) and [the type-II shift has the other half](hyp:hshift), then [the normalized density is within the full relative error budget](goal). -/
-- @node: hill_density_relative_error_of_convolution
lemma hill_density_relative_error_of_convolution {m : ℕ} (a : Fin m → ℝ)
    {beta r u kappa f b : ℝ}
    (hb : 0 < beta) (hr : 0 < r) (ha : ∀ i, 0 < a i) (hu : ∀ i, a i ≤ u)
    (hkappa : 0 < kappa) (hsum : 0 < ∑ i, (a i) ^ beta)
    (hconv : |f - kappa * ∑ i, beta * (a i) ^ beta * (a i + r) ^ (-beta - 1)| ≤
      (beta * (kappa * ∑ i, (a i) ^ beta) * r ^ (-beta - 1)) * (b / 2))
    (hshift : (beta + 1) * u / r ≤ b / 2) :
    |f / (beta * (kappa * ∑ i, (a i) ^ beta) * r ^ (-beta - 1)) - 1| ≤ b := by
  let scale := beta * (kappa * ∑ i, (a i) ^ beta) * r ^ (-beta - 1)
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hnominal : |kappa * (∑ i, beta * (a i) ^ beta * (a i + r) ^ (-beta - 1)) -
      scale| ≤ scale * (b / 2) := by
    have h := mul_le_mul_of_nonneg_left (hill_nominal_density_error a hb hr ha hu) hkappa.le
    rw [← abs_of_pos hkappa, ← abs_mul] at h
    have heq : kappa * (beta * (∑ i, (a i) ^ beta) * r ^ (-beta - 1)) = scale := by
      dsimp [scale]
      ring
    rw [mul_sub, heq] at h
    exact h.trans (by
      rw [abs_of_pos hkappa, ← mul_assoc, heq]
      exact mul_le_mul_of_nonneg_left hshift hscale.le)
  have herr : |f - scale| ≤ scale * b := by
    have htriangle := abs_sub_le f
      (kappa * ∑ i, beta * (a i) ^ beta * (a i + r) ^ (-beta - 1)) scale
    have h := htriangle.trans (add_le_add hconv hnominal)
    calc
      _ ≤ scale * (b / 2) + scale * (b / 2) := h
      _ = scale * b := by ring
  rw [show f / scale - 1 = (f - scale) / scale by field_simp,
    abs_div, abs_of_pos hscale]
  exact (div_le_iff₀ hscale).mpr (by simpa only [mul_comm] using herr)

end Papers.TbsExtremeEffects
