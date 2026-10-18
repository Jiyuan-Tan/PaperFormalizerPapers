module
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileScoreRemainder
/-! The combined truncated-moment and CDF boundary change is a quadratic remainder. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

-- Subtracting the linear CDF term leaves only the interval swept by the
-- boundary. The negative orientation is essential for downward moves.
-- @node: debiased_quantile_boundary_pointwise
/-- [The change in the lower-tail ramp from threshold a to threshold b, after
subtracting the threshold change times the original lower-tail indicator, equals
the ramp b minus the outcome on the interval between the thresholds, with positive
orientation for an upward move and negative orientation for a downward move](goal). -/
lemma debiased_quantile_boundary_pointwise (a b y : ℝ) :
    (b - y) * indicator (y ≤ b) - (a - y) * indicator (y ≤ a) -
      (b - a) * indicator (y ≤ a) =
    (if a ≤ b then 1 else -1) *
      (Ioc (min a b) (max a b)).indicator (fun y => b - y) y := by
  by_cases hab : a ≤ b
  · rw [if_pos hab, min_eq_left hab, max_eq_right hab]
    by_cases hya : y ≤ a
    · have hyb : y ≤ b := hya.trans hab
      simp [indicator, Set.indicator, hya, hyb, not_lt.mpr hya]
    · by_cases hyb : y ≤ b
      · simp [indicator, Set.indicator, hya, hyb, lt_of_not_ge hya]
      · simp [indicator, Set.indicator, hya, hyb]
  · have hba : b ≤ a := le_of_not_ge hab
    rw [if_neg hab, min_eq_right hba, max_eq_left hba]
    by_cases hyb : y ≤ b
    · have hya : y ≤ a := hyb.trans hba
      simp [indicator, Set.indicator, hya, hyb, not_lt.mpr hyb]
    · by_cases hya : y ≤ a
      · simp [indicator, Set.indicator, hya, hyb, lt_of_not_ge hyb]
      · simp [indicator, Set.indicator, hya, hyb]

-- @node: debiased_quantile_boundary_integral
/-- [The integrated lower-tail ramp change from a to b, after subtracting its
linear indicator term at a, equals the integral of b minus the outcome over the
left-open, right-closed interval between a and b, multiplied by one for an upward
move and minus one for a downward move](goal). -/
lemma debiased_quantile_boundary_integral (ν : Measure ℝ) (a b : ℝ) :
    (∫ y, (b - y) * indicator (y ≤ b) - (a - y) * indicator (y ≤ a) -
      (b - a) * indicator (y ≤ a) ∂ν) =
    (if a ≤ b then 1 else -1) *
      ∫ y in Ioc (min a b) (max a b), b - y ∂ν := by
  simp_rw [debiased_quantile_boundary_pointwise]
  rw [integral_const_mul, integral_indicator measurableSet_Ioc]

-- @node: debiased_quantile_boundary_local_quadratic
/-- If [the threshold displacement is at most r](hyp:herr) and [every left-open,
right-closed interval within distance r of a has mass at most C times its
length](hyp:hdensity), then [the absolute integrated lower-tail ramp change after
subtracting its linear term is at most C times the squared threshold
displacement](goal). -/
lemma debiased_quantile_boundary_local_quadratic
    (ν : Measure ℝ) [IsFiniteMeasure ν] (a b r C : ℝ)
    (herr : |b - a| ≤ r)
    (hdensity : ∀ u v, a - r ≤ u → u ≤ v → v ≤ a + r →
      (ν (Ioc u v)).toReal ≤ C * (v - u)) :
    |∫ y, (b - y) * indicator (y ≤ b) - (a - y) * indicator (y ≤ a) -
      (b - a) * indicator (y ≤ a) ∂ν| ≤ C * |b - a| ^ 2 := by
  rw [debiased_quantile_boundary_integral, abs_mul]
  have hs : |(if a ≤ b then 1 else -1 : ℝ)| = 1 := by
    split_ifs <;> norm_num
  rw [hs, one_mul]
  exact quantile_boundary_integral_local ν a b r C herr hdensity

-- The global bound uses only finite mass. Thus an L2 path does not need
-- pointwise bounded directions or a global density bound.
-- @node: debiased_quantile_boundary_linear_bound
/-- [For a finite outcome measure, the absolute integrated lower-tail ramp change
from a to b after subtracting its linear indicator term is at most the absolute
threshold displacement times the total mass](goal). -/
lemma debiased_quantile_boundary_linear_bound
    (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) :
    |∫ y, (b - y) * indicator (y ≤ b) - (a - y) * indicator (y ≤ a) -
      (b - a) * indicator (y ≤ a) ∂ν| ≤ |b - a| * (ν univ).toReal := by
  rw [debiased_quantile_boundary_integral, abs_mul]
  have hs : |(if a ≤ b then 1 else -1 : ℝ)| = 1 := by
    split_ifs <;> norm_num
  rw [hs, one_mul]
  have hbound : ∀ᵐ y ∂ν.restrict (Ioc (min a b) (max a b)),
      ‖b - y‖ ≤ |b - a| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs]
    by_cases hab : a ≤ b
    · simp only [min_eq_left hab, max_eq_right hab] at hy
      rw [abs_of_nonneg (by linarith [hy.2] : 0 ≤ b - y),
        abs_of_nonneg (sub_nonneg.mpr hab)]
      linarith [hy.1]
    · have hba : b ≤ a := le_of_not_ge hab
      simp only [min_eq_right hba, max_eq_left hba] at hy
      rw [abs_of_nonpos (by linarith [hy.1] : b - y ≤ 0),
        abs_of_nonpos (sub_nonpos.mpr hba)]
      linarith [hy.2]
  have hint := norm_integral_le_of_norm_le_const hbound
  simp only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] at hint
  exact hint.trans (mul_le_mul_of_nonneg_left
    (measureReal_mono (subset_univ _)) (abs_nonneg _))

-- @node: debiased_quantile_boundary_global_quadratic
/-- If [r is positive](hyp:hr), [C is nonnegative](hyp:hC), and [intervals within
distance r of a have mass at most C times their length](hyp:hdensity), then [for
any new threshold b the absolute integrated debiased lower-tail ramp change is
at most the squared displacement times the sum of C and the total mass divided
by r](goal). -/
lemma debiased_quantile_boundary_global_quadratic
    (ν : Measure ℝ) [IsFiniteMeasure ν] (a b r C : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ u v, a - r ≤ u → u ≤ v → v ≤ a + r →
      (ν (Ioc u v)).toReal ≤ C * (v - u)) :
    |∫ y, (b - y) * indicator (y ≤ b) - (a - y) * indicator (y ≤ a) -
      (b - a) * indicator (y ≤ a) ∂ν| ≤
        (C + (ν univ).toReal / r) * (b - a) ^ 2 := by
  by_cases he : |b - a| ≤ r
  · have hb := debiased_quantile_boundary_local_quadratic ν a b r C he hdensity
    rw [sq_abs] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (by positivity)) (sq_nonneg _))
  · have he' : r ≤ |b - a| := le_of_not_ge he
    have hlarge : |b - a| * (ν univ).toReal ≤
        ((ν univ).toReal / r) * (b - a) ^ 2 := by
      have hsq : r * |b - a| ≤ (b - a) ^ 2 := by
        nlinarith [sq_abs (b - a)]
      have hm := mul_le_mul_of_nonneg_left hsq (ENNReal.toReal_nonneg (a := ν univ))
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hr).mpr
      nlinarith
    exact (debiased_quantile_boundary_linear_bound ν a b).trans
      (hlarge.trans (by nlinarith [sq_nonneg (b - a)]))

end Papers.TbsPrteOptimalTransport
