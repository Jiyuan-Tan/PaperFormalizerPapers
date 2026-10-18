module
public import Papers.TbsPrteOptimalTransport.Helpers.DebiasedBandBoundary
/-! Exact boundary decomposition with crossed fitted endpoints.
A crossing of a separated population band forces a large endpoint error, so
its bounded-outcome correction is controlled by squared endpoint errors. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set
open scoped Classical

-- @node: continuous_band_indicator_ramp_crossing_identity
/-- [The outcome restricted to the band above the first endpoint and at or below the second, plus the first endpoint times its lower-tail indicator minus the second endpoint times its lower-tail indicator, equals the difference of the two endpoint-minus-outcome lower-tail ramps plus the outcome restricted to the reversed band](goal). -/
lemma continuous_band_indicator_ramp_crossing_identity (a b y : ℝ) :
    y * indicator (a < y ∧ y ≤ b) + a * indicator (y ≤ a) -
      b * indicator (y ≤ b) =
    (a - y) * indicator (y ≤ a) - (b - y) * indicator (y ≤ b) +
      y * indicator (b < y ∧ y ≤ a) := by
  by_cases ha : y ≤ a <;> by_cases hb : y ≤ b
  all_goals simp [indicator, ha, hb, not_lt.mpr, lt_of_not_ge]
  all_goals ring

-- @node: continuous_debiased_band_boundary_crossing_decomposition
/-- If [the population lower endpoint does not exceed the upper endpoint](hyp:hab), [the debiased band-boundary error equals the lower ramp's linearization remainder minus the upper ramp's linearization remainder, plus the outcome when it lies above the fitted upper endpoint and at or below the fitted lower endpoint](goal). -/
lemma continuous_debiased_band_boundary_crossing_decomposition (a b a' b' y : ℝ)
    (hab : a ≤ b) :
    continuousDebiasedBandBoundary a b a' b' y =
    ((a' - y) * indicator (y ≤ a') - (a - y) * indicator (y ≤ a) -
      (a' - a) * indicator (y ≤ a)) -
    ((b' - y) * indicator (y ≤ b') - (b - y) * indicator (y ≤ b) -
      (b' - b) * indicator (y ≤ b)) + y * indicator (b' < y ∧ y ≤ a') := by
  unfold continuousDebiasedBandBoundary
  rw [continuous_band_indicator_ramp_crossing_identity,
    continuous_band_indicator_ramp_identity a b y hab]
  ring

-- @node: crossed_band_endpoint_error_sum_ge_gap
/-- If [the population band width is at least the specified gap](hyp:hgap) and [the fitted upper endpoint lies below the fitted lower endpoint](hyp:hcross), [the sum of the absolute errors in the two fitted endpoints is at least that gap](goal). -/
lemma crossed_band_endpoint_error_sum_ge_gap (a b a' b' delta : ℝ)
    (hgap : delta ≤ b - a) (hcross : b' < a') :
    delta ≤ |a' - a| + |b' - b| := by
  have ha := le_abs_self (a' - a)
  have hb := neg_le_abs (b' - b)
  linarith

-- @node: crossed_band_quadratic_correction_bound
/-- If [the gap is positive](hyp:hdelta), [the population band width is at least that gap](hyp:hgap), [the outcome bound is nonnegative](hyp:hB), and [the absolute outcome is at most that bound](hyp:hy), [the absolute outcome restricted to the reversed fitted band is at most twice the outcome bound divided by the squared gap, times the sum of the two squared endpoint errors](goal). -/
lemma crossed_band_quadratic_correction_bound (a b a' b' y delta B : ℝ)
    (hdelta : 0 < delta) (hgap : delta ≤ b - a)
    (hB : 0 ≤ B) (hy : |y| ≤ B) :
    |y * indicator (b' < y ∧ y ≤ a')| ≤
      (2 * B / delta ^ 2) * ((a' - a) ^ 2 + (b' - b) ^ 2) := by
  have hs : 0 ≤ (a' - a) ^ 2 + (b' - b) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases hc : b' < y ∧ y ≤ a'
  · have he := crossed_band_endpoint_error_sum_ge_gap a b a' b' delta hgap
      (hc.1.trans_le hc.2)
    have hsq : delta ^ 2 ≤ 2 * ((a' - a) ^ 2 + (b' - b) ^ 2) := by
      have hdiff := sq_nonneg (|a' - a| - |b' - b|)
      have hsum := abs_nonneg (a' - a)
      have hsum' := abs_nonneg (b' - b)
      nlinarith [sq_abs (a' - a), sq_abs (b' - b)]
    have hunit : 1 ≤ (2 / delta ^ 2) * ((a' - a) ^ 2 + (b' - b) ^ 2) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hdelta)).2
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hunit hB
    simp only [indicator, if_pos hc, mul_one] at ⊢
    calc
      |y| ≤ B := hy
      _ ≤ B * ((2 / delta ^ 2) * ((a' - a) ^ 2 + (b' - b) ^ 2)) := by
        simpa only [mul_one] using hmul
      _ = _ := by ring
  · simp only [indicator, if_neg hc, mul_zero, abs_zero]
    positivity

-- @node: continuous_debiased_band_boundary_unordered_bound
/-- If [the gap is positive](hyp:hdelta), [the population band width is at least that gap](hyp:hgap), [the outcome bound is nonnegative](hyp:hB), and [the outcome's absolute value is bounded by it](hyp:hy), [the absolute debiased band-boundary error is at most the sum of the absolute lower and upper ramp linearization remainders plus twice the outcome bound divided by the squared gap times the sum of squared endpoint errors, without requiring ordered fitted endpoints](goal). -/
lemma continuous_debiased_band_boundary_unordered_bound (a b a' b' y delta B : ℝ)
    (hdelta : 0 < delta) (hgap : delta ≤ b - a)
    (hB : 0 ≤ B) (hy : |y| ≤ B) :
    |continuousDebiasedBandBoundary a b a' b' y| ≤
      |(a' - y) * indicator (y ≤ a') - (a - y) * indicator (y ≤ a) -
        (a' - a) * indicator (y ≤ a)| +
      |(b' - y) * indicator (y ≤ b') - (b - y) * indicator (y ≤ b) -
        (b' - b) * indicator (y ≤ b)| +
      (2 * B / delta ^ 2) * ((a' - a) ^ 2 + (b' - b) ^ 2) := by
  have hab : a ≤ b := by linarith
  rw [continuous_debiased_band_boundary_crossing_decomposition a b a' b' y hab]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_sub _ _) (crossed_band_quadratic_correction_bound a b a' b' y delta B
      hdelta hgap hB hy))

-- @node: crossed_band_integrated_quadratic_correction_bound
/-- Suppose [the population lower endpoint](hyp:ha), [population upper endpoint](hyp:hb), [fitted lower endpoint](hyp:hah), [fitted upper endpoint](hyp:hbh), and [outcome](hyp:hy) are measurable, [the gap is positive](hyp:hdelta), and [the outcome bound is nonnegative](hyp:hB). If [the population band width is almost surely at least the gap](hyp:hgap), [the absolute outcome is almost surely bounded by the outcome bound](hyp:hyB), and [both squared endpoint errors are integrable](hyp:ia,ib), then [the outcome restricted to the reversed fitted band is integrable, and its integrated absolute value is at most twice the outcome bound divided by the squared gap times the sum of the integrated squared endpoint errors](goal). -/
lemma crossed_band_integrated_quadratic_correction_bound
    {A : Type*} [MeasurableSpace A] (mu : Measure A)
    (a b ah bh y : A → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (hah : Measurable ah) (hbh : Measurable bh) (hy : Measurable y)
    (delta B : ℝ) (hdelta : 0 < delta) (hB : 0 ≤ B)
    (hgap : ∀ᵐ x ∂mu, delta ≤ b x - a x)
    (hyB : ∀ᵐ x ∂mu, |y x| ≤ B)
    (ia : Integrable (fun x => (ah x - a x) ^ 2) mu)
    (ib : Integrable (fun x => (bh x - b x) ^ 2) mu) :
    Integrable (fun x => y x * indicator (bh x < y x ∧ y x ≤ ah x)) mu ∧
    (∫ x, |y x * indicator (bh x < y x ∧ y x ≤ ah x)| ∂mu) ≤
      (2 * B / delta ^ 2) *
        ((∫ x, (ah x - a x) ^ 2 ∂mu) + (∫ x, (bh x - b x) ^ 2 ∂mu)) := by
  let C := 2 * B / delta ^ 2
  have hi : Integrable (fun x => C * ((ah x - a x) ^ 2 + (bh x - b x) ^ 2)) mu :=
    (ia.fun_add ib).const_mul C
  have hbound : ∀ᵐ x ∂mu,
      |y x * indicator (bh x < y x ∧ y x ≤ ah x)| ≤
        C * ((ah x - a x) ^ 2 + (bh x - b x) ^ 2) := by
    filter_upwards [hgap, hyB] with x hx hxy
    exact crossed_band_quadratic_correction_bound _ _ _ _ _ delta B hdelta hx hB hxy
  have hm : Measurable (fun x => y x * indicator (bh x < y x ∧ y x ≤ ah x)) := by
    fun_prop
  have hc := hi.mono' hm.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hc, ?_⟩
  calc
    _ ≤ ∫ x, C * ((ah x - a x) ^ 2 + (bh x - b x) ^ 2) ∂mu :=
      integral_mono_ae hc.abs hi hbound
    _ = _ := by rw [integral_const_mul, integral_add ia ib]

end Papers.TbsPrteOptimalTransport
