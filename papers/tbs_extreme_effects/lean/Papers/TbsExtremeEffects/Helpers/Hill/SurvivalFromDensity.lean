module
public import Papers.TbsExtremeEffects.Helpers.Hill.NominalDensity
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Integrating the radial density envelope in the adaptive Hill proof.
A uniform relative density error on a tail gives the same relative survival
error. This preserves the logarithmic envelope at index one. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped ENNReal

/-- If [the tail exponent is positive](hyp:hb) and [the lower integration limit is positive](hyp:hr), then [the integral of the leading power-law density above that limit equals its survival tail](goal).
Here [the exponent, scale, and lower limit](hyp:beta,C,r) specify the leading density. -/
-- @node: hill_leading_density_integral
lemma hill_leading_density_integral {beta C r : ℝ} (hb : 0 < beta) (hr : 0 < r) :
    (∫ x : ℝ in Set.Ioi r, beta * C * x ^ (-beta - 1)) = C * r ^ (-beta) := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hr,
    show -beta - 1 + 1 = -beta by ring]
  field_simp

/-- If [the exponent is positive](hyp:hb), [the scale is positive](hyp:hC), [the evaluation point is positive](hyp:hx), and [the density has the stated relative error](hyp:h), then [its absolute error is bounded by that relative error times the leading density](goal).
Here [the exponent, scale, point, error bound, and density value](hyp:beta,C,x,b,f) specify the comparison. -/
-- @node: hill_absolute_density_error_of_relative
lemma hill_absolute_density_error_of_relative {beta C x b f : ℝ}
    (hb : 0 < beta) (hC : 0 < C) (hx : 0 < x)
    (h : |f / (beta * C * x ^ (-beta - 1)) - 1| ≤ b) :
    |f - beta * C * x ^ (-beta - 1)| ≤ b * (beta * C * x ^ (-beta - 1)) := by
  have hs : 0 < beta * C * x ^ (-beta - 1) := by positivity
  rw [show f / (beta * C * x ^ (-beta - 1)) - 1 =
      (f - beta * C * x ^ (-beta - 1)) / (beta * C * x ^ (-beta - 1)) by
      field_simp, abs_div, abs_of_pos hs] at h
  exact (div_le_iff₀ hs).mp h

/-- If [the exponent](hyp:hb), [scale](hyp:hC), and [tail threshold](hyp:hr) are positive, [the density is measurable](hyp:hf), and [its relative error is uniformly bounded above the threshold](hyp:herror), then [the density is integrable on that upper tail](goal).
Here [the density](hyp:f) and [the exponent, scale, threshold, and error bound](hyp:beta,C,r,b) specify the tail model. -/
-- @node: hill_density_integrable_of_relative_error
lemma hill_density_integrable_of_relative_error (f : ℝ → ℝ) {beta C r b : ℝ}
    (hb : 0 < beta) (hC : 0 < C) (hr : 0 < r) (hf : Measurable f)
    (herror : ∀ x > r, |f x / (beta * C * x ^ (-beta - 1)) - 1| ≤ b) :
    IntegrableOn f (Set.Ioi r) := by
  have hlead := (integrableOn_Ioi_rpow_of_lt (by linarith : -beta - 1 < -1) hr).const_mul (beta * C)
  apply (hlead.const_mul (b + 1)).mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos := hr.trans hx
  have hs : 0 ≤ beta * C * x ^ (-beta - 1) := by positivity
  have he := hill_absolute_density_error_of_relative hb hC hxpos (herror x hx)
  rw [Real.norm_eq_abs]
  calc
    |f x| ≤ |f x - beta * C * x ^ (-beta - 1)| +
        |beta * C * x ^ (-beta - 1)| := by
      simpa only [sub_zero] using abs_sub_le (f x) (beta * C * x ^ (-beta - 1)) 0
    _ ≤ b * (beta * C * x ^ (-beta - 1)) + beta * C * x ^ (-beta - 1) :=
      add_le_add he (le_of_eq (abs_of_nonneg hs))
    _ = _ := by ring

/-- If [the exponent](hyp:hb), [scale](hyp:hC), and [tail threshold](hyp:hr) are positive, [the density is measurable](hyp:hf), [survival equals its tail density integral](hyp:hS), and [the density has uniformly bounded relative error](hyp:herror), then [survival has the same relative error as the leading power-law tail](goal).
Here [the density](hyp:f) and [the exponent, scale, threshold, error bound, and survival value](hyp:beta,C,r,b,S) specify the comparison. -/
-- @node: hill_survival_relative_error_of_density
lemma hill_survival_relative_error_of_density (f : ℝ → ℝ) {beta C r b S : ℝ}
    (hb : 0 < beta) (hC : 0 < C) (hr : 0 < r) (hf : Measurable f)
    (hS : S = ∫ x : ℝ in Set.Ioi r, f x)
    (herror : ∀ x > r, |f x / (beta * C * x ^ (-beta - 1)) - 1| ≤ b) :
    |S / (C * r ^ (-beta)) - 1| ≤ b := by
  have hlead := (integrableOn_Ioi_rpow_of_lt (by linarith : -beta - 1 < -1) hr).const_mul (beta * C)
  have hfi := hill_density_integrable_of_relative_error f hb hC hr hf herror
  have he : |∫ x : ℝ in Set.Ioi r, f x - beta * C * x ^ (-beta - 1)| ≤
      ∫ x : ℝ in Set.Ioi r, b * (beta * C * x ^ (-beta - 1)) := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (hlead.const_mul b)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs]
    exact hill_absolute_density_error_of_relative hb hC (hr.trans hx) (herror x hx)
  rw [integral_sub hfi hlead, ← hS, hill_leading_density_integral hb hr] at he
  rw [integral_const_mul, hill_leading_density_integral hb hr] at he
  have hs : 0 < C * r ^ (-beta) := by positivity
  rw [show S / (C * r ^ (-beta)) - 1 = (S - C * r ^ (-beta)) / (C * r ^ (-beta)) by
    field_simp, abs_div, abs_of_pos hs]
  exact (div_le_iff₀ hs).mpr he

/-- If [the exponent is positive](hyp:hb), [the scale is positive](hyp:hC), [the point is positive](hyp:hx), [the density has the stated relative error](hyp:h), and [that error bound is less than one](hyp:hsmall), then [the density is positive at that point](goal).
Here [the exponent, scale, point, error bound, and density value](hyp:beta,C,x,b,f) specify the comparison. -/
-- @node: hill_density_pos_of_relative_error
lemma hill_density_pos_of_relative_error {beta C x b f : ℝ}
    (hb : 0 < beta) (hC : 0 < C) (hx : 0 < x)
    (h : |f / (beta * C * x ^ (-beta - 1)) - 1| ≤ b) (hsmall : b < 1) :
    0 < f := by
  have hs : 0 < beta * C * x ^ (-beta - 1) := by positivity
  have he := (abs_le.mp h).1
  have hratio : 0 < f / (beta * C * x ^ (-beta - 1)) := by linarith
  exact (div_pos_iff_of_pos_right hs).mp hratio

/-- If [the density is measurable](hyp:hf), [nonnegative above the threshold](hyp:hpos), and [the measure's upper-tail mass equals the weighted Lebesgue tail mass](hyp:hLaw), then [the measure's real upper-tail mass equals the density integral](goal).
Here [the measure](hyp:nu), [the density](hyp:f), and [the threshold](hyp:r) define the tail. -/
-- @node: hill_tail_mass_eq_density_integral
lemma hill_tail_mass_eq_density_integral (nu : Measure ℝ) (f : ℝ → ℝ)
    {r : ℝ} (hf : Measurable f) (hpos : ∀ x > r, 0 ≤ f x)
    (hLaw : nu (Set.Ioi r) = (volume.withDensity (fun x => ENNReal.ofReal (f x)))
      (Set.Ioi r)) :
    nu.real (Set.Ioi r) = ∫ x : ℝ in Set.Ioi r, f x := by
  rw [Measure.real, hLaw, withDensity_apply _ measurableSet_Ioi]
  apply (integral_eq_lintegral_of_nonneg_ae _ hf.aestronglyMeasurable).symm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact hpos x hx

end Papers.TbsExtremeEffects
