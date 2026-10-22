module
public import Mathlib.Probability.Distributions.Pareto
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

/-! Pareto radial moments for the identification limit. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- If [the Pareto shape parameter is positive](hyp:hb), then [the Pareto density times a power of the radius clamped below at one equals the displayed power density on the unit half-line and zero below it](goal).

@node: pareto_clamped_power_density -/
lemma pareto_clamped_power_density {beta a : ℝ} (hb : 0 < beta) (x : ℝ) :
    (paretoPDF 1 beta x).toReal * (max 1 x) ^ a =
      (Set.Ici (1 : ℝ)).indicator (fun x => beta * x ^ (a - beta - 1)) x := by
  rw [paretoPDF, ENNReal.toReal_ofReal (paretoPDFReal_nonneg (by norm_num) hb.le x)]
  by_cases hx : 1 ≤ x
  · rw [Set.indicator_of_mem (show x ∈ Set.Ici (1 : ℝ) from hx),
      paretoPDFReal, if_pos hx, max_eq_right hx,
      Real.one_rpow, mul_one]
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    rw [mul_assoc, ← Real.rpow_add hxpos]
    congr 2
    ring
  · rw [Set.indicator_of_notMem (show x ∉ Set.Ici (1 : ℝ) from hx),
      paretoPDFReal, if_neg hx, zero_mul]

/-- If [the Pareto shape parameter is positive](hyp:hb) and [the power is smaller than that shape parameter](hyp:ha), then [the power of the radius clamped below at one is integrable under the unit-scale Pareto law](goal).

@node: pareto_clamped_power_integrable -/
lemma pareto_clamped_power_integrable {beta a : ℝ} (hb : 0 < beta) (ha : a < beta) :
    Integrable (fun x : ℝ => (max 1 x) ^ a) (paretoMeasure 1 beta) := by
  have hmeas : Measurable (paretoPDF 1 beta) := by unfold paretoPDF; fun_prop
  have hfin : ∀ᵐ x ∂(volume : Measure ℝ), paretoPDF 1 beta x < ∞ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  rw [paretoMeasure, integrable_withDensity_iff_integrable_smul' hmeas hfin]
  simp only [smul_eq_mul, pareto_clamped_power_density hb]
  apply (integrable_indicator_iff measurableSet_Ici).2
  have hp : IntegrableOn (fun x : ℝ => x ^ (a - beta - 1)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (hp.const_mul beta)

/-- If [the Pareto shape parameter is positive](hyp:hb) and [the power is smaller than that shape parameter](hyp:ha), then [the mean of the power of the radius clamped below at one is the shape parameter divided by shape minus power](goal).

@node: pareto_clamped_power_moment -/
lemma pareto_clamped_power_moment {beta a : ℝ} (hb : 0 < beta) (ha : a < beta) :
    (∫ x : ℝ, (max 1 x) ^ a ∂paretoMeasure 1 beta) = beta / (beta - a) := by
  have hmeas : Measurable (paretoPDF 1 beta) := by unfold paretoPDF; fun_prop
  have hfin : ∀ᵐ x ∂(volume : Measure ℝ), paretoPDF 1 beta x < ∞ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  rw [paretoMeasure, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
  simp only [smul_eq_mul, pareto_clamped_power_density hb]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : a - beta - 1 < -1)
      (by norm_num : (0 : ℝ) < 1), Real.one_rpow]
  have hne : beta - a ≠ 0 := (sub_pos.mpr ha).ne'
  have hne' : a - beta - 1 + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- If [the Pareto shape parameter is positive](hyp:hb) and [the radial cutoff is at least one](hyp:hr), then [the unit-scale Pareto survival probability beyond that cutoff is the cutoff raised to minus the shape parameter](goal).

@node: pareto_unit_survival -/
lemma pareto_unit_survival {beta r : ℝ} (hb : 0 < beta) (hr : 1 ≤ r) :
    ((paretoMeasure 1 beta) (Set.Ioi r)).toReal = r ^ (-beta) := by
  rw [paretoMeasure, withDensity_apply _ measurableSet_Ioi]
  change (∫⁻ x in Set.Ioi r, ENNReal.ofReal (paretoPDFReal 1 beta x)).toReal = _
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => paretoPDFReal_nonneg (by norm_num) hb.le x))
    (by fun_prop : AEStronglyMeasurable (paretoPDFReal 1 beta)
      (volume.restrict (Set.Ioi r)))]
  have heq : (∫ x in Set.Ioi r, paretoPDFReal 1 beta x) =
      ∫ x in Set.Ioi r, beta * x ^ (-(beta + 1)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [paretoPDFReal, if_pos (hr.trans hx.le), Real.one_rpow, mul_one]
  rw [heq, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -(beta + 1) < -1)
      (lt_of_lt_of_le (by norm_num) hr)]
  have he : -(beta + 1) + 1 = -beta := by ring
  rw [he]
  field_simp

end Papers.TbsExtremeEffects
