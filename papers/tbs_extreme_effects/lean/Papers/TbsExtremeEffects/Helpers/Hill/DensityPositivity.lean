module
public import Papers.TbsExtremeEffects.Helpers.Hill.TailCalibration
public import Papers.TbsExtremeEffects.Helpers.Hill.SurvivalFromDensity

/-! Eventual positivity of the partition density from the convolution envelope. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped Topology BigOperators

/-- For [a positive tail exponent](hyp:hb), [the radial remainder shape converges to zero at large radii](goal).
@node: hill_radial_remainder_tendsto_zero -/
lemma hill_radial_remainder_tendsto_zero {beta : ℝ} (hb : 0 < beta) :
    Tendsto (hillRadialRemainderShape beta) atTop (𝓝 0) := by
  unfold hillRadialRemainderShape
  split_ifs with hsmall heq
  · exact tendsto_rpow_neg_atTop hb
  · have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa only [Real.rpow_neg_one, pow_one, one_mul, mul_one, add_zero,
      div_eq_mul_inv, mul_comm] using h
  · exact tendsto_rpow_neg_atTop zero_lt_one

/-- For [component scales](hyp:a), [a positive tail exponent](hyp:hb), [a positive prefactor](hyp:hk), [positive component scales](hyp:ha), [a common upper bound on those scales](hyp:hu), and [a positive sum of powered scales](hyp:hsum), [the nominal partition density eventually has relative error at most one half from its leading tail term](goal).
@node: hill_nominal_partition_relative_error_eventually -/
lemma hill_nominal_partition_relative_error_eventually {m : ℕ} (a : Fin m → ℝ)
    {beta kappa u : ℝ} (hb : 0 < beta) (hk : 0 < kappa)
    (ha : ∀ i, 0 < a i) (hu : ∀ i, a i ≤ u)
    (hsum : 0 < ∑ i, (a i) ^ beta) :
    ∀ᶠ r : ℝ in atTop,
      |(kappa * ∑ i, ∫ z,
          hillLargestSummandIntegrand a beta r (fun j => a j * z j) i
            ∂hillNominalComponentLaw beta m) /
        (beta * (kappa * ∑ i, (a i) ^ beta) * r ^ (-beta - 1)) - 1| ≤ 1 / 2 := by
  have hscale : 0 < beta * (kappa * ∑ i, (a i) ^ beta) := by positivity
  have hBudget := (hill_radial_remainder_tendsto_zero hb).const_mul
    (hillNumericalBudgetCoefficient a beta kappa)
  have hBudgetSmall := (tendsto_order.mp hBudget).2
    (beta * (kappa * ∑ i, (a i) ^ beta) * ((1 / 2 : ℝ) / 2))
    (by simpa only [mul_zero] using (show 0 <
      beta * (kappa * ∑ i, (a i) ^ beta) * ((1 / 2 : ℝ) / 2) by positivity))
  have hShift := (tendsto_rpow_neg_atTop zero_lt_one).const_mul ((beta + 1) * u)
  have hShiftSmall := (tendsto_order.mp hShift).2 ((1 / 2 : ℝ) / 2)
    (by norm_num)
  filter_upwards [hBudgetSmall, hShiftSmall,
    eventually_ge_atTop (max 2 (Real.exp 1))] with r hbudget hshift hr
  have hr2 : 2 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := by linarith
  have hlog : 1 ≤ Real.log r := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hr)
  have hNominal := hill_nominal_data_of_partition_and_radial_bound a hb ha hk.le
    hr2 hlog rfl hbudget.le
  have hConvolution := hill_convolution_data_of_largest_summand a hb hrpos ha
    (hill_largest_summand_data_of_component_data a hb hrpos ha hk.le
      (hill_component_data_of_polynomial_data a hb hrpos ha hk.le
        (hill_polynomial_data_of_pareto_data a ha
          (hill_pareto_data_of_nominal_data a hb ha hNominal))))
  apply hill_density_relative_error_of_convolution a hb hrpos ha hu hk hsum
    (hill_convolution_error_of_remainder_data a hb hrpos ha hk.le hConvolution)
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hshift.le

/-- For [component scales](hyp:a), [a positive tail exponent](hyp:hb), [a positive prefactor](hyp:hk), [positive component scales](hyp:ha), [their common upper bound](hyp:hu), and [a positive sum of powered scales](hyp:hsum), [the nominal partition density is eventually positive](goal).
@node: hill_nominal_partition_density_eventually_pos -/
lemma hill_nominal_partition_density_eventually_pos {m : ℕ} (a : Fin m → ℝ)
    {beta kappa u : ℝ} (hb : 0 < beta) (hk : 0 < kappa)
    (ha : ∀ i, 0 < a i) (hu : ∀ i, a i ≤ u)
    (hsum : 0 < ∑ i, (a i) ^ beta) :
    ∀ᶠ r : ℝ in atTop, 0 < kappa * ∑ i, ∫ z,
      hillLargestSummandIntegrand a beta r (fun j => a j * z j) i
        ∂hillNominalComponentLaw beta m := by
  filter_upwards [hill_nominal_partition_relative_error_eventually a hb hk ha hu hsum,
    eventually_gt_atTop (0 : ℝ)] with r herr hr
  exact hill_density_pos_of_relative_error hb (mul_pos hk hsum) hr herr (by norm_num)

/-- For [component scales](hyp:a), [a positive tail exponent](hyp:hb), [a positive prefactor](hyp:hk), [positive component scales](hyp:ha), [their common upper bound](hyp:hu), [a positive sum of powered scales](hyp:hsum), and [a requested cutoff](hyp:cutoff), [there is a larger positive threshold beyond which the nominal partition density remains positive](goal).
@node: hill_nominal_partition_density_positive_tail -/
lemma hill_nominal_partition_density_positive_tail {m : ℕ} (a : Fin m → ℝ)
    {beta kappa u : ℝ} (hb : 0 < beta) (hk : 0 < kappa)
    (ha : ∀ i, 0 < a i) (hu : ∀ i, a i ≤ u)
    (hsum : 0 < ∑ i, (a i) ^ beta) (cutoff : ℝ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ cutoff < r₀ ∧ ∀ r ≥ r₀,
      0 < kappa * ∑ i, ∫ z,
        hillLargestSummandIntegrand a beta r (fun j => a j * z j) i
          ∂hillNominalComponentLaw beta m := by
  obtain ⟨r₁, hpos⟩ := eventually_atTop.mp
    (hill_nominal_partition_density_eventually_pos a hb hk ha hu hsum)
  refine ⟨max (max 1 (cutoff + 1)) r₁, ?_, ?_, ?_⟩
  · exact zero_lt_one.trans_le ((le_max_left _ _).trans (le_max_left _ _))
  · have := (le_max_right 1 (cutoff + 1)).trans
      (le_max_left (max 1 (cutoff + 1)) r₁)
    linarith
  · intro r hr
    exact hpos r ((le_max_right _ _).trans hr)

end Papers.TbsExtremeEffects
