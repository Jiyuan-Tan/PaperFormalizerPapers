module
public import Papers.TbsExtremeEffects.Helpers.Hill.NominalProductLaw
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-! Numerical convolution budgets in the three radial tail regimes. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped BigOperators
open Classical

/-- For [a tail index](hyp:beta) and [a radius](hyp:r), [the radial remainder shape](goal) is the appropriate power-law expression, retaining a logarithm at the boundary index one. -/
-- @node: hillRadialRemainderShape
noncomputable def hillRadialRemainderShape (beta r : ℝ) : ℝ :=
  if beta < 1 then r ^ (-beta)
  else if beta = 1 then r ^ (-1 : ℝ) * Real.log r
  else r ^ (-1 : ℝ)

/-- For [a tail index](hyp:beta) and [a cap coefficient](hyp:C), [the capped-moment coefficient](goal) is defined by the corresponding subcritical, boundary, or supercritical formula. -/
-- @node: hillCappedMomentCoefficient
noncomputable def hillCappedMomentCoefficient (beta C : ℝ) : ℝ :=
  if beta < 1 then 1 + C / (1 - beta)
  else if beta = 1 then 1 + C
  else 1 + C / (beta - 1)

/-- [A nonnegative cap coefficient](hyp:hC) guarantees that [the capped-moment coefficient](goal) is nonnegative. -/
-- @node: hill_capped_moment_coefficient_nonneg
lemma hill_capped_moment_coefficient_nonneg {beta C : ℝ} (hC : 0 ≤ C) :
    0 ≤ hillCappedMomentCoefficient beta C := by
  unfold hillCappedMomentCoefficient
  split_ifs with h h1
  · positivity
  · positivity
  · have : 0 < beta - 1 := sub_pos.mpr (lt_of_le_of_ne (not_lt.mp h) (Ne.symm h1))
    positivity

/-- Given [a nonnegative cap coefficient](hyp:hC), [a radius at least two](hyp:hr), and [a logarithm at least one](hyp:hlog), [the capped moment envelope](goal) is bounded by its coefficient times the appropriate radial growth. -/
-- @node: hill_capped_moment_radial_bound
lemma hill_capped_moment_radial_bound {beta C r : ℝ}
    (hC : 0 ≤ C) (hr : 2 ≤ r) (hlog : 1 ≤ Real.log r) :
    hillCappedMomentEnvelope beta C (max 1 (r / 2)) ≤
      hillCappedMomentCoefficient beta C *
        (if beta < 1 then r ^ (1 - beta) else if beta = 1 then Real.log r else 1) := by
  have hr1 : 1 ≤ r := by linarith
  have hcap : max 1 (r / 2) ≤ r := max_le hr1 (by linarith)
  unfold hillCappedMomentEnvelope hillCappedMomentCoefficient
  split_ifs with hb hb1
  · have hp := Real.rpow_le_rpow (by positivity : 0 ≤ max 1 (r / 2)) hcap
      (by linarith : 0 ≤ 1 - beta)
    have hone := Real.one_le_rpow hr1 (by linarith : 0 ≤ 1 - beta)
    have hcoef : 0 ≤ C / (1 - beta) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hp hcoef]
  · have hl := Real.log_le_log (by positivity : 0 < max 1 (r / 2)) hcap
    nlinarith [mul_le_mul_of_nonneg_left hl hC]
  · simp

/-- [For a positive radius](hyp:hr), [multiplying the near-region growth by its density slope](goal) equals the density scale times the radial remainder shape. -/
-- @node: hill_near_radial_scale
lemma hill_near_radial_scale {beta r : ℝ} (hr : 0 < r) :
    r ^ (-beta - 2) *
      (if beta < 1 then r ^ (1 - beta) else if beta = 1 then Real.log r else 1) =
    r ^ (-beta - 1) * hillRadialRemainderShape beta r := by
  unfold hillRadialRemainderShape
  split_ifs with hb hb1
  · rw [← Real.rpow_add hr, ← Real.rpow_add hr]
    congr 1 <;> ring
  · subst beta
    rw [← mul_assoc, ← Real.rpow_add hr]
    norm_num
  · rw [mul_one, ← Real.rpow_add hr]
    congr 1 <;> ring

/-- Given [a radius at least two](hyp:hr) with [logarithm at least one](hyp:hlog), [the far-region power-law tail](goal) is no larger than the density scale using the radial remainder shape. -/
-- @node: hill_far_radial_scale
lemma hill_far_radial_scale {beta r : ℝ} (hr : 2 ≤ r) (hlog : 1 ≤ Real.log r) :
    r ^ (-beta - 1) * r ^ (-beta) ≤
      r ^ (-beta - 1) * hillRadialRemainderShape beta r := by
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
  unfold hillRadialRemainderShape
  split_ifs with hb hb1
  · exact le_rfl
  · subst beta
    exact le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) hlog
  · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- For [component scales](hyp:a), [a tail index](hyp:beta), and [a convolution multiplier](hyp:kappa), [the numerical budget coefficient](goal) is the stated finite sum of near- and far-region contributions. -/
-- @node: hillNumericalBudgetCoefficient
noncomputable def hillNumericalBudgetCoefficient {m : ℕ} (a : Fin m → ℝ)
    (beta kappa : ℝ) : ℝ :=
  kappa * ∑ i : Fin m, beta * (a i) ^ beta *
    ((beta + 1) * (2 : ℝ) ^ (beta + 2) *
        (∑ j ∈ Finset.univ.erase i, hillCappedMomentCoefficient beta ((a j) ^ beta)) +
      (m : ℝ) ^ (beta + 1) * (m : ℝ) ^ beta * (2 : ℝ) ^ beta *
        (∑ j ∈ Finset.univ.erase i, (a j) ^ beta))

/-- Given [a positive tail index](hyp:hb), [a nonnegative convolution multiplier](hyp:hk), and [positive component scales](hyp:ha), [the numerical budget coefficient](goal) is nonnegative. -/
-- @node: hill_numerical_budget_coefficient_nonneg
lemma hill_numerical_budget_coefficient_nonneg {m : ℕ} (a : Fin m → ℝ)
    {beta kappa : ℝ} (hb : 0 < beta) (hk : 0 ≤ kappa) (ha : ∀ i, 0 < a i) :
    0 ≤ hillNumericalBudgetCoefficient a beta kappa := by
  unfold hillNumericalBudgetCoefficient
  apply mul_nonneg hk
  apply Finset.sum_nonneg
  intro i _
  have hai := ha i
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun j _ =>
      hill_capped_moment_coefficient_nonneg (Real.rpow_nonneg (ha j).le _))
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (ha j).le _)

/-- Given [a positive tail index](hyp:hb), [positive component scales](hyp:ha), [a nonnegative convolution multiplier](hyp:hk), [a radius at least two](hyp:hr), and [a logarithm at least one](hyp:hlog), [the full finite convolution budget](goal) is bounded by the numerical coefficient times the radial density scale. -/
-- @node: hill_numerical_convolution_budget_bound
lemma hill_numerical_convolution_budget_bound {m : ℕ} (a : Fin m → ℝ)
    {beta r kappa : ℝ} (hb : 0 < beta) (ha : ∀ i, 0 < a i)
    (hk : 0 ≤ kappa) (hr : 2 ≤ r) (hlog : 1 ≤ Real.log r) :
    kappa * (∑ i : Fin m,
      ((beta * (a i) ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2)) *
        (∑ j ∈ Finset.univ.erase i,
          hillCappedMomentEnvelope beta ((a j) ^ beta) (max 1 (r / 2))) +
        (beta * (a i) ^ beta * (r / m) ^ (-beta - 1)) *
          (((∑ j ∈ Finset.univ.erase i, (a j) ^ beta) * (m : ℝ) ^ beta) *
            (r / 2) ^ (-beta)))) ≤
      hillNumericalBudgetCoefficient a beta kappa *
        (r ^ (-beta - 1) * hillRadialRemainderShape beta r) := by
  have hrpos : 0 < r := by linarith
  unfold hillNumericalBudgetCoefficient
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ hk
  apply Finset.sum_le_sum
  intro i _
  have hai := ha i
  have hsumpos : 0 ≤ ∑ j ∈ Finset.univ.erase i, (a j) ^ beta :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (ha j).le _)
  have hm : 0 < (m : ℝ) := by exact_mod_cast ((Nat.zero_le i.val).trans_lt i.isLt)
  have hhalf : (r / 2) ^ (-beta - 2) = (2 : ℝ) ^ (beta + 2) * r ^ (-beta - 2) := by
    rw [Real.div_rpow hrpos.le (by norm_num), show -beta - 2 = -(beta + 2) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  have hhalfTail : (r / 2) ^ (-beta) = (2 : ℝ) ^ beta * r ^ (-beta) := by
    rw [Real.div_rpow hrpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  have havg : (r / m) ^ (-beta - 1) = (m : ℝ) ^ (beta + 1) * r ^ (-beta - 1) := by
    rw [Real.div_rpow hrpos.le hm.le, show -beta - 1 = -(beta + 1) by ring,
      Real.rpow_neg hm.le, div_inv_eq_mul, mul_comm]
  have hcap := Finset.sum_le_sum (s := Finset.univ.erase i)
    (fun j _ => hill_capped_moment_radial_bound (beta := beta) (Real.rpow_nonneg (ha j).le beta) hr hlog)
  rw [← Finset.sum_mul] at hcap
  rw [hhalf, hhalfTail, havg]
  calc
    _ ≤ (beta * (a i) ^ beta * (beta + 1) *
          ((2 : ℝ) ^ (beta + 2) * r ^ (-beta - 2))) *
        ((∑ j ∈ Finset.univ.erase i, hillCappedMomentCoefficient beta ((a j) ^ beta)) *
          (if beta < 1 then r ^ (1 - beta) else if beta = 1 then Real.log r else 1)) +
        (beta * (a i) ^ beta * ((m : ℝ) ^ (beta + 1) * r ^ (-beta - 1))) *
          (((∑ j ∈ Finset.univ.erase i, (a j) ^ beta) * (m : ℝ) ^ beta) *
            ((2 : ℝ) ^ beta * r ^ (-beta))) := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left hcap (by positivity)
    _ = (beta * (a i) ^ beta * (beta + 1) * (2 : ℝ) ^ (beta + 2) *
        (∑ j ∈ Finset.univ.erase i, hillCappedMomentCoefficient beta ((a j) ^ beta))) *
          (r ^ (-beta - 1) * hillRadialRemainderShape beta r) +
        (beta * (a i) ^ beta * (m : ℝ) ^ (beta + 1) * (m : ℝ) ^ beta *
          (2 : ℝ) ^ beta * (∑ j ∈ Finset.univ.erase i, (a j) ^ beta)) *
          (r ^ (-beta - 1) * r ^ (-beta)) := by
      rw [← hill_near_radial_scale hrpos]
      ring
    _ ≤ _ := by
      have hfar := mul_le_mul_of_nonneg_left (hill_far_radial_scale (beta := beta) hr hlog)
        (show 0 ≤ beta * (a i) ^ beta * (m : ℝ) ^ (beta + 1) * (m : ℝ) ^ beta *
          (2 : ℝ) ^ beta * (∑ j ∈ Finset.univ.erase i, (a j) ^ beta) by positivity)
      convert add_le_add_left hfar
        ((beta * (a i) ^ beta * (beta + 1) * (2 : ℝ) ^ (beta + 2) *
          (∑ j ∈ Finset.univ.erase i, hillCappedMomentCoefficient beta ((a j) ^ beta))) *
            (r ^ (-beta - 1) * hillRadialRemainderShape beta r)) using 1 <;> first | rfl | ring

/-- Given [a positive tail index](hyp:hb), [positive component scales](hyp:ha), [a nonnegative convolution multiplier](hyp:hk), [a radius at least two](hyp:hr), [a logarithm at least one](hyp:hlog), [a density partition identity](hyp:hpartition), and [a radial coefficient bound](hyp:hscale), [the resulting nominal largest-summand data](goal) have the stated error budget. -/
-- @node: hill_nominal_data_of_partition_and_radial_bound
lemma hill_nominal_data_of_partition_and_radial_bound {m : ℕ} (a : Fin m → ℝ)
    {beta r kappa density scale b : ℝ} (hb : 0 < beta) (ha : ∀ i, 0 < a i)
    (hk : 0 ≤ kappa) (hr : 2 ≤ r) (hlog : 1 ≤ Real.log r)
    (hpartition : density = kappa * ∑ i, ∫ z,
      hillLargestSummandIntegrand a beta r (fun j => a j * z j) i
        ∂hillNominalComponentLaw beta m)
    (hscale : hillNumericalBudgetCoefficient a beta kappa * hillRadialRemainderShape beta r ≤
      scale * (b / 2)) :
    HillNominalLargestSummandData a beta r kappa density
      ((scale * r ^ (-beta - 1)) * (b / 2)) := by
  refine ⟨hpartition, (hill_numerical_convolution_budget_bound a hb ha hk hr hlog).trans ?_⟩
  convert mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg (by linarith : 0 ≤ r) (-beta - 1)) using 1 <;> first | rfl | ring

/-- Given [a positive tail index](hyp:hb), [a positive constant](hyp:hc) no larger than one [as required](hyp:hc1), [a quantile level at least one](hyp:hv), [a base lower bound](hyp:hbase), and [a lower bound on the radius](hyp:hQ), [the radial remainder shape at that radius](goal) is bounded by the stated quantile-scale expression.

At tail index one, the logarithmic case follows from monotonicity of `log(r) / r`. -/
-- @node: hill_radial_remainder_quantile_bound
lemma hill_radial_remainder_quantile_bound {beta c v r : ℝ}
    (hb : 0 < beta) (hc : 0 < c) (hc1 : c ≤ 1) (hv : 1 ≤ v)
    (hbase : Real.exp 1 ≤ c * v ^ (1 / beta))
    (hQ : c * v ^ (1 / beta) ≤ r) :
    hillRadialRemainderShape beta r ≤
      (c ^ (-beta) + c⁻¹) *
        (if beta = 1 then v ^ (-1 : ℝ) * Real.log v
          else v ^ (-min 1 (1 / beta))) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hxpos : 0 < c * v ^ (1 / beta) := by positivity
  have hrpos : 0 < r := hxpos.trans_le hQ
  have hcinv : 0 ≤ c⁻¹ := by positivity
  have hcpow : 0 ≤ c ^ (-beta) := by positivity
  unfold hillRadialRemainderShape
  by_cases hsmall : beta < 1
  · have hbeta : beta ≠ 1 := ne_of_lt hsmall
    rw [if_pos hsmall, if_neg hbeta]
    have hmin : min 1 (1 / beta) = 1 := min_eq_left ((le_div_iff₀ hb).mpr (by linarith))
    rw [hmin]
    have hpow : (c * v ^ (1 / beta)) ^ (-beta) = c ^ (-beta) * v ^ (-1 : ℝ) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hvpos.le _), ← Real.rpow_mul hvpos.le]
      congr 2
      field_simp
    calc
      _ ≤ (c * v ^ (1 / beta)) ^ (-beta) :=
        Real.rpow_le_rpow_of_nonpos hxpos hQ (by linarith)
      _ = _ := hpow
      _ ≤ _ := by nlinarith [mul_nonneg hcinv (Real.rpow_nonneg hvpos.le (-1))]
  · rw [if_neg hsmall]
    by_cases heq : beta = 1
    · subst beta
      simp only [Real.rpow_one, div_one, if_true, Real.rpow_neg_one] at hbase hQ ⊢
      have hl := Real.log_div_self_antitoneOn hbase (hbase.trans hQ) hQ
      have hcLog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
      have hvLog : 0 ≤ Real.log v := Real.log_nonneg hv
      dsimp only at hl
      rw [Real.log_mul hc.ne' hvpos.ne'] at hl
      calc
        _ = Real.log r / r := by ring
        _ ≤ (Real.log c + Real.log v) / (c * v) := hl
        _ ≤ Real.log v / (c * v) := div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = c⁻¹ * (v⁻¹ * Real.log v) := by ring
        _ ≤ _ := by nlinarith [mul_nonneg hcinv (mul_nonneg (inv_nonneg.mpr hvpos.le) hvLog)]
    · simp only [if_neg heq]
      have hbig : 1 < beta := lt_of_le_of_ne (not_lt.mp hsmall) (Ne.symm heq)
      rw [min_eq_right ((div_le_one hb).mpr hbig.le)]
      have hpow : (c * v ^ (1 / beta)) ^ (-1 : ℝ) = c⁻¹ * v ^ (-(1 / beta)) := by
        rw [Real.mul_rpow hc.le (Real.rpow_nonneg hvpos.le _), ← Real.rpow_mul hvpos.le,
          Real.rpow_neg_one, mul_neg_one]
      calc
        _ ≤ (c * v ^ (1 / beta)) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hxpos hQ (by norm_num)
        _ = _ := hpow
        _ ≤ _ := by nlinarith [mul_nonneg hcpow (Real.rpow_nonneg hvpos.le (-(1 / beta)))]

/-- Given [a positive tail index](hyp:hb), [a positive constant](hyp:hc) no larger than one [as required](hyp:hc1), [a quantile level at least one](hyp:hv), [a base lower bound](hyp:hbase), and [a lower bound on the radius](hyp:hQ), [the inverse radius](goal) is bounded by the stated quantile-scale expression. -/
-- @node: hill_inverse_radius_quantile_bound
lemma hill_inverse_radius_quantile_bound {beta c v r : ℝ}
    (hb : 0 < beta) (hc : 0 < c) (hc1 : c ≤ 1) (hv : 1 ≤ v)
    (hbase : Real.exp 1 ≤ c * v ^ (1 / beta))
    (hQ : c * v ^ (1 / beta) ≤ r) :
    r⁻¹ ≤ (c ^ (-beta) + c⁻¹) *
      (if beta = 1 then v ^ (-1 : ℝ) * Real.log v
        else v ^ (-min 1 (1 / beta))) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hxpos : 0 < c * v ^ (1 / beta) := by positivity
  have hinv : r⁻¹ ≤ c⁻¹ * v ^ (-(1 / beta)) := by
    have h := one_div_le_one_div_of_le hxpos hQ
    simpa only [one_div, mul_inv_rev, Real.rpow_neg hvpos.le, mul_comm] using h
  have hcpow : 0 ≤ c ^ (-beta) := by positivity
  by_cases heq : beta = 1
  · subst beta
    simp only [div_one, Real.rpow_one] at hbase hinv
    have heV : Real.exp 1 ≤ v := hbase.trans (mul_le_of_le_one_left hvpos.le hc1)
    have hlog : 1 ≤ Real.log v := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) heV
    simp only [if_true, Real.rpow_neg_one]
    have hnonneg : 0 ≤ c⁻¹ * v⁻¹ := by positivity
    calc
      _ ≤ c⁻¹ * v⁻¹ := by simpa only [Real.rpow_neg_one] using hinv
      _ ≤ c⁻¹ * (v⁻¹ * Real.log v) := by nlinarith
      _ ≤ _ := by nlinarith [mul_nonneg (inv_nonneg.mpr hc.le) (mul_nonneg (inv_nonneg.mpr hvpos.le) (by linarith : 0 ≤ Real.log v))]
  · rw [if_neg heq]
    have hp := Real.rpow_le_rpow_of_exponent_le hv (neg_le_neg (min_le_right 1 (1 / beta)))
    calc
      _ ≤ c⁻¹ * v ^ (-(1 / beta)) := hinv
      _ ≤ c⁻¹ * v ^ (-min 1 (1 / beta)) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hcpow (Real.rpow_nonneg hvpos.le (-min 1 (1 / beta)))]

/-- If [the quantile expression is at least `exp(1)`](hyp:hbase) and [the radius is no smaller than that expression](hyp:hQ), then [the radius is at least two and its logarithm is at least one](goal). -/
-- @node: hill_radius_large_of_quantile_lower
lemma hill_radius_large_of_quantile_lower {beta c v r : ℝ}
    (hbase : Real.exp 1 ≤ c * v ^ (1 / beta))
    (hQ : c * v ^ (1 / beta) ≤ r) : 2 ≤ r ∧ 1 ≤ Real.log r := by
  have he : 2 < Real.exp 1 := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  refine ⟨he.le.trans (hbase.trans hQ), ?_⟩
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hbase.trans hQ)

end Papers.TbsExtremeEffects
