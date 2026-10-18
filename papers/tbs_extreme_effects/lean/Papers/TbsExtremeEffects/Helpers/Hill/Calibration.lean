module
public import Papers.TbsExtremeEffects.Helpers.Hill.Maximal

/-! Deterministic asymptotics of the adaptive Hill confidence calibration. -/

public section
namespace Papers.TbsExtremeEffects
open Filter
open scoped Topology

/-- [A positive sample size](hyp:hn) has logarithm no larger than [the adaptive cutoff](goal), even when its cap is active.
@node: hill_log_le_lower -/
lemma hill_log_le_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.log n ≤ (hillLower n : ℝ) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnreal
  rw [hillLower, Nat.cast_min]
  apply le_min
  · have h := Real.log_le_sub_one_of_pos (by linarith : 0 < (n : ℝ))
    simpa only [Nat.cast_sub hn, Nat.cast_one] using h
  · exact (by linarith : Real.log n ≤ 100 * Real.log n).trans (Nat.le_ceil _)

/-- For [a confidence level in its admissible domain](hyp:hd) and [a sample size whose logarithm is at least one](hyp:hn), [the logarithmic grid budget](goal) is bounded by a constant plus the logarithm of the sample-size logarithm.
@node: hill_logBudget_le_loglog -/
lemma hill_logBudget_le_loglog {n : ℕ} {delta : ℝ}
    (hd : ConfidenceDomain delta) (hn : 1 ≤ Real.log n) :
    hillLogBudget n delta ≤
      Real.log ((4 / delta) * (2 + 1 / Real.log 2)) + Real.log (Real.log n) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ Real.log n) htwo.le)
  have hgrid : (hillGridSize n : ℝ) ≤ (2 + 1 / Real.log 2) * Real.log n := by
    unfold hillGridSize
    push_cast
    have hdiv : Real.log n / Real.log 2 = (1 / Real.log 2) * Real.log n := by ring
    rw [hdiv] at hceil ⊢
    nlinarith
  have hdpos := hd.1
  have hC : 0 < (4 / delta) * (2 + 1 / Real.log 2) := by positivity
  calc
    hillLogBudget n delta ≤
        Real.log (((4 / delta) * (2 + 1 / Real.log 2)) * Real.log n) := by
      apply Real.log_le_log (by
        have hgridpos : (0 : ℝ) < hillGridSize n := by
          exact_mod_cast (show 0 < hillGridSize n by unfold hillGridSize; omega)
        exact div_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hgridpos) hd.1)
      have := mul_le_mul_of_nonneg_left hgrid (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 4) hd.1))
      convert this using 1 <;> first | rfl | ring
    _ = _ := Real.log_mul hC.ne' (by linarith : Real.log n ≠ 0)

/-- For [an admissible confidence level](hyp:hd), [the logarithmic budget divided by the cutoff](goal) converges to zero as the sample size grows.
@node: hill_logBudget_div_lower_tendsto_zero -/
lemma hill_logBudget_div_lower_tendsto_zero {delta : ℝ} (hd : ConfidenceDomain delta) :
    Tendsto (fun n : ℕ => hillLogBudget n delta / (hillLower n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlog
  let C := Real.log ((4 / delta) * (2 + 1 / Real.log 2))
  have hconst : Tendsto (fun n : ℕ => C / Real.log n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul C
  have hupper : Tendsto (fun n : ℕ => (C + Real.log (Real.log n)) / Real.log n)
      atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using hconst.add hloglog
  apply squeeze_zero' (Eventually.of_forall fun n =>
    div_nonneg (hill_logBudget_pos n hd).le (Nat.cast_nonneg _)) _ hupper
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hn hnNat
  have hL := hill_log_le_lower hnNat
  have hq := hill_logBudget_le_loglog hd hn
  have hnum : 0 ≤ C + Real.log (Real.log n) := (hill_logBudget_pos n hd).le.trans hq
  exact div_le_div₀ hnum hq (by linarith : 0 < Real.log n) hL

/-- For [an admissible confidence level](hyp:hd), [the deviation penalty divided by the cutoff's square root](goal) converges to zero with sample size.
@node: hillDeviation_div_sqrt_lower_tendsto_zero -/
lemma hillDeviation_div_sqrt_lower_tendsto_zero {delta : ℝ} (hd : ConfidenceDomain delta) :
    Tendsto (fun n : ℕ => hillDeviation n delta / Real.sqrt (hillLower n))
      atTop (𝓝 0) := by
  have hratio := hill_logBudget_div_lower_tendsto_zero hd
  have hsqrt := hratio.sqrt
  have hlim := (hsqrt.const_mul 2).add hratio
  simp only [Real.sqrt_zero, mul_zero, zero_add] at hlim
  apply hlim.congr
  intro n
  rw [hillDeviation, add_div, mul_div_assoc,
    Real.sqrt_div (hill_logBudget_pos n hd).le,
    div_div, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg (hillLower n))]

/-- For [an admissible confidence level](hyp:hd), [the deviation penalty is eventually at most one sixth of the cutoff's square root](goal).
@node: hillDeviation_eventually_small -/
lemma hillDeviation_eventually_small {delta : ℝ} (hd : ConfidenceDomain delta) :
    ∀ᶠ n : ℕ in atTop,
      hillDeviation n delta / Real.sqrt (hillLower n) ≤ 1 / 6 := by
  exact ((tendsto_order.mp (hillDeviation_div_sqrt_lower_tendsto_zero hd)).2
    (1 / 6) (by norm_num)).mono fun _ h => h.le

/-- Given [an admissible confidence level](hyp:hd) and [a budget no larger than the cutoff](hyp:hqL), [the squared deviation penalty is at most nine times the budget](goal).
@node: hillDeviation_sq_le_nine_budget -/
lemma hillDeviation_sq_le_nine_budget {n : ℕ} {delta : ℝ}
    (hd : ConfidenceDomain delta) (hqL : hillLogBudget n delta ≤ (hillLower n : ℝ)) :
    hillDeviation n delta ^ 2 ≤ 9 * hillLogBudget n delta := by
  have hq := hill_logBudget_pos n hd
  have hL : 0 < Real.sqrt (hillLower n : ℝ) := Real.sqrt_pos.mpr (hq.trans_le hqL)
  have hsqrt := Real.sqrt_le_sqrt hqL
  have hmul := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (hillLogBudget n delta))
  rw [Real.mul_self_sqrt hq.le] at hmul
  have hcorrection : hillLogBudget n delta / Real.sqrt (hillLower n) ≤
      Real.sqrt (hillLogBudget n delta) := (div_le_iff₀ hL).mpr hmul
  have hdev : hillDeviation n delta ≤ 3 * Real.sqrt (hillLogBudget n delta) := by
    unfold hillDeviation
    linarith
  have hnonneg : 0 ≤ hillDeviation n delta := by unfold hillDeviation; positivity
  nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg (hillLogBudget n delta)]

/-- For [an admissible confidence level](hyp:hd), [the squared deviation penalty is eventually bounded by the explicit log-log expression](goal).
@node: hillDeviation_sq_eventually_le_loglog -/
lemma hillDeviation_sq_eventually_le_loglog {delta : ℝ} (hd : ConfidenceDomain delta) :
    ∀ᶠ n : ℕ in atTop,
      hillDeviation n delta ^ 2 ≤ 18 * Real.log ((8 / delta) * Real.log n) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htarget : Tendsto (fun n : ℕ => Real.log ((8 / delta) * Real.log n))
      atTop atTop :=
    Real.tendsto_log_atTop.comp (hlog.const_mul_atTop (by
      exact div_pos (by norm_num) hd.1))
  have hratio := (tendsto_order.mp (hill_logBudget_div_lower_tendsto_zero hd)).2
    (1 : ℝ) zero_lt_one
  let D := Real.log ((4 / delta) * (2 + 1 / Real.log 2)) - Real.log (8 / delta)
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    htarget.eventually (eventually_ge_atTop D), hratio] with n hn hD hratio
  have hL : 0 < (hillLower n : ℝ) := by
    by_contra hnot
    have hz : (hillLower n : ℝ) = 0 := le_antisymm (le_of_not_gt hnot) (Nat.cast_nonneg _)
    have hnNat : 1 ≤ n := by
      by_contra hn0
      have : n = 0 := by omega
      norm_num [this] at hn
    have := hill_log_le_lower hnNat
    linarith
  have hqL : hillLogBudget n delta ≤ (hillLower n : ℝ) := by
    have := (div_lt_iff₀ hL).mp hratio
    linarith
  have htargeteq : Real.log ((8 / delta) * Real.log n) =
      Real.log (8 / delta) + Real.log (Real.log n) :=
    Real.log_mul (ne_of_gt (div_pos (by norm_num) hd.1)) (by linarith)
  have hq := hill_logBudget_le_loglog hd hn
  have hqtarget : hillLogBudget n delta ≤ 2 * Real.log ((8 / delta) * Real.log n) := by
    dsimp [D] at hD
    rw [htargeteq] at hD ⊢
    linarith
  exact (hillDeviation_sq_le_nine_budget hd hqL).trans (by linarith)

end Papers.TbsExtremeEffects
