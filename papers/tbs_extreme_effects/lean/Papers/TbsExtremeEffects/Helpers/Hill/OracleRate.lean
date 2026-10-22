module
public import Papers.TbsExtremeEffects.Helpers.Hill.Calibration
/-! Rounding and power balance for the three adaptive Hill oracle rates. -/
@[expose] public section
namespace Papers.TbsExtremeEffects
open Filter

/-- If [a real candidate is at least two](hyp:hx), then [rounding it down to a natural number retains at least half of it](goal). -/
-- @node: hill_floor_ge_half
lemma hill_floor_ge_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

/-- If [the sample size](hyp:hn), [confidence scale](hyp:hc), and [power exponent](hyp:hp) are positive, then [the power-law candidate exactly balances the squared normalized error at the confidence scale](goal). -/
-- @node: hill_power_oracle_balance
lemma hill_power_oracle_balance {n c p : ℝ} (hn : 0 < n) (hc : 0 < c)
    (hp : 0 < p) :
    (n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))) *
      ((c ^ 2 / n) ^ (p / (1 + 2 * p))) ^ 2 = c ^ 2 := by
  have hden : 1 + 2 * p ≠ 0 := by positivity
  rw [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hc,
    Real.rpow_def_of_pos (div_pos (sq_pos_of_pos hc) hn),
    Real.log_div (ne_of_gt (sq_pos_of_pos hc)) hn.ne', Real.log_pow,
    ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  convert Real.exp_log (sq_pos_of_pos hc) using 1
  rw [Real.log_pow]
  congr 1
  push_cast
  field_simp
  ring

/-- If [the scaling constant is positive](hyp:ha), [the error scale is positive](hyp:hr), [the unrounded candidate balances squared error with the confidence scale](hyp:hbalance), [that candidate is at least two](hyp:hsize), and [the chosen index is at least its rounded-down value](hyp:hk), then [the normalized error at the chosen index has the displayed square-root bound](goal). -/
-- @node: hill_error_of_balanced_oracle
lemma hill_error_of_balanced_oracle {c a r x : ℝ} {k : ℕ}
    (ha : 0 < a) (hr : 0 < r)
    (hbalance : x * r ^ 2 = a * c ^ 2)
    (hsize : 2 ≤ x) (hk : ⌊x⌋₊ ≤ k) :
    c / Real.sqrt k ≤ Real.sqrt (2 / a) * r := by
  have hlower : x / 2 ≤ (k : ℝ) :=
    (hill_floor_ge_half hsize).trans (by exact_mod_cast hk)
  have hkpos : 0 < (k : ℝ) := by linarith
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  apply (div_le_iff₀ hspos).mpr
  have hmul := mul_le_mul_of_nonneg_right hlower (sq_nonneg r)
  have hs := Real.sq_sqrt (le_of_lt hkpos)
  have hsconst := Real.sq_sqrt (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 2) ha))
  have htarget : c ^ 2 ≤ (Real.sqrt (2 / a) * r * Real.sqrt k) ^ 2 := by
    have htwok : a * c ^ 2 ≤ 2 * (k : ℝ) * r ^ 2 := by nlinarith
    have h : c ^ 2 ≤ 2 * (k : ℝ) * r ^ 2 / a :=
      (le_div_iff₀ ha).mpr (by nlinarith)
    calc
      _ ≤ _ := h
      _ = _ := by
        rw [mul_pow, mul_pow, hs, hsconst]
        ring
  have hnonneg : 0 ≤ Real.sqrt (2 / a) * r * Real.sqrt k := by positivity
  nlinarith

/-- If [the sample size](hyp:hn), [confidence scale](hyp:hc), [power exponent](hyp:hp), and [candidate constant](hyp:ha) are positive, [the unrounded power candidate is at least two](hyp:hsize), and [the chosen index is at least its rounded-down value](hyp:hk), then [its normalized error is bounded by the stated power-oracle rate](goal). -/
-- @node: hill_power_oracle_error
lemma hill_power_oracle_error {n c p a : ℝ} {k : ℕ}
    (hn : 0 < n) (hc : 0 < c) (hp : 0 < p) (ha : 0 < a)
    (hsize : 2 ≤ a * n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p)))
    (hk : ⌊a * n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))⌋₊ ≤ k) :
    c / Real.sqrt k ≤ Real.sqrt (2 / a) * (c ^ 2 / n) ^ (p / (1 + 2 * p)) := by
  apply hill_error_of_balanced_oracle ha (Real.rpow_pos_of_pos (by positivity) _) _ hsize hk
  calc
    _ = a * ((n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))) *
        ((c ^ 2 / n) ^ (p / (1 + 2 * p))) ^ 2) := by ring
    _ = _ := by rw [hill_power_oracle_balance hn hc hp]

/-- If [the sample size](hyp:hn), [confidence scale](hyp:hc), [logarithmic factor](hyp:hl), and [candidate constant](hyp:ha) are positive, [the unrounded logarithmic candidate is at least two](hyp:hsize), and [the chosen index is at least its rounded-down value](hyp:hk), then [its normalized error is bounded by the stated beta-one logarithmic rate](goal). -/
-- @node: hill_log_oracle_error
lemma hill_log_oracle_error {n c l a : ℝ} {k : ℕ}
    (hn : 0 < n) (hc : 0 < c) (hl : 0 < l) (ha : 0 < a)
    (hsize : 2 ≤ a * n ^ (2 / 3 : ℝ) * (c / l) ^ (2 / 3 : ℝ))
    (hk : ⌊a * n ^ (2 / 3 : ℝ) * (c / l) ^ (2 / 3 : ℝ)⌋₊ ≤ k) :
    c / Real.sqrt k ≤ Real.sqrt (2 / a) * (l * c ^ 2 / n) ^ (1 / 3 : ℝ) := by
  have hcandidate : a * (n / l) ^ (2 / 3 : ℝ) * c ^ (2 / 3 : ℝ) =
      a * n ^ (2 / 3 : ℝ) * (c / l) ^ (2 / 3 : ℝ) := by
    rw [Real.div_rpow hn.le hl.le, Real.div_rpow hc.le hl.le]
    ring
  have h := hill_power_oracle_error (p := 1) (div_pos hn hl) hc (by norm_num) ha
    (by norm_num only at *; simpa only [hcandidate] using hsize)
    (by norm_num only at *; simpa only [hcandidate] using hk)
  norm_num only at h
  convert h using 1
  congr 2
  field_simp

/-- If [the sample size](hyp:hn) and [confidence scale](hyp:hc) are positive, [the exponent is nonnegative](hyp:hs), and [the squared confidence scale is bounded by eighteen times the log budget](hyp:hbudget), then [raising the normalized bound to that exponent gives the displayed penalty-rate bound](goal). -/
-- @node: hill_oracle_budget_transfer
lemma hill_oracle_budget_transfer {n c q s : ℝ} (hn : 0 < n) (hc : 0 < c)
    (hs : 0 ≤ s) (hbudget : c ^ 2 ≤ 18 * q) :
    (c ^ 2 / n) ^ s ≤ (18 : ℝ) ^ s * (q / n) ^ s := by
  have hq : 0 < q := by nlinarith [sq_pos_of_pos hc]
  calc
    _ ≤ (18 * q / n) ^ s :=
      Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hbudget hn.le) hs
    _ = _ := by
      rw [show 18 * q / n = 18 * (q / n) by ring,
        Real.mul_rpow (by norm_num) (div_nonneg hq.le hn.le)]

/-- Given [a tail parameter](hyp:beta), [a sample size](hyp:n), and [a confidence scale](hyp:c), [the Hill oracle scale](goal) is the beta-one logarithmic candidate when the tail parameter equals one, and otherwise the corresponding power-law candidate. -/
-- @node: hillOracleScale
noncomputable def hillOracleScale (beta : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  if beta = 1 then (n : ℝ) ^ (2 / 3 : ℝ) * (c / Real.log n) ^ (2 / 3 : ℝ)
  else let p := min 1 (1 / beta)
       (n : ℝ) ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))

/-- If [the tail parameter exceeds one](hyp:hbeta), then [the generic power-rate exponent equals the displayed Hill exponent](goal). -/
-- @node: hill_power_rate_exponent
lemma hill_power_rate_exponent {beta : ℝ} (hbeta : 1 < beta) :
    (1 / beta) / (1 + 2 * (1 / beta)) = 1 / (2 + beta) := by
  have hb : beta ≠ 0 := by linarith
  have hb2 : 2 + beta ≠ 0 := by linarith
  field_simp
  ring

/-- If [the tail parameter is positive](hyp:hbeta), [the confidence level lies in its allowed domain](hyp:hd), and [the candidate constant is positive](hyp:ha), then [eventually every index at least the rounded oracle candidate, whenever that candidate is at least two, has the displayed Hill penalty-rate bound](goal). -/
-- @node: hill_oracle_penalty_rate
lemma hill_oracle_penalty_rate {beta delta a : ℝ}
    (hbeta : 0 < beta) (hd : ConfidenceDomain delta) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      2 ≤ a * hillOracleScale beta n (hillDeviation n delta) →
      ⌊a * hillOracleScale beta n (hillDeviation n delta)⌋₊ ≤ k →
      hillDeviation n delta / Real.sqrt k ≤
        (Real.sqrt (2 / a) * (18 : ℝ) ^
          (min 1 (1 / beta) / (1 + 2 * min 1 (1 / beta)))) *
          hillRateShape beta n (8 / delta) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ), hillDeviation_sq_eventually_le_loglog hd]
    with n hnlog hn hbudget
  intro k hsize hk
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < hillDeviation n delta := by
    unfold hillDeviation
    have hq := hill_logBudget_pos n hd
    have hs := Real.sqrt_pos.mpr hq
    have hcorr : 0 ≤ hillLogBudget n delta / Real.sqrt (hillLower n) := by positivity
    linarith
  have hl : 0 < Real.log n := by linarith
  by_cases hb : beta = 1
  · subst beta
    simp only [hillOracleScale, ↓reduceIte, ← mul_assoc] at hsize hk
    have herr := hill_log_oracle_error hnpos hc hl ha hsize hk
    have htransfer := hill_oracle_budget_transfer (div_pos hnpos hl) hc
      (by norm_num : (0 : ℝ) ≤ 1 / 3) hbudget
    have hid : ∀ x : ℝ, x / ((n : ℝ) / Real.log n) = Real.log n * x / n := by
      intro x
      field_simp
    simp_rw [hid] at htransfer
    have hresult := herr.trans (mul_le_mul_of_nonneg_left htransfer (Real.sqrt_nonneg _))
    norm_num [hillRateShape, mul_assoc] at hresult ⊢
    exact hresult
  · let p : ℝ := min 1 (1 / beta)
    have hp : 0 < p := lt_min (by norm_num) (div_pos (by norm_num) hbeta)
    simp only [hillOracleScale, if_neg hb, ← mul_assoc] at hsize hk
    have herr := hill_power_oracle_error hnpos hc hp ha hsize hk
    have htransfer := hill_oracle_budget_transfer hnpos hc
      (div_nonneg hp.le (by positivity : 0 ≤ 1 + 2 * p)) hbudget
    have hresult := herr.trans (mul_le_mul_of_nonneg_left htransfer (Real.sqrt_nonneg _))
    by_cases hblt : beta < 1
    · have hp1 : p = 1 := min_eq_left ((le_div_iff₀ hbeta).mpr (by linarith))
      dsimp only [p] at hresult
      change min 1 (1 / beta) = 1 at hp1
      rw [hp1] at hresult ⊢
      norm_num [hillRateShape, hblt, mul_assoc] at hresult ⊢
      exact hresult
    · have hbgt : 1 < beta := lt_of_le_of_ne (le_of_not_gt hblt) (Ne.symm hb)
      have hpval : p = 1 / beta := min_eq_right ((div_le_iff₀ hbeta).mpr (by linarith))
      have hexp := hill_power_rate_exponent hbgt
      dsimp only [p] at hresult
      change min 1 (1 / beta) = 1 / beta at hpval
      simpa only [hillRateShape, if_neg hblt, if_neg hb, hpval, hexp,
        mul_assoc] using hresult

end Papers.TbsExtremeEffects
