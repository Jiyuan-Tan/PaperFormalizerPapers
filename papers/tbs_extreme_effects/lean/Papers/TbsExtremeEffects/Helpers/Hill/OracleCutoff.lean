module
public import Papers.TbsExtremeEffects.Helpers.Hill.OracleBias
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Eventual admissibility of the rounded adaptive Hill oracle candidates. -/

public section
namespace Papers.TbsExtremeEffects
open Filter
open scoped Topology

/-- [Every fixed real lower bound is eventually no larger than the lower Hill index cutoff](goal). -/
-- @node: hillLower_eventually_ge
lemma hillLower_eventually_ge (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, a ≤ (hillLower n : ℝ) := by
  have hlog : ∀ᶠ n : ℕ in atTop, a / 100 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (a / 100))
  filter_upwards [eventually_ge_atTop (⌈a⌉₊ + 1), hlog] with n hn hlog
  rw [hillLower, Nat.cast_min]
  apply le_min
  · exact (Nat.le_ceil a).trans (by exact_mod_cast (by omega : ⌈a⌉₊ ≤ n - 1))
  · exact (show a ≤ 100 * Real.log n by linarith).trans (Nat.le_ceil _)

/-- If [the confidence level lies in its allowed domain](hyp:hd), then [the Hill confidence penalty is at least one for every sample size](goal). -/
-- @node: hillDeviation_ge_one
lemma hillDeviation_ge_one (n : ℕ) {delta : ℝ} (hd : ConfidenceDomain delta) :
    1 ≤ hillDeviation n delta := by
  have hgrid : (1 : ℝ) ≤ hillGridSize n := by
    exact_mod_cast (show 1 ≤ hillGridSize n by unfold hillGridSize; omega)
  have harg : (2 : ℝ) ≤ 4 * (hillGridSize n : ℝ) / delta := by
    apply (le_div_iff₀ hd.1).mpr
    nlinarith [hd.2]
  have hlog : Real.log 2 ≤ hillLogBudget n delta :=
    Real.log_le_log (by norm_num) harg
  have hq : 1 / 4 ≤ hillLogBudget n delta := by
    have := Real.log_two_gt_d9
    linarith
  have hs := Real.sqrt_le_sqrt hq
  norm_num at hs
  unfold hillDeviation
  have hcorr : 0 ≤ hillLogBudget n delta / Real.sqrt (hillLower n) := by positivity
  linarith

/-- If [the leading constant is positive](hyp:ha) and [the power exponent is positive](hyp:hr), then [eventually the lower Hill cutoff is no greater than the rounded-down power divided by the stated logarithmic power](goal). -/
-- @node: hill_lower_le_floor_power_log
lemma hill_lower_le_floor_power_log {a r s : ℝ} (ha : 0 < a) (hr : 0 < r)
    :
    ∀ᶠ n : ℕ in atTop,
      hillLower n ≤ ⌊a * ((n : ℝ) ^ r / (Real.log n) ^ s)⌋₊ := by
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (s + 1) hr).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (show 0 < a / 101 by positivity)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hsmall, hlog] with n hn hlog
  simp only [Function.comp_apply] at hn hlog
  have hln : 0 < Real.log n := by linarith
  have hnpos : 0 < (n : ℝ) := by
    by_contra h
    have : n = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n))
    norm_num [this] at hlog
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hln) _),
    abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hn
  have hpower := Real.rpow_add hln s 1
  rw [Real.rpow_one] at hpower
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 100 * Real.log n by positivity)
  have hL : (hillLower n : ℝ) ≤ 101 * Real.log n := by
    have hmin : hillLower n ≤ ⌈100 * Real.log n⌉₊ := min_le_right _ _
    have hminreal : (hillLower n : ℝ) ≤ (⌈100 * Real.log n⌉₊ : ℝ) := by exact_mod_cast hmin
    linarith
  apply (Nat.le_floor_iff (by positivity)).mpr
  apply hL.trans
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hln s)).mpr
  rw [hpower] at hn
  nlinarith

/-- If [the tail parameter is positive](hyp:hb), [the confidence level lies in its allowed domain](hyp:hd), and [the candidate constant is positive](hyp:ha), then [eventually the rounded Hill oracle candidate is at least the lower cutoff](goal). -/
-- @node: hill_oracle_candidate_eventually_ge_lower
lemma hill_oracle_candidate_eventually_ge_lower {beta delta a : ℝ}
    (hb : 0 < beta) (hd : ConfidenceDomain delta) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      hillLower n ≤ ⌊a * hillOracleScale beta n (hillDeviation n delta)⌋₊ := by
  by_cases hbeta : beta = 1
  · have h := hill_lower_le_floor_power_log (r := 2 / 3) (s := 2 / 3) ha
      (by norm_num)
    have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
    filter_upwards [h, hlog] with n hn hlog
    simp only [Function.comp_apply] at hlog
    apply hn.trans
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_left _ ha.le
    simp only [hillOracleScale, hbeta, if_true]
    rw [Real.div_rpow (zero_le_one.trans (hillDeviation_ge_one n hd))
      (by linarith : 0 ≤ Real.log n)]
    have hc : 1 ≤ hillDeviation n delta ^ (2 / 3 : ℝ) := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
        (hillDeviation_ge_one n hd) (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have hmul := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (Nat.cast_nonneg n) (2 / 3 : ℝ))
    simpa only [mul_one, mul_div_assoc] using div_le_div_of_nonneg_right hmul
      (Real.rpow_nonneg (by linarith : 0 ≤ Real.log n) (2 / 3 : ℝ))
  · let p := min 1 (1 / beta)
    have hp : 0 < p := lt_min (by norm_num) (one_div_pos.mpr hb)
    have hr : 0 < 2 * p / (1 + 2 * p) := by positivity
    have h := hill_lower_le_floor_power_log (s := 0) ha hr
    filter_upwards [h] with n hn
    simp only [Real.rpow_zero, div_one] at hn
    apply hn.trans
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_left _ ha.le
    simp only [hillOracleScale, hbeta, if_false]
    change (n : ℝ) ^ (2 * p / (1 + 2 * p)) ≤
      (n : ℝ) ^ (2 * p / (1 + 2 * p)) * hillDeviation n delta ^ (2 / (1 + 2 * p))
    have hc : 1 ≤ hillDeviation n delta ^ (2 / (1 + 2 * p)) := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
        (hillDeviation_ge_one n hd) (by positivity : 0 ≤ 2 / (1 + 2 * p))
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (2 * p / (1 + 2 * p))]

/-- If [the confidence level lies in its allowed domain](hyp:hd), then [there is a positive constant such that eventually the Hill confidence penalty is at most that constant times the log of sample size](goal). -/
-- @node: hillDeviation_eventually_le_log
lemma hillDeviation_eventually_le_log {delta : ℝ} (hd : ConfidenceDomain delta) :
    ∃ D > 0, ∀ᶠ n : ℕ in atTop, hillDeviation n delta ≤ D * Real.log n := by
  let D := 18 * (1 + |Real.log (8 / delta)|)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hillDeviation_sq_eventually_le_loglog hd, hlog] with n hn hlog
  simp only [Function.comp_apply] at hlog
  have hlpos : 0 < Real.log n := by linarith
  rw [Real.log_mul (div_ne_zero (by norm_num) hd.1.ne') hlpos.ne'] at hn
  have hll := Real.log_le_sub_one_of_pos hlpos
  have hc := hillDeviation_ge_one n hd
  have hD : Real.log (8 / delta) ≤ |Real.log (8 / delta)| := le_abs_self _
  have hprod : |Real.log (8 / delta)| ≤ |Real.log (8 / delta)| * Real.log n := by
    nlinarith [abs_nonneg (Real.log (8 / delta))]
  dsimp [D]
  nlinarith

/-- For a penalty sequence, if [the leading constant](hyp:ha), [the target fraction](hyp:hb), and [the logarithmic bound constant](hyp:hD) are positive, [the power exponent is below one](hyp:hr), [the logarithmic exponent is nonnegative](hyp:hs), and [eventually the penalty is nonnegative and bounded by that constant times log sample size](hyp:hc), then [eventually the resulting power-log expression is smaller than the target fraction of sample size](goal). -/
-- @node: hill_power_log_eventually_lt_linear
lemma hill_power_log_eventually_lt_linear (c : ℕ → ℝ) {a b D r s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) (hr : r < 1) (hs : 0 ≤ s)
    (hc : ∀ᶠ n : ℕ in atTop, 0 ≤ c n ∧ c n ≤ D * Real.log n) :
    ∀ᶠ n : ℕ in atTop, a * (n : ℝ) ^ r * (c n) ^ s < b * n := by
  have hsmall := ((isLittleO_log_rpow_rpow_atTop s (show 0 < 1 - r by linarith)).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (show 0 < b / (2 * a * D ^ s) by positivity)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hsmall, hlog, hc, eventually_ge_atTop (1 : ℕ)] with n hn hlog hc hnNat
  simp only [Function.comp_apply] at hn hlog
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hlpos : 0 < Real.log n := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlpos.le _),
    abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hn
  have hcp : c n ^ s ≤ D ^ s * Real.log n ^ s := by
    simpa only [Real.mul_rpow hD.le hlpos.le] using Real.rpow_le_rpow hc.1 hc.2 hs
  have hmul := mul_le_mul_of_nonneg_left hn (show 0 ≤ a * (n : ℝ) ^ r * D ^ s by positivity)
  have hid : (n : ℝ) ^ r * (n : ℝ) ^ (1 - r) = n := by
    rw [← Real.rpow_add hnpos, show r + (1 - r) = 1 by ring, Real.rpow_one]
  have hcoef : a * D ^ s * (b / (2 * a * D ^ s)) = b / 2 := by
    field_simp
  have hupper : a * (n : ℝ) ^ r * (c n) ^ s ≤ b / 2 * n := by
    calc
      _ ≤ a * (n : ℝ) ^ r * (D ^ s * Real.log n ^ s) :=
        mul_le_mul_of_nonneg_left hcp (by positivity)
      _ ≤ (a * D ^ s * (b / (2 * a * D ^ s))) *
          ((n : ℝ) ^ r * (n : ℝ) ^ (1 - r)) := by nlinarith [hmul]
      _ = _ := by rw [hcoef, hid]
  exact hupper.trans_lt (by nlinarith)

/-- If [the tail parameter](hyp:hbeta), [candidate constant](hyp:ha), and [tail fraction](hyp:hb) are positive and [the confidence level lies in its allowed domain](hyp:hd), then [eventually the rounded Hill oracle candidate is smaller than that fraction of sample size](goal). -/
-- @node: hill_oracle_candidate_eventually_lt_fraction
lemma hill_oracle_candidate_eventually_lt_fraction {beta delta a b : ℝ}
    (hbeta : 0 < beta) (hd : ConfidenceDomain delta) (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      (⌊a * hillOracleScale beta n (hillDeviation n delta)⌋₊ : ℝ) < b * n := by
  obtain ⟨D, hD, hbound⟩ := hillDeviation_eventually_le_log hd
  have hc : ∀ᶠ n : ℕ in atTop,
      0 ≤ hillDeviation n delta ∧ hillDeviation n delta ≤ D * Real.log n :=
    hbound.mono fun n hn => ⟨zero_le_one.trans (hillDeviation_ge_one n hd), hn⟩
  by_cases hbetaone : beta = 1
  · have h := hill_power_log_eventually_lt_linear (fun n => hillDeviation n delta)
      (r := 2 / 3) (s := 2 / 3) ha hb hD (by norm_num) (by norm_num) hc
    have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
    filter_upwards [h, hlog] with n hn hlog
    simp only [Function.comp_apply] at hlog
    have hc0 := zero_le_one.trans (hillDeviation_ge_one n hd)
    have hscale : hillOracleScale beta n (hillDeviation n delta) ≤
        (n : ℝ) ^ (2 / 3 : ℝ) * hillDeviation n delta ^ (2 / 3 : ℝ) := by
      simp only [hillOracleScale, hbetaone, if_true]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      exact div_le_self hc0 hlog
    have hscale0 : 0 ≤ a * hillOracleScale beta n (hillDeviation n delta) := by
      simp only [hillOracleScale, hbetaone, if_true]
      positivity
    exact (Nat.floor_le hscale0).trans_lt
      ((mul_le_mul_of_nonneg_left hscale ha.le).trans_lt (by simpa only [mul_assoc] using hn))
  · let p := min 1 (1 / beta)
    have hp : 0 < p := lt_min (by norm_num) (one_div_pos.mpr hbeta)
    have hr : 2 * p / (1 + 2 * p) < 1 := by
      apply (div_lt_one (by positivity)).mpr
      linarith
    have h := hill_power_log_eventually_lt_linear (fun n => hillDeviation n delta)
      (r := 2 * p / (1 + 2 * p)) (s := 2 / (1 + 2 * p)) ha hb hD hr (by positivity) hc
    filter_upwards [h] with n hn
    have hc0 := zero_le_one.trans (hillDeviation_ge_one n hd)
    have hscale0 : 0 ≤ a * hillOracleScale beta n (hillDeviation n delta) := by
      simp only [hillOracleScale, hbetaone, if_false]
      positivity
    apply (Nat.floor_le hscale0).trans_lt
    simpa only [hillOracleScale, hbetaone, if_false, mul_assoc] using hn

/-- If [the tail parameter](hyp:hb), [candidate constant](hyp:ha), and [tail threshold](hyp:hv) are positive and [the confidence level lies in its allowed domain](hyp:hd), then [eventually the rounded oracle candidate is positive, lies between the lower cutoff and one below sample size, and places its quantile threshold above the tail threshold](goal). -/
-- @node: hill_oracle_candidate_eventually_admissible
lemma hill_oracle_candidate_eventually_admissible {beta delta a v₀ : ℝ}
    (hb : 0 < beta) (hd : ConfidenceDomain delta) (ha : 0 < a) (hv : 0 < v₀) :
    ∀ᶠ n : ℕ in atTop,
      let k := ⌊a * hillOracleScale beta n (hillDeviation n delta)⌋₊
      1 ≤ k ∧ k ∈ Finset.Icc (hillLower n) (n - 1) ∧ v₀ ≤ (n : ℝ) / (2 * k) := by
  have hf := hill_oracle_candidate_eventually_lt_fraction hb hd ha
    (b := min 1 (1 / (2 * v₀))) (lt_min zero_lt_one (by positivity))
  filter_upwards [hillLower_eventually_ge 1,
    hill_oracle_candidate_eventually_ge_lower hb hd ha, hf] with n hL hlow hupper
  dsimp only
  let k := ⌊a * hillOracleScale beta n (hillDeviation n delta)⌋₊
  have hkpos : 1 ≤ k := by
    have hLnat : 1 ≤ hillLower n := by exact_mod_cast hL
    exact hLnat.trans hlow
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hnreal : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkn : (k : ℝ) < n := hupper.trans_le
    (by simpa using mul_le_mul_of_nonneg_right (min_le_left 1 (1 / (2 * v₀))) hnreal)
  have hknNat : k < n := by exact_mod_cast hkn
  have htail : (k : ℝ) < (n : ℝ) / (2 * v₀) := hupper.trans_le (by
    simpa only [one_div_mul_eq_div] using
      mul_le_mul_of_nonneg_right (min_le_right 1 (1 / (2 * v₀))) hnreal)
  refine ⟨hkpos, Finset.mem_Icc.mpr ⟨hlow, by omega⟩, ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 2 * (k : ℝ))).mpr
  have hmul := (lt_div_iff₀ (by positivity : 0 < 2 * v₀)).mp htail
  nlinarith

end Papers.TbsExtremeEffects
