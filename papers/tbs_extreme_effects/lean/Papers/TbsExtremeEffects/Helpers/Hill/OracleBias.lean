module
public import Papers.TbsExtremeEffects.Helpers.Hill.OracleRate

/-! Bias admissibility of the rounded Hill oracle candidates. -/

public section
namespace Papers.TbsExtremeEffects

/-- If [the sample size is positive](hyp:hn), [the confidence scale is positive](hyp:hc), [the power exponent is positive](hyp:hp), and [the candidate constant is positive](hyp:ha), then [the unrounded power candidate makes its normalized bias term equal to the candidate constant's bias factor times the confidence scale](goal). -/
-- @node: hill_power_candidate_bias_balance
lemma hill_power_candidate_bias_balance {n c p a : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hp : 0 < p) (ha : 0 < a) :
    (a * n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))) ^ (p + 1 / 2) /
      n ^ p = a ^ (p + 1 / 2) * c := by
  have hden : 1 + 2 * p ≠ 0 := by positivity
  have he1 : 2 * p / (1 + 2 * p) * (p + 1 / 2) = p := by field_simp; ring
  have he2 : 2 / (1 + 2 * p) * (p + 1 / 2) = 1 := by field_simp; ring
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow ha.le (by positivity), ← Real.rpow_mul hn.le,
    ← Real.rpow_mul hc.le, he1, he2, Real.rpow_one]
  field_simp

/-- If [the sample size](hyp:hn), [confidence scale](hyp:hc), [power exponent](hyp:hp), and [candidate constant](hyp:ha) are positive, [the envelope coefficient is nonnegative](hyp:hD), [the candidate constant meets the bias budget](hyp:hsmall), and [the integer index is no larger than the rounded-down power candidate](hyp:hk), then [that index meets the normalized power-envelope bias bound](goal). -/
-- @node: hill_power_candidate_bias_le
lemma hill_power_candidate_bias_le {n c p a D gamma : ℝ} {k : ℕ}
    (hn : 0 < n) (hc : 0 < c) (hp : 0 < p) (ha : 0 < a) (hD : 0 ≤ D)
    (hsmall : D * a ^ (p + 1 / 2) ≤ gamma)
    (hk : k ≤ ⌊a * n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))⌋₊) :
    D * (k : ℝ) ^ (p + 1 / 2) / n ^ p ≤ gamma * c := by
  have hkcast : (k : ℝ) ≤ (⌊a * n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))⌋₊ : ℝ) := by
    exact_mod_cast hk
  have hfloor : (k : ℝ) ≤
      a * n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p)) :=
    hkcast.trans (Nat.floor_le (by positivity))
  calc
    _ ≤ D * (a * n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))) ^
        (p + 1 / 2) / n ^ p := by
      gcongr
    _ = (D * a ^ (p + 1 / 2)) * c := by
      rw [mul_div_assoc, hill_power_candidate_bias_balance hn hc hp ha]
      ring
    _ ≤ gamma * c := mul_le_mul_of_nonneg_right hsmall hc.le

/-- If [the sample size](hyp:hn), [confidence scale](hyp:hc), [logarithmic factor](hyp:hl), and [candidate constant](hyp:ha) are positive, then [the beta-one candidate exactly balances its normalized bias term, including the logarithmic factor](goal). -/
-- @node: hill_log_candidate_bias_balance
lemma hill_log_candidate_bias_balance {n c l a : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hl : 0 < l) (ha : 0 < a) :
    (a * n ^ (2 / 3 : ℝ) * (c / l) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) / n * l =
      a ^ (3 / 2 : ℝ) * c := by
  have h := hill_power_candidate_bias_balance hn (div_pos hc hl) (by norm_num : (0 : ℝ) < 1) ha
  norm_num at h
  rw [h]
  field_simp

/-- If [the sample size](hyp:hn), [confidence scale](hyp:hc), [logarithmic factor](hyp:hl), and [candidate constant](hyp:ha) are positive, [the envelope coefficient is nonnegative](hyp:hD), [the candidate constant meets the beta-one bias budget](hyp:hsmall), and [the integer index is no larger than the rounded-down logarithmic candidate](hyp:hk), then [that index meets the normalized logarithmic-envelope bias bound](goal). -/
-- @node: hill_log_candidate_bias_le
lemma hill_log_candidate_bias_le {n c l a D gamma : ℝ} {k : ℕ}
    (hn : 0 < n) (hc : 0 < c) (hl : 0 < l) (ha : 0 < a) (hD : 0 ≤ D)
    (hsmall : D * a ^ (3 / 2 : ℝ) ≤ gamma)
    (hk : k ≤ ⌊a * n ^ (2 / 3 : ℝ) * (c / l) ^ (2 / 3 : ℝ)⌋₊) :
    D * (k : ℝ) ^ (3 / 2 : ℝ) / n * l ≤ gamma * c := by
  have h := hill_power_candidate_bias_le hn (div_pos hc hl) (by norm_num : (0 : ℝ) < 1)
    ha hD (by norm_num; exact hsmall) (by norm_num; exact hk)
  norm_num at h
  calc
    _ ≤ gamma * (c / l) * l := mul_le_mul_of_nonneg_right h hl.le
    _ = gamma * c := by field_simp

/-- If [the envelope coefficient is nonnegative](hyp:hD), [the target is positive](hyp:hg), and [the bias exponent is positive](hyp:hb), then [there is a positive candidate constant whose envelope contribution does not exceed the target](goal).

It depends only on the envelope coefficient, target, and exponent. -/
-- @node: hill_exists_small_candidate_constant
lemma hill_exists_small_candidate_constant {D gamma b : ℝ}
    (hD : 0 ≤ D) (hg : 0 < gamma) (hb : 0 < b) :
    ∃ a > 0, D * a ^ b ≤ gamma := by
  let z := gamma / (D + 1)
  have hz : 0 < z := div_pos hg (by positivity)
  refine ⟨z ^ (1 / b), Real.rpow_pos_of_pos hz _, ?_⟩
  have hpower : (z ^ (1 / b)) ^ b = z := by
    rw [← Real.rpow_mul hz.le, one_div_mul_cancel hb.ne', Real.rpow_one]
  rw [hpower]
  change D * (gamma / (D + 1)) ≤ gamma
  rw [← mul_div_assoc]
  exact (div_le_iff₀ (by positivity : 0 < D + 1)).mpr (by nlinarith)

/-- For a bias envelope, if [the sample size](hyp:hn), [confidence scale](hyp:hc), [power exponent](hyp:hp), and [candidate constant](hyp:ha) are positive, [the envelope coefficient is nonnegative](hyp:hC), [the index is positive](hyp:hkpos), [the envelope has power decay on its tail domain](hyp:henvelope), [the threshold lies in that domain](hyp:hdomain), [the candidate constant meets the resulting bias budget](hyp:hsmall), and [the index is below the rounded power candidate](hyp:hk), then [the index's tail bias is within the target confidence budget](goal). -/
-- @node: hill_power_candidate_envelope_admissible
lemma hill_power_candidate_envelope_admissible (eta : ℝ → ℝ)
    {n c p a C gamma v₀ : ℝ} {k : ℕ}
    (hn : 0 < n) (hc : 0 < c) (hp : 0 < p) (ha : 0 < a) (hC : 0 ≤ C)
    (hkpos : 0 < k)
    (henvelope : ∀ v ≥ v₀, eta v ≤ C * v ^ (-p))
    (hdomain : v₀ ≤ n / (2 * k))
    (hsmall : (C * (2 : ℝ) ^ p) * a ^ (p + 1 / 2) ≤ gamma)
    (hk : k ≤ ⌊a * n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))⌋₊) :
    Real.sqrt k * eta (n / (2 * k)) ≤ gamma * c := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hid : Real.sqrt k * (C * (n / (2 * k)) ^ (-p)) =
      (C * (2 : ℝ) ^ p) * (k : ℝ) ^ (p + 1 / 2) / n ^ p := by
    rw [Real.div_rpow hn.le (by positivity), Real.rpow_neg hn.le,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * k),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hkreal.le,
      Real.sqrt_eq_rpow, Real.rpow_add hkreal]
    field_simp
  calc
    _ ≤ Real.sqrt k * (C * (n / (2 * k)) ^ (-p)) :=
      mul_le_mul_of_nonneg_left (henvelope _ hdomain) (Real.sqrt_nonneg _)
    _ = _ := hid
    _ ≤ gamma * c := hill_power_candidate_bias_le hn hc hp ha
      (by positivity) hsmall hk

/-- For a bias envelope, if [the sample size exceeds one](hyp:hn), [the confidence scale](hyp:hc) and [candidate constant](hyp:ha) are positive, [the envelope coefficient is nonnegative](hyp:hC), [the index is positive](hyp:hkpos), [the beta-one envelope bound holds on its tail domain](hyp:henvelope), [the threshold lies in that domain](hyp:hdomain), [the candidate constant meets the logarithmic bias budget](hyp:hsmall), and [the index is below the rounded logarithmic candidate](hyp:hk), then [the index's tail bias is within the target confidence budget](goal). -/
-- @node: hill_log_candidate_envelope_admissible
lemma hill_log_candidate_envelope_admissible (eta : ℝ → ℝ)
    {n c a C gamma v₀ : ℝ} {k : ℕ}
    (hn : 1 < n) (hc : 0 < c) (ha : 0 < a) (hC : 0 ≤ C)
    (hkpos : 0 < k)
    (henvelope : ∀ v ≥ v₀, eta v ≤ C * v ^ (-1 : ℝ) * Real.log v)
    (hdomain : v₀ ≤ n / (2 * k))
    (hsmall : (2 * C) * a ^ (3 / 2 : ℝ) ≤ gamma)
    (hk : k ≤ ⌊a * n ^ (2 / 3 : ℝ) * (c / Real.log n) ^ (2 / 3 : ℝ)⌋₊) :
    Real.sqrt k * eta (n / (2 * k)) ≤ gamma * c := by
  have hnpos : 0 < n := by linarith
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
  have hvpos : 0 < n / (2 * k) := by positivity
  have hvle : n / (2 * k) ≤ n := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
    nlinarith
  have hlog := Real.log_le_log hvpos hvle
  have hid : Real.sqrt k * (C * (n / (2 * k)) ^ (-1 : ℝ) * Real.log n) =
      (2 * C) * (k : ℝ) ^ (3 / 2 : ℝ) / n * Real.log n := by
    rw [Real.rpow_neg_one, Real.sqrt_eq_rpow]
    have hpower : (k : ℝ) ^ (3 / 2 : ℝ) = (k : ℝ) ^ (1 / 2 : ℝ) * k := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
        Real.rpow_add hkreal, Real.rpow_one]
    rw [hpower]
    field_simp
  calc
    _ ≤ Real.sqrt k * (C * (n / (2 * k)) ^ (-1 : ℝ) * Real.log (n / (2 * k))) :=
      mul_le_mul_of_nonneg_left (henvelope _ hdomain) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt k * (C * (n / (2 * k)) ^ (-1 : ℝ) * Real.log n) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := hid
    _ ≤ gamma * c := hill_log_candidate_bias_le hnpos hc (Real.log_pos hn) ha
      (by positivity) hsmall hk

/-- For a bias envelope, if [the power exponent is positive](hyp:hp), [the envelope coefficient is nonnegative](hyp:hC), [the target is positive](hyp:hg), and [the envelope has the stated power decay on its tail domain](hyp:henvelope), then [there is one positive candidate constant that gives the target bias bound for every admissible rounded power candidate](goal). -/
-- @node: hill_power_envelope_candidate_constant
lemma hill_power_envelope_candidate_constant (eta : ℝ → ℝ)
    {p C gamma v₀ : ℝ} (hp : 0 < p) (hC : 0 ≤ C) (hg : 0 < gamma)
    (henvelope : ∀ v ≥ v₀, eta v ≤ C * v ^ (-p)) :
    ∃ a > 0, ∀ (n c : ℝ) (k : ℕ), 0 < n → 0 < c → 0 < k →
      v₀ ≤ n / (2 * k) →
      k ≤ ⌊a * n ^ (2 * p / (1 + 2 * p)) * c ^ (2 / (1 + 2 * p))⌋₊ →
      Real.sqrt k * eta (n / (2 * k)) ≤ gamma * c := by
  obtain ⟨a, ha, hsmall⟩ := hill_exists_small_candidate_constant
    (D := C * (2 : ℝ) ^ p) (b := p + 1 / 2) (by positivity) hg (by positivity)
  refine ⟨a, ha, ?_⟩
  intro n c k hn hc hkpos hdomain hk
  exact hill_power_candidate_envelope_admissible eta hn hc hp ha hC hkpos
    henvelope hdomain hsmall hk

/-- For a bias envelope, if [the envelope coefficient is nonnegative](hyp:hC), [the target is positive](hyp:hg), and [the beta-one logarithmic envelope bound holds on its tail domain](hyp:henvelope), then [there is one positive candidate constant that gives the target bias bound for every admissible rounded logarithmic candidate](goal). -/
-- @node: hill_log_envelope_candidate_constant
lemma hill_log_envelope_candidate_constant (eta : ℝ → ℝ)
    {C gamma v₀ : ℝ} (hC : 0 ≤ C) (hg : 0 < gamma)
    (henvelope : ∀ v ≥ v₀, eta v ≤ C * v ^ (-1 : ℝ) * Real.log v) :
    ∃ a > 0, ∀ (n c : ℝ) (k : ℕ), 1 < n → 0 < c → 0 < k →
      v₀ ≤ n / (2 * k) →
      k ≤ ⌊a * n ^ (2 / 3 : ℝ) * (c / Real.log n) ^ (2 / 3 : ℝ)⌋₊ →
      Real.sqrt k * eta (n / (2 * k)) ≤ gamma * c := by
  obtain ⟨a, ha, hsmall⟩ := hill_exists_small_candidate_constant
    (D := 2 * C) (b := 3 / 2) (by positivity) hg (by norm_num)
  refine ⟨a, ha, ?_⟩
  intro n c k hn hc hkpos hdomain hk
  exact hill_log_candidate_envelope_admissible eta hn hc ha hC hkpos
    henvelope hdomain hsmall hk

end Papers.TbsExtremeEffects
