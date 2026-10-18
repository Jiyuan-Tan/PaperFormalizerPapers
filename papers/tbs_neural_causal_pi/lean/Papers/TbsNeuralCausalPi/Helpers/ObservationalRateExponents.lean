module
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalTailRates
/-! # Exponents at the prescribed observational sampling tolerance

These are numerical estimates, not an empirical concentration theorem.
They handle the critical dimension two logarithmic denominator and random
stratum counts uniformly above half their expected value. The actual
joint-latent empirical tail estimate remains an independent obligation.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open Filter
open scoped Topology
noncomputable section

-- @node: observationalRateScale
/-- For [dimension d](hyp:d) and [a real sample scale x](hyp:x), the
[observational tolerance](goal) is x raised to minus the reciprocal of the
larger of two and d, multiplied by the square of the natural logarithm of x. -/
def observationalRateScale (d : ℕ) (x : ℝ) : ℝ :=
  x ^ (-(1 : ℝ) / (max 2 d : ℕ)) * (Real.log x)^2

-- @node: observationalRateScale_pos
/-- If [x exceeds one](hyp:hx), [the observational tolerance in any dimension
is strictly positive](goal). -/
lemma observationalRateScale_pos (d : ℕ) {x : ℝ} (hx : 1 < x) :
    0 < observationalRateScale d x := by
  unfold observationalRateScale
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (sq_pos_of_pos (Real.log_pos hx))

-- @node: observationalRateScale_quadratic
/-- If [the dimension is at most two](hyp:hd) and [x is positive](hyp:hx),
[x times the squared observational tolerance equals the fourth power of the
natural logarithm of x](goal). -/
lemma observationalRateScale_quadratic {d : ℕ} (hd : d ≤ 2) {x : ℝ} (hx : 0 < x) :
    x * (observationalRateScale d x)^2 = (Real.log x)^4 := by
  have he : (x ^ (-((1 : ℝ) / 2)))^2 = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  simp only [observationalRateScale, max_eq_left hd]
  norm_num only [Nat.cast_ofNat]
  rw [mul_pow, he]
  field_simp

-- @node: observationalRateScale_dimension_power
/-- If [the dimension d is at least two](hyp:hd) and [x is positive](hyp:hx),
[x times the d-th power of the observational tolerance equals the natural
logarithm of x raised to the power twice d](goal). -/
lemma observationalRateScale_dimension_power {d : ℕ} (hd : 2 ≤ d)
    {x : ℝ} (hx : 0 < x) :
    x * (observationalRateScale d x)^d = (Real.log x)^(2*d) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have he : (x ^ (-(1 : ℝ) / d))^d = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    rw [div_mul_cancel₀ _ hd0, Real.rpow_neg_one]
  simp only [observationalRateScale, max_eq_right hd, mul_pow, he, ← pow_mul]
  field_simp

-- @node: observationalRateScale_critical_log_le
/-- If [x is at least three](hyp:hx) and [its natural logarithm is at least
one](hyp:hlog), [the logarithm of two plus the reciprocal dimension-two
observational tolerance is at most twice the logarithm of x](goal). -/
lemma observationalRateScale_critical_log_le {x : ℝ} (hx : 3 ≤ x)
    (hlog : 1 ≤ Real.log x) :
    Real.log (2 + (observationalRateScale 2 x)⁻¹) ≤ 2 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hs : x⁻¹ ≤ observationalRateScale 2 x := by
    have hp : x ^ (-(1 : ℝ)) ≤ x ^ (-(1 : ℝ)/2) :=
      Real.monotone_rpow_of_base_ge_one (by linarith) (by norm_num)
    have hl : 1 ≤ (Real.log x)^2 := by nlinarith
    unfold observationalRateScale
    norm_num only [max_self, Nat.cast_ofNat]
    rw [← Real.rpow_neg_one]
    have hp' : x ^ (-(1 : ℝ)) ≤ x ^ (-((1 : ℝ)/2)) := by
      simpa only [neg_div] using hp
    exact hp'.trans (le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) hl)
  have hs0 := observationalRateScale_pos 2 (by linarith : 1 < x)
  have hi : (observationalRateScale 2 x)⁻¹ ≤ x := by
    calc
      _ ≤ (x⁻¹)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (inv_pos.mpr hx0) hs
      _ = x := inv_inv x
  calc
    _ ≤ Real.log (x^2) := Real.log_le_log (by have := inv_pos.mpr hs0; linarith) (by nlinarith)
    _ = _ := by rw [Real.log_pow]; norm_num

-- @node: observationalRateScale_critical_exponent_ge
/-- If [x is at least three](hyp:hx) and [its natural logarithm is at least
one](hyp:hlog), [x times the squared ratio of the dimension-two tolerance to
the logarithm of two plus its reciprocal is at least one quarter of the
squared logarithm of x](goal). -/
lemma observationalRateScale_critical_exponent_ge {x : ℝ} (hx : 3 ≤ x)
    (hlog : 1 ≤ Real.log x) :
    (Real.log x)^2 / 4 ≤ x *
      (observationalRateScale 2 x / Real.log (2 + (observationalRateScale 2 x)⁻¹))^2 := by
  have hx0 : 0 < x := by linarith
  have hs0 := observationalRateScale_pos 2 (by linarith : 1 < x)
  have hl0 : 0 < Real.log x := by linarith
  have hden : 0 < Real.log (2 + (observationalRateScale 2 x)⁻¹) :=
    Real.log_pos (by have := inv_pos.mpr hs0; linarith)
  have hdenle := observationalRateScale_critical_log_le hx hlog
  have hsq : (Real.log (2 + (observationalRateScale 2 x)⁻¹))^2 ≤
      (2 * Real.log x)^2 := pow_le_pow_left₀ hden.le hdenle 2
  rw [div_pow, ← mul_div_assoc, observationalRateScale_quadratic (by omega) hx0]
  apply (le_div_iff₀ (sq_pos_of_pos hden)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.log x))]

-- @node: observationalRateScale_exponent_ge
/-- For [a positive dimension](hyp:hd), if [x is at least three](hyp:hx) and
[its natural logarithm is at least one](hyp:hlog), [x times the concentration
exponent evaluated at the observational tolerance is at least one quarter of
the squared logarithm of x: use the squared tolerance in dimension one, the
squared ratio of the tolerance to the logarithm of two plus its reciprocal in
dimension two, and the d-th power of the tolerance in higher dimensions](goal). -/
lemma observationalRateScale_exponent_ge {d : ℕ} (hd : 0 < d)
    {x : ℝ} (hx : 3 ≤ x) (hlog : 1 ≤ Real.log x) :
    (Real.log x)^2 / 4 ≤ x *
      (if d = 1 then (observationalRateScale d x)^2
       else if d = 2 then
         (observationalRateScale d x / Real.log (2 + (observationalRateScale d x)⁻¹))^2
       else (observationalRateScale d x)^d) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := by linarith
  by_cases h1 : d = 1
  · subst d
    rw [if_pos rfl, observationalRateScale_quadratic (by omega) hx0]
    nlinarith [sq_nonneg ((Real.log x)^2 - 1)]
  by_cases h2 : d = 2
  · subst d
    simpa only [show ¬ (2 : ℕ) = 1 by omega, if_false, if_pos, ↓reduceIte] using
      observationalRateScale_critical_exponent_ge hx hlog
  rw [if_neg h1, if_neg h2, observationalRateScale_dimension_power (by omega) hx0]
  have hp : (Real.log x)^2 ≤ (Real.log x)^(2*d) :=
    pow_le_pow_right₀ hlog (by omega)
  nlinarith [sq_nonneg (Real.log x)]

-- @node: observational_log_sq_exp_eventually_le_inverse_power
/-- For [a positive coefficient a](hyp:ha), [the exponential of minus a times
the squared logarithm of n is eventually at most n to the power minus k, for
any natural number k](goal). -/
lemma observational_log_sq_exp_eventually_le_inverse_power {a : ℝ} (ha : 0 < a)
    (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-a * (Real.log n)^2) ≤ (n : ℝ)^(-(k : ℤ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop ((k : ℝ) / a)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hmul : (k : ℝ) ≤ a * Real.log n := by simpa only [mul_comm] using (div_le_iff₀ ha).mp hn
  calc
    _ ≤ Real.exp (-(k : ℝ) * Real.log n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hmul hl0]
    _ = _ := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0,
        zpow_neg, zpow_natCast]

-- @node: observational_random_count_exponential_tail
/-- For [a positive dimension](hyp:hd), [positive stratum probability p](hyp:hp),
and [positive exponential rate c](hyp:hc), [eventually in n, uniformly over
counts N at least n times p divided by two, the exponential of minus c times N
times the concentration exponent at the observational tolerance is at most n
to the power minus k; this exponent is the squared tolerance in dimension one,
the squared ratio of the tolerance to the logarithm of two plus its reciprocal
in dimension two, and the d-th power of the tolerance in higher dimensions](goal). -/
lemma observational_random_count_exponential_tail {d : ℕ} (hd : 0 < d)
    {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, (n : ℝ) * p / 2 ≤ N →
      Real.exp (-c * N *
        (if d = 1 then (observationalRateScale d n)^2
         else if d = 2 then
           (observationalRateScale d n /
             Real.log (2 + (observationalRateScale d n)⁻¹))^2
         else (observationalRateScale d n)^d)) ≤ (n : ℝ)^(-(k : ℤ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [observational_log_sq_exp_eventually_le_inverse_power
    (mul_pos hc hp |> fun h => div_pos h (by norm_num : (0 : ℝ) < 8)) k,
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (3 : ℕ)] with n htail hlog hn N hN
  have hx : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he := observationalRateScale_exponent_ge hd hx hlog
  let E : ℝ := if d = 1 then (observationalRateScale d n)^2
    else if d = 2 then
      (observationalRateScale d n / Real.log (2 + (observationalRateScale d n)⁻¹))^2
    else (observationalRateScale d n)^d
  change (Real.log n)^2 / 4 ≤ (n : ℝ) * E at he
  have hE : 0 ≤ E := by
    dsimp only [E]
    split_ifs
    · exact sq_nonneg _
    · exact sq_nonneg _
    · exact pow_nonneg (observationalRateScale_pos d (by linarith : (1 : ℝ) < n)).le _
  have hcount := mul_le_mul_of_nonneg_right hN hE
  apply le_trans (Real.exp_le_exp.mpr ?_) htail
  have hscale := mul_le_mul_of_nonneg_left he (show 0 ≤ c * p / 2 by positivity)
  have hscale' := mul_le_mul_of_nonneg_left hcount hc.le
  dsimp only [E] at hscale' hscale ⊢
  nlinarith

-- @node: observationalRateScale_tendsto_zero
/-- [For every dimension, the observational tolerance converges to zero as
the natural-number sample size tends to infinity](goal). -/
lemma observationalRateScale_tendsto_zero (d : ℕ) :
    Tendsto (fun n : ℕ => observationalRateScale d n) atTop (𝓝 0) := by
  have hp : 0 < (1 : ℝ) / (max 2 d : ℕ) := by positivity
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hp).tendsto_div_nhds_zero
  have hnat := h.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  change (Real.log (n : ℝ))^2 / (n : ℝ)^((1 : ℝ) / (max 2 d : ℕ)) = _
  unfold observationalRateScale
  rw [neg_div, Real.rpow_neg hn0, div_eq_mul_inv, mul_comm]
  norm_num

-- @node: observationalRateScale_eventually_small
/-- [For every dimension, the observational tolerance is eventually strictly
between zero and one as the sample size increases](goal). -/
lemma observationalRateScale_eventually_small (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < observationalRateScale d n ∧
      observationalRateScale d n < 1 := by
  filter_upwards [(observationalRateScale_tendsto_zero d).eventually
    (gt_mem_nhds zero_lt_one), eventually_gt_atTop (1 : ℕ)] with n hn hn1
  exact ⟨observationalRateScale_pos d (by exact_mod_cast hn1), hn⟩

-- @node: observational_finite_strata_exponential_tail
/-- In [positive dimension](hyp:hd), suppose [each positive-mass label has a
positive exponential rate](hyp:hc) and [all prefactors are nonnegative](hyp:hB).
[A single eventual sample-size cutoff ensures, for every positive-mass label
and every count at least half its expected count, that its prefactor times the
exponential of minus the rate times the count times the concentration exponent
at the observational tolerance is at most that prefactor times the inverse
fourth power of the sample size; the concentration exponent is the squared
tolerance in dimension one, the squared ratio of the tolerance to the logarithm
of two plus its reciprocal in dimension two, and the d-th power of the tolerance
in higher dimensions](goal). -/
lemma observational_finite_strata_exponential_tail
    {A : Type*} [Finite A] {d : ℕ} (hd : 0 < d)
    (p c B : A → ℝ) (hc : ∀ a, 0 < p a → 0 < c a)
    (hB : ∀ a, 0 ≤ B a) :
    ∀ᶠ n : ℕ in atTop, ∀ a, 0 < p a → ∀ N : ℕ, (n : ℝ) * p a / 2 ≤ N →
      B a * Real.exp (-c a * N *
        (if d = 1 then (observationalRateScale d n)^2
         else if d = 2 then
           (observationalRateScale d n /
             Real.log (2 + (observationalRateScale d n)⁻¹))^2
         else (observationalRateScale d n)^d)) ≤ B a * (n : ℝ)^(-(4 : ℤ)) := by
  apply eventually_all.mpr
  intro a
  by_cases hp : 0 < p a
  · filter_upwards [observational_random_count_exponential_tail hd hp (hc a hp) 4]
      with n hn
    intro _ N hN
    exact mul_le_mul_of_nonneg_left (hn N hN) (hB a)
  · exact Eventually.of_forall (fun _ ha => False.elim (hp ha))

end
end Papers.TbsNeuralCausalPi
