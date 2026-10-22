module
public import Papers.TbsExtremeEffects.Helpers.AdaptiveProduct
public import Papers.TbsExtremeEffects.Helpers.ExponentError

/-! Uniform fitted-exponent moment errors on deterministic polynomial bands. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped Topology
variable {q d : ℕ}

/-- If [the threshold is at least one](hyp:ht), [the exponent is nonnegative](hyp:ha), [the envelope constant is nonnegative](hyp:hK), and [the exponent times the log threshold is small](hyp:hsmall), then [the power and its increment satisfy the two stated exponential bounds](goal).

@node: small_exponent_increment_bound -/
lemma small_exponent_increment_bound {t a K : ℝ}
    (ht : 1 ≤ t) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hsmall : a * Real.log t ≤ 1 / 2) :
    t ^ a ≤ 2 ∧ t ^ a - 1 + K * a * t ^ a ≤ 2 * a * (Real.log t + K) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hx : 0 ≤ a * Real.log t := mul_nonneg ha (Real.log_nonneg ht)
  have hExp := Real.abs_exp_sub_one_le
    (show |a * Real.log t| ≤ 1 by rw [abs_of_nonneg hx]; linarith)
  rw [abs_of_nonneg hx] at hExp
  have hPow : t ^ a = Real.exp (a * Real.log t) := by
    rw [Real.rpow_def_of_pos htpos, mul_comm]
  have hsub : t ^ a - 1 ≤ 2 * (a * Real.log t) := by
    rw [hPow]
    exact (le_abs_self _).trans hExp
  have htwo : t ^ a ≤ 2 := by linarith
  refine ⟨htwo, ?_⟩
  have hterm := mul_le_mul_of_nonneg_left htwo (mul_nonneg hK ha)
  nlinarith

/-- If [the nuisance rate has polynomial order](hyp:hRate), [that order is positive](hyp:ha), and [the confidence argument lies in its admissible domain](hyp:hd), then [the rate times the logarithm of sample size tends to zero](goal).

@node: rateTheta_log_tendsto_zero -/
lemma rateTheta_log_tendsto_zero {rate : ℕ → ℝ → ℝ} {a eps : ℝ}
    (hRate : RateTheta rate a) (ha : 0 < a) (hd : ConfidenceDomain eps) :
    Tendsto (fun n => rate n eps * Real.log n) atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hcC, n0, _, hBounds⟩ := hRate
  have hl : 0 ≤ Real.log (1 / eps) :=
    Real.log_nonneg ((one_le_div hd.1).mpr hd.2.le)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-a) * Real.log n)
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    ext n
    dsimp only [Function.comp_apply]
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    ring
  apply squeeze_zero' _ _
    (by simpa only [mul_zero] using hlim.const_mul (C * Real.log (1 / eps)))
  · filter_upwards [eventually_ge_atTop n0, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    exact mul_nonneg
      ((mul_nonneg (mul_nonneg hc.le hl) (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
        (hBounds n hn eps hd.1 hd.2).1)
      (Real.log_nonneg (by exact_mod_cast hn1))
  · filter_upwards [eventually_ge_atTop n0, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hlN : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    calc
      rate n eps * Real.log n ≤
          (C * Real.log (1 / eps) * (n : ℝ) ^ (-a)) * Real.log n :=
        mul_le_mul_of_nonneg_right (hBounds n hn eps hd.1 hd.2).2 hlN
      _ = C * Real.log (1 / eps) * ((n : ℝ) ^ (-a) * Real.log n) := by ring

/-- If [the threshold multiplier is positive](hyp:hc), [the polynomial exponent is nonnegative](hyp:hk), [the sample logarithm is at least one](hyp:hn), [the threshold is positive](hyp:ht), and [the threshold is below its polynomial upper bound](hyp:htu), then [its logarithm is bounded by the stated multiple of log sample size](goal).

@node: polynomial_threshold_log_bound -/
lemma polynomial_threshold_log_bound {c k t : ℝ} {n : ℕ}
    (hc : 0 < c) (hk : 0 ≤ k) (hn : 1 ≤ Real.log (n : ℝ))
    (ht : 0 < t) (htu : t ≤ c * (n : ℝ) ^ k) :
    Real.log t ≤ (k + |Real.log c|) * Real.log n := by
  have hnpos : 0 < (n : ℝ) := by
    by_contra h
    have hz : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    norm_num [hz] at hn
  calc
    Real.log t ≤ Real.log (c * (n : ℝ) ^ k) := Real.log_le_log ht htu
    _ = Real.log c + k * Real.log n := by
      rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hnpos k).ne', Real.log_rpow hnpos]
    _ ≤ (k + |Real.log c|) * Real.log n := by
      have h := le_mul_of_one_le_right (abs_nonneg (Real.log c)) hn
      nlinarith [le_abs_self (Real.log c)]

/-- If [the fitted-exponent rate has polynomial order](hyp:hRate), [its order is positive](hyp:ha), [the confidence argument is valid](hyp:hd), [both band constants are positive](hyp:hcm,hcp), [the band-growth exponent is positive](hyp:hk), [the envelope constant is nonnegative](hyp:hK), then [a positive constant eventually gives the stated uniform exponent-increment bound on the polynomial band](goal).

@node: polynomial_band_exponent_increment_rate -/
lemma polynomial_band_exponent_increment_rate
    {rate : ℕ → ℝ → ℝ} {cminus cplus k a eps K T : ℝ}
    (hRate : RateTheta rate a) (ha : 0 < a) (hd : ConfidenceDomain eps)
    (hcm : 0 < cminus) (hcp : 0 < cplus) (hk : 0 < k) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Set.Icc ((cminus / 2) * (n : ℝ) ^ k) (2 * cplus * (n : ℝ) ^ k),
        max 1 T ≤ t ∧ 0 ≤ rate n eps ∧ t ^ (rate n eps) ≤ 2 ∧
        t ^ (rate n eps) - 1 + K * rate n eps * t ^ (rate n eps) ≤
          D * ((n : ℝ) ^ (-a) * Real.log n * Real.log (1 / eps)) := by
  have hRateLog := rateTheta_log_tendsto_zero hRate ha hd
  obtain ⟨c, C, hc, hcC, n0, _, hBounds⟩ := hRate
  let H := k + |Real.log (2 * cplus)|
  have hH : 0 < H := by dsimp [H]; positivity
  let D := 2 * C * (H + K)
  have hD : 0 < D := by dsimp [D]; have := hc.trans_le hcC; positivity
  have hlim := hRateLog.const_mul H
  have hsmall : ∀ᶠ n : ℕ in atTop, H * (rate n eps * Real.log n) < 1 / 2 :=
    (tendsto_order.mp (by simpa using hlim)).2 _ (by norm_num)
  have hLower : Tendsto (fun n : ℕ => (cminus / 2) * (n : ℝ) ^ k) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity)).mpr
      ((tendsto_rpow_atTop hk).comp tendsto_natCast_atTop_atTop)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  refine ⟨D, hD, ?_⟩
  filter_upwards [eventually_ge_atTop n0, hlog, hsmall,
    hLower.eventually (eventually_ge_atTop (max 1 T))] with n hn hnlog hnsmall hnLower
  change 1 ≤ Real.log (n : ℝ) at hnlog
  intro t ht
  have htlarge : max 1 T ≤ t := hnLower.trans ht.1
  have ht1 : 1 ≤ t := (le_max_left _ _).trans htlarge
  have hl : 0 ≤ Real.log (1 / eps) :=
    Real.log_nonneg ((one_le_div hd.1).mpr hd.2.le)
  have hrate : 0 ≤ rate n eps :=
    (mul_nonneg (mul_nonneg hc.le hl) (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
      (hBounds n hn eps hd.1 hd.2).1
  have hlt := polynomial_threshold_log_bound (by positivity : 0 < 2 * cplus)
    hk.le hnlog (zero_lt_one.trans_le ht1) ht.2
  change Real.log t ≤ H * Real.log n at hlt
  have hsmallt : rate n eps * Real.log t ≤ 1 / 2 := by
    calc
      _ ≤ rate n eps * (H * Real.log n) := mul_le_mul_of_nonneg_left hlt hrate
      _ = H * (rate n eps * Real.log n) := by ring
      _ ≤ _ := hnsmall.le
  obtain ⟨hpow, hincrement⟩ := small_exponent_increment_bound ht1 hrate hK hsmallt
  refine ⟨htlarge, hrate, hpow, hincrement.trans ?_⟩
  have hlogK : Real.log t + K ≤ (H + K) * Real.log n := by
    have h := le_mul_of_one_le_right hK hnlog
    nlinarith
  calc
    2 * rate n eps * (Real.log t + K) ≤
        2 * rate n eps * ((H + K) * Real.log n) :=
      mul_le_mul_of_nonneg_left hlogK (by positivity)
    _ ≤ 2 * (C * Real.log (1 / eps) * (n : ℝ) ^ (-a)) *
        ((H + K) * Real.log n) := by
      gcongr
      exact (hBounds n hn eps hd.1 hd.2).2
    _ = _ := by dsimp [D]; ring

/-- Given [regularly varying noise](hyp:hRV), [a polynomial fitted-exponent rate](hyp:hRate), [a positive rate order](hyp:ha), [a valid confidence argument](hyp:hd), [positive lower and upper band constants](hyp:hcm,hcp), [positive band growth](hyp:hk), and [a positive exponent margin below the tail index](hyp:ha0,ha0beta), [a positive constant eventually controls the radial moment uniformly over the band](goal).

@node: adaptive_band_radial_moment_rate -/
lemma adaptive_band_radial_moment_rate (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M)
    {rate : ℕ → ℝ → ℝ} {cminus cplus k a eps a0 : ℝ}
    (hRate : RateTheta rate a) (ha : 0 < a) (hd : ConfidenceDomain eps)
    (hcm : 0 < cminus) (hcp : 0 < cplus) (hk : 0 < k)
    (ha0 : 0 < a0) (ha0beta : a0 < M.beta) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Set.Icc ((cminus / 2) * (n : ℝ) ^ k) (2 * cplus * (n : ℝ) ^ k),
        1 ≤ t ∧ 0 ≤ rate n eps ∧ rate n eps ≤ a0 ∧
        Integrable (fun w => radius M w ^ (rate n eps) - 1) (tailLaw M t) ∧
        (∫ w, radius M w ^ (rate n eps) - 1 ∂tailLaw M t) ≤
          D * ((n : ℝ) ^ (-a) * Real.log n * Real.log (1 / eps)) := by
  obtain ⟨K, T, hK, hT, hMoment⟩ := tail_power_increment_uniform_bound M hRV ha0 ha0beta
  obtain ⟨D, hD, hEnvelope⟩ := polynomial_band_exponent_increment_rate
    (T := T) hRate ha hd hcm hcp hk hK.le
  have hsmall := (tendsto_order.mp (rateTheta_tendsto_zero hRate ha hd)).2 a0 ha0
  refine ⟨D, hD, ?_⟩
  filter_upwards [hEnvelope, hsmall] with n hn hna
  intro t ht
  obtain ⟨htlarge, hrate, hpow, herror⟩ := hn t ht
  have htT : T ≤ t := (le_max_right _ _).trans htlarge
  obtain ⟨hInt, hBound⟩ := hMoment t htT (rate n eps) hrate hna.le
  exact ⟨hT.trans htT, hrate, hna.le, hInt, hBound.trans herror⟩

/-- Given [regularly varying noise](hyp:hRV), [a polynomial fitted-exponent rate](hyp:hRate), [a positive rate order](hyp:ha), [a valid confidence argument](hyp:hd), [positive band constants](hyp:hcm,hcp), [positive band growth](hyp:hk), [an exponent margin below the tail index](hyp:ha0,ha0beta), and [a positive denominator with a nonnegative homogeneity envelope](hyp:hc,hG), [a positive constant eventually controls every scaled radial moment on the band](goal).

@node: adaptive_band_exponent_mean_rate -/
lemma adaptive_band_exponent_mean_rate (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M)
    {rate : ℕ → ℝ → ℝ} {cminus cplus k a eps a0 c G : ℝ}
    (hRate : RateTheta rate a) (ha : 0 < a) (hd : ConfidenceDomain eps)
    (hcm : 0 < cminus) (hcp : 0 < cplus) (hk : 0 < k)
    (ha0 : 0 < a0) (ha0beta : a0 < M.beta) (hc : 0 < c) (hG : 0 ≤ G) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Set.Icc ((cminus / 2) * (n : ℝ) ^ k) (2 * cplus * (n : ℝ) ^ k),
        1 ≤ t ∧ 0 ≤ rate n eps ∧ rate n eps ≤ a0 ∧
        Integrable (fun w => radius M w ^ (rate n eps) - 1) (tailLaw M t) ∧
        ∀ g : ℝ, 0 ≤ g → g ≤ G →
          (2 * g / c) * (∫ w, radius M w ^ (rate n eps) - 1 ∂tailLaw M t) ≤
            D * ((n : ℝ) ^ (-a) * Real.log n * Real.log (1 / eps)) := by
  obtain ⟨D, hD, hMoment⟩ := adaptive_band_radial_moment_rate M hRV
    hRate ha hd hcm hcp hk ha0 ha0beta
  refine ⟨(2 * G / c + 1) * D, by positivity, ?_⟩
  filter_upwards [hMoment, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro t ht
  obtain ⟨ht1, hrate, hsmall, hInt, hBound⟩ := hn t ht
  refine ⟨ht1, hrate, hsmall, hInt, ?_⟩
  intro g hg hgG
  have hscale : 0 ≤ (n : ℝ) ^ (-a) * Real.log n * Real.log (1 / eps) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Real.log_nonneg (by exact_mod_cast hn1)))
      (Real.log_nonneg ((one_le_div hd.1).mpr hd.2.le))
  calc
    _ ≤ (2 * g / c) * (D * ((n : ℝ) ^ (-a) * Real.log n * Real.log (1 / eps))) :=
      mul_le_mul_of_nonneg_left hBound (by positivity)
    _ ≤ (2 * G / c + 1) * (D * ((n : ℝ) ^ (-a) * Real.log n * Real.log (1 / eps))) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hD.le hscale)
      have h := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgG (by norm_num : (0 : ℝ) ≤ 2)) hc.le
      linarith
    _ = _ := by ring

end Papers.TbsExtremeEffects
