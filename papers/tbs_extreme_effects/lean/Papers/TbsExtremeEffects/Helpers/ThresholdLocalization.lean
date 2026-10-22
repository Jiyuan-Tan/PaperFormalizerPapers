module
public import Papers.TbsExtremeEffects.Helpers.ThresholdBand
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Deterministic localization of the adaptive threshold on the Hill event. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- If [the regime index is nonnegative](hyp:hs) and [at most one half](hyp:hs'), then [the low-regime exponent changes by no more than its two inputs differ](goal). -/
-- @node: lowRegimeExponent_sub_le
lemma lowRegimeExponent_sub_le {s x y : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    |lowRegimeExponent s x - lowRegimeExponent s y| ≤ |x - y| := by
  have ha : 0 ≤ 1 - 2 * s := by linarith
  have hb : 1 - 2 * s ≤ 1 := by linarith
  calc
    _ = |1 - 2 * s| * |x - y| := by
      rw [← abs_mul]; congr 1; unfold lowRegimeExponent; ring
    _ ≤ 1 * |x - y| := mul_le_mul_of_nonneg_right (by rwa [abs_of_nonneg ha])
      (abs_nonneg _)
    _ = _ := one_mul _

/-- If [the first argument is nonnegative](hyp:hx) and [does not exceed the second](hyp:hxy), then [the high-regime exponent increases by a nonnegative amount no larger than the input increase](goal). -/
-- @node: highRegimeExponent_increment
lemma highRegimeExponent_increment {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    0 ≤ highRegimeExponent y - highRegimeExponent x ∧
      highRegimeExponent y - highRegimeExponent x ≤ y - x := by
  have small : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ 1 →
      0 ≤ highRegimeExponent v - highRegimeExponent u ∧
        highRegimeExponent v - highRegimeExponent u ≤ v - u := by
    intro u v hu huv hv
    have hvpos : 0 ≤ v := hu.trans huv
    have hdu : 0 < 1 + 2 * u := by positivity
    have hdv : 0 < 1 + 2 * v := by positivity
    have hd : 0 < (1 + 2 * v) * (1 + 2 * u) := by positivity
    have hid : highRegimeExponent v - highRegimeExponent u =
        (v - u) / ((1 + 2 * v) * (1 + 2 * u)) := by
      simp only [highRegimeExponent, min_eq_right hv, min_eq_right (huv.trans hv)]
      field_simp [hdu.ne', hdv.ne']
      ring
    rw [hid]
    refine ⟨div_nonneg (sub_nonneg.mpr huv) hd.le,
      div_le_self (sub_nonneg.mpr huv) ?_⟩
    nlinarith
  have large : ∀ {u v : ℝ}, 1 ≤ u → u ≤ v →
      0 ≤ highRegimeExponent v - highRegimeExponent u ∧
        highRegimeExponent v - highRegimeExponent u ≤ v - u := by
    intro u v hu huv
    simp only [highRegimeExponent, min_eq_left hu, min_eq_left (hu.trans huv)]
    constructor <;> linarith
  by_cases hy : y ≤ 1
  · exact small hx hxy hy
  by_cases hx' : 1 ≤ x
  · exact large hx' hxy
  have hleft := small hx (le_of_not_ge hx') le_rfl
  have hright := large (u := 1) le_rfl (le_of_not_ge hy)
  constructor <;> linarith [hleft.1, hleft.2, hright.1, hright.2]

/-- If [the first argument is nonnegative](hyp:hx) and [the second argument is nonnegative](hyp:hy), then [the high-regime exponent differs by no more than the arguments do](goal). -/
-- @node: highRegimeExponent_sub_le
lemma highRegimeExponent_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |highRegimeExponent x - highRegimeExponent y| ≤ |x - y| := by
  rcases le_total y x with h | h
  · obtain ⟨ha, hb⟩ := highRegimeExponent_increment hy h
    simpa only [abs_of_nonneg ha, abs_of_nonneg (sub_nonneg.mpr h)] using hb
  · rw [abs_sub_comm (highRegimeExponent x), abs_sub_comm x]
    obtain ⟨ha, hb⟩ := highRegimeExponent_increment hx h
    simpa only [abs_of_nonneg ha, abs_of_nonneg (sub_nonneg.mpr h)] using hb

/-- If [the base is at least one](hyp:hn) and [the exponent discrepancy times its logarithm is at most log two](hyp:hsmall), then [the two powers are within a factor of two](goal). -/
-- @node: threshold_power_ratio_bounds
lemma threshold_power_ratio_bounds {n x y : ℝ} (hn : 1 ≤ n)
    (hsmall : |x - y| * Real.log n ≤ Real.log 2) :
    (1 / 2 : ℝ) * n ^ y ≤ n ^ x ∧ n ^ x ≤ 2 * n ^ y := by
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  have habs : |Real.log n * (x - y)| ≤ Real.log 2 := by
    rwa [abs_mul, abs_of_nonneg hlog, mul_comm]
  have he := abs_le.mp habs
  have hlo := Real.exp_le_exp.mpr he.1
  have hhi := Real.exp_le_exp.mpr he.2
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hlo
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hhi
  have hid : n ^ x = Real.exp (Real.log n * (x - y)) * n ^ y := by
    rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos, ← Real.exp_add]
    congr 1
    ring
  rw [hid]
  constructor
  · simpa using mul_le_mul_of_nonneg_right hlo (Real.rpow_nonneg hnpos.le y)
  · exact mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg hnpos.le y)

/-- If [the selected threshold has the specified two-sided order](hyp:hOrder), [the sample size is an admissible even size](hyp:hn), and [the exponent error is logarithmically small](hyp:hsmall), then [the selected threshold belongs to the fixed threshold band](goal). -/
-- @node: selected_threshold_mem_band
lemma selected_threshold_mem_band (E : NeteExperiment M) {cminus cplus : ℝ}
    {kappa : ℝ → ℝ} {gammaHat tn : ℕ → E.Om → ℝ}
    (hOrder : SelectedThresholdOrder cminus cplus kappa gammaHat tn)
    {n : ℕ} (hn : EvenSampleSize n) (w : E.Om)
    (hsmall : |kappa (gammaHat n w) - kappa (gamma M)| * Real.log n ≤ Real.log 2) :
    tn n w ∈ thresholdBand M cminus cplus kappa n := by
  have hnpos : 1 ≤ (n : ℝ) := by
    have := hn.1
    exact_mod_cast (show 1 ≤ n by omega)
  obtain ⟨hlo, hhi⟩ := threshold_power_ratio_bounds hnpos hsmall
  obtain ⟨hOrderLo, hOrderHi⟩ := hOrder.2.2 n hn w
  have hplus : 0 ≤ cplus := (hOrder.1.trans_le hOrder.2.1).le
  constructor
  · calc
      _ = cminus * ((1 / 2 : ℝ) * (n : ℝ) ^ kappa (gamma M)) := by ring
      _ ≤ cminus * (n : ℝ) ^ kappa (gammaHat n w) :=
        mul_le_mul_of_nonneg_left hlo hOrder.1.le
      _ ≤ tn n w := hOrderLo
  · calc
      tn n w ≤ cplus * (n : ℝ) ^ kappa (gammaHat n w) := hOrderHi
      _ ≤ cplus * (2 * (n : ℝ) ^ kappa (gamma M)) :=
        mul_le_mul_of_nonneg_left hhi hplus
      _ = _ := by ring

/-- If [the model's tail index is positive](hyp:hb), then [the low-regime exceedance-count exponent equals the regime index](goal). -/
-- @node: lowRegime_count_exponent
lemma lowRegime_count_exponent {s : ℝ} (hb : 0 < M.beta) :
    (1 - M.beta * lowRegimeExponent s (gamma M)) / 2 = s := by
  unfold lowRegimeExponent gamma
  field_simp
  ring

/-- If [the model's tail index is positive](hyp:hb), then [the high-regime exceedance-count exponent equals the corollary rate exponent](goal). -/
-- @node: highRegime_count_exponent
lemma highRegime_count_exponent (hb : 0 < M.beta) :
    (1 - M.beta * highRegimeExponent (gamma M)) / 2 = corRateExponent M.beta := by
  by_cases h : M.beta ≤ 1
  · have hg : 1 ≤ gamma M := by
      unfold gamma
      exact (le_div_iff₀ hb).mpr (by linarith)
    simp only [highRegimeExponent, min_eq_left hg, corRateExponent, max_eq_right h]
    unfold gamma
    field_simp
    ring
  · have hg : gamma M ≤ 1 := by
      unfold gamma
      exact (div_le_iff₀ hb).mpr (by linarith)
    have hb' : 1 ≤ M.beta := le_of_not_ge h
    simp only [highRegimeExponent, min_eq_right hg, corRateExponent, max_eq_left hb']
    unfold gamma
    have hbne := hb.ne'
    have hden : 1 + 2 * (1 / M.beta) ≠ 0 := by positivity
    have hden' : 2 + M.beta ≠ 0 := by positivity
    field_simp
    ring

/-- If [the tail index is positive](hyp:hb) and [the scaling constant is positive](hyp:ha), then [the Hill-rate shape times log sample size converges to zero](goal). -/
-- @node: hillRateShape_log_tendsto_zero
lemma hillRateShape_log_tendsto_zero {beta a : ℝ} (hb : 0 < beta) (ha : 0 < a) :
    Tendsto (fun n : ℕ => hillRateShape beta n a * Real.log n) atTop (𝓝 0) := by
  let r : ℝ := if beta ≤ 1 then 1 / 3 else 1 / (2 + beta)
  have hr : 0 < r := by dsimp [r]; split_ifs <;> positivity
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogRatio : Tendsto (fun n : ℕ => a * (Real.log n / (n : ℝ))) atTop (𝓝 0) := by
    simpa using ((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop).const_mul a
  have hLogBounds : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log n ∧ 0 ≤ Real.log (a * Real.log n) ∧
        Real.log (a * Real.log n) ≤ Real.log n := by
    filter_upwards [hlog.eventually (eventually_ge_atTop (max 1 (1 / a))),
      (tendsto_order.mp hlogRatio).2 1 (by norm_num), eventually_ge_atTop (1 : ℕ)]
      with n hn hsmall hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hl : 1 ≤ Real.log n := (le_max_left _ _).trans hn
    have hal : 1 ≤ a * Real.log n := by
      have := (le_max_right 1 (1 / a)).trans hn
      simpa only [mul_comm] using (div_le_iff₀ ha).mp this
    have hupper : a * Real.log n ≤ n := by
      have := (div_lt_iff₀ hnpos).mp (show a * Real.log n / n < 1 by
        simpa [mul_div_assoc] using hsmall)
      linarith
    exact ⟨hl, Real.log_nonneg hal, Real.log_le_log (zero_lt_one.trans_le hal) hupper⟩
  have hBound : ∀ᶠ n : ℕ in atTop,
      0 ≤ hillRateShape beta n a * Real.log n ∧
        hillRateShape beta n a * Real.log n ≤
          (Real.log n) ^ (2 * r + 1) / (n : ℝ) ^ r := by
    filter_upwards [hLogBounds, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hlpos : 0 < Real.log n := zero_lt_one.trans_le hn.1
    have hll : 0 ≤ Real.log (a * Real.log n) := hn.2.1
    have hnum : Real.log (a * Real.log n) ≤ (Real.log n) ^ 2 := by
      nlinarith [hn.2.2]
    have hmid : Real.log n * Real.log (a * Real.log n) ≤ (Real.log n) ^ 2 := by
      nlinarith [hn.2.2]
    have hRate : hillRateShape beta n a ≤ ((Real.log n) ^ 2 / (n : ℝ)) ^ r := by
      unfold hillRateShape
      split_ifs with hlt heq
      · have hrval : r = 1 / 3 := by simp [r, hlt.le]
        rw [hrval]
        exact Real.rpow_le_rpow (div_nonneg hn.2.1 hnpos.le)
          (div_le_div_of_nonneg_right hnum hnpos.le) (by norm_num)
      · have hrval : r = 1 / 3 := by simp [r, heq]
        rw [hrval]
        exact Real.rpow_le_rpow (by positivity)
          (div_le_div_of_nonneg_right hmid hnpos.le) (by norm_num)
      · have hgt : ¬ beta ≤ 1 := by intro h; exact heq (le_antisymm h (le_of_not_gt hlt))
        have hrval : r = 1 / (2 + beta) := by simp [r, hgt]
        rw [hrval]
        exact Real.rpow_le_rpow (div_nonneg hn.2.1 hnpos.le)
          (div_le_div_of_nonneg_right hnum hnpos.le) (by positivity)
    refine ⟨mul_nonneg (by unfold hillRateShape; split_ifs <;> positivity) hlpos.le,
      (mul_le_mul_of_nonneg_right hRate hlpos.le).trans_eq ?_⟩
    rw [Real.div_rpow (sq_nonneg _) hnpos.le, ← Real.rpow_natCast (Real.log n) 2,
      ← Real.rpow_mul hlpos.le]
    rw [div_mul_eq_mul_div, ← Real.rpow_add_one hlpos.ne']
    norm_num
  have hUpper : Tendsto (fun n : ℕ =>
      (Real.log n) ^ (2 * r + 1) / (n : ℝ) ^ r) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_rpow_atTop (2 * r + 1) hr).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  exact squeeze_zero' (hBound.mono fun _ h => h.1) (hBound.mono fun _ h => h.2) hUpper

/-- If [the model's tail index is positive](hyp:hb), [the confidence level is positive](hyp:hd), [the selected threshold obeys the two-sided order](hyp:hOrder), and [the exponent rule is one-Lipschitz on nonnegative inputs](hyp:hLip), then [eventually every Hill-accurate selected threshold lies in the fixed band](goal). -/
-- @node: hill_event_selected_threshold_mem_band
lemma hill_event_selected_threshold_mem_band (E : NeteExperiment M)
    {cminus cplus Cg delta : ℝ} {kappa : ℝ → ℝ} {tn : ℕ → E.Om → ℝ}
    (hb : 0 < M.beta) (hd : 0 < delta)
    (hOrder : SelectedThresholdOrder cminus cplus kappa
      (fun n => hillAdaptive E n (delta / 6)) tn)
    (hLip : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |kappa x - kappa y| ≤ |x - y|) :
    ∀ᶠ n : ℕ in atTop, EvenSampleSize n → ∀ w,
      |gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n →
      tn n w ∈ thresholdBand M cminus cplus kappa n := by
  have hg : 0 < gamma M := by unfold gamma; positivity
  have hlim : Tendsto (fun n : ℕ => hillErrorBound M Cg delta n * Real.log n)
      atTop (𝓝 0) := by
    simpa only [hillErrorBound, mul_assoc, mul_zero] using
      (hillRateShape_log_tendsto_zero hb (by positivity : 0 < 48 / delta)).const_mul Cg
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  have hsmall := (tendsto_order.mp hlim).2 (min (gamma M) (Real.log 2))
    (lt_min hg (Real.log_pos (by norm_num)))
  filter_upwards [hlog, hsmall] with n hnlog hnsmall
  change 1 ≤ Real.log (n : ℝ) at hnlog
  intro hn w hw
  have hnonneg : 0 ≤ hillErrorBound M Cg delta n := (abs_nonneg _).trans hw
  have hbsmall : hillErrorBound M Cg delta n ≤ gamma M := by
    calc
      _ = hillErrorBound M Cg delta n * 1 := (mul_one _).symm
      _ ≤ hillErrorBound M Cg delta n * Real.log n :=
        mul_le_mul_of_nonneg_left hnlog hnonneg
      _ ≤ gamma M := hnsmall.le.trans (min_le_left _ _)
  have hhat : 0 ≤ hillAdaptive E n (delta / 6) w := by
    have h := (abs_le.mp hw).2
    linarith
  apply selected_threshold_mem_band E hOrder hn w
  calc
    _ ≤ |hillAdaptive E n (delta / 6) w - gamma M| * Real.log n :=
      mul_le_mul_of_nonneg_right (hLip _ _ hhat hg.le) (by linarith)
    _ ≤ hillErrorBound M Cg delta n * Real.log n :=
      mul_le_mul_of_nonneg_right (by simpa only [abs_sub_comm] using hw) (by linarith)
    _ ≤ Real.log 2 := hnsmall.le.trans (min_le_right _ _)

/-- If [the model's tail index is positive](hyp:hb), [the confidence level is positive](hyp:hd), [the Hill estimator has its stated constant](hyp:hHill), [the selected threshold obeys the two-sided order](hyp:hOrder), and [the exponent rule is one-Lipschitz on nonnegative inputs](hyp:hLip), then [eventually the Hill event together with membership in the fixed band has probability at least one minus one sixth of the confidence level](goal). -/
-- @node: hill_selected_threshold_band_probability
lemma hill_selected_threshold_band_probability (E : NeteExperiment M)
    {cminus cplus Cg delta : ℝ} {kappa : ℝ → ℝ} {tn : ℕ → E.Om → ℝ} {n0 : ℕ}
    (hb : 0 < M.beta) (hd : 0 < delta)
    (hHill : HillConstantAt E (delta / 6) n0 Cg)
    (hOrder : SelectedThresholdOrder cminus cplus kappa
      (fun n => hillAdaptive E n (delta / 6)) tn)
    (hLip : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |kappa x - kappa y| ≤ |x - y|) :
    ∀ᶠ n : ℕ in atTop, EvenSampleSize n → IIDSampling E n →
      1 - delta / 6 ≤ E.P.real {w |
        |gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n ∧
        tn n w ∈ thresholdBand M cminus cplus kappa n} := by
  filter_upwards [eventually_ge_atTop n0,
    hill_event_selected_threshold_mem_band E hb hd hOrder hLip] with n hn hband
  intro heven hiid
  have hsource := hHill n hn hiid
  have hid : 8 / (delta / 6) = (48 : ℝ) / delta := by ring
  rw [hid] at hsource
  apply hsource.trans
  apply measureReal_mono (h₂ := measure_ne_top E.P _)
  intro w hw
  exact ⟨hw, hband heven w hw⟩

end Papers.TbsExtremeEffects
