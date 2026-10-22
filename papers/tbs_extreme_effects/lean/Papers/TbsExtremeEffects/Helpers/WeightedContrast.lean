module
public import Papers.TbsExtremeEffects.Helpers.HomogeneityError
public import Papers.TbsExtremeEffects.Helpers.AngularFactor

/-! Integrability and higher-moment control of the radial-weighted angular contrast. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

-- @node: weightedAngularContrast
/-- The [weighted angular contrast](goal) for [an extreme model](hyp:M), threshold [t](hyp:t), and observation [w](hyp:w) is the treatment contrast in the outcome regression, multiplied by the normalized radial power. -/
noncomputable def weightedAngularContrast (M : ExtremeModel q d) (t : ℝ) (w : M.Om) : ℝ :=
  (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w)) *
    (radius M w ^ M.alpha / t ^ M.alpha)

-- @node: regressionContrast
/-- The [regression contrast](goal) for [an extreme model](hyp:M), threshold [t](hyp:t), and observation [w](hyp:w) is the difference between its treated and untreated conditional regressions, normalized by the threshold power. -/
noncomputable def regressionContrast (M : ExtremeModel q d) (t : ℝ) (w : M.Om) : ℝ :=
  (M.f (M.X w) true (M.U w) - M.f (M.X w) false (M.U w)) / t ^ M.alpha

-- @node: conditional_power_moment_tendsto
/-- If [the noise is regularly varying](hyp:hRV) and [the power is below the tail index](hyp:ha), then [the conditional normalized radial-power moment converges to the corresponding Pareto moment](goal). -/
lemma conditional_power_moment_tendsto (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {a : ℝ} (ha : a < M.beta) :
    Tendsto (fun t => ∫ w, radius M w ^ a / t ^ a ∂tailLaw M t)
      atTop (𝓝 (M.beta / (M.beta - a))) := by
  by_cases hz : a = 0
  · subst a
    have heq : (fun t => ∫ w, radius M w ^ (0 : ℝ) / t ^ (0 : ℝ) ∂tailLaw M t) =
        fun _ => (1 : ℝ) := by
      funext t
      let := tailLaw_probability M hRV t
      simp
    rw [heq, sub_zero, div_self hRV.1.ne']
    exact tendsto_const_nhds
  · apply (tail_integral_limit M hRV ha).congr'
    filter_upwards [conditional_radial_power_layercake M hRV ha hz] with t ht
    exact ht.symm

-- @node: conditional_power_moment_eventually_bounded
/-- If [the noise is regularly varying](hyp:hRV) and [the power is below the tail index](hyp:ha), then [the conditional normalized radial-power moment is eventually at most its Pareto limit plus one](goal). -/
lemma conditional_power_moment_eventually_bounded (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {a : ℝ} (ha : a < M.beta) :
    ∀ᶠ t in atTop, (∫ w, radius M w ^ a / t ^ a ∂tailLaw M t) ≤
      M.beta / (M.beta - a) + 1 := by
  exact ((tendsto_order.mp (conditional_power_moment_tendsto M hRV ha)).2 _
    (by linarith)).mono fun _ h => h.le

-- @node: weightedAngularContrast_ae_extension
/-- Given [bounded covariates](hyp:hX), a [bounded continuous extension](hyp:H) that [agrees with the treatment contrast on the relevant covariates and directions](hyp:hH), and [a positive threshold](hyp:ht), [the weighted angular contrast agrees almost surely with that extension times the normalized radial power](goal). -/
lemma weightedAngularContrast_ae_extension (M : ExtremeModel q d)
    (hX : CovariateBounded M)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (hH : ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
      H (x, s) = M.g x true s - M.g x false s)
    {t : ℝ} (ht : 0 < t) :
    weightedAngularContrast M t =ᵐ[tailLaw M t]
      (fun w => H (M.X w, direction M w) * (radius M w ^ M.alpha / t ^ M.alpha)) := by
  have hx : ∀ᵐ w ∂tailLaw M t, l1Norm (M.X w) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  filter_upwards [hx, ae_cond_mem (μ := M.mu)
    (measurableSet_lt measurable_const (measurable_radius M))] with w hwX hw
  dsimp [weightedAngularContrast]
  rw [hH _ hwX _ (direction_mem_positiveSphere M (ht.trans hw))]

-- @node: weightedAngularContrast_eventually_integrable
/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), and [the homogeneity exponent is below the tail index](hyp:hAlpha), then [the weighted angular contrast is integrable under all sufficiently extreme conditional laws](goal). -/
lemma weightedAngularContrast_eventually_integrable (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hAlpha : M.alpha < M.beta) :
    ∀ᶠ t in atTop, Integrable (weightedAngularContrast M t) (tailLaw M t) := by
  obtain ⟨H, hH⟩ := angular_contrast_bounded_extension M hHom
  filter_upwards [conditional_radial_power_integrable M hRV hAlpha,
    eventually_gt_atTop (0 : ℝ)] with t hint ht
  have heq := weightedAngularContrast_ae_extension M hX H hH ht
  apply Integrable.congr _ heq.symm
  apply Integrable.mono' (hint.const_mul ‖H‖)
  · apply Measurable.aestronglyMeasurable
    have hXm := M.measurable_X
    fun_prop
  · filter_upwards [scaled_radius_ge_one_tailLaw M ht] with w hw
    have hr : 0 ≤ radius M w := by
      have := (le_div_iff₀ ht).mp hw
      linarith
    rw [norm_mul, Real.norm_eq_abs (radius M w ^ M.alpha / t ^ M.alpha),
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg ht.le _))]
    exact mul_le_mul_of_nonneg_right (H.norm_coe_le_norm _)
      (div_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg ht.le _))

-- @node: weightedAngularContrast_power_bound
/-- Given [bounded covariates](hyp:hX), a [bounded continuous extension](hyp:H) that [matches the treatment contrast where needed](hyp:hH), a [positive threshold](hyp:ht), and [a nonnegative power](hyp:hp), [the powered absolute weighted angular contrast is almost surely bounded by the extension norm times the normalized radial power](goal). -/
lemma weightedAngularContrast_power_bound (M : ExtremeModel q d)
    (hX : CovariateBounded M)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (hH : ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
      H (x, s) = M.g x true s - M.g x false s)
    {t p : ℝ} (ht : 0 < t) (hp : 0 ≤ p) :
    ∀ᵐ w ∂tailLaw M t, |weightedAngularContrast M t w| ^ p ≤
      ‖H‖ ^ p * (radius M w ^ (M.alpha * p) / t ^ (M.alpha * p)) := by
  filter_upwards [weightedAngularContrast_ae_extension M hX H hH ht,
    scaled_radius_ge_one_tailLaw M ht] with w heq hw
  have hr : 0 ≤ radius M w := by
    have := (le_div_iff₀ ht).mp hw
    linarith
  rw [heq, abs_mul, abs_of_nonneg
    (div_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg ht.le _)),
    Real.mul_rpow (abs_nonneg _) (by positivity),
    ← Real.div_rpow hr ht.le, ← Real.rpow_mul (div_nonneg hr ht.le)]
  rw [Real.div_rpow hr ht.le]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.rpow_le_rpow (abs_nonneg _) _ hp
  simpa only [Real.norm_eq_abs] using H.norm_coe_le_norm (M.X w, direction M w)

-- @node: weightedAngularContrast_power_eventually_integrable
/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), [the requested power is nonnegative](hyp:hp), and [its homogeneity-scaled value is below the tail index](hyp:hgap), then [the corresponding power of the weighted angular contrast is eventually integrable](goal). -/
lemma weightedAngularContrast_power_eventually_integrable (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) {p : ℝ}
    (hp : 0 ≤ p) (hgap : M.alpha * p < M.beta) :
    ∀ᶠ t in atTop, Integrable (fun w => |weightedAngularContrast M t w| ^ p)
      (tailLaw M t) := by
  obtain ⟨H, hH⟩ := angular_contrast_bounded_extension M hHom
  filter_upwards [conditional_radial_power_integrable M hRV hgap,
    eventually_gt_atTop (0 : ℝ)] with t hint ht
  apply Integrable.mono' (hint.const_mul (‖H‖ ^ p))
  · have heq := weightedAngularContrast_ae_extension M hX H hH ht
    have hmeas : Measurable (fun w =>
        |H (M.X w, direction M w) * (radius M w ^ M.alpha / t ^ M.alpha)| ^ p) := by
      have hXm := M.measurable_X
      fun_prop
    apply hmeas.aestronglyMeasurable.congr
    exact heq.mono fun w hw => by dsimp only; rw [hw]
  · simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using
        weightedAngularContrast_power_bound M hX H hH ht hp

-- @node: weightedAngularContrast_uniform_power_moment
/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), and [the homogeneity exponent is below the tail index](hyp:hAlpha), then [there are a power above one and a nonnegative constant giving eventual integrability and a uniform bound on that power moment of the weighted angular contrast](goal). -/
lemma weightedAngularContrast_uniform_power_moment (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hAlpha : M.alpha < M.beta) :
    ∃ p C : ℝ, 1 < p ∧ 0 ≤ C ∧ ∀ᶠ t in atTop,
      Integrable (weightedAngularContrast M t) (tailLaw M t) ∧
      Integrable (fun w => |weightedAngularContrast M t w| ^ p) (tailLaw M t) ∧
      (∫ w, |weightedAngularContrast M t w| ^ p ∂tailLaw M t) ≤ C := by
  have hex : ∃ p : ℝ, 1 < p ∧ M.alpha * p < M.beta := by
    by_cases ha : 0 < M.alpha
    · have hr : 1 < M.beta / M.alpha := (lt_div_iff₀ ha).mpr (by simpa using hAlpha)
      obtain ⟨p, hp, hp'⟩ := exists_between hr
      exact ⟨p, hp, by simpa only [mul_comm] using (lt_div_iff₀ ha).mp hp'⟩
    · exact ⟨2, by norm_num, by nlinarith [hRV.1]⟩
  obtain ⟨p, hp, hgap⟩ := hex
  obtain ⟨H, hH⟩ := angular_contrast_bounded_extension M hHom
  let C := ‖H‖ ^ p * (M.beta / (M.beta - M.alpha * p) + 1)
  refine ⟨p, C, hp, ?_, ?_⟩
  · dsimp [C]
    have hb := hRV.1
    have hg : 0 < M.beta - M.alpha * p := sub_pos.mpr hgap
    positivity
  · filter_upwards [weightedAngularContrast_eventually_integrable M hRV hX hHom hAlpha,
      weightedAngularContrast_power_eventually_integrable M hRV hX hHom (by linarith) hgap,
      conditional_radial_power_integrable M hRV hgap,
      conditional_power_moment_eventually_bounded M hRV hgap,
      eventually_gt_atTop (0 : ℝ)] with t hInt hPow hRad hBound ht
    refine ⟨hInt, hPow, ?_⟩
    calc
      _ ≤ ∫ w, ‖H‖ ^ p * (radius M w ^ (M.alpha * p) / t ^ (M.alpha * p))
          ∂tailLaw M t := integral_mono_ae hPow (hRad.const_mul _)
            (weightedAngularContrast_power_bound M hX H hH ht (by linarith))
      _ = ‖H‖ ^ p * (∫ w, radius M w ^ (M.alpha * p) / t ^ (M.alpha * p)
          ∂tailLaw M t) := integral_const_mul _ _
      _ ≤ C := mul_le_mul_of_nonneg_left hBound (by positivity)

-- @node: clip_error_le_power
/-- For [a positive clipping level](hyp:hB) and [a power greater than one](hyp:hp), [the error from clipping a real value to that level is bounded by the level's negative power factor times the value's power](goal). -/
lemma clip_error_le_power {z B p : ℝ} (hB : 0 < B) (hp : 1 < p) :
    |z - max (-B) (min B z)| ≤ B ^ (1 - p) * |z| ^ p := by
  by_cases hz : |z| ≤ B
  · obtain ⟨hlo, hhi⟩ := abs_le.mp hz
    rw [min_eq_right hhi, max_eq_right hlo, sub_self, abs_zero]
    positivity
  · have hBz : B ≤ |z| := (lt_of_not_ge hz).le
    have hzpos : 0 < |z| := hB.trans_le hBz
    have htail : |z| ≤ B ^ (1 - p) * |z| ^ p := by
      calc
        |z| = |z| ^ (1 - p) * |z| ^ p := by
          rw [← Real.rpow_add hzpos, sub_add_cancel, Real.rpow_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hB hBz (by linarith)) (by positivity)
    apply le_trans _ htail
    by_cases hhi : z ≤ B
    · have hlo : z < -B := by
        have hn := not_le.mp hz
        rcases le_total 0 z with hpos | hneg
        · rw [abs_of_nonneg hpos] at hn
          exact (hn.not_ge hhi).elim
        · rw [abs_of_nonpos hneg] at hn
          linarith
      rw [min_eq_right hhi, max_eq_left hlo.le, abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith : z ≤ 0)]
      linarith
    · have hhi' : B < z := lt_of_not_ge hhi
      rw [min_eq_left hhi'.le, max_eq_right (by linarith),
        abs_of_nonneg (by linarith), abs_of_pos (hB.trans hhi')]
      linarith

-- @node: integrable_clip
/-- For a probability measure, [an integrable real-valued function](hyp:hf), and [a nonnegative clipping level](hyp:hB), [clipping the function at that level remains integrable](goal). -/
lemma integrable_clip {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) {B : ℝ} (hB : 0 ≤ B) :
    Integrable (fun w => max (-B) (min B (f w))) μ := by
  apply Integrable.mono' (integrable_const B)
  · have hc : Continuous (fun z : ℝ => max (-B) (min B z)) := by fun_prop
    exact hc.comp_aestronglyMeasurable hf.aestronglyMeasurable
  · apply Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

-- @node: integral_clip_error_le_power_moment
/-- For a probability measure, [an integrable function](hyp:hf), [a positive clipping level](hyp:hB), [a power greater than one](hyp:hp), and [an integrable power transform](hyp:hPow), [the difference between the original and clipped averages is bounded by the clipping factor times the power moment](goal). -/
lemma integral_clip_error_le_power_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    {B p : ℝ} (hB : 0 < B) (hp : 1 < p)
    (hPow : Integrable (fun w => |f w| ^ p) μ) :
    |(∫ w, f w ∂μ) - ∫ w, max (-B) (min B (f w)) ∂μ| ≤
      B ^ (1 - p) * (∫ w, |f w| ^ p ∂μ) := by
  rw [← integral_sub hf (integrable_clip μ hf hB.le)]
  have hbound : ∀ᵐ w ∂μ, ‖f w - max (-B) (min B (f w))‖ ≤
      B ^ (1 - p) * |f w| ^ p := by
    exact Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs] using clip_error_le_power (z := f w) hB hp
  have hnorm := norm_integral_le_of_norm_le (hPow.const_mul (B ^ (1 - p))) hbound
  simpa only [Real.norm_eq_abs, integral_const_mul] using hnorm

/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), [the homogeneity exponent is below the tail index](hyp:hAlpha), and [the requested error tolerance is positive](hyp:hε), then [there are positive clipping and tail thresholds after which clipping the weighted angular contrast changes its conditional average by at most that tolerance](goal). -/
-- @node: weightedAngularContrast_uniform_truncation
lemma weightedAngularContrast_uniform_truncation (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hAlpha : M.alpha < M.beta)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B₀ t₀ : ℝ, 0 < B₀ ∧ 0 < t₀ ∧ ∀ B ≥ B₀, ∀ t ≥ t₀,
      |(∫ w, weightedAngularContrast M t w ∂tailLaw M t) -
        ∫ w, max (-B) (min B (weightedAngularContrast M t w)) ∂tailLaw M t| ≤ ε := by
  obtain ⟨p, C, hp, hC, hMom⟩ :=
    weightedAngularContrast_uniform_power_moment M hRV hX hHom hAlpha
  have hlim : Tendsto (fun B : ℝ => B ^ (1 - p) * C) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < p - 1)).mul_const C
    simpa only [neg_sub, zero_mul] using h
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 ε hε)
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.mp hMom
  refine ⟨max 1 B₁, max 1 t₁, by positivity, by positivity, ?_⟩
  intro B hB t ht
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity : 0 < max (1 : ℝ) B₁) hB
  have hm := ht₁ t ((le_max_right _ _).trans ht)
  let := tailLaw_probability M hRV t
  calc
    _ ≤ B ^ (1 - p) * (∫ w, |weightedAngularContrast M t w| ^ p ∂tailLaw M t) :=
      integral_clip_error_le_power_moment (tailLaw M t) hm.1 hBpos hp hm.2.1
    _ ≤ B ^ (1 - p) * C := mul_le_mul_of_nonneg_left hm.2.2 (by positivity)
    _ ≤ ε := (hB₁ B ((le_max_right _ _).trans hB)).le

-- @node: measurable_regressionContrast
/-- If [the regression is a measurable conditional-mean version](hyp:hMean), then [the normalized regression contrast is measurable](goal). -/
@[fun_prop] lemma measurable_regressionContrast (M : ExtremeModel q d)
    (hMean : ConditionalMeanVersion M) (t : ℝ) : Measurable (regressionContrast M t) := by
  first | fun_prop | skip
  have h1 : Measurable (fun w => M.f (M.X w) true (M.U w)) :=
    hMean.1.comp (M.measurable_X.prodMk (measurable_const.prodMk M.measurable_U))
  have h0 : Measurable (fun w => M.f (M.X w) false (M.U w)) :=
    hMean.1.comp (M.measurable_X.prodMk (measurable_const.prodMk M.measurable_U))
  exact (h1.sub h0).div_const _

-- @node: regressionContrast_eventually_integrable
/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), [the regression is a measurable conditional-mean version](hyp:hMean), and [the homogeneity exponent is below the tail index](hyp:hAlpha), then [the normalized regression contrast is eventually integrable under the conditional tail laws](goal). -/
lemma regressionContrast_eventually_integrable (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    (hAlpha : M.alpha < M.beta) :
    ∀ᶠ t in atTop, Integrable (regressionContrast M t) (tailLaw M t) := by
  filter_upwards [weightedAngularContrast_eventually_integrable M hRV hX hHom hAlpha,
    conditional_radial_power_integrable M hRV hAlpha,
    eBar_eventually_bddAbove M hHom, eventually_gt_atTop (0 : ℝ)]
      with t hwInt hrInt hb ht
  have hx : ∀ᵐ w ∂tailLaw M t, l1Norm (M.X w) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  have hErr : Integrable (fun w => regressionContrast M t w - weightedAngularContrast M t w)
      (tailLaw M t) := by
    apply Integrable.mono' (hrInt.const_mul (2 * eBar M t))
    · exact (measurable_regressionContrast M hMean t).aestronglyMeasurable.sub
        hwInt.aestronglyMeasurable
    · filter_upwards [hx, ae_cond_mem (μ := M.mu)
        (measurableSet_lt measurable_const (measurable_radius M))] with w hwX hw
      simpa only [regressionContrast, weightedAngularContrast, Real.norm_eq_abs] using
        homogeneity_weighted_contrast_tail_bound M hHom ht hb w hwX hw
  apply (hErr.add hwInt).congr
  exact Eventually.of_forall fun w => sub_add_cancel _ _

-- @node: regression_weighted_integral_difference_tendsto_zero
/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), [the regression is a measurable conditional-mean version](hyp:hMean), and [the homogeneity exponent is below the tail index](hyp:hAlpha), then [the difference between the regression-contrast and weighted-angular-contrast averages converges to zero](goal). -/
lemma regression_weighted_integral_difference_tendsto_zero (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    (hAlpha : M.alpha < M.beta) :
    Tendsto (fun t => (∫ w, regressionContrast M t w ∂tailLaw M t) -
      ∫ w, weightedAngularContrast M t w ∂tailLaw M t) atTop (𝓝 0) := by
  apply (homogeneity_integrated_error_tendsto_zero M hRV hX hHom hAlpha).congr'
  filter_upwards [regressionContrast_eventually_integrable M hRV hX hHom hMean hAlpha,
    weightedAngularContrast_eventually_integrable M hRV hX hHom hAlpha] with t hr hw
  exact integral_sub hr hw

-- @node: regression_integral_tendsto_of_weighted
/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), [the regression is a measurable conditional-mean version](hyp:hMean), [the homogeneity exponent is below the tail index](hyp:hAlpha), and [the weighted angular-contrast average converges to the stated limit](hyp:hWeighted), then [the regression-contrast average converges to that same limit](goal). -/
lemma regression_integral_tendsto_of_weighted (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    (hAlpha : M.alpha < M.beta) {l : ℝ}
    (hWeighted : Tendsto (fun t => ∫ w, weightedAngularContrast M t w ∂tailLaw M t)
      atTop (𝓝 l)) :
    Tendsto (fun t => ∫ w, regressionContrast M t w ∂tailLaw M t) atTop (𝓝 l) := by
  have h := (regression_weighted_integral_difference_tendsto_zero M hRV hX hHom hMean
    hAlpha).add hWeighted
  simpa only [sub_add_cancel, zero_add] using h

end Papers.TbsExtremeEffects
