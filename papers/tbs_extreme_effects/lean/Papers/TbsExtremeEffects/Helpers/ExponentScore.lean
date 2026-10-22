module
public import Papers.TbsExtremeEffects.Helpers.ExponentError
public import Papers.TbsExtremeEffects.Helpers.HomogeneityError
public import Papers.TbsExtremeEffects.Helpers.ScoreMoments

/-! The fitted-exponent contribution to the conditional DR score mean. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

/-- If [the base is at least one](hyp:hr) and [the exponent error is bounded in absolute value by a nonnegative margin](hyp:hb), then [the absolute power error is no larger than the radius-power increment at that margin](goal).

@node: abs_rpow_sub_one_le_increment -/
lemma abs_rpow_sub_one_le_increment {r b a : ℝ} (hr : 1 ≤ r) (hb : |b| ≤ a) :
    |r ^ b - 1| ≤ r ^ a - 1 := by
  have ha : 0 ≤ a := (abs_nonneg b).trans hb
  have hra : 1 ≤ r ^ a := Real.one_le_rpow hr ha
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  have hu := Real.rpow_le_rpow_of_exponent_le hr hhi
  have hl := Real.rpow_le_rpow_of_exponent_le hr hlo
  rw [Real.rpow_neg (by linarith : 0 ≤ r)] at hl
  apply abs_le.mpr
  constructor
  · have hinv : 1 - (r ^ a)⁻¹ ≤ r ^ a - 1 := by
      have hpos : 0 < r ^ a := lt_of_lt_of_le zero_lt_one hra
      have hdiv : 2 - r ^ a ≤ (r ^ a)⁻¹ := by
        rw [inv_eq_one_div]
        apply (le_div_iff₀ hpos).mpr
        nlinarith [sq_nonneg (r ^ a - 1)]
      linarith
    linarith
  · linarith

/-- If [the overlap constant is positive](hyp:hc), [the true propensity lies between zero and one](hyp:hp,hp1), [both fitted treatment probabilities are at least the overlap constant](hyp:hph,hph1), and [both regression values are bounded by the same envelope](hyp:hf1,hf0), then [the absolute propensity-weighted regression contrast is bounded by twice that envelope divided by the overlap constant](goal).

@node: propensity_weighted_regression_bound -/
lemma propensity_weighted_regression_bound {p ph f1 f0 c G : ℝ}
    (hc : 0 < c) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hph : c ≤ ph) (hph1 : c ≤ 1 - ph)
    (hf1 : |f1| ≤ G) (hf0 : |f0| ≤ G) :
    |p / ph * f1 - (1 - p) / (1 - ph) * f0| ≤ 2 * G / c := by
  have hG : 0 ≤ G := (abs_nonneg f1).trans hf1
  have h1 : 0 ≤ p / ph := div_nonneg hp (hc.trans_le hph).le
  have h0 : 0 ≤ (1 - p) / (1 - ph) :=
    div_nonneg (sub_nonneg.mpr hp1) (hc.trans_le hph1).le
  have hw1 : p / ph ≤ 1 / c := div_le_div₀ (by norm_num) hp1 hc hph
  have hw0 : (1 - p) / (1 - ph) ≤ 1 / c :=
    div_le_div₀ (by norm_num) (by linarith) hc hph1
  calc
    _ ≤ |p / ph * f1| + |(1 - p) / (1 - ph) * f0| := abs_sub _ _
    _ = p / ph * |f1| + (1 - p) / (1 - ph) * |f0| := by
      rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h0]
    _ ≤ (1 / c) * G + (1 / c) * G :=
      add_le_add (mul_le_mul hw1 hf1 (abs_nonneg _) (by positivity))
        (mul_le_mul hw0 hf0 (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- If [the model is asymptotically homogeneous](hyp:hHom), [the regression envelope is bounded by the supplied constant](hyp:hG), [the threshold is positive](hyp:ht), [the tail envelope is bounded above beyond that threshold](hyp:hb), [the covariate lies in its bounded domain](hyp:hx), and [the observation exceeds the threshold](hyp:hw), then [the normalized realized regression is bounded by the envelope constant plus the tail approximation error](goal).

@node: normalized_regression_tail_bound -/
lemma normalized_regression_tail_bound (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) {C t : ℝ} (hG : GBound M C)
    (ht : 0 < t) (hb : BddAbove (M.e '' Set.Ici t))
    (w : M.Om) (hx : l1Norm (M.X w) ≤ M.R) (hw : t < radius M w) (a : Bool) :
    |M.f (M.X w) a (M.U w) / radius M w ^ M.alpha| ≤ C + eBar M t := by
  have h := homogeneity_at_realized_radius M hHom w a hx (ht.trans hw)
  have hg := hG.2 _ hx a _ (direction_mem_positiveSphere M (ht.trans hw))
  calc
    _ ≤ |M.f (M.X w) a (M.U w) / radius M w ^ M.alpha -
        M.g (M.X w) a (direction M w)| + |M.g (M.X w) a (direction M w)| :=
      by
        simpa only [sub_zero] using (abs_sub_le
          (M.f (M.X w) a (M.U w) / radius M w ^ M.alpha)
          (M.g (M.X w) a (direction M w)) 0)
    _ ≤ M.e (radius M w) + C := add_le_add h hg
    _ ≤ C + eBar M t := by linarith [e_le_eBar M hb hw.le]

/-- If [the noise tail is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the regression is bounded by the given envelope](hyp:hG), [the maximum exponent error is positive](hyp:ha0), and [it is below the tail index](hyp:ha0beta), then [there is a threshold after which every experiment with estimated overlap, even sample size, and exponent error within that range has its conditional DR exponent contribution bounded by the displayed explicit expression](goal).

@node: dr_exponent_mean_explicit_bound -/
lemma dr_exponent_mean_explicit_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) {C a0 : ℝ} (hG : GBound M C)
    (ha0 : 0 < a0) (ha0beta : a0 < M.beta) :
    ∃ T : ℝ, 1 ≤ T ∧
      ∀ t ≥ T, ∀ (E : NeteExperiment M) (c : ℝ), EstimatedOverlap E c →
      ∀ n, EvenSampleSize n → ∀ w : E.Om, ∀ a : ℝ, 0 ≤ a → a ≤ a0 →
      |M.alpha - E.alphaHat n w| ≤ a →
      |∫ v, (M.p (M.X v) / E.pHat n w (M.X v) *
          (M.f (M.X v) true (M.U v) / radius M v ^ M.alpha) -
        (1 - M.p (M.X v)) / (1 - E.pHat n w (M.X v)) *
          (M.f (M.X v) false (M.U v) / radius M v ^ M.alpha)) *
        (radius M v ^ (M.alpha - E.alphaHat n w) - 1) ∂tailLaw M t| ≤
        (2 * (C + eBar M t) / c) * (t ^ a - 1 + (4 / (M.beta - a0)) * a * t ^ a) := by
  obtain ⟨T, hT, hPower⟩ := tail_power_increment_explicit_bound M hRV ha0 ha0beta
  obtain ⟨T', hT'⟩ := eventually_atTop.mp (eBar_eventually_bddAbove M hHom)
  refine ⟨max T T', hT.trans (le_max_left _ _), ?_⟩
  intro t ht E c hOverlap n hn w a ha haa0 hErr
  have htT := (le_max_left T T').trans ht
  have htpos : 0 < t := zero_lt_one.trans_le (hT.trans htT)
  have hb := hT' t ((le_max_right T T').trans ht)
  have hGpos : 0 ≤ C + eBar M t := add_nonneg hG.1 (eBar_nonneg M hHom htpos hb)
  have hconst : 0 ≤ 2 * (C + eBar M t) / c := by
    exact div_nonneg (mul_nonneg (by norm_num) hGpos) hOverlap.1.le
  obtain ⟨hint, hmoment⟩ := hPower t htT a ha haa0
  have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  have hbound : ∀ᵐ v ∂tailLaw M t,
      ‖(M.p (M.X v) / E.pHat n w (M.X v) *
          (M.f (M.X v) true (M.U v) / radius M v ^ M.alpha) -
        (1 - M.p (M.X v)) / (1 - E.pHat n w (M.X v)) *
          (M.f (M.X v) false (M.U v) / radius M v ^ M.alpha)) *
        (radius M v ^ (M.alpha - E.alphaHat n w) - 1)‖ ≤
        (2 * (C + eBar M t) / c) * (radius M v ^ a - 1) := by
    filter_upwards [hx, ae_cond_mem (μ := M.mu)
      (measurableSet_lt measurable_const (measurable_radius M))] with v hv hw
    have hr : 1 ≤ radius M v := (hT.trans htT).trans hw.le
    have hp := M.p_range (M.X v)
    have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
    have hf := normalized_regression_tail_bound M hHom hG htpos hb v hv hw
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul
      (propensity_weighted_regression_bound hOverlap.1 hp.1 hp.2 hph.1
        (by linarith [hph.2]) (hf true) (hf false))
      (abs_rpow_sub_one_le_increment hr hErr) (abs_nonneg _) hconst
  have hnorm := norm_integral_le_of_norm_le
    (hint.const_mul (2 * (C + eBar M t) / c)) hbound
  rw [Real.norm_eq_abs, integral_const_mul] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left hmoment hconst)

/-- If [the noise tail is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the regression is bounded by the given envelope](hyp:hG), [the maximum exponent error is positive](hyp:ha0), and [it is below the tail index](hyp:ha0beta), then [positive uniform constants bound the conditional DR exponent contribution for all sufficiently high thresholds and all admissible experiments and exponent errors](goal).

@node: dr_exponent_mean_bound -/
lemma dr_exponent_mean_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) {C a0 : ℝ} (hG : GBound M C)
    (ha0 : 0 < a0) (ha0beta : a0 < M.beta) :
    ∃ K T : ℝ, 0 < K ∧ 1 ≤ T ∧
      ∀ t ≥ T, ∀ (E : NeteExperiment M) (c : ℝ), EstimatedOverlap E c →
      ∀ n, EvenSampleSize n → ∀ w : E.Om, ∀ a : ℝ, 0 ≤ a → a ≤ a0 →
      |M.alpha - E.alphaHat n w| ≤ a →
      |∫ v, (M.p (M.X v) / E.pHat n w (M.X v) *
          (M.f (M.X v) true (M.U v) / radius M v ^ M.alpha) -
        (1 - M.p (M.X v)) / (1 - E.pHat n w (M.X v)) *
          (M.f (M.X v) false (M.U v) / radius M v ^ M.alpha)) *
        (radius M v ^ (M.alpha - E.alphaHat n w) - 1) ∂tailLaw M t| ≤
        (2 * (C + eBar M t) / c) * (t ^ a - 1 + K * a * t ^ a) := by
  obtain ⟨T, hT, hbound⟩ := dr_exponent_mean_explicit_bound M hRV hX hHom hG ha0 ha0beta
  exact ⟨4 / (M.beta - a0), T, by positivity, hT, hbound⟩

end Papers.TbsExtremeEffects
