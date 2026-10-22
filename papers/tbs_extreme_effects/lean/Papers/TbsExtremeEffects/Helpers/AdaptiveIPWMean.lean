module
public import Papers.TbsExtremeEffects.Helpers.AdaptiveMean
public import Papers.TbsExtremeEffects.Helpers.IPWOutcomeMean

/-! Propensity and population mean bounds for the adaptive IPW threshold. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
variable {q d : ℕ} {M : ExtremeModel q d}

/-- Given [regularly varying noise](hyp:hRV), [independent noise](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional mean version](hyp:hMean), [an even sample](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression envelope](hyp:hG), [a threshold at least one](hyp:ht), [a bounded tail envelope](hyp:hb), [an antitone propensity rate](hyp:hRp), [the nuisance-event conditions](hyp:hNuisance), [a fitted tail-index error bound](hyp:hErr), [radial integrability](hyp:hRad), and [a finite second score moment](hyp:hLp), [the IPW mean admits its stated decomposition](goal).

@node: ipw_mean_decomposition_of_score_moment -/
lemma ipw_mean_decomposition_of_score_moment (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t eps a : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 1 ≤ t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w)
    (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t))
    (hLp : MemLp (score E .ipw n w) 2 (obsTailLaw M t)) :
    IpwMeanDecomposition E n t w := by
  let := obsTailLaw_probability M hRV t
  have hi := hLp.integrable (by norm_num)
  have hOutcome := ipw_outcome_score_mean_of_integrable E hRV hMean n t w hi
  have hIdentity := ipw_conditional_score_mean_of_outcome_score_mean E hRV hNoise
    hX hHom hMean hn hOverlap hG ht hb w hErr hRad hOutcome
  exact ipw_mean_decomposition_of_conditional_score_mean E hRV hX hHom hMean hn
    hOverlap hG ht hb Rp Rg Ralpha hRp reg w hNuisance hErr hRad hIdentity

/-- If [the propensity rate has order one half](hyp:hRp) and [the confidence argument is valid](hyp:hd), then [the same rate bound holds eventually at the training-half sample size](goal).

@node: propensity_rate_at_even_half -/
lemma propensity_rate_at_even_half {Rp : ℕ → ℝ → ℝ} {eps : ℝ}
    (hRp : RateTheta Rp (1 / 2)) (hd : ConfidenceDomain eps) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, EvenSampleSize n →
      0 ≤ Rp (n / 2) eps ∧
      Rp (n / 2) eps ≤ D * Real.log (1 / eps) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨D, hD, hRate⟩ := rateTheta_at_polynomial_count hRp (by norm_num)
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num) hd
  refine ⟨D, hD, ?_⟩
  filter_upwards [hRate] with n hn
  intro heven
  have hHalf : (1 / 2 : ℝ) * (n : ℝ) ^ (1 : ℝ) ≤ (n / 2 : ℕ) := by
    rw [even_sample_half_cast heven, Real.rpow_one]
    linarith
  simpa using hn (n / 2) hHalf

/-- Given [regularly varying noise](hyp:hRV), [independent noise](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional mean version](hyp:hMean), [an even sample](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression envelope](hyp:hG), [a threshold at least one](hyp:ht), [a bounded tail envelope](hyp:hb), [the IPW decomposition](hyp:hIdentity), [a bias bound](hyp:hBias), [a tail-index error bound](hyp:hErr), [radial integrability](hyp:hRad), and [a radial-moment bound](hyp:hMoment), [the IPW population score mean has the stated total error bound](goal).

@node: adaptive_ipw_mean_error_bound -/
lemma adaptive_ipw_mean_error_bound (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) {n : ℕ} (hn : EvenSampleSize n)
    {c C t a b z : ℝ} (hOverlap : EstimatedOverlap E c) (hG : GBound M C)
    (ht : 1 ≤ t) (hb : BddAbove (M.e '' Set.Ici t))
    (w : E.Om)
    (hIdentity : IpwMeanDecomposition E n t w)
    (hBias : |∫ v, ipwBiasIntegrand E n w v ∂tailLaw M t| ≤ b)
    (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t))
    (hMoment : (∫ v, radius M v ^ a - 1 ∂tailLaw M t) ≤ z) :
    |thresholdScoreMean E .ipw n t w - etaTarget M| ≤
      b + (2 * (C + eBar M t) / c) * z +
        (2 * eBar M t + 2 * M.L * angularW1 M t) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hconst : 0 ≤ 2 * (C + eBar M t) / c := by
    exact div_nonneg (mul_nonneg (by norm_num)
      (add_nonneg hG.1 (eBar_nonneg M hHom htpos hb))) hOverlap.1.le
  have hExp := (dr_exponent_integral_bound_by_radial_moment E hX hHom hn
    hOverlap hG ht hb w hErr hRad).trans
      (mul_le_mul_of_nonneg_left hMoment hconst)
  have hTarget := normalized_contrast_target_bound M hRV hX hHom hMean hG htpos hb
    (angularFactor_target_wasserstein_bound M hRV hNoise hX hHom htpos)
  change |(∫ v, score E .ipw n w v ∂obsTailLaw M t) - etaTarget M| ≤ _
  rw [hIdentity]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add hBias hExp) hTarget)

/-- Given [regularly varying noise](hyp:hRV), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [an even sample](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression envelope](hyp:hG), [a positive threshold](hyp:ht), [a bounded tail envelope](hyp:hb), and [an almost-everywhere propensity-error bound](hyp:hp), [the IPW bias integral is bounded by that error times the stated envelope](goal).

@node: ipw_bias_integral_bound_at_training_size -/
lemma ipw_bias_integral_bound_at_training_size (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) {n : ℕ} (hn : EvenSampleSize n)
    {c C t rp : ℝ} (hOverlap : EstimatedOverlap E c) (hG : GBound M C)
    (ht : 0 < t) (hb : BddAbove (M.e '' Set.Ici t)) (w : E.Om)
    (hp : ∀ᵐ x ∂(M.mu.map M.X), |M.p x - E.pHat n w x| ≤ rp) :
    |∫ v, ipwBiasIntegrand E n w v ∂tailLaw M t| ≤
      (2 * (C + eBar M t) / c) * rp := by
  let := tailLaw_probability M hRV t
  have hpTail : ∀ᵐ v ∂tailLaw M t, |M.p (M.X v) - E.pHat n w (M.X v)| ≤ rp :=
    cond_absolutelyContinuous.ae_le
    (ae_of_ae_map M.measurable_X.aemeasurable hp)
  have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  have hbound : ∀ᵐ v ∂tailLaw M t, ‖ipwBiasIntegrand E n w v‖ ≤
      (2 * (C + eBar M t) / c) * rp := by
    filter_upwards [hpTail, hx, ae_cond_mem (μ := M.mu)
      (measurableSet_lt measurable_const (measurable_radius M))] with v hpv hxv htv
    have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
    have hph' : c ≤ 1 - E.pHat n w (M.X v) := by linarith [hph.2]
    have hf := normalized_regression_tail_bound M hHom hG ht hb v hxv htv
    rw [Real.norm_eq_abs, ipwBiasIntegrand, ← ipw_conditional_bias_identity
      (hOverlap.1.trans_le hph.1).ne' (hOverlap.1.trans_le hph').ne']
    exact ipw_conditional_bias_bound hOverlap.1 hph.1 hph' hpv (hf true) (hf false)
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using norm_integral_le_of_norm_le_const hbound

/-- Given [regularly varying noise](hyp:hRV), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [estimated overlap](hyp:hOverlap), [a regression envelope](hyp:hG), [a half-order propensity rate](hyp:hRp), [a valid confidence domain](hyp:hd), [a positive lower band constant](hyp:hcm), and [positive band growth](hyp:hk), [a positive constant eventually bounds IPW bias uniformly over the threshold band](goal).

@node: adaptive_band_ipw_bias_rate -/
lemma adaptive_band_ipw_bias_rate (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) {Rp : ℕ → ℝ → ℝ}
    {C c delta cminus cplus : ℝ} {kappa : ℝ → ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C)
    (hRp : RateTheta Rp (1 / 2)) (hd : ConfidenceDomain (delta / 6))
    (hcm : 0 < cminus) (hk : 0 < kappa (gamma M)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, EvenSampleSize n → ∀ w,
      ∀ t ∈ thresholdBand M cminus cplus kappa n,
        (∀ᵐ x ∂(M.mu.map M.X), |M.p x - E.pHat n w x| ≤ Rp (n / 2) (delta / 6)) →
        |∫ v, ipwBiasIntegrand E n w v ∂tailLaw M t| ≤
          D * Real.log (6 / delta) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨D, hD, hRate⟩ := propensity_rate_at_even_half hRp hd
  let K := 2 * (C + 1) / c
  have hK : 0 < K := by dsimp [K]; positivity [hG.1, hOverlap.1]
  refine ⟨K * D, mul_pos hK hD, ?_⟩
  filter_upwards [hRate, adaptive_band_homogeneity_envelope M hHom
    (cplus := cplus) hcm hk] with n hn hEnvelope
  intro heven w t ht hp
  obtain ⟨ht1, hb, he0, he1⟩ := hEnvelope t ht
  have hcoef : 2 * (C + eBar M t) / c ≤ K := by
    apply div_le_div_of_nonneg_right _ hOverlap.1.le
    linarith
  have hr := hn heven
  have hBias := ipw_bias_integral_bound_at_training_size E hRV hX hHom heven
    hOverlap hG (zero_lt_one.trans_le ht1) hb w hp
  have htol : 1 / (delta / 6) = 6 / delta := by ring
  calc
    _ ≤ (2 * (C + eBar M t) / c) * Rp (n / 2) (delta / 6) := hBias
    _ ≤ K * Rp (n / 2) (delta / 6) := mul_le_mul_of_nonneg_right hcoef hr.1
    _ ≤ K * (D * Real.log (6 / delta) * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [← htol]
      exact mul_le_mul_of_nonneg_left hr.2 hK.le
    _ = _ := by ring

end Papers.TbsExtremeEffects
