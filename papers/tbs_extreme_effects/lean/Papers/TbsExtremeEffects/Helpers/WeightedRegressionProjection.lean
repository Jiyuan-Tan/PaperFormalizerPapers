module
public import Papers.TbsExtremeEffects.Helpers.TailRegressionProjection
public import Papers.TbsExtremeEffects.Helpers.DRAugmentation

/-! Treatment-weighted identities for the projected population regression. -/

public section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {q d : ℕ}

-- @node: treatment_weighted_regression_projection
/-- If [the noise is regularly varying](hyp:hRV), [noise is independent](hyp:hNoise), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), [the regression is a measurable conditional-mean version](hyp:hMean), [the regression bound holds](hyp:hG), [the threshold is positive](hyp:ht), [the tail envelope is bounded above](hyp:hb), [the regression from covariates, treatment, and direction to a real value is measurable](hyp:hreg), [it is a conditional projection of the normalized outcome](hyp:hProjection), [the weight from covariates and direction to a real value is measurable](hyp:hW), [the normalized outcome section is integrable after weighting](hyp:hf), and [the fitted regression section is integrable after weighting](hyp:hr), then [the treatment-probability-weighted fitted-regression average equals the corresponding normalized-outcome average](goal). -/
lemma treatment_weighted_regression_projection (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) {C t : ℝ} (hG : GBound M C)
    (ht : 0 < t) (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (hreg : Measurable reg)
    (hProjection : (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[tailLaw M t]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) | MeasurableSpace.comap
          (fun v => (M.X v, M.D v, direction M v)) inferInstance])
    (W : ((Fin q → ℝ) × (Fin d → ℝ)) → ℝ) (hW : Measurable W) (a : Bool)
    (hf : Integrable (fun v => W (M.X v, direction M v) *
      (M.f (M.X v) a (M.U v) / radius M v ^ M.alpha)) (tailLaw M t))
    (hr : Integrable (fun v => W (M.X v, direction M v) *
      reg (M.X v, a, direction M v)) (tailLaw M t)) :
    (∫ v, W (M.X v, direction M v) * reg (M.X v, a, direction M v) *
      (if a then M.p (M.X v) else 1 - M.p (M.X v)) ∂tailLaw M t) =
    ∫ v, W (M.X v, direction M v) *
      (M.f (M.X v) a (M.U v) / radius M v ^ M.alpha) *
      (if a then M.p (M.X v) else 1 - M.p (M.X v)) ∂tailLaw M t := by
  let I : M.Om → ℝ := ({v | M.D v = a}).indicator (fun _ => (1 : ℝ))
  let H : M.Om → ℝ := fun v => W (M.X v, direction M v) * I v
  have hIm : MeasurableSet {v | M.D v = a} :=
    M.measurable_D (measurableSet_singleton a)
  have hH : Measurable[MeasurableSpace.comap
      (fun v => (M.X v, M.D v, direction M v)) inferInstance] H := by
    have hz : Measurable[MeasurableSpace.comap
      (fun v => (M.X v, M.D v, direction M v)) inferInstance]
      (fun v => (M.X v, M.D v, direction M v)) := Measurable.of_comap_le le_rfl
    have hI : Measurable[MeasurableSpace.comap
      (fun v => (M.X v, M.D v, direction M v)) inferInstance] I :=
      measurable_const.indicator (hz.snd.fst (measurableSet_singleton a))
    exact (hW.comp (hz.fst.prodMk hz.snd.snd)).mul hI
  have heqf : (fun v => H v * (M.f (M.X v) (M.D v) (M.U v) /
      radius M v ^ M.alpha)) =
      ({v | M.D v = a}).indicator (fun v => W (M.X v, direction M v) *
        (M.f (M.X v) a (M.U v) / radius M v ^ M.alpha)) := by
    funext v
    by_cases hd : M.D v = a <;> simp [H, I, hd]
  have hproj := normalized_projection_weighted_integral M hRV hX hHom hMean
    hG ht hb reg hProjection H hH (by rw [heqf]; exact hf.indicator hIm)
  have hx : Measurable[sigmaXU M] (fun v => (M.X v, M.U v)) :=
    Measurable.of_comap_le le_rfl
  have hdir : Measurable[sigmaXU M] (direction M) := by
    first | fun_prop | skip
    let : MeasurableSpace M.Om := sigmaXU M
    unfold direction radius
    apply measurable_pi_iff.mpr
    intro i
    exact ((measurable_pi_apply i).comp hx.snd).div
      (measurable_l1Norm.comp hx.snd)
  have hwm : Measurable[sigmaXU M] (fun v => W (M.X v, direction M v)) :=
    hW.comp (hx.fst.prodMk hdir)
  have hrm : Measurable[sigmaXU M] (fun v => reg (M.X v, a, direction M v)) :=
    hreg.comp (hx.fst.prodMk (measurable_const.prodMk hdir))
  have hfm : Measurable[sigmaXU M] (fun v => M.f (M.X v) a (M.U v) /
      radius M v ^ M.alpha) := by
    exact (hMean.1.comp (hx.fst.prodMk (measurable_const.prodMk hx.snd))).div
      ((measurable_l1Norm.comp hx.snd).pow_const M.alpha)
  have hri : Integrable (fun v => W (M.X v, direction M v) *
      reg (M.X v, a, direction M v) * I v) (tailLaw M t) := by
    apply (hr.indicator hIm).congr
    apply Eventually.of_forall
    intro v
    by_cases hd : M.D v = a <;> simp [I, hd]
  have hfi : Integrable (fun v => W (M.X v, direction M v) *
      (M.f (M.X v) a (M.U v) / radius M v ^ M.alpha) * I v) (tailLaw M t) := by
    apply (hf.indicator hIm).congr
    apply Eventually.of_forall
    intro v
    by_cases hd : M.D v = a <;> simp [I, hd]
  have htr := treatment_weighted_integral_tail M hRV hNoise t a _ (hwm.mul hrm) hri
  have htf := treatment_weighted_integral_tail M hRV hNoise t a _ (hwm.mul hfm) hfi
  simp only [Pi.mul_apply] at htr htf
  rw [← htr.2, ← htf.2]
  calc
    _ = ∫ v, H v * reg (M.X v, M.D v, direction M v) ∂tailLaw M t := by
      apply integral_congr_ae
      exact Eventually.of_forall fun v => by
        by_cases hd : M.D v = a <;> simp [H, I, hd, mul_assoc, mul_comm, mul_left_comm]
    _ = _ := hproj.2
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun v => by
        by_cases hd : M.D v = a <;> simp [H, I, hd, mul_assoc, mul_comm, mul_left_comm]

-- @node: normalized_regression_section_tail_integrable
/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), [the regression is a measurable conditional-mean version](hyp:hMean), [the regression bound holds](hyp:hG), [the threshold is positive](hyp:ht), and [the tail envelope is bounded above](hyp:hb), then [each treatment section of the normalized outcome regression is integrable under the conditional tail law](goal). -/
lemma normalized_regression_section_tail_integrable (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) (a : Bool) :
    Integrable (fun v => M.f (M.X v) a (M.U v) / radius M v ^ M.alpha)
      (tailLaw M t) := by
  let := tailLaw_probability M hRV t
  have hm : Measurable (fun v => M.f (M.X v) a (M.U v) / radius M v ^ M.alpha) := by
    first | fun_prop | skip
    exact (hMean.1.comp
    (M.measurable_X.prodMk (measurable_const.prodMk M.measurable_U))).div
      ((measurable_radius M).pow_const M.alpha)
  apply Integrable.of_bound hm.aestronglyMeasurable (C + eBar M t)
  have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  filter_upwards [hx, ae_cond_mem (μ := M.mu)
    (measurableSet_lt measurable_const (measurable_radius M))] with v hx hv
  simpa only [Real.norm_eq_abs] using
    normalized_regression_tail_bound M hHom hG ht hb v hx hv a

-- @node: fitted_treatment_weight_integrable
/-- Given [an experiment](hyp:E), [an even sample size](hyp:hn), [estimated overlap bounded away from zero](hyp:hOverlap), and [an integrable input function](hyp:hZ), [multiplying that function by the fitted treatment weight preserves integrability](goal). -/
lemma fitted_treatment_weight_integrable {M : ExtremeModel q d}
    (E : NeteExperiment M) {n : ℕ} (hn : EvenSampleSize n)
    {c t : ℝ} (hOverlap : EstimatedOverlap E c) (w : E.Om) (a : Bool)
    (Z : M.Om → ℝ) (hZ : Integrable Z (tailLaw M t)) :
    Integrable (fun v =>
      (if a then M.p (M.X v) else 1 - M.p (M.X v)) /
      (if a then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v)) * Z v)
      (tailLaw M t) := by
  have hp : Measurable (fun v => E.pHat n w (M.X v)) :=
    (E.pHat_training n).comp (measurable_const.prodMk M.measurable_X)
  have hmeas : Measurable (fun v =>
      (if a then M.p (M.X v) else 1 - M.p (M.X v)) /
      (if a then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v))) := by
    first | fun_prop | skip
    cases a
    · exact (measurable_const.sub (M.measurable_p.comp M.measurable_X)).div
        (measurable_const.sub hp)
    · exact (M.measurable_p.comp M.measurable_X).div hp
  apply hZ.bdd_mul hmeas.aestronglyMeasurable (c := 1 / c)
  apply Eventually.of_forall
  intro v
  have hpv := M.p_range (M.X v)
  have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
  have hnum : 0 ≤ (if a then M.p (M.X v) else 1 - M.p (M.X v)) ∧
      (if a then M.p (M.X v) else 1 - M.p (M.X v)) ≤ 1 := by
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith
  have hden : c ≤ (if a then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v)) := by
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith [hph.1, hph.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum.1
    (hOverlap.1.trans_le hden).le)]
  exact div_le_div₀ (by norm_num) hnum.2 hOverlap.1 hden

-- @node: fitted_propensity_regression_projection
/-- If [the noise is regularly varying](hyp:hRV), [noise is independent](hyp:hNoise), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), [the regression is a measurable conditional-mean version](hyp:hMean), [the sample size is even](hyp:hn), [estimated overlap is bounded away from zero](hyp:hOverlap), [the regression bound holds](hyp:hG), [the threshold is positive](hyp:ht), [the tail envelope is bounded above](hyp:hb), [the regression from covariates, treatment, and direction to a real value is measurable](hyp:hreg), [it is a conditional projection of the normalized outcome](hyp:hProjection), and [its chosen treatment section is integrable](hyp:hr), then [the fitted-propensity-weighted regression average equals the fitted-propensity-weighted normalized-outcome average](goal). -/
lemma fitted_propensity_regression_projection {M : ExtremeModel q d}
    (E : NeteExperiment M) (hRV : NoiseRegularlyVarying M)
    (hNoise : NoiseIndependent M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (hreg : Measurable reg)
    (hProjection : (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[tailLaw M t]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) | MeasurableSpace.comap
          (fun v => (M.X v, M.D v, direction M v)) inferInstance])
    (a : Bool) (hr : Integrable (fun v => reg (M.X v, a, direction M v))
      (tailLaw M t)) (w : E.Om) :
    (∫ v, (if a then M.p (M.X v) else 1 - M.p (M.X v)) /
      (if a then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v)) *
      reg (M.X v, a, direction M v) ∂tailLaw M t) =
    ∫ v, (if a then M.p (M.X v) else 1 - M.p (M.X v)) /
      (if a then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v)) *
      (M.f (M.X v) a (M.U v) / radius M v ^ M.alpha) ∂tailLaw M t := by
  let := tailLaw_probability M hRV t
  let W : ((Fin q → ℝ) × (Fin d → ℝ)) → ℝ := fun z =>
    (if a then E.pHat n w z.1 else 1 - E.pHat n w z.1)⁻¹
  have hp : Measurable (fun z : ((Fin q → ℝ) × (Fin d → ℝ)) => E.pHat n w z.1) :=
    (E.pHat_training n).comp (measurable_const.prodMk measurable_fst)
  have hW : Measurable W := by
    first | fun_prop | skip
    cases a
    · exact (measurable_const.sub hp).inv
    · exact hp.inv
  have hWbound : ∀ᵐ v ∂tailLaw M t, ‖W (M.X v, direction M v)‖ ≤ c⁻¹ := by
    apply Eventually.of_forall
    intro v
    have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
    have hden : c ≤ (if a then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v)) := by
      cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith [hph.1, hph.2]
    dsimp [W]
    rw [abs_of_pos (inv_pos.mpr (hOverlap.1.trans_le hden))]
    exact (inv_le_inv₀ (hOverlap.1.trans_le hden) hOverlap.1).mpr hden
  have hf := normalized_regression_section_tail_integrable M hRV hX hHom hMean hG ht hb a
  have hwmeas := hW.comp (M.measurable_X.prodMk (measurable_direction M))
  have heq := treatment_weighted_regression_projection M hRV hNoise hX hHom hMean
    hG ht hb reg hreg hProjection W hW a
    (hf.bdd_mul hwmeas.aestronglyMeasurable hWbound)
    (hr.bdd_mul hwmeas.aestronglyMeasurable hWbound)
  simpa only [W, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using heq

-- @node: dr_regression_average_of_normalized_projection
/-- If [the noise is regularly varying](hyp:hRV), [noise is independent](hyp:hNoise), [covariates are bounded](hyp:hX), [the regression is asymptotically homogeneous](hyp:hHom), [the regression is a measurable conditional-mean version](hyp:hMean), [the sample size is even](hyp:hn), [estimated overlap is bounded away from zero](hyp:hOverlap), [the regression bound holds](hyp:hG), [the threshold is at least one](hyp:ht), [the tail envelope is bounded above](hyp:hb), [the regression from covariates, treatment, and direction to a real value is measurable](hyp:hreg), [it is a conditional projection of the normalized outcome](hyp:hProjection), [both treatment sections are integrable](hyp:hr), [the fitted augmentation is integrable in both sections](hyp:hg), [the fitted exponent is close enough to the true exponent](hyp:hErr), and [the required radial error transform is integrable](hyp:hRad), then [the inverse-probability fitted mean plus its augmentation average equals the doubly robust fitted-regression average](goal). -/
lemma dr_regression_average_of_normalized_projection {M : ExtremeModel q d}
    (E : NeteExperiment M) (hRV : NoiseRegularlyVarying M)
    (hNoise : NoiseIndependent M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t a : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 1 ≤ t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (hreg : Measurable reg)
    (hProjection : (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[tailLaw M t]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) | MeasurableSpace.comap
          (fun v => (M.X v, M.D v, direction M v)) inferInstance])
    (hr : ∀ b : Bool, Integrable (fun v => reg (M.X v, b, direction M v)) (tailLaw M t))
    (w : E.Om)
    (hg : ∀ b : Bool, Integrable (fun v => E.gHat n w (M.X v) b (direction M v))
      (tailLaw M t))
    (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t)) :
    (∫ v, ipwFittedMeanIntegrand E n w v ∂tailLaw M t) +
      (∫ v, drAugmentationMean E n w v ∂tailLaw M t) =
        ∫ v, drFittedRegressionMean E n reg w v ∂tailLaw M t := by
  have htpos := zero_lt_one.trans_le ht
  let Z : M.Om → ℝ := fun v =>
    M.p (M.X v) / E.pHat n w (M.X v) *
      (M.f (M.X v) true (M.U v) / radius M v ^ M.alpha) -
    (1 - M.p (M.X v)) / (1 - E.pHat n w (M.X v)) *
      (M.f (M.X v) false (M.U v) / radius M v ^ M.alpha)
  let R : M.Om → ℝ := fun v =>
    M.p (M.X v) / E.pHat n w (M.X v) * reg (M.X v, true, direction M v) -
    (1 - M.p (M.X v)) / (1 - E.pHat n w (M.X v)) * reg (M.X v, false, direction M v)
  have hf := fun b => normalized_regression_section_tail_integrable M hRV hX hHom hMean
    hG htpos hb b
  have hfi := fun b => fitted_treatment_weight_integrable E hn hOverlap w b _ (hf b)
  have hri := fun b => fitted_treatment_weight_integrable E hn hOverlap w b _ (hr b)
  have hgi := fun b => fitted_treatment_weight_integrable E hn hOverlap w b _ (hg b)
  have hZ : Integrable Z (tailLaw M t) := (hfi true).sub (hfi false)
  have hR : Integrable R (tailLaw M t) := (hri true).sub (hri false)
  have hAug : Integrable (drAugmentationMean E n w) (tailLaw M t) :=
    ((hg true).sub (hg false)).sub ((hgi true).sub (hgi false))
  have hExp := exponentMeanIntegrand_integrable E hX hHom hMean hn hOverlap hG ht hb
    w hErr hRad
  have hZeq : (∫ v, Z v ∂tailLaw M t) = ∫ v, R v ∂tailLaw M t := by
    have h1 := fitted_propensity_regression_projection E hRV hNoise hX hHom hMean hn
      hOverlap hG htpos hb reg hreg hProjection true (hr true) w
    have h0 := fitted_propensity_regression_projection E hRV hNoise hX hHom hMean hn
      hOverlap hG htpos hb reg hreg hProjection false (hr false) w
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h0
    have hf1 := hfi true
    have hf0 := hfi false
    have hr1 := hri true
    have hr0 := hri false
    simp only [Bool.false_eq_true, ↓reduceIte] at hf1 hf0 hr1 hr0
    dsimp [Z, R]
    rw [integral_sub hf1 hf0, integral_sub hr1 hr0, h1, h0]
  have hipw : ipwFittedMeanIntegrand E n w =ᵐ[tailLaw M t]
      (fun v => Z v + exponentMeanIntegrand E n w v) := by
    filter_upwards [ipw_fitted_mean_integrand_decomposition_ae E hn hOverlap htpos w] with v hv
    rw [hv]
    have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
    have hp0 := (hOverlap.1.trans_le hph.1).ne'
    have hp1 : 1 - E.pHat n w (M.X v) ≠ 0 := by linarith [hOverlap.1, hph.2]
    have hBias := ipw_conditional_bias_identity
      (p := M.p (M.X v))
      (m1 := M.f (M.X v) true (M.U v) / radius M v ^ M.alpha)
      (m0 := M.f (M.X v) false (M.U v) / radius M v ^ M.alpha) hp0 hp1
    dsimp [Z, ipwBiasIntegrand, normalizedRegressionContrast]
    rw [sub_div]
    linarith only [hBias]
  calc
    _ = (∫ v, Z v ∂tailLaw M t) + (∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t) +
        (∫ v, drAugmentationMean E n w v ∂tailLaw M t) := by
      rw [integral_congr_ae hipw, integral_add hZ hExp]
    _ = (∫ v, R v ∂tailLaw M t) + (∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t) +
        (∫ v, drAugmentationMean E n w v ∂tailLaw M t) := by rw [hZeq]
    _ = ∫ v, R v + exponentMeanIntegrand E n w v + drAugmentationMean E n w v
        ∂tailLaw M t := by
      rw [integral_add (show Integrable (fun v => R v + exponentMeanIntegrand E n w v)
        (tailLaw M t) from hR.add hExp) hAug, integral_add hR hExp]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun v => by
        dsimp [R, drAugmentationMean, drFittedRegressionMean]
        ring

end Papers.TbsExtremeEffects
