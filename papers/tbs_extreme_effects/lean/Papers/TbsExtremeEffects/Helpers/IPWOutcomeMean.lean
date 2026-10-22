module
public import Papers.TbsExtremeEffects.Helpers.IPWMean
public import Papers.TbsExtremeEffects.Helpers.TailTreatment
public import Papers.TbsExtremeEffects.Helpers.OutcomeConditioning
public import Papers.TbsExtremeEffects.Helpers.ScoreMeasurability

/-! IPW treatment averaging after the outcome conditional-mean step. -/

@[expose] public section
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- Given [regularly varying noise](hyp:hRV), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional-mean version](hyp:hMean), [a regression bound](hyp:hG), [a threshold at least one](hyp:ht), [bounded tail error](hyp:hb), [an exponent-error bound](hyp:hErr), and [an integrable radial increment](hyp:hRad), [the fitted normalized regression for the treatment value `d` is tail-integrable](goal).
@node: fitted_normalized_regression_integrable -/
lemma fitted_normalized_regression_integrable (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) {n : ℕ} {C t a : ℝ}
    (hG : GBound M C) (ht : 1 ≤ t) (hb : BddAbove (M.e '' Set.Ici t))
    (w : E.Om) (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t)) (d : Bool) :
    Integrable (fun v => M.f (M.X v) d (M.U v) / radius M v ^ E.alphaHat n w)
      (tailLaw M t) := by
  let := tailLaw_probability M hRV t
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hpower : Integrable (fun v => radius M v ^ a) (tailLaw M t) := by
    have hi : Integrable (fun v => (radius M v ^ a - 1) + 1) (tailLaw M t) :=
      hRad.add (integrable_const (1 : ℝ))
    simpa only [sub_add_cancel] using hi
  apply Integrable.mono' (hpower.const_mul (C + eBar M t))
  · have hf : Measurable (fun v => M.f (M.X v) d (M.U v)) :=
      hMean.1.comp (M.measurable_X.prodMk (measurable_const.prodMk M.measurable_U))
    exact (hf.div ((measurable_radius M).pow_const (E.alphaHat n w))).aestronglyMeasurable
  · have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
      cond_absolutelyContinuous.ae_le hX.2
    filter_upwards [hx, ae_cond_mem (μ := M.mu)
      (measurableSet_lt measurable_const (measurable_radius M))] with v hxv hv
    have hr : 1 ≤ radius M v := ht.trans hv.le
    have hrpos : 0 < radius M v := zero_lt_one.trans_le hr
    have hbound := normalized_regression_tail_bound M hHom hG htpos hb v hxv hv d
    have hC : 0 ≤ C + eBar M t := (abs_nonneg _).trans hbound
    have hpow := Real.rpow_le_rpow_of_exponent_le hr ((le_abs_self _).trans hErr)
    have heq : M.f (M.X v) d (M.U v) / radius M v ^ E.alphaHat n w =
        (M.f (M.X v) d (M.U v) / radius M v ^ M.alpha) *
          radius M v ^ (M.alpha - E.alphaHat n w) := by
      rw [Real.rpow_sub hrpos]
      field_simp
    rw [Real.norm_eq_abs, heq, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hrpos _)]
    exact mul_le_mul hbound hpow (Real.rpow_nonneg hrpos.le _) hC

/-- [The extreme-value model](hyp:M), [experiment](hyp:E), [sample size](hyp:n), [tail threshold](hyp:t), and [training realization](hyp:w) define the [outcome-conditioned IPW score-mean identity](goal).
@node: IpwOutcomeScoreMean -/
def IpwOutcomeScoreMean (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) : Prop :=
  (∫ z, score E .ipw n w z ∂obsTailLaw M t) =
    ∫ v, if M.D v then
      (M.f (M.X v) true (M.U v) / radius M v ^ E.alphaHat n w) / E.pHat n w (M.X v)
    else -((M.f (M.X v) false (M.U v) / radius M v ^ E.alphaHat n w) /
      (1 - E.pHat n w (M.X v))) ∂tailLaw M t

/-- For [the extreme-value model](hyp:M) and [tail threshold](hyp:t), [the observed tail law is the pushforward of the population tail law through the observation map](goal).
@node: obsTailLaw_eq_map_tailLaw -/
lemma obsTailLaw_eq_map_tailLaw (M : ExtremeModel q d) (t : ℝ) :
    obsTailLaw M t = (tailLaw M t).map (observation M) := by
  have hm : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk
      (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  have hs : MeasurableSet {z : Obs q d | t < l1Norm z.2.2.2} :=
    measurableSet_lt measurable_const (by fun_prop)
  unfold obsTailLaw tailLaw ProbabilityTheory.cond
  rw [Measure.map_smul, Measure.map_apply hm hs, Measure.restrict_map hm hs]
  rfl

/-- Given [regularly varying noise](hyp:hRV), [a conditional-mean version](hyp:hMean), and [an integrable IPW score](hyp:hScore), [the outcome-conditioned IPW score-mean identity holds](goal).
@node: ipw_outcome_score_mean_of_integrable -/
lemma ipw_outcome_score_mean_of_integrable (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hMean : ConditionalMeanVersion M)
    (n : ℕ) (t : ℝ) (w : E.Om)
    (hScore : Integrable (score E .ipw n w) (obsTailLaw M t)) :
    IpwOutcomeScoreMean E n t w := by
  have hm : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk
      (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  let h : M.Om → ℝ := fun v => (radius M v ^ E.alphaHat n w)⁻¹ *
    ((if M.D v then (1 : ℝ) else 0) / E.pHat n w (M.X v) -
      (if M.D v then (0 : ℝ) else 1) / (1 - E.pHat n w (M.X v)))
  have hpair : Measurable[sigmaXDU M] (fun v => (M.X v, M.D v, M.U v)) :=
    Measurable.of_comap_le le_rfl
  have hh : Measurable[sigmaXDU M] h := by
    first | fun_prop | skip
    have hp : Measurable[sigmaXDU M] (fun v => E.pHat n w (M.X v)) :=
      (E.pHat_training n).comp (measurable_const.prodMk hpair.fst)
    have hr : Measurable[sigmaXDU M] (radius M) := measurable_l1Norm.comp hpair.snd.snd
    have h1 := (measurable_of_finite (fun a : Bool => if a then (1 : ℝ) else 0)).comp hpair.snd.fst
    have h0 := (measurable_of_finite (fun a : Bool => if a then (0 : ℝ) else 1)).comp hpair.snd.fst
    exact (hr.pow_const _).inv.mul ((h1.div hp).sub (h0.div (measurable_const.sub hp)))
  have hrep : (fun v => score E .ipw n w (observation M v)) =
      (fun v => h v * M.Y v) := by
    funext v
    cases hd : M.D v <;>
      simp only [h, score, ipwScore, pseudoOutcome, observation, radius, hd,
        Bool.false_eq_true, ↓reduceIte, div_eq_mul_inv] <;> ring
  have hY : Integrable (fun v => h v * M.Y v) (tailLaw M t) := by
    have hi := (obsTailLaw_eq_map_tailLaw M t) ▸ hScore
    have hc := hi.comp_aemeasurable hm.aemeasurable
    change Integrable (fun v => score E .ipw n w (observation M v)) (tailLaw M t) at hc
    rwa [hrep] at hc
  have hMeanInt := weighted_observed_mean_integral_tailLaw M hRV hMean t h hh hY
  unfold IpwOutcomeScoreMean
  rw [obsTailLaw_eq_map_tailLaw, integral_map hm.aemeasurable
    (measurable_score_frozen E .ipw n w).aestronglyMeasurable, hrep, ← hMeanInt.2]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro v
  dsimp only [h]
  cases hd : M.D v <;> simp only [hd, Bool.false_eq_true, ↓reduceIte,
    zero_div, zero_sub, sub_zero, div_eq_mul_inv] <;> ring

/-- Given [regularly varying noise](hyp:hRV), [noise independence](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional-mean version](hyp:hMean), [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression bound](hyp:hG), [a threshold at least one](hyp:ht), [bounded tail error](hyp:hb), [an exponent-error bound](hyp:hErr), [an integrable radial increment](hyp:hRad), and [the outcome-conditioned identity](hyp:hOutcome), [the conditional IPW score-mean identity holds](goal).
@node: ipw_conditional_score_mean_of_outcome_score_mean -/
lemma ipw_conditional_score_mean_of_outcome_score_mean (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) {n : ℕ} (hn : EvenSampleSize n)
    {c C t a : ℝ} (hOverlap : EstimatedOverlap E c) (hG : GBound M C)
    (ht : 1 ≤ t) (hb : BddAbove (M.e '' Set.Ici t))
    (w : E.Om) (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t))
    (hOutcome : IpwOutcomeScoreMean E n t w) : IpwConditionalScoreMean E n t w := by
  let H : Bool → M.Om → ℝ := fun d v =>
    (M.f (M.X v) d (M.U v) / radius M v ^ E.alphaHat n w) /
      (if d then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v))
  have hpair : Measurable[sigmaXU M] (fun v => (M.X v, M.U v)) :=
    Measurable.of_comap_le le_rfl
  have hHm (d : Bool) : Measurable[sigmaXU M] (H d) := by
    have hf : Measurable[sigmaXU M] (fun v => M.f (M.X v) d (M.U v)) :=
      hMean.1.comp (hpair.fst.prodMk (measurable_const.prodMk hpair.snd))
    have hp : Measurable[sigmaXU M] (fun v => E.pHat n w (M.X v)) :=
      (E.pHat_training n).comp (measurable_const.prodMk hpair.fst)
    have hr : Measurable[sigmaXU M] (radius M) := measurable_l1Norm.comp hpair.snd
    cases d
    · exact (hf.div (hr.pow_const _)).div (measurable_const.sub hp)
    · exact (hf.div (hr.pow_const _)).div hp
  have hHi (d : Bool) : Integrable (H d) (tailLaw M t) := by
    have hf := fitted_normalized_regression_integrable E hRV hX hHom hMean hG ht hb w hErr hRad d
    apply Integrable.mono' (hf.norm.const_mul c⁻¹)
    · exact ((hHm d).mono ((M.measurable_X.prodMk M.measurable_U).comap_le)
        le_rfl).aestronglyMeasurable
    · apply Eventually.of_forall
      intro v
      have hp := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
      have hden : c ≤ (if d then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v)) := by
        cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith [hp.1, hp.2]
      dsimp only [H]
      rw [norm_div, Real.norm_eq_abs (if d then _ else _),
        abs_of_pos (hOverlap.1.trans_le hden), div_eq_mul_inv]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ (hOverlap.1.trans_le hden) hOverlap.1).mpr hden)
        (norm_nonneg (M.f (M.X v) d (M.U v) / radius M v ^ E.alphaHat n w))
  have htreated (d : Bool) : Integrable (fun v => H d v *
      ({v | M.D v = d}).indicator (fun _ => (1 : ℝ)) v) (tailLaw M t) := by
    have hs : MeasurableSet {v | M.D v = d} :=
      M.measurable_D (measurableSet_singleton d)
    apply ((hHi d).indicator hs).congr
    exact Eventually.of_forall fun v => by
      by_cases hd : M.D v = d <;> simp [hd]
  have h1 := treatment_weighted_integral_tail M hRV hNoise t true
    (H true) (hHm true) (htreated true)
  have h0 := treatment_weighted_integral_tail M hRV hNoise t false
    (H false) (hHm false) (htreated false)
  have hsplit : (fun v => if M.D v then H true v else -(H false v)) =
      (fun v => H true v * ({v | M.D v = true}).indicator (fun _ => (1 : ℝ)) v -
        H false v * ({v | M.D v = false}).indicator (fun _ => (1 : ℝ)) v) := by
    funext v
    cases hd : M.D v <;> simp [hd]
  change (∫ z, score E .ipw n w z ∂obsTailLaw M t) = _
  rw [hOutcome]
  change (∫ v, if M.D v then H true v else -(H false v) ∂tailLaw M t) = _
  rw [hsplit, integral_sub (htreated true) (htreated false), h1.2, h0.2,
    ← integral_sub h1.1 h0.1]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro v
  simp only [H, Bool.false_eq_true, ↓reduceIte, ipwFittedMeanIntegrand]
  ring

end Papers.TbsExtremeEffects
