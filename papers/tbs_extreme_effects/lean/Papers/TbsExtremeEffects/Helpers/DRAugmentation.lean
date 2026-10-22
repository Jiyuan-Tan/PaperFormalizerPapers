module
public import Papers.TbsExtremeEffects.Helpers.DRConditionalMean
public import Papers.TbsExtremeEffects.Helpers.DRScoreIntegrability
public import Papers.TbsExtremeEffects.Helpers.IPWOutcomeMean

/-! Treatment averaging of the fitted DR augmentation, shared with the IPW mean. -/

@[expose] public section
set_option linter.unusedVariables false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- [Mapping the tail-conditioned latent-variable law through the observation map gives the tail-conditioned observation law](goal).

@node: observation_tailLaw_map
-/
lemma observation_tailLaw_map (M : ExtremeModel q d) (t : ℝ) :
    (tailLaw M t).map (observation M) = obsTailLaw M t := by
  have hm : Measurable (observation M) :=
    M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  have hs : MeasurableSet {z : Obs q d | t < l1Norm z.2.2.2} := by
    exact measurableSet_lt measurable_const (measurable_l1Norm.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  ext s hsm
  rw [Measure.map_apply hm hsm, obsTailLaw, cond_apply hs,
    Measure.map_apply hm (hs.inter hsm), Measure.map_apply hm hs,
    tailLaw, cond_apply (measurableSet_lt measurable_const (measurable_radius M))
      ]
  rfl

/-- For [an experiment](hyp:E), [a sample size](hyp:n), [a realized training outcome](hyp:w), and [an observed covariate, treatment, outcome, and direction](hyp:z), [the doubly robust augmentation](goal) is the fitted treatment contrast minus the treatment-specific fitted terms weighted by estimated treatment probabilities.

@node: drAugmentation
-/
noncomputable def drAugmentation (E : NeteExperiment M) (n : ℕ) (w : E.Om)
    (z : Obs q d) : ℝ :=
  E.gHat n w z.1 true (obsDirection z) - E.gHat n w z.1 false (obsDirection z) -
    (if z.2.1 then E.gHat n w z.1 true (obsDirection z) / E.pHat n w z.1
      else -(E.gHat n w z.1 false (obsDirection z) / (1 - E.pHat n w z.1)))

/-- For [an experiment](hyp:E), [a sample size](hyp:n), [a realized training outcome](hyp:w), and [a latent population observation](hyp:v), [the treatment-averaged doubly robust augmentation](goal) replaces realized treatment terms by their true treatment probabilities.

@node: drAugmentationMean
-/
noncomputable def drAugmentationMean (E : NeteExperiment M) (n : ℕ) (w : E.Om)
    (v : M.Om) : ℝ :=
  E.gHat n w (M.X v) true (direction M v) - E.gHat n w (M.X v) false (direction M v) -
    (M.p (M.X v) / E.pHat n w (M.X v) * E.gHat n w (M.X v) true (direction M v) -
      (1 - M.p (M.X v)) / (1 - E.pHat n w (M.X v)) *
        E.gHat n w (M.X v) false (direction M v))

/-- Given [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), and [an observation whose estimated treatment probability lies in the overlap interval](hyp:hp), [the doubly robust score equals the inverse-probability-weighted score plus its augmentation](goal).

@node: dr_score_eq_ipw_add_augmentation
-/
lemma dr_score_eq_ipw_add_augmentation (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n) {c : ℝ} (hOverlap : EstimatedOverlap E c)
    (w : E.Om) (z : Obs q d)
    (hp : c ≤ E.pHat n w z.1 ∧ E.pHat n w z.1 ≤ 1 - c) :
    score E .dr n w z = score E .ipw n w z + drAugmentation E n w z := by
  have hp0 := (hOverlap.1.trans_le hp.1).ne'
  have hp1 : 1 - E.pHat n w z.1 ≠ 0 := by linarith [hOverlap.1, hp.2]
  simp only [score, drScore, ipwScore, drAugmentation]
  rw [dr_residual_weight_identity hp0 hp1]
  cases hd : z.2.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_div]
  all_goals ring

/-- If [the noise is regularly varying](hyp:hRV), [the noise is independent](hyp:hNoise), [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap), and [both fitted treatment regressions are integrable on the observation tail law](hyp:hg), then [the augmentation is integrable and its observation-tail mean equals its treatment-averaged latent-tail mean](goal).

@node: dr_augmentation_integral_tail
-/
lemma dr_augmentation_integral_tail (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    {n : ℕ} (hn : EvenSampleSize n) {c t : ℝ} (hOverlap : EstimatedOverlap E c)
    (w : E.Om)
    (hg : ∀ a : Bool, Integrable
      (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z)) (obsTailLaw M t)) :
    Integrable (drAugmentation E n w) (obsTailLaw M t) ∧
      (∫ z, drAugmentation E n w z ∂obsTailLaw M t) =
        ∫ v, drAugmentationMean E n w v ∂tailLaw M t := by
  have hObs : Measurable (observation M) :=
    M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  let g : Bool → M.Om → ℝ := fun a v => E.gHat n w (M.X v) a (direction M v)
  have hgmeas (a : Bool) : Measurable[sigmaXU M] (g a) := by
    have hpair : Measurable[sigmaXU M] (fun v => (M.X v, M.U v)) :=
      Measurable.of_comap_le le_rfl
    have hdir : Measurable[sigmaXU M] (direction M) := by
      let : MeasurableSpace M.Om := sigmaXU M
      unfold direction radius
      apply measurable_pi_iff.mpr
      intro i
      exact ((measurable_pi_apply i).comp hpair.snd).div
        (measurable_l1Norm.comp hpair.snd)
    exact (E.gHat_training n).comp (measurable_const.prodMk
      (hpair.fst.prodMk (measurable_const.prodMk hdir)))
  have hgi (a : Bool) : Integrable (g a) (tailLaw M t) := by
    have hi := hg a
    rw [← observation_tailLaw_map M t] at hi
    exact hi.comp_aemeasurable hObs.aemeasurable
  let H : Bool → M.Om → ℝ := fun a v => g a v /
    (if a then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v))
  have hHm (a : Bool) : Measurable[sigmaXU M] (H a) := by
    have hpair : Measurable[sigmaXU M] (fun v => (M.X v, M.U v)) :=
      Measurable.of_comap_le le_rfl
    have hp : Measurable[sigmaXU M] (fun v => E.pHat n w (M.X v)) :=
      (E.pHat_training n).comp (measurable_const.prodMk hpair.fst)
    cases a
    · exact (hgmeas false).div (measurable_const.sub hp)
    · exact (hgmeas true).div hp
  have hHi (a : Bool) : Integrable (H a) (tailLaw M t) := by
    apply Integrable.mono' ((hgi a).norm.const_mul c⁻¹)
    · exact ((hHm a).mono ((M.measurable_X.prodMk M.measurable_U).comap_le)
        le_rfl).aestronglyMeasurable
    · apply Eventually.of_forall
      intro v
      have hp := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
      have hden : c ≤ (if a then E.pHat n w (M.X v) else 1 - E.pHat n w (M.X v)) := by
        cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith [hp.1, hp.2]
      dsimp only [H]
      rw [norm_div, Real.norm_eq_abs (if a then _ else _),
        abs_of_pos (hOverlap.1.trans_le hden), div_eq_mul_inv]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ (hOverlap.1.trans_le hden) hOverlap.1).mpr hden) (norm_nonneg (g a v))
  have htreated (a : Bool) : Integrable (fun v => H a v *
      ({v | M.D v = a}).indicator (fun _ => (1 : ℝ)) v) (tailLaw M t) := by
    apply ((hHi a).indicator (M.measurable_D (measurableSet_singleton a))).congr
    exact Eventually.of_forall fun v => by
      by_cases hd : M.D v = a <;> simp [hd]
  have h1 := treatment_weighted_integral_tail M hRV hNoise t true (H true) (hHm true)
    (htreated true)
  have h0 := treatment_weighted_integral_tail M hRV hNoise t false (H false) (hHm false)
    (htreated false)
  have hrep : (fun v => drAugmentation E n w (observation M v)) =
      (fun v => g true v - g false v -
        (H true v * ({v | M.D v = true}).indicator (fun _ => (1 : ℝ)) v -
          H false v * ({v | M.D v = false}).indicator (fun _ => (1 : ℝ)) v)) := by
    funext v
    cases hd : M.D v <;> simp [drAugmentation, observation, g, H, hd]
    all_goals rfl
  have hInt : Integrable (fun v => drAugmentation E n w (observation M v)) (tailLaw M t) := by
    rw [hrep]
    exact ((hgi true).sub (hgi false)).sub ((htreated true).sub (htreated false))
  have hm : Measurable (drAugmentation E n w) := by
    have hg' (a : Bool) : Measurable (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z)) := by
      have hdir : Measurable (obsDirection (q := q) (d := d)) := by unfold obsDirection; fun_prop
      exact (E.gHat_training n).comp (measurable_const.prodMk
        (measurable_fst.prodMk (measurable_const.prodMk hdir)))
    have hp : Measurable (fun z : Obs q d => E.pHat n w z.1) :=
      (E.pHat_training n).comp (measurable_const.prodMk measurable_fst)
    exact ((hg' true).sub (hg' false)).sub
      (((hg' true).div hp).ite ((measurable_fst.comp measurable_snd)
        (measurableSet_singleton true)) (((hg' false).div (measurable_const.sub hp)).neg))
  refine ⟨?_, ?_⟩
  · rw [← observation_tailLaw_map M t]
    exact (integrable_map_measure hm.aestronglyMeasurable hObs.aemeasurable).mpr hInt
  · rw [← observation_tailLaw_map M t,
      integral_map hObs.aemeasurable hm.aestronglyMeasurable]
    change (∫ v, drAugmentation E n w (observation M v) ∂tailLaw M t) = _
    rw [hrep]
    rw [integral_sub (show Integrable (fun v => g true v - g false v) (tailLaw M t) from
      (hgi true).sub (hgi false))
      (show Integrable (fun v => H true v * ({v | M.D v = true}).indicator (fun _ => (1 : ℝ)) v -
        H false v * ({v | M.D v = false}).indicator (fun _ => (1 : ℝ)) v) (tailLaw M t) from
          (htreated true).sub (htreated false)), integral_sub (htreated true) (htreated false),
      h1.2, h0.2]
    have hweighted : Integrable (fun v =>
      H true v * (if true then M.p (M.X v) else 1 - M.p (M.X v)) -
      H false v * (if false then M.p (M.X v) else 1 - M.p (M.X v))) (tailLaw M t) :=
        h1.1.sub h0.1
    rw [← integral_sub h1.1 h0.1]
    rw [← integral_sub (show Integrable (fun v => g true v - g false v) (tailLaw M t) from
        (hgi true).sub (hgi false)) hweighted]
    apply integral_congr_ae
    exact Eventually.of_forall fun v => by
      simp only [drAugmentationMean, H, g, Bool.false_eq_true, ↓reduceIte]
      ring

/-- If [the noise is regularly varying](hyp:hRV), [the noise is independent](hyp:hNoise), [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap), [the inverse-probability-weighted score is integrable](hyp:hi), and [both fitted treatment regressions are integrable](hyp:hg), then [the doubly robust score mean is the inverse-probability-weighted score mean plus the treatment-averaged augmentation mean](goal).

@node: dr_score_integral_eq_ipw_add_augmentation
-/
lemma dr_score_integral_eq_ipw_add_augmentation (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    {n : ℕ} (hn : EvenSampleSize n) {c t : ℝ} (hOverlap : EstimatedOverlap E c)
    (w : E.Om) (hi : Integrable (score E .ipw n w) (obsTailLaw M t))
    (hg : ∀ a : Bool, Integrable
      (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z)) (obsTailLaw M t)) :
    (∫ z, score E .dr n w z ∂obsTailLaw M t) =
      (∫ z, score E .ipw n w z ∂obsTailLaw M t) +
        ∫ v, drAugmentationMean E n w v ∂tailLaw M t := by
  obtain ⟨hInt, hMean⟩ := dr_augmentation_integral_tail E hRV hNoise hn hOverlap w hg
  have hScoreEq : score E .dr n w =ᵐ[obsTailLaw M t]
      fun z => score E .ipw n w z + drAugmentation E n w z := by
    filter_upwards [estimatedOverlap_obsTailLaw E hn hOverlap t w] with z hz
    exact dr_score_eq_ipw_add_augmentation E hn hOverlap w z hz
  rw [integral_congr_ae hScoreEq,
    integral_add hi hInt, hMean]

/-- For [an experiment](hyp:E), [a sample size](hyp:n), [a tail threshold](hyp:t), [a regression function](hyp:reg), and [a realized training outcome](hyp:w), [the treatment-averaged mean condition](goal) requires: [the inverse-probability-weighted conditional-score condition](step:1), [agreement of its fitted mean plus augmentation with the fitted DR mean](step:2), [integrability of the regression contrast](step:3), and [equality of that contrast's tail mean with the normalized regression contrast](step:4).

@node: DrTreatmentAveragedMean
-/
def DrTreatmentAveragedMean (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om) : Prop :=
  IpwConditionalScoreMean E n t w ∧
  ((∫ v, ipwFittedMeanIntegrand E n w v ∂tailLaw M t) +
      (∫ v, drAugmentationMean E n w v ∂tailLaw M t) =
    ∫ v, drFittedRegressionMean E n reg w v ∂tailLaw M t) ∧
  Integrable (fun v => reg (M.X v, true, direction M v) -
    reg (M.X v, false, direction M v)) (tailLaw M t) ∧
  (∫ v, reg (M.X v, true, direction M v) - reg (M.X v, false, direction M v)
      ∂tailLaw M t) = ∫ v, normalizedRegressionContrast M v ∂tailLaw M t

/-- If [the noise is regularly varying](hyp:hRV), [the noise is independent](hyp:hNoise), [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap), [the inverse-probability-weighted score is integrable](hyp:hi), [both fitted regressions are integrable](hyp:hg), and [the treatment-averaged mean condition holds](hyp:h), then [the doubly robust conditional-score mean condition holds](goal).

@node: dr_conditional_score_mean_of_treatment_averaged
-/
lemma dr_conditional_score_mean_of_treatment_averaged (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    {n : ℕ} (hn : EvenSampleSize n) {c t : ℝ} (hOverlap : EstimatedOverlap E c)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hi : Integrable (score E .ipw n w) (obsTailLaw M t))
    (hg : ∀ a : Bool, Integrable
      (fun z : Obs q d => E.gHat n w z.1 a (obsDirection z)) (obsTailLaw M t))
    (h : DrTreatmentAveragedMean E n t reg w) : DrConditionalScoreMean E n t reg w := by
  obtain ⟨hIpw, hReg, hInt, hTarget⟩ := h
  refine ⟨?_, hInt, hTarget⟩
  rw [dr_score_integral_eq_ipw_add_augmentation E hRV hNoise hn hOverlap w hi hg,
    hIpw, hReg]

end Papers.TbsExtremeEffects
