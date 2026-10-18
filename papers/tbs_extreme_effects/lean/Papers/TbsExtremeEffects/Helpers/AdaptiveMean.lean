module
public import Papers.TbsExtremeEffects.Helpers.AdaptiveNuisance
public import Papers.TbsExtremeEffects.Helpers.DRConditionalMean
public import Papers.TbsExtremeEffects.Helpers.AngularDual

/-! Population DR mean errors on a deterministic threshold band. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- Under [asymptotic homogeneity](hyp:hHom), [there is a finite common bound for the two regression functions on the covariate and direction domain](goal).

@node: homogeneous_regression_has_bound -/
lemma homogeneous_regression_has_bound (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) : ∃ C : ℝ, GBound M C := by
  have hsection (a : Bool) : ∃ C : ℝ, ∀ x, l1Norm x ≤ M.R →
      ∀ s ∈ positiveSphere l1Norm, |M.g x a s| ≤ C := by
    have hLip : LipschitzOnWith ⟨M.L * (q + d), by positivity [hHom.2.2.2.1]⟩
        (fun z : (Fin q → ℝ) × (Fin d → ℝ) => M.g z.1 a z.2)
        ({x | l1Norm x ≤ M.R} ×ˢ positiveSphere l1Norm) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro z hz z' hz'
      have hg := hHom.2.2.2.2 z.1 z'.1 hz.1 hz'.1 a z.2 hz.2 z'.2 hz'.2
      have hq := l1Norm_le_card_mul_norm (z.1 - z'.1)
      have hd := l1Norm_le_card_mul_norm (z.2 - z'.2)
      have hx : ‖z.1 - z'.1‖ ≤ dist z z' := by
        simpa [dist_eq_norm] using norm_fst_le (z - z')
      have hs : ‖z.2 - z'.2‖ ≤ dist z z' := by
        simpa [dist_eq_norm] using norm_snd_le (z - z')
      have hsum : l1Norm (z.1 - z'.1) + l1Norm (z.2 - z'.2) ≤
          ((q : ℝ) + d) * dist z z' := by
        nlinarith [mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg q),
          mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg d)]
      rw [Real.dist_eq]
      apply hg.trans
      change M.L * _ ≤ (M.L * ((q : ℝ) + d)) * dist z z'
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum hHom.2.2.2.1
    obtain ⟨C, hC⟩ := ((isCompact_covariate_l1Ball M.R).prod
      isCompact_positiveSphere_l1).exists_bound_of_continuousOn hLip.continuousOn
    exact ⟨C, fun x hx s hs => by simpa only [Real.norm_eq_abs] using hC (x, s) ⟨hx, hs⟩⟩
  obtain ⟨C1, h1⟩ := hsection true
  obtain ⟨C0, h0⟩ := hsection false
  refine ⟨max 0 (max C1 C0), le_max_left _ _, ?_⟩
  intro x hx a s hs
  cases a
  · exact (h0 x hx s hs).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (h1 x hx s hs).trans ((le_max_left _ _).trans (le_max_right _ _))

/-- Under [asymptotic homogeneity](hyp:hHom), [a positive lower band constant](hyp:hcm), and [positive band growth](hyp:hk), [every sufficiently large polynomial band has thresholds at least one with a well-defined homogeneity envelope between zero and one](goal).

@node: adaptive_band_homogeneity_envelope -/
lemma adaptive_band_homogeneity_envelope (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) {cminus cplus k : ℝ}
    (hcm : 0 < cminus) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Set.Icc ((cminus / 2) * (n : ℝ) ^ k) (2 * cplus * (n : ℝ) ^ k),
        1 ≤ t ∧ BddAbove (M.e '' Set.Ici t) ∧ 0 ≤ eBar M t ∧ eBar M t ≤ 1 := by
  have hSmall := (tendsto_order.mp (eBar_tendsto_zero M hHom)).2 1 zero_lt_one
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eBar_eventually_bddAbove M hHom).and hSmall)
  have hGrowth : Tendsto (fun n : ℕ => (cminus / 2) * (n : ℝ) ^ k) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (half_pos hcm)).mpr
      ((tendsto_rpow_atTop hk).comp tendsto_natCast_atTop_atTop)
  filter_upwards [hGrowth.eventually (eventually_ge_atTop (max 1 T))] with n hn
  intro t ht
  have hlarge := hn.trans ht.1
  have ht1 : 1 ≤ t := (le_max_left _ _).trans hlarge
  obtain ⟨hb, he⟩ := hT t ((le_max_right _ _).trans hlarge)
  exact ⟨ht1, hb, eBar_nonneg M hHom (zero_lt_one.trans_le ht1) hb, he.le⟩

/-- If [the selected threshold lies in the band](hyp:ht), [the denominator is positive](hyp:hN), [the endpoint count exceeds that denominator](hyp:hCount), [the centered score, centered count, and score mean are uniformly controlled on the band](hyp:hProcesses), and [the selected-threshold score mean is close to the target](hyp:hMean), then [the selected estimator has the stated target-error bound](goal).

@node: selected_threshold_error_of_selected_mean -/
lemma selected_threshold_error_of_selected_mean (E : NeteExperiment M)
    (kind : EstimatorKind) (n : ℕ) (w : E.Om) {ell u t N A B U e : ℝ}
    (ht : t ∈ Set.Icc ell u) (hN : 0 < N)
    (hCount : N ≤ (evalCount E n u w : ℝ))
    (hProcesses : ∀ v ∈ Set.Icc ell u,
      |thresholdCenteredScore E kind n v w| ≤ A ∧
      |thresholdCenteredCount E n v w| ≤ B ∧
      |thresholdScoreMean E kind n v w| ≤ U)
    (hMean : |thresholdScoreMean E kind n t w - etaTarget M| ≤ e) :
    |etaEstimate E kind n t w - etaTarget M| ≤ (A + U * B) / N + e := by
  obtain ⟨hA, hB, hU⟩ := hProcesses t ht
  have hCountT : N ≤ (evalCount E n t w : ℝ) :=
    hCount.trans (by exact_mod_cast evalCount_antitone_threshold E n w ht.2)
  exact (abs_sub_le (etaEstimate E kind n t w) (thresholdScoreMean E kind n t w)
    (etaTarget M)).trans (add_le_add
      (threshold_sampling_error_bound E kind n t w hN hCountT hA hB hU) hMean)

/-- Given [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [an even sample](hyp:hn), [overlap](hyp:hOverlap), [a regression envelope](hyp:hG), [a threshold at least one](hyp:ht), [a bounded homogeneity tail envelope](hyp:hb), [a fitted tail-index error bound](hyp:hErr), and [integrability of the radial increment](hyp:hRad), [the DR exponent integral is bounded by the corresponding radial moment](goal).

@node: dr_exponent_integral_bound_by_radial_moment -/
lemma dr_exponent_integral_bound_by_radial_moment (E : NeteExperiment M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t a : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 1 ≤ t)
    (hb : BddAbove (M.e '' Set.Ici t)) (w : E.Om)
    (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t)) :
    |∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t| ≤
      (2 * (C + eBar M t) / c) *
        (∫ v, radius M v ^ a - 1 ∂tailLaw M t) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hconst : 0 ≤ 2 * (C + eBar M t) / c := by
    exact div_nonneg (mul_nonneg (by norm_num)
      (add_nonneg hG.1 (eBar_nonneg M hHom htpos hb))) hOverlap.1.le
  have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  have hbound : ∀ᵐ v ∂tailLaw M t,
      ‖exponentMeanIntegrand E n w v‖ ≤
        (2 * (C + eBar M t) / c) * (radius M v ^ a - 1) := by
    filter_upwards [hx, ae_cond_mem (μ := M.mu)
      (measurableSet_lt measurable_const (measurable_radius M))] with v hv hw
    have hp := M.p_range (M.X v)
    have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
    have hf := normalized_regression_tail_bound M hHom hG htpos hb v hv hw
    rw [Real.norm_eq_abs, exponentMeanIntegrand, abs_mul]
    exact mul_le_mul
      (propensity_weighted_regression_bound hOverlap.1 hp.1 hp.2 hph.1
        (by linarith [hph.2]) (hf true) (hf false))
      (abs_rpow_sub_one_le_increment (ht.trans hw.le) hErr) (abs_nonneg _) hconst
  have hnorm := norm_integral_le_of_norm_le
    (hRad.const_mul (2 * (C + eBar M t) / c)) hbound
  simpa only [Real.norm_eq_abs, integral_const_mul] using hnorm

/-- Given [regularly varying noise](hyp:hRV), [independent noise](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a valid conditional mean version](hyp:hMean), [an even sample](hyp:hn), [overlap](hyp:hOverlap), [a regression envelope](hyp:hG), [a threshold at least one](hyp:ht), [a bounded tail envelope](hyp:hb), [the DR decomposition](hyp:hIdentity), [a bias bound](hyp:hBias), [a tail-index error bound](hyp:hErr), [radial integrability](hyp:hRad), and [a radial-moment bound](hyp:hMoment), [the DR population score mean has the stated total error bound](goal).

@node: adaptive_dr_mean_error_bound -/
lemma adaptive_dr_mean_error_bound (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) {n : ℕ} (hn : EvenSampleSize n)
    {c C t a b z : ℝ} (hOverlap : EstimatedOverlap E c) (hG : GBound M C)
    (ht : 1 ≤ t) (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hIdentity : DrMeanDecomposition E n t reg w)
    (hBias : |∫ v, drBiasIntegrand E n reg w v ∂tailLaw M t| ≤ b)
    (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t))
    (hMoment : (∫ v, radius M v ^ a - 1 ∂tailLaw M t) ≤ z) :
    |thresholdScoreMean E .dr n t w - etaTarget M| ≤
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
  change |(∫ v, score E .dr n w v ∂obsTailLaw M t) - etaTarget M| ≤ _
  rw [hIdentity]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add hBias hExp) hTarget)

end Papers.TbsExtremeEffects
