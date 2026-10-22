module
public import Papers.TbsExtremeEffects.Helpers.AngularFactor
public import Papers.TbsExtremeEffects.Helpers.Angular
/-! Angular Lipschitz dual control of the covariate-averaged contrast. -/
public section
namespace Papers.TbsExtremeEffects
set_option linter.style.haveILetI false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
variable {q d : ℕ}

-- @node: positiveSphere_l1_distance_le_two
/-- If [both vectors lie on the positive unit l1 sphere](hyp:hu,hv), their [l1 distance is at most two](goal). -/
lemma positiveSphere_l1_distance_le_two {u v : Fin d → ℝ}
    (hu : u ∈ positiveSphere l1Norm) (hv : v ∈ positiveSphere l1Norm) :
    l1Norm (u - v) ≤ 2 := by
  calc
    _ ≤ l1Norm u + l1Norm v := by
      unfold l1Norm
      simp only [Pi.sub_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => abs_sub _ _
    _ = 2 := by rw [hu.2, hv.2]; norm_num

-- @node: angular_test_integrable
/-- A [probability measure supported on the positive unit l1 sphere](hyp:hs) makes every [angular test function integrable](goal), provided [that function is measurable and 1-Lipschitz on the sphere](hyp:hphi). -/
lemma angular_test_integrable (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hs : ∀ᵐ u ∂μ, u ∈ positiveSphere l1Norm)
    {phi : (Fin d → ℝ) → ℝ} (hphi : angularTest phi) : Integrable phi μ := by
  obtain ⟨v, hv⟩ := hs.exists
  apply Integrable.of_bound hphi.1.aestronglyMeasurable (2 + |phi v|)
  filter_upwards [hs] with u hu
  rw [Real.norm_eq_abs]
  have hdist := (hphi.2 u hu v hv).trans (positiveSphere_l1_distance_le_two hu hv)
  calc
    |phi u| ≤ |phi u - phi v| + |phi v| := by simpa using abs_sub_le (phi u) (phi v) 0
    _ ≤ _ := add_le_add hdist le_rfl

-- @node: angular_test_integral_sub_bound
/-- If [each of two probability laws is supported on the positive unit l1 sphere](hyp:hμ,hν) and [the test function is measurable and 1-Lipschitz on that sphere](hyp:hphi), then the [difference of their expectations is at most four](goal). -/
lemma angular_test_integral_sub_bound (μ ν : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ u ∂μ, u ∈ positiveSphere l1Norm)
    (hν : ∀ᵐ u ∂ν, u ∈ positiveSphere l1Norm)
    {phi : (Fin d → ℝ) → ℝ} (hphi : angularTest phi) :
    |(∫ u, phi u ∂μ) - ∫ u, phi u ∂ν| ≤ 4 := by
  obtain ⟨v, hv⟩ := hν.exists
  have hcenter (ξ : Measure (Fin d → ℝ)) [IsProbabilityMeasure ξ]
      (hξ : ∀ᵐ u ∂ξ, u ∈ positiveSphere l1Norm) :
      |(∫ u, phi u ∂ξ) - phi v| ≤ 2 := by
    have hc : (∫ _u, phi v ∂ξ) = phi v := by simp
    rw [← hc, ← integral_sub (angular_test_integrable ξ hξ hphi) (integrable_const _)]
    have hb : ∀ᵐ u ∂ξ, ‖phi u - phi v‖ ≤ 2 := by
      filter_upwards [hξ] with u hu
      simpa only [Real.norm_eq_abs] using
        (hphi.2 u hu v hv).trans (positiveSphere_l1_distance_le_two hu hv)
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
      mul_one] using norm_integral_le_of_norm_le_const hb
  calc
    _ ≤ |(∫ u, phi u ∂μ) - phi v| + |phi v - ∫ u, phi u ∂ν| := abs_sub_le _ _ _
    _ ≤ 2 + 2 := by rw [abs_sub_comm (phi v)]; exact add_le_add (hcenter μ hμ) (hcenter ν hν)
    _ = 4 := by norm_num

-- @node: angularW1_bddAbove
/-- For a [regularly varying noise model](hyp:hRV) and a [positive threshold](hyp:ht), the set of angular-test expectation gaps is [bounded above](goal). -/
lemma angularW1_bddAbove (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    {t : ℝ} (ht : 0 < t) :
    BddAbove {a | ∃ phi : (Fin d → ℝ) → ℝ, angularTest phi ∧
      a = |(∫ u, phi u ∂directionLaw M t) - ∫ u, phi u ∂M.S|} := by
  letI : IsProbabilityMeasure M.S := hRV.2.2.spectral_probability
  letI : IsProbabilityMeasure (tailLaw M t) := tailLaw_probability M hRV t
  letI : IsProbabilityMeasure (directionLaw M t) := by
    change IsProbabilityMeasure ((tailLaw M t).map (direction M))
    exact Measure.isProbabilityMeasure_map (measurable_direction M).aemeasurable
  refine ⟨4, ?_⟩
  rintro a ⟨phi, hphi, rfl⟩
  exact angular_test_integral_sub_bound (directionLaw M t) M.S (angular_law_ae_sphere M ht)
    (spectral_ae_sphere M hRV) hphi

-- @node: angularW1_integral_bound
/-- Under [regular variation of the noise](hyp:hRV), at a [positive threshold](hyp:ht), [a measurable test function that is 1-Lipschitz on the angular sphere](hyp:hphi) has [an expectation gap no larger than angular Wasserstein distance](goal). -/
lemma angularW1_integral_bound (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    {t : ℝ} (ht : 0 < t) {phi : (Fin d → ℝ) → ℝ} (hphi : angularTest phi) :
    |(∫ u, phi u ∂directionLaw M t) - ∫ u, phi u ∂M.S| ≤ angularW1 M t := by
  exact le_csSup (angularW1_bddAbove M hRV ht) ⟨phi, hphi, rfl⟩

-- @node: covariate_average_angular_lipschitz
/-- With [bounded covariates](hyp:hX), [asymptotically homogeneous outcomes](hyp:hHom), and a [bounded extension of the treatment contrast on the covariate ball and angular sphere](hyp:hH), the [covariate-averaged contrast changes at most at rate `2L` times l1 distance](goal) between two [sphere directions](hyp:hu,hv). -/
lemma covariate_average_angular_lipschitz (M : ExtremeModel q d)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (hH : ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
      H (x, s) = M.g x true s - M.g x false s)
    {u v : Fin d → ℝ} (hu : u ∈ positiveSphere l1Norm) (hv : v ∈ positiveSphere l1Norm) :
    |(∫ x, H (x, u) ∂M.mu.map M.X) - ∫ x, H (x, v) ∂M.mu.map M.X| ≤
      2 * M.L * l1Norm (u - v) := by
  letI : IsProbabilityMeasure (M.mu.map M.X) :=
    Measure.isProbabilityMeasure_map M.measurable_X.aemeasurable
  have hint (s : Fin d → ℝ) : Integrable (fun x => H (x, s)) (M.mu.map M.X) := by
    apply Integrable.of_bound (by fun_prop) ‖H‖
    exact ae_of_all _ fun x => H.norm_coe_le_norm (x, s)
  rw [← integral_sub (hint u) (hint v)]
  have hxe : ∀ᵐ x ∂M.mu.map M.X, l1Norm x ≤ M.R :=
    (ae_map_iff M.measurable_X.aemeasurable
      (measurableSet_le measurable_l1Norm measurable_const)).mpr hX.2
  have hb : ∀ᵐ x ∂M.mu.map M.X, ‖H (x, u) - H (x, v)‖ ≤
      2 * M.L * l1Norm (u - v) := by
    filter_upwards [hxe] with x hx
    rw [Real.norm_eq_abs, hH x hx u hu, hH x hx v hv]
    have h1 := hHom.2.2.2.2 x x hx hx true u hu v hv
    have h0 := hHom.2.2.2.2 x x hx hx false u hu v hv
    simp only [sub_self, l1Norm, Pi.zero_apply, abs_zero, Finset.sum_const_zero,
      zero_add] at h1 h0
    calc
      _ = |(M.g x true u - M.g x true v) - (M.g x false u - M.g x false v)| := by
        congr 1; ring
      _ ≤ _ := abs_sub _ _
      _ ≤ _ := by unfold l1Norm; linarith
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using norm_integral_le_of_norm_le_const hb

/-- For a [regularly varying noise model](hyp:hRV), [positive threshold](hyp:ht), [nonnegative Lipschitz constant](hyp:hK), [measurable test function](hyp:hphi), and [its K-Lipschitz bound on the positive unit l1 sphere](hyp:hLip), the [test's angular expectation gap is bounded by `K` times angular Wasserstein distance](goal). -/
-- @node: angularW1_scaled_integral_bound
lemma angularW1_scaled_integral_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {t K : ℝ} (ht : 0 < t) (hK : 0 ≤ K)
    (phi : (Fin d → ℝ) → ℝ) (hphi : Measurable phi)
    (hLip : ∀ u ∈ positiveSphere l1Norm, ∀ v ∈ positiveSphere l1Norm,
      |phi u - phi v| ≤ K * l1Norm (u - v)) :
    |(∫ u, phi u ∂directionLaw M t) - ∫ u, phi u ∂M.S| ≤ K * angularW1 M t := by
  letI : IsProbabilityMeasure M.S := hRV.2.2.spectral_probability
  letI : IsProbabilityMeasure (tailLaw M t) := tailLaw_probability M hRV t
  letI : IsProbabilityMeasure (directionLaw M t) := by
    change IsProbabilityMeasure ((tailLaw M t).map (direction M))
    exact Measure.isProbabilityMeasure_map (measurable_direction M).aemeasurable
  by_cases hzero : K = 0
  · obtain ⟨v, hv⟩ := (spectral_ae_sphere M hRV).exists
    have heq : ∀ u ∈ positiveSphere l1Norm, phi u = phi v := by
      intro u hu
      have h := hLip u hu v hv
      rw [hzero, zero_mul] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    have hμ : (∫ u, phi u ∂directionLaw M t) = phi v := by
      calc
        _ = ∫ _u, phi v ∂directionLaw M t := by
          apply integral_congr_ae
          filter_upwards [angular_law_ae_sphere M ht] with u hu
          exact heq u hu
        _ = _ := by simp
    have hν : (∫ u, phi u ∂M.S) = phi v := by
      calc
        _ = ∫ _u, phi v ∂M.S := by
          apply integral_congr_ae
          filter_upwards [spectral_ae_sphere M hRV] with u hu
          exact heq u hu
        _ = _ := by simp
    rw [hμ, hν, sub_self, abs_zero, hzero, zero_mul]
  · have hpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hzero)
    have htest : angularTest (fun u => phi u / K) := by
      constructor
      · fun_prop
      · intro u hu v hv
        rw [← sub_div, abs_div, abs_of_pos hpos]
        exact (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hLip u hu v hv)
    have h := angularW1_integral_bound M hRV ht htest
    rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hpos] at h
    exact (div_le_iff₀ hpos).mp h |>.trans_eq (mul_comm _ _)

/-- For a [regularly varying noise model](hyp:hRV) with [noise independent of covariates and treatment](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotically homogeneous outcomes](hyp:hHom), and a [positive threshold](hyp:ht), the [angular component of eta bias is at most `2L` times angular Wasserstein distance](goal). -/
-- @node: angularFactor_target_wasserstein_bound
lemma angularFactor_target_wasserstein_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    {t : ℝ} (ht : 0 < t) :
    |angularFactor M t - etaTarget M| ≤ 2 * M.L * angularW1 M t := by
  obtain ⟨H, hH⟩ := angular_contrast_bounded_extension M hHom
  let phi : (Fin d → ℝ) → ℝ := fun s => ∫ x, H (x, s) ∂M.mu.map M.X
  have hphi : Measurable phi := by
    have hc := continuous_covariate_average M H
    fun_prop
  have hLip : ∀ u ∈ positiveSphere l1Norm, ∀ v ∈ positiveSphere l1Norm,
      |phi u - phi v| ≤ (2 * M.L) * l1Norm (u - v) := by
    intro u hu v hv
    exact covariate_average_angular_lipschitz M hX hHom H hH hu hv
  have hxe : ∀ᵐ x ∂M.mu.map M.X, l1Norm x ≤ M.R :=
    (ae_map_iff M.measurable_X.aemeasurable
      (measurableSet_le measurable_l1Norm measurable_const)).mpr hX.2
  have htarget : (∫ s, phi s ∂M.S) = etaTarget M := by
    apply integral_congr_ae
    filter_upwards [spectral_ae_sphere M hRV] with s hs
    apply integral_congr_ae
    filter_upwards [hxe] with x hx
    exact hH x hx s hs
  have hbound := angularW1_scaled_integral_bound M hRV ht
    (by positivity [hHom.2.2.2.1] : 0 ≤ 2 * M.L) phi hphi hLip
  rw [htarget] at hbound
  rw [angularFactor_eq_covariate_average M hRV hNoise hX H hH ht]
  exact hbound

end Papers.TbsExtremeEffects
