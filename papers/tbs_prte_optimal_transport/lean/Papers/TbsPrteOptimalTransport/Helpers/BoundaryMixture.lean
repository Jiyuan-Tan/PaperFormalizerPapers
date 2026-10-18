module
public import Papers.TbsPrteOptimalTransport.Helpers.BoundaryLocalization
public import Papers.TbsPrteOptimalTransport.Helpers.ObservationalCompatibility
public import Papers.TbsPrteOptimalTransport.Helpers.GapKernelQuantile
/-! Transfer of boundary localization through probability mixtures. -/
public section
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal

-- @node: normalized_weighted_window_probability
/-- For [a nonnegative, possibly infinite weighting function](hyp:f), if [its integral over the selection window is nonzero](hyp:hzero) and [finite](hyp:hfinite), [weighting the measure on that window and dividing by this integral gives a probability measure](goal). -/
lemma normalized_weighted_window_probability {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (D : Set A) (f : A → ℝ≥0∞)
    (hzero : (∫⁻ z in D, f z ∂μ) ≠ 0)
    (hfinite : (∫⁻ z in D, f z ∂μ) ≠ ⊤) :
    IsProbabilityMeasure ((∫⁻ z in D, f z ∂μ)⁻¹ •
      (μ.restrict D).withDensity f) := by
  constructor
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hzero hfinite

-- @node: normalized_weighted_window_ae
/-- If [the selection window is measurable](hyp:hD) and [the nonnegative weighting function](hyp:f) [is measurable](hyp:hf), [almost every point under the normalized weighted window measure belongs to the window and has nonzero weight](goal). -/
lemma normalized_weighted_window_ae {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (D : Set A) (hD : MeasurableSet D)
    (f : A → ℝ≥0∞) (hf : Measurable f) :
    ∀ᵐ z ∂((∫⁻ z in D, f z ∂μ)⁻¹ • (μ.restrict D).withDensity f),
      z ∈ D ∧ f z ≠ 0 := by
  apply Measure.ae_smul_measure
  apply (ae_withDensity_iff hf).mpr
  exact (ae_restrict_mem hD).mono fun z hz hpos => ⟨hz, hpos⟩

-- @node: normalized_weighted_window_lintegral
/-- For [nonnegative weight and evaluation functions f and g](hyp:f,g) that [are both measurable](hyp:hf,hg), [the integral of g under the normalized weighted window measure equals the integral of f times g over the window divided by the window's total weight](goal). -/
lemma normalized_weighted_window_lintegral {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (D : Set A) (f g : A → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ z, g z ∂((∫⁻ z in D, f z ∂μ)⁻¹ • (μ.restrict D).withDensity f) =
      (∫⁻ z in D, f z ∂μ)⁻¹ * ∫⁻ z in D, f z * g z ∂μ := by
  rw [lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ hf hg]
  rfl

-- @node: normalized_weighted_window_cancel
/-- For [nonnegative functions f and g](hyp:f,g) that [are measurable](hyp:hf,hg), suppose [f is finite everywhere](hyp:hfinite) and [g vanishes wherever f vanishes](hyp:hzero). Then [integrating g divided by f under the normalized f-weighted window measure gives the window integral of g divided by the window integral of f](goal). -/
lemma normalized_weighted_window_cancel {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (D : Set A) (f g : A → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfinite : ∀ z, f z ≠ ⊤) (hzero : ∀ z, f z = 0 → g z = 0) :
    ∫⁻ z, (f z)⁻¹ * g z
      ∂((∫⁻ z in D, f z ∂μ)⁻¹ • (μ.restrict D).withDensity f) =
        (∫⁻ z in D, f z ∂μ)⁻¹ * ∫⁻ z in D, g z ∂μ := by
  rw [normalized_weighted_window_lintegral μ D f (fun z => (f z)⁻¹ * g z)
    hf (hf.inv.mul hg)]
  congr 1
  apply lintegral_congr
  intro z
  by_cases hz : f z = 0
  · simp [hz, hzero z hz]
  · rw [← mul_assoc, ENNReal.mul_inv_cancel hz (hfinite z), one_mul]

-- @node: boundary_mixture_cdf
/-- [At any threshold, the CDF of a probability mixture equals the average of the component CDFs under its mixing distribution](goal). -/
lemma boundary_mixture_cdf {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (K : Kernel A ℝ) [IsMarkovKernel K] (t : ℝ) :
    cdf (μ.bind K) t = ∫ a, cdf (K a) t ∂μ := by
  haveI : IsProbabilityMeasure (μ.bind K) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ (by fun_prop)]
    simp
  simp_rw [cdf_eq_real, measureReal_def]
  exact (markov_bind_evaluation_integral μ K (Iic t) measurableSet_Iic).symm

-- @node: boundary_mixture_cdf_localization
/-- If [the weight a is nonnegative](hyp:ha) and [almost every component's absolute CDF difference from the reference law, multiplied by a, is at most d at every threshold](hyp:h), [the mixture's absolute CDF difference from that law, multiplied by a, is also at most d](goal). -/
lemma boundary_mixture_cdf_localization {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (K : Kernel A ℝ) [IsMarkovKernel K]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a d : ℝ) (ha : 0 ≤ a)
    (h : ∀ᵐ z ∂μ, ∀ t : ℝ, a * |cdf (K z) t - cdf ν t| ≤ d) (t : ℝ) :
    a * |cdf (μ.bind K) t - cdf ν t| ≤ d := by
  have hi : Integrable (fun z => cdf (K z) t) μ := by
    simp_rw [cdf_eq_real, measureReal_def]
    exact markov_evaluation_integrable μ K (Iic t) measurableSet_Iic
  have he : Integrable (fun z => cdf (K z) t - cdf ν t) μ :=
    hi.sub (integrable_const _)
  have hmix : cdf (μ.bind K) t - cdf ν t =
      ∫ z, cdf (K z) t - cdf ν t ∂μ := by
    rw [integral_sub hi (integrable_const _), integral_const]
    simp [boundary_mixture_cdf, probReal_univ]
  rw [hmix]
  calc
    _ ≤ a * ∫ z, |cdf (K z) t - cdf ν t| ∂μ :=
      mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) ha
    _ = ∫ z, a * |cdf (K z) t - cdf ν t| ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ _z, d ∂μ := integral_mono_ae (he.abs.const_mul a)
      (integrable_const _) (h.mono fun z hz => hz t)
    _ = d := by simp

-- @node: boundary_mixture_quantile_localization
/-- Suppose [a is nonnegative](hyp:ha), [lo does not exceed hi](hyp:hlohi), [almost every component is supported between lo and hi](hyp:hK), and [the reference law has the same support bound](hyp:hν). If [every component's CDF difference from the reference law, weighted by a, is almost surely at most d at every threshold](hyp:h), [a times the integrated absolute quantile difference between the mixture and reference law is at most (hi − lo) times d](goal). -/
lemma boundary_mixture_quantile_localization {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (K : Kernel A ℝ) [IsMarkovKernel K]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a d lo hi : ℝ) (ha : 0 ≤ a) (hlohi : lo ≤ hi)
    (hK : ∀ᵐ z ∂μ, K z (Icc lo hi)ᶜ = 0)
    (hν : ν (Icc lo hi)ᶜ = 0)
    (h : ∀ᵐ z ∂μ, ∀ t : ℝ, a * |cdf (K z) t - cdf ν t| ≤ d) :
    a * quantileDistanceIntegral (μ.bind K) ν ≤ (hi - lo) * d := by
  haveI : IsProbabilityMeasure (μ.bind K) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ (by fun_prop)]
    simp
  have hs : μ.bind K (Icc lo hi)ᶜ = 0 := by
    rw [Measure.bind_apply measurableSet_Icc.compl (by fun_prop)]
    rw [lintegral_congr_ae hK, lintegral_zero]
  rw [quantileDistanceIntegral, restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    Causalean.Stat.Quantile.Transport.quantile_transport_eq_cdf_distance
      (μ.bind K) ν hlohi hs hν, ← intervalIntegral.integral_const_mul]
  calc
    _ ≤ ∫ _t in lo..hi, d := by
      apply intervalIntegral.integral_mono hlohi
        ((Causalean.Stat.Quantile.Transport.intervalIntegrable_abs_cdf_sub
          (μ.bind K) ν lo hi).const_mul a) intervalIntegrable_const
      intro t
      exact boundary_mixture_cdf_localization μ K ν a d ha h t
    _ = (hi - lo) * d := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: canonical_treated_instrument_kernel
/-- If [the propensity is measurable in the instrument at the fixed covariate value](hyp:hp), [there exists a probability kernel over instruments whose multiplication by the propensity recovers the canonical treated submeasure everywhere and whose value at positive propensity is that submeasure divided by the propensity](goal). -/
lemma canonical_treated_instrument_kernel (M : LatentIVModel Ω X Z)
    (x : X) (hp : Measurable (fun z => M.prop z x)) :
    ∃ L : Kernel Z ℝ, IsMarkovKernel L ∧
      (∀ z, ENNReal.ofReal (M.prop z x) • L z =
        canonSubmeasure M true x (M.prop z x)) ∧
      (∀ z, 0 < M.prop z x → L z =
        (ENNReal.ofReal (M.prop z x))⁻¹ • canonSubmeasure M true x (M.prop z x)) := by
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun uz : ℝ × Z => (uz.1, x)) (by fun_prop)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  obtain ⟨L, hL, hrep⟩ := exists_normalized_interval_kernel K
    (fun _ => 0) (fun z => M.prop z x) measurable_const hp M.yMin
  have hpos (z : Z) (hz : 0 < M.prop z x) : L z =
      (ENNReal.ofReal (M.prop z x))⁻¹ • canonSubmeasure M true x (M.prop z x) := by
    rw [hrep z, if_pos hz]
    simp only [sub_zero, canonSubmeasure, selRegion, ite_true]
    rfl
  refine ⟨L, hL, ?_, hpos⟩
  intro z
  by_cases hz : 0 < M.prop z x
  · rw [hpos z hz, smul_smul,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hz) ENNReal.ofReal_ne_top,
      one_smul]
  · have hpzero : M.prop z x = 0 :=
      le_antisymm (le_of_not_gt hz) (M.rangeProp z x).1
    simp [hpzero, canonSubmeasure, selRegion]

-- @node: selected_boundary_mixture_localization
/-- Given [supported fallback outcome distributions](hyp:zeroLaw), [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he), [fitted propensities between zero and one](hyp:hp), and [nonnegative window widths](hyp:hdelta), [for almost every covariate value, every probability mixture of normalized treated laws selected within the fitted lower boundary window has lower-endpoint-weighted integrated absolute quantile distance from the boundary law at most the outcome range multiplied by the sum of the window width and twice the uniform first-stage error](goal). -/
lemma selected_boundary_mixture_localization (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hp : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (delta : ℕ → ℝ) (hdelta : ∀ n, 0 ≤ delta n) :
    ∀ᵐ x ∂xLaw M, ∀ n a (μz : Measure Z), IsProbabilityMeasure μz →
      ∀ L : Kernel Z ℝ, IsMarkovKernel L →
      (∀ᵐ z ∂μz, L z = (ENNReal.ofReal (M.prop z x))⁻¹ •
        canonSubmeasure M true x (M.prop z x)) →
      (∀ᵐ z ∂μz, pHat n a z x ≤ pLow (pHat n a) x + delta n) →
      pLow M.prop x * quantileDistanceIntegral (μz.bind L) (boundaryLaw M zeroLaw x) ≤
        (M.yMax - M.yMin) * (delta n + 2 * uniformFirstStageError M pHat n a) := by
  filter_upwards [canonical_submeasure_supported M h true] with x hs
  intro n a μz hμz L hL hrep hsel
  letI : IsProbabilityMeasure μz := hμz
  letI : IsMarkovKernel L := hL
  have ha := (propensity_support_endpoints M.prop M.rangeProp x).1
  have horder : M.yMin ≤ M.yMax := he.1.2 he.2.1
  have herr := uniform_first_stage_error_bounds M pHat hp n a
  by_cases hapos : 0 < pLow M.prop x
  · let K := (outcomeKernel (latentMarginal M true)).comap
      (fun u : ℝ => (u, x)) (by fun_prop)
    letI := outcomeKernel_isMarkov (latentMarginal M true)
    let νa := (ENNReal.ofReal (pLow M.prop x))⁻¹ •
      (volume.restrict (Ioc 0 (pLow M.prop x))).bind K
    haveI : IsProbabilityMeasure νa := normalized_interval_probability K _ hapos
    have hsupport (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
        ((ENNReal.ofReal p)⁻¹ • canonSubmeasure M true x p) (Icc M.yMin M.yMax)ᶜ = 0 := by
      rw [Measure.smul_apply]
      have hz : canonSubmeasure M true x p (Icc M.yMin M.yMax)ᶜ = 0 := by
        apply measure_mono_null _ (hs p hp)
        intro y hy hyS
        exact hy ⟨he.1.2 hyS, he.2.2 hyS⟩
      rw [hz, smul_zero]
    have hsν : νa (Icc M.yMin M.yMax)ᶜ = 0 := hsupport _ ha
    have hsL : ∀ᵐ z ∂μz, L z (Icc M.yMin M.yMax)ᶜ = 0 := by
      filter_upwards [hrep] with z hz
      rw [hz]
      exact hsupport _ (M.rangeProp z x)
    have hc : ∀ᵐ z ∂μz, ∀ t : ℝ,
        pLow M.prop x * |cdf (L z) t - cdf νa t| ≤
          delta n + 2 * uniformFirstStageError M pHat n a := by
      filter_upwards [hrep, hsel] with z hz hsz
      intro t
      have hw := selected_propensity_localization M.prop (pHat n a) M.rangeProp
        (hp n a) _ herr.2 (delta n) z x hsz
      have hpz : 0 < M.prop z x := hapos.trans_le hw.1
      rw [hz]
      have hcdf := normalized_interval_cdf_localization K (pLow M.prop x)
        (M.prop z x) hapos hw.1 t
      have hratio : pLow M.prop x * ((M.prop z x - pLow M.prop x) / M.prop z x) ≤
          M.prop z x - pLow M.prop x := by
        calc
          _ ≤ M.prop z x * ((M.prop z x - pLow M.prop x) / M.prop z x) :=
            mul_le_mul_of_nonneg_right hw.1
              (div_nonneg (sub_nonneg.mpr hw.1) hpz.le)
          _ = _ := mul_div_cancel₀ _ hpz.ne'
      exact (mul_le_mul_of_nonneg_left hcdf ha.1).trans (hratio.trans (by linarith [hw.2]))
    rw [boundaryLaw, if_pos hapos]
    exact boundary_mixture_quantile_localization μz L νa _ _ _ _ ha.1 horder hsL hsν hc
  · have hazero : pLow M.prop x = 0 := le_antisymm (le_of_not_gt hapos) ha.1
    rw [hazero, zero_mul]
    exact mul_nonneg (sub_nonneg.mpr horder)
      (add_nonneg (hdelta n) (mul_nonneg (by norm_num) herr.1))

end Papers.TbsPrteOptimalTransport
