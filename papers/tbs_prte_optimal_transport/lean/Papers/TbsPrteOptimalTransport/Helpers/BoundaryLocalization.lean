module
public import Papers.TbsPrteOptimalTransport.Helpers.FirstStageTransfer
public import Causalean.Stat.Quantile.Transport
/-! Weighted localization of the normalized treated laws near the lower propensity endpoint. -/
public section
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal Topology

-- @node: normalized_interval_probability
/-- If [the interval length r is positive](hyp:hr), [averaging a probability kernel over the interval from zero to r and dividing by r gives a probability measure](goal). -/
lemma normalized_interval_probability (K : Kernel ℝ ℝ) [IsMarkovKernel K]
    (r : ℝ) (hr : 0 < r) :
    IsProbabilityMeasure ((ENNReal.ofReal r)⁻¹ • (volume.restrict (Ioc 0 r)).bind K) := by
  constructor
  rw [Measure.smul_apply, interval_kernel_mass, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hr)
    ENNReal.ofReal_ne_top

-- @node: normalized_interval_cdf_localization
/-- If [a is positive](hyp:ha) and [p is at least a](hyp:hap), [the CDFs obtained by averaging the same probability kernel from zero to p and from zero to a differ at any threshold by at most (p − a) / p](goal). -/
lemma normalized_interval_cdf_localization (K : Kernel ℝ ℝ) [IsMarkovKernel K]
    (a p : ℝ) (ha : 0 < a) (hap : a ≤ p) (t : ℝ) :
    |cdf ((ENNReal.ofReal p)⁻¹ • (volume.restrict (Ioc 0 p)).bind K) t -
      cdf ((ENNReal.ofReal a)⁻¹ • (volume.restrict (Ioc 0 a)).bind K) t| ≤
        (p - a) / p := by
  have hp : 0 < p := ha.trans_le hap
  letI := normalized_interval_probability K p hp
  letI := normalized_interval_probability K a ha
  let A := ((volume.restrict (Ioc 0 a)).bind K) (Iic t)
  let B := ((volume.restrict (Ioc a p)).bind K) (Iic t)
  have hA : A ≤ ENNReal.ofReal a := by
    simpa only [interval_kernel_mass, sub_zero] using
      (measure_mono (subset_univ (Iic t)) :
        ((volume.restrict (Ioc 0 a)).bind K) (Iic t) ≤
          ((volume.restrict (Ioc 0 a)).bind K) univ)
  have hB : B ≤ ENNReal.ofReal (p - a) := by
    simpa only [interval_kernel_mass] using
      (measure_mono (subset_univ (Iic t)) :
        ((volume.restrict (Ioc a p)).bind K) (Iic t) ≤
          ((volume.restrict (Ioc a p)).bind K) univ)
  have hAf : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA
  have hBf : B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB
  have hAr : A.toReal ≤ a := by
    simpa only [ENNReal.toReal_ofReal ha.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hA
  have hBr : B.toReal ≤ p - a := by
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hap)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hB
  rw [cdf_eq_real, cdf_eq_real]
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal ha.le]
  rw [interval_kernel_add K 0 a p ha.le hap, Measure.add_apply]
  change |p⁻¹ * (A + B).toReal - a⁻¹ * A.toReal| ≤ (p - a) / p
  rw [ENNReal.toReal_add hAf hBf]
  have hform : p⁻¹ * (A.toReal + B.toReal) - a⁻¹ * A.toReal =
      (B.toReal - (p - a) * (A.toReal / a)) / p := by
    field_simp
    <;> ring
  rw [hform, abs_div, abs_of_pos hp]
  apply (div_le_div_iff_of_pos_right hp).mpr
  apply abs_le.mpr
  constructor
  · have hratio : A.toReal / a ≤ 1 := (div_le_one ha).mpr hAr
    have hmul := mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr hap)
    linarith [ENNReal.toReal_nonneg (a := B)]
  · have hmul : 0 ≤ (p - a) * (A.toReal / a) := by positivity
    linarith

-- @node: normalized_interval_quantile_localization
/-- Suppose [a is positive](hyp:ha), [p is at least a](hyp:hap), and [lo does not exceed hi](hyp:hlohi). If [the kernel integrated from zero to a](hyp:hsA) and [the kernel integrated from zero to p](hyp:hsP) both put no mass outside the interval from lo to hi, [a times the integrated absolute quantile difference between their normalized laws is at most (hi − lo) times (p − a)](goal). -/
lemma normalized_interval_quantile_localization (K : Kernel ℝ ℝ) [IsMarkovKernel K]
    (a p lo hi : ℝ) (ha : 0 < a) (hap : a ≤ p) (hlohi : lo ≤ hi)
    (hsA : ((volume.restrict (Ioc 0 a)).bind K) (Icc lo hi)ᶜ = 0)
    (hsP : ((volume.restrict (Ioc 0 p)).bind K) (Icc lo hi)ᶜ = 0) :
    a * quantileDistanceIntegral
      ((ENNReal.ofReal p)⁻¹ • (volume.restrict (Ioc 0 p)).bind K)
      ((ENNReal.ofReal a)⁻¹ • (volume.restrict (Ioc 0 a)).bind K) ≤
        (hi - lo) * (p - a) := by
  have hp : 0 < p := ha.trans_le hap
  let νp := (ENNReal.ofReal p)⁻¹ • (volume.restrict (Ioc 0 p)).bind K
  let νa := (ENNReal.ofReal a)⁻¹ • (volume.restrict (Ioc 0 a)).bind K
  letI : IsProbabilityMeasure νp := normalized_interval_probability K p hp
  letI : IsProbabilityMeasure νa := normalized_interval_probability K a ha
  have hsp : νp (Icc lo hi)ᶜ = 0 := by simp [νp, Measure.smul_apply, hsP]
  have hsa : νa (Icc lo hi)ᶜ = 0 := by simp [νa, Measure.smul_apply, hsA]
  have hcost : quantileDistanceIntegral νp νa ≤ (hi - lo) * ((p - a) / p) := by
    rw [quantileDistanceIntegral, restrict_Ioo_eq_restrict_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one,
      Causalean.Stat.Quantile.Transport.quantile_transport_eq_cdf_distance
        νp νa hlohi hsp hsa]
    calc
      _ ≤ ∫ _t in lo..hi, (p - a) / p := by
        apply intervalIntegral.integral_mono hlohi
          (Causalean.Stat.Quantile.Transport.intervalIntegrable_abs_cdf_sub νp νa lo hi)
          (intervalIntegrable_const)
        intro t
        exact normalized_interval_cdf_localization K a p ha hap t
      _ = _ := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  have hratio : a * ((p - a) / p) ≤ p - a := by
    have hr : 0 ≤ (p - a) / p := div_nonneg (sub_nonneg.mpr hap) hp.le
    calc
      _ ≤ p * ((p - a) / p) := mul_le_mul_of_nonneg_right hap hr
      _ = p - a := mul_div_cancel₀ _ hp.ne'
  exact (mul_le_mul_of_nonneg_left hcost ha.le).trans (by
    rw [← mul_assoc, mul_comm a (hi - lo), mul_assoc]
    exact mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr hlohi))

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: boundary_treated_law_localization
/-- Given [a fallback outcome distribution supported on the outcome set at each covariate value](hyp:zeroLaw), [the structural assumptions](hyp:h), and [known lower and upper outcome endpoints](hyp:he), [for almost every covariate value and every propensity between its lower support endpoint and one, the lower endpoint times the integrated absolute quantile difference between the normalized treated law and the boundary law is bounded by the outcome range times the propensity's distance from that endpoint](goal). -/
lemma boundary_treated_law_localization (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ Icc (0 : ℝ) 1, pLow M.prop x ≤ p →
      pLow M.prop x * quantileDistanceIntegral
        ((ENNReal.ofReal p)⁻¹ • canonSubmeasure M true x p)
        (boundaryLaw M zeroLaw x) ≤ (M.yMax - M.yMin) * (p - pLow M.prop x) := by
  filter_upwards [canonical_submeasure_supported M h true] with x hs
  intro p hp hap
  have ha := (propensity_support_endpoints M.prop M.rangeProp x).1
  have horder : M.yMin ≤ M.yMax := he.1.2 he.2.1
  by_cases haPos : 0 < pLow M.prop x
  · let K := (outcomeKernel (latentMarginal M true)).comap
      (fun u : ℝ => (u, x)) (by fun_prop)
    letI := outcomeKernel_isMarkov (latentMarginal M true)
    have hs' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
        ((volume.restrict (Ioc 0 r)).bind K) (Icc M.yMin M.yMax)ᶜ = 0 := by
      apply measure_mono_null _ (hs r hr)
      intro y hy hyS
      exact hy ⟨he.1.2 hyS, he.2.2 hyS⟩
    rw [boundaryLaw, if_pos haPos]
    exact normalized_interval_quantile_localization K (pLow M.prop x) p
      M.yMin M.yMax haPos hap horder (hs' _ ha) (hs' _ hp)
  · have haZero : pLow M.prop x = 0 := le_antisymm (le_of_not_gt haPos) ha.1
    rw [haZero, zero_mul, sub_zero]
    exact mul_nonneg (sub_nonneg.mpr horder) hp.1

-- @node: selected_instrument_boundary_localization
/-- Given [fallback outcome distributions supported on the outcome set](hyp:zeroLaw), [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and [fitted propensities lying between zero and one](hyp:hp), [for almost every covariate value, any instrument whose fitted propensity is within delta of its fitted lower endpoint has lower-endpoint-weighted quantile distance from the true boundary law at most the outcome range multiplied by the sum of delta and twice the uniform first-stage error](goal). -/
lemma selected_instrument_boundary_localization (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hp : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1) (delta : ℕ → ℝ) :
    ∀ᵐ x ∂xLaw M, ∀ n a z,
      pHat n a z x ≤ pLow (pHat n a) x + delta n →
      pLow M.prop x * quantileDistanceIntegral
        ((ENNReal.ofReal (M.prop z x))⁻¹ • canonSubmeasure M true x (M.prop z x))
        (boundaryLaw M zeroLaw x) ≤
          (M.yMax - M.yMin) * (delta n + 2 * uniformFirstStageError M pHat n a) := by
  filter_upwards [boundary_treated_law_localization M zeroLaw h he] with x hx
  intro n a z hsel
  have herr := (uniform_first_stage_error_bounds M pHat hp n a).2
  have hwindow := selected_propensity_localization M.prop (pHat n a) M.rangeProp
    (hp n a) _ herr (delta n) z x hsel
  exact (hx _ (M.rangeProp z x) hwindow.1).trans
    (mul_le_mul_of_nonneg_left (by linarith [hwindow.2])
      (sub_nonneg.mpr (he.1.2 he.2.1)))

end Papers.TbsPrteOptimalTransport
