module
public import Papers.TbsExtremeEffects.Helpers.TailIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Conditional radial power moments from layer cake.

For either sign of a nonzero exponent, the nonnegative kernel
`r ^ (a - 1)` on `r > 1` integrates to `(z ^ a - 1) / a`.
The tail integral first establishes integrability and then identifies the moment.
For positive exponents its finiteness follows from the dyadic Potter bound;
for negative exponents survival probabilities bounded by one suffice.
-/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

-- @node: power_increment_interval
/-- For a [nonzero exponent](hyp:ha) and [upper endpoint at least one](hyp:hz), the [integral of the power kernel above one equals the power increment divided by the exponent](goal). -/
lemma power_increment_interval {a z : ℝ} (ha : a ≠ 0) (hz : 1 ≤ z) :
    (∫ r in (0 : ℝ)..z, (Ioi 1).indicator (fun r : ℝ => r ^ (a - 1)) r) =
      (z ^ a - 1) / a := by
  rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ z),
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi (1 : ℝ) ∩ Ioc 0 z = Ioc 1 z := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨hr, _, hrz⟩
      exact ⟨hr, hrz⟩
    · rintro ⟨hr, hrz⟩
      exact ⟨hr, by linarith, hrz⟩
  rw [hset, ← intervalIntegral.integral_of_le hz,
    integral_rpow (Or.inr ⟨by simpa using ha,
      by rw [uIcc_of_le hz]; simp⟩)]
  simp

-- @node: power_increment_kernel_intervalIntegrable
/-- For a [positive interval endpoint](hyp:hz), the [power kernel restricted to values above one is integrable over the interval from zero to that endpoint](goal). -/
lemma power_increment_kernel_intervalIntegrable (a : ℝ) {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable ((Ioi 1).indicator (fun r : ℝ => r ^ (a - 1))) volume 0 z := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le,
    integrableOn_indicator_iff measurableSet_Ioi]
  have hcont : ContinuousOn (fun r : ℝ => r ^ (a - 1)) (Icc 1 (max 1 z)) := by
    apply continuousOn_id.rpow_const
    intro r hr
    exact Or.inl (by change r ≠ 0; linarith [hr.1])
  exact (hcont.integrableOn_Icc).mono_set (by
    intro r hr
    exact ⟨hr.1.le, hr.2.2.trans (le_max_right _ _)⟩)

-- @node: power_increment_nonneg
/-- For a [nonzero exponent](hyp:ha) and [value at least one](hyp:hz), the [corresponding power increment divided by the exponent is nonnegative](goal). -/
lemma power_increment_nonneg {a z : ℝ} (ha : a ≠ 0) (hz : 1 ≤ z) :
    0 ≤ (z ^ a - 1) / a := by
  rw [← power_increment_interval ha hz, intervalIntegral.integral_of_le (by linarith : 0 ≤ z)]
  apply integral_nonneg
  intro r
  simp only [Pi.zero_apply]
  by_cases hr : 1 < r
  · simp only [indicator_of_mem (show r ∈ Ioi (1 : ℝ) from hr)]
    exact Real.rpow_nonneg (by linarith) _
  · simp [indicator_of_notMem (show r ∉ Ioi (1 : ℝ) from hr)]

-- @node: power_moment_layercake
/-- For a [measurable random variable](hyp:hZ) that is [at least one almost surely](hyp:hzone), a [nonzero exponent](hyp:ha), and an [integrable tail kernel](hyp:hTail), its [power is integrable and its expectation has the stated tail-integral representation](goal). -/
lemma power_moment_layercake {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (hzone : ∀ᵐ w ∂μ, 1 ≤ Z w) {a : ℝ} (ha : a ≠ 0)
    (hTail : IntegrableOn (fun r : ℝ => r ^ (a - 1) * μ.real {w | r < Z w}) (Ioi 1)) :
    Integrable (fun w => Z w ^ a) μ ∧
      (∫ w, Z w ^ a ∂μ) = 1 + ∫ r in Ioi 1, a * r ^ (a - 1) * μ.real {w | r < Z w} := by
  let P : Ω → ℝ := fun w => (Z w ^ a - 1) / a
  have hPmeas : Measurable P := by fun_prop
  have hPpos : 0 ≤ᵐ[μ] P := hzone.mono fun w hw => power_increment_nonneg ha hw
  have hcake := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (hzone.mono fun w hw => (by linarith : 0 ≤ Z w)) hZ.aemeasurable
    (fun z hz => power_increment_kernel_intervalIntegrable a hz)
    (Eventually.of_forall fun r => (by
      by_cases hr : 1 < r
      · simp only [indicator_of_mem (show r ∈ Ioi (1 : ℝ) from hr)]
        exact Real.rpow_nonneg (by linarith) _
      · simp [indicator_of_notMem (show r ∉ Ioi (1 : ℝ) from hr)]))
  have hleft : (∫⁻ w, ENNReal.ofReal (∫ r in (0 : ℝ)..Z w,
      (Ioi 1).indicator (fun r : ℝ => r ^ (a - 1)) r) ∂μ) =
      ∫⁻ w, ENNReal.ofReal (P w) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hzone] with w hw
    rw [power_increment_interval ha hw]
  have hright : (∫⁻ r in Ioi (0 : ℝ), μ {w | r < Z w} *
      ENNReal.ofReal ((Ioi 1).indicator (fun r : ℝ => r ^ (a - 1)) r)) =
      ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (r ^ (a - 1) * μ.real {w | r < Z w}) := by
    have heq : (fun r : ℝ => μ {w | r < Z w} *
        ENNReal.ofReal ((Ioi 1).indicator (fun r : ℝ => r ^ (a - 1)) r)) =
        (Ioi 1).indicator (fun r : ℝ => ENNReal.ofReal
          (r ^ (a - 1) * μ.real {w | r < Z w})) := by
      funext r
      by_cases hr : 1 < r
      · simp only [indicator_of_mem (show r ∈ Ioi (1 : ℝ) from hr),
          ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _),
          measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact mul_comm _ _
      · simp [indicator_of_notMem (show r ∉ Ioi (1 : ℝ) from hr)]
    rw [heq, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    rw [inter_eq_left.mpr (show Ioi (1 : ℝ) ⊆ Ioi 0 from fun r hr => by
      exact lt_trans zero_lt_one (mem_Ioi.mp hr))]
  rw [hleft, hright] at hcake
  have hPint : Integrable P μ :=
    (lintegral_ofReal_ne_top_iff_integrable hPmeas.aestronglyMeasurable hPpos).mp
      (hcake.trans_ne hTail.lintegral_lt_top.ne)
  have hrep : (fun w => Z w ^ a) = (fun w => a * P w + 1) := by
    funext w
    dsimp [P]
    field_simp
    ring
  have hint : Integrable (fun w => Z w ^ a) μ := by
    rw [hrep]
    exact (hPint.const_mul a).add (integrable_const 1)
  have hTailpos : 0 ≤ᵐ[volume.restrict (Ioi 1)]
      (fun r : ℝ => r ^ (a - 1) * μ.real {w | r < Z w}) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.rpow_nonneg (by linarith [mem_Ioi.mp hr]) _) ENNReal.toReal_nonneg
  have hreal := congrArg ENNReal.toReal hcake
  rw [← integral_eq_lintegral_of_nonneg_ae hPpos hPmeas.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae hTailpos hTail.aestronglyMeasurable] at hreal
  refine ⟨hint, ?_⟩
  rw [hrep, integral_add (hPint.const_mul a) (integrable_const 1), integral_const_mul,
    hreal]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [show (fun r : ℝ => a * r ^ (a - 1) * μ.real {w | r < Z w}) =
    (fun r => a * (r ^ (a - 1) * μ.real {w | r < Z w})) by funext r; ring,
    integral_const_mul]
  ring
variable {q d : ℕ}

-- @node: tailLaw_probability
/-- Under [regular variation of the noise](hyp:hRV), the [tail-conditioned law is a probability measure](goal). -/
lemma tailLaw_probability (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M) (t : ℝ) :
    IsProbabilityMeasure (tailLaw M t) := by
  apply cond_isProbabilityMeasure
  intro hz
  have hpos := tailProb_pos_of_regularVariation M hRV t
  simp only [tailProb, hz, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos

-- @node: scaled_radius_ge_one_tailLaw
/-- At a [positive threshold](hyp:ht), the [radius divided by that threshold is at least one under the tail law](goal), almost surely. -/
lemma scaled_radius_ge_one_tailLaw (M : ExtremeModel q d) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ w ∂tailLaw M t, 1 ≤ radius M w / t := by
  have hm : MeasurableSet {w | t < radius M w} :=
    measurableSet_lt measurable_const (measurable_radius M)
  filter_upwards [ae_cond_mem (μ := M.mu) hm] with w hw
  exact ((le_div_iff₀ ht).mpr (by simpa using hw.le))

-- @node: tailLaw_scaled_radius_survival
/-- At a [positive threshold](hyp:ht) and for a [scale at least one](hyp:hr), the [tail-law survival probability of the scaled radius equals the ratio of tail probabilities](goal). -/
lemma tailLaw_scaled_radius_survival (M : ExtremeModel q d) {t r : ℝ}
    (ht : 0 < t) (hr : 1 ≤ r) :
    (tailLaw M t).real {w | r < radius M w / t} =
      tailProb M (t * r) / tailProb M t := by
  have hm : MeasurableSet {w | t < radius M w} :=
    measurableSet_lt measurable_const (measurable_radius M)
  have hset : {w | t < radius M w} ∩ {w | r < radius M w / t} =
      {w | t * r < radius M w} := by
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, lt_div_iff₀ ht]
    constructor
    · intro hw
      simpa only [mul_comm] using hw.2
    · intro hw
      constructor
      · exact (by nlinarith : t ≤ t * r).trans_lt hw
      · simpa only [mul_comm] using hw
  unfold Measure.real tailLaw
  rw [cond_apply hm, hset]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, tailProb, div_eq_mul_inv]
  ring

-- @node: tail_power_kernel_eventually_integrable
/-- For [regularly varying noise](hyp:hRV), an [exponent below the tail index](hyp:ha), and a [nonzero exponent](hyp:hzero), the [scaled-tail power kernel is eventually integrable](goal) as the threshold grows. -/
lemma tail_power_kernel_eventually_integrable (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {a : ℝ} (ha : a < M.beta) (hzero : a ≠ 0) :
    ∀ᶠ t in atTop, IntegrableOn
      (fun r : ℝ => r ^ (a - 1) * (tailProb M (t * r) / tailProb M t)) (Ioi 1) := by
  rcases lt_or_gt_of_ne hzero with hneg | hpos
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    apply Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (by linarith : a - 1 < -1)
        (by norm_num : (0 : ℝ) < 1))
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hrpos : 0 < r := by linarith [mem_Ioi.mp hr]
      have hratio : 0 ≤ tailProb M (t * r) / tailProb M t :=
        div_nonneg (tailProb_nonneg M _) (tailProb_nonneg M _)
      have hratio_le : tailProb M (t * r) / tailProb M t ≤ 1 := by
        apply (div_le_iff₀ (tailProb_pos_of_regularVariation M hRV t)).2
        simpa using tailProb_antitone M (by nlinarith [mem_Ioi.mp hr] : t ≤ t * r)
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hrpos.le _),
        abs_of_nonneg hratio]
      exact (mul_le_mul_of_nonneg_left hratio_le
        (Real.rpow_nonneg hrpos.le _)).trans_eq (mul_one _)
  · let eps := min M.beta (M.beta - a) / 2
    have heps : 0 < eps := div_pos (lt_min hRV.1 (sub_pos.mpr ha)) (by norm_num)
    have hepsbeta : eps < M.beta := by
      dsimp [eps]
      linarith [min_le_left M.beta (M.beta - a)]
    have hepsgap : a - M.beta + eps - 1 < -1 := by
      dsimp [eps]
      linarith [min_le_right M.beta (M.beta - a)]
    obtain ⟨T, hT, hbound⟩ := tail_potter_integrand_bound (tailProb M) heps hepsbeta
      ((tailProb_antitone M).antitoneOn (Ioi 0)) (fun t _ => tailProb_nonneg M t)
      (Eventually.of_forall (tailProb_pos_of_regularVariation M hRV))
      (by simpa only [mul_comm] using tailProb_ratio_limit M hRV (x := 2) (by norm_num))
      (a := a)
    filter_upwards [eventually_ge_atTop T] with t ht
    have hint : IntegrableOn
        (fun r : ℝ => a * r ^ (a - 1) * (tailProb M (t * r) / tailProb M t)) (Ioi 1) := by
      apply Integrable.mono'
        ((integrableOn_Ioi_rpow_of_lt hepsgap
          (by norm_num : (0 : ℝ) < 1)).const_mul (|a| * (2 : ℝ) ^ (M.beta - eps)))
      · apply Measurable.aestronglyMeasurable
        fun_prop
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        simpa only [Real.norm_eq_abs] using hbound t ht r (mem_Ioi.mp hr).le
    exact (hint.div_const a).congr (Eventually.of_forall fun r => by
      dsimp only
      field_simp)

-- @node: conditional_radial_power_layercake
/-- For [regularly varying noise](hyp:hRV), an [exponent below the tail index](hyp:ha), and a [nonzero exponent](hyp:hzero), the [conditional scaled radial power moment eventually equals its tail-integral formula](goal). -/
lemma conditional_radial_power_layercake (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {a : ℝ} (ha : a < M.beta) (hzero : a ≠ 0) :
    ∀ᶠ t in atTop,
      (∫ w, radius M w ^ a / t ^ a ∂tailLaw M t) =
        1 + ∫ r : ℝ in Ioi 1,
          a * r ^ (a - 1) * (tailProb M (t * r) / tailProb M t) := by
  filter_upwards [tail_power_kernel_eventually_integrable M hRV ha hzero,
    eventually_gt_atTop (0 : ℝ)] with t hTail ht
  let := tailLaw_probability M hRV t
  have hZ : Measurable (fun w => radius M w / t) := by fun_prop
  have hTail' : IntegrableOn
      (fun r : ℝ => r ^ (a - 1) * (tailLaw M t).real {w | r < radius M w / t}) (Ioi 1) := by
    apply hTail.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only
    rw [tailLaw_scaled_radius_survival M ht (mem_Ioi.mp hr).le]
  have hcake := (power_moment_layercake (tailLaw M t) _ hZ
    (scaled_radius_ge_one_tailLaw M ht) hzero hTail').2
  have heq : (∫ w, radius M w ^ a / t ^ a ∂tailLaw M t) =
      ∫ w, (radius M w / t) ^ a ∂tailLaw M t := by
    apply integral_congr_ae
    filter_upwards [scaled_radius_ge_one_tailLaw M ht] with w hw
    have hr : 0 ≤ radius M w := by
      have := (le_div_iff₀ ht).mp hw
      linarith
    exact (Real.div_rpow hr ht.le a).symm
  rw [heq, hcake]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [tailLaw_scaled_radius_survival M ht (mem_Ioi.mp hr).le]

end Papers.TbsExtremeEffects
