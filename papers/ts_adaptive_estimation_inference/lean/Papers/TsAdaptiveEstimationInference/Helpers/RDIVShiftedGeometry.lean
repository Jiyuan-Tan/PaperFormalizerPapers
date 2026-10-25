module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVLossBridge
/-! Deterministic curvature and density geometry for the shifted likelihood. -/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

/-- Under a probability measure, if [f is square-integrable](hyp:hf), [minus the logarithm of f is integrable](hyp:hlog), [f is positive almost everywhere](hyp:hpos), and [the integral of f squared is at most one](hyp:hmass), then [the squared L2 distance of f from one is at most twice the integral of minus its logarithm](goal). -/
-- @node: rdiv_shifted_log_curvature
lemma rdiv_shifted_log_curvature {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (f : Y → ℝ)
    (hf : MemLp f 2 μ) (hlog : Integrable (fun y => -Real.log (f y)) μ)
    (hpos : ∀ᵐ y ∂μ, 0 < f y) (hmass : (∫ y, f y ^ 2 ∂μ) ≤ 1) :
    inputL2Norm μ (f - fun _ => 1) ^ 2 ≤ 2 * ∫ y, -Real.log (f y) ∂μ := by
  have hi := hf.integrable (by norm_num)
  have hsq := hf.integrable_sq
  have hd : (∫ y, (f y - 1) ^ 2 ∂μ) =
      (∫ y, f y ^ 2 ∂μ) - 2 * (∫ y, f y ∂μ) + 1 := by
    have he : (fun y => (f y - 1) ^ 2) =
        (fun y => f y ^ 2 - 2 * f y + 1) := by funext y; ring
    have hdi : Integrable (fun y => f y ^ 2 - 2 * f y) μ := hsq.sub (hi.const_mul 2)
    rw [he, integral_add hdi (integrable_const 1),
      integral_sub hsq (hi.const_mul 2), integral_const_mul]
    simp
  have hl : (∫ y, 1 - f y ∂μ) ≤ ∫ y, -Real.log (f y) ∂μ := by
    apply integral_mono_ae ((integrable_const 1).sub hi) hlog
    filter_upwards [hpos] with y hy
    change 1 - f y ≤ -Real.log (f y)
    linarith only [Real.log_le_sub_one_of_pos hy]
  rw [integral_sub (integrable_const 1) hi] at hl
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] at hl
  rw [inputL2Norm, Real.sq_sqrt (integral_nonneg (fun y => sq_nonneg _))]
  simp only [Pi.sub_apply]
  rw [hd]
  linarith only [hmass, hl]

/-- If [a is nonnegative](hyp:ha) and [b is positive](hyp:hb), then [the squared difference between their square roots is at most sixteen times b times the squared difference between one and the square root of their midpoint divided by b](goal). -/
-- @node: rdiv_shifted_sqrt_comparison
lemma rdiv_shifted_sqrt_comparison (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤
      16 * (Real.sqrt ((a + b) / (2 * b)) - 1) ^ 2 * b := by
  let s := Real.sqrt a
  let v := Real.sqrt b
  let q := Real.sqrt ((a + b) / 2)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hv : 0 < v := Real.sqrt_pos.mpr hb
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha
  have hv2 : v ^ 2 = b := Real.sq_sqrt hb.le
  have hq2 : q ^ 2 = (a + b) / 2 := Real.sq_sqrt (by positivity)
  have hqv : q ≤ s + v := by
    apply (sq_le_sq₀ hq (by positivity : 0 ≤ s + v)).mp
    nlinarith only [hs2, hv2, hq2, mul_nonneg hs hv.le, ha, hb]
  have hid : (s - v) * (s + v) = 2 * (q - v) * (q + v) := by
    nlinarith only [hs2, hv2, hq2]
  have habs : |s - v| * (s + v) = 2 * |q - v| * (q + v) := by
    simpa only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ s + v),
      abs_of_nonneg (by positivity : 0 ≤ q + v),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using congrArg abs hid
  have hbound : |s - v| ≤ 4 * |q - v| := by
    have hp : 0 < s + v := by positivity
    apply (mul_le_mul_iff_left₀ hp).mp
    have ht := mul_le_mul_of_nonneg_left
      (show q + v ≤ 2 * (s + v) by linarith only [hqv, hs]) (abs_nonneg (q - v))
    nlinarith only [habs, ht]
  have hsq := pow_le_pow_left₀ (abs_nonneg (s - v)) hbound 2
  rw [sq_abs, mul_pow, sq_abs] at hsq
  have he : Real.sqrt ((a + b) / (2 * b)) = q / v := by
    rw [show (a + b) / (2 * b) = ((a + b) / 2) / b by ring,
      Real.sqrt_div (by positivity)]
  rw [he]
  have he' : (q / v - 1) ^ 2 * b = (q - v) ^ 2 := by
    rw [← hv2]
    field_simp
  nlinarith only [hsq, he']

/-- If [the instrumental-variable model has true conditional density g₀ relative to μ](hyp:hIV), [the density class contains g₀ and consists of measurable, nonnegative, normalized conditional densities](hyp:hDensity), [the densities satisfy the common support and lower and upper bounds](hyp:hBounds), and [g belongs to this class](hyp:hg), then [under the true joint law the squared L2 distance from one of the square root of the midpoint-density ratio is at most twice its negative-log integral, and the instrument-averaged squared Hellinger distance between g and g₀ is at most sixteen times that squared L2 distance](goal). -/
-- @node: rdiv_shifted_density_geometry
lemma rdiv_shifted_density_geometry
    {𝒲 X Z : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X] [MeasurableSpace Z]
    (V : IVWorld 𝒲 X Z) (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG) (hg : g ∈ G) :
    let f := fun y : X × Z =>
      Real.sqrt ((g y.1 y.2 + g₀ y.1 y.2) / (2 * g₀ y.1 y.2))
    let Q := V.law.map (fun w => (V.xOf w, V.zOf w))
    inputL2Norm Q (f - fun _ => 1) ^ 2 ≤ 2 * (∫ y, -Real.log (f y) ∂Q) ∧
      (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ 16 * inputL2Norm Q (f - fun _ => 1) ^ 2 := by
  dsimp only
  let Q := V.law.map (fun w => (V.xOf w, V.zOf w))
  let ν := V.law.map V.zOf
  let f := fun y : X × Z =>
    Real.sqrt ((g y.1 y.2 + g₀ y.1 y.2) / (2 * g₀ y.1 y.2))
  have : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map (V.measurable_x.prodMk V.measurable_z).aemeasurable
  have : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  have hgm := (hDensity.2 g hg).1
  have h₀m := (hDensity.2 g₀ hDensity.1).1
  have hg0 := (hDensity.2 g hg).2.1
  have h₀0 := (hDensity.2 g₀ hDensity.1).2.1
  have hratio := rdiv_density_ratio_of_bounds G g₀ g support c₀ CG
    hBounds hDensity.1 hg
  have hzero (x : X) (z : Z) (hx : g₀ x z = 0) : g x z = 0 := by
    exact le_antisymm (by simpa [hx] using hratio x z) (hg0 x z)
  have hfm : Measurable f := by
    dsimp [f]
    fun_prop
  let M := Real.sqrt ((CG / c₀ + 1) / 2)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hfbound (y : X × Z) : f y ≤ M := by
    apply Real.sqrt_le_sqrt
    by_cases hz : g₀ y.1 y.2 = 0
    · simp only [hz, mul_zero, div_zero]
      exact div_nonneg
        (add_nonneg (div_nonneg hBounds.2.1.le hBounds.1.le) (by norm_num)) (by norm_num)
    · have hp : 0 < g₀ y.1 y.2 := lt_of_le_of_ne (h₀0 _ _) (Ne.symm hz)
      apply (div_le_iff₀ (mul_pos (by norm_num) hp)).2
      nlinarith only [hratio y.1 y.2]
  have hfLp : MemLp f 2 Q := MemLp.of_bound hfm.aestronglyMeasurable M
    (by
      apply ae_of_all
      intro y
      change |f y| ≤ M
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hfbound y)
  have hpositive : ∀ᵐ y ∂Q, 0 < g₀ y.1 y.2 := by
    dsimp [Q]
    rw [hIV.2.1]
    apply (ae_withDensity_iff h₀m.ennreal_ofReal).2
    exact ae_of_all _ fun y hy =>
      lt_of_not_ge (fun h => hy (ENNReal.ofReal_eq_zero.mpr h))
  have hflower : ∀ᵐ y ∂Q, 1 / 2 ≤ f y := by
    filter_upwards [hpositive] with y hy
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (by positivity : 0 < 2 * g₀ y.1 y.2)).2
    nlinarith only [hg0 y.1 y.2, hy]
  have hlog : Integrable (fun y => -Real.log (f y)) Q := by
    apply (integrable_const (M + 2)).mono' hfm.log.neg.aestronglyMeasurable
    filter_upwards [hflower] with y hy
    have hp : 0 < f y := by linarith only [hy]
    have hupper := Real.log_le_sub_one_of_pos hp
    have hlower := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw [Real.log_inv] at hlower
    have hinv : (f y)⁻¹ ≤ 2 := by
      apply (inv_le_comm₀ hp (by norm_num : (0 : ℝ) < 2)).2
      simpa using hy
    change ‖-Real.log (f y)‖ ≤ M + 2
    rw [Real.norm_eq_abs, abs_neg]
    apply abs_le.mpr
    constructor <;> linarith only [hupper, hlower, hinv, hfbound y, hM]
  have hweight (x : X) (z : Z) : f (x, z) ^ 2 * g₀ x z = (g x z + g₀ x z) / 2 := by
    by_cases hz : g₀ x z = 0
    · simp [f, hz, hzero x z hz]
    · dsimp [f]
      rw [Real.sq_sqrt (div_nonneg (add_nonneg (hg0 x z) (h₀0 x z))
        (mul_nonneg (by norm_num) (h₀0 x z)))]
      field_simp
  have hmass : (∫ y, f y ^ 2 ∂Q) = 1 := by
    obtain ⟨_, _, he⟩ := rdiv_density_integral_disintegration V μ G g₀ hIV hDensity
      (fun y => f y ^ 2) (hfm.pow_const 2) hfLp.integrable_sq
    have hsections : (fun z => ∫ x, f (x, z) ^ 2 * g₀ x z ∂μ) =ᵐ[ν] fun _ => 1 := by
      filter_upwards [rdiv_density_integrable_of_realizable V μ G g₀ g hDensity hg,
        rdiv_density_integrable_of_realizable V μ G g₀ g₀ hDensity hDensity.1,
        (hDensity.2 g hg).2.2, (hDensity.2 g₀ hDensity.1).2.2] with z hi hi₀ hn hn₀
      simp_rw [hweight]
      rw [integral_div, integral_add hi hi₀, hn, hn₀]
      norm_num
    rw [integral_congr_ae hsections] at he
    have hmap := integral_map (μ := V.law) (V.measurable_x.prodMk V.measurable_z).aemeasurable
      (hfm.pow_const 2).aestronglyMeasurable
    change (∫ y, f y ^ 2 ∂Q) = _ at hmap
    rw [hmap, ← he]
    simp
  refine ⟨rdiv_shifted_log_curvature Q f hfLp hlog
    (hflower.mono fun y hy => by linarith only [hy]) hmass.le, ?_⟩
  have heLp : MemLp (fun y => f y - 1) 2 Q := hfLp.sub (memLp_const 1)
  have hem : Measurable (fun y => (f y - 1) ^ 2) := by fun_prop
  obtain ⟨hsec, hint, he⟩ := rdiv_density_integral_disintegration V μ G g₀ hIV hDensity
    (fun y => (f y - 1) ^ 2) hem heLp.integrable_sq
  have hHmeas : AEStronglyMeasurable
      (fun z => hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)) ν := by
    apply rdiv_density_supported_integral_aestronglyMeasurable V μ G g₀ hIV hDensity
      (fun p => (Real.sqrt (g p.1 p.2) - Real.sqrt (g₀ p.1 p.2)) ^ 2)
      ((hgm.sqrt.sub h₀m.sqrt).pow_const 2)
    intro x z hx
    simp [hx, hzero x z hx]
  have hHbounds : ∀ᵐ z ∂ν, 0 ≤ hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z) ∧
      hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z) ≤ 2 := by
    filter_upwards [rdiv_density_integrable_of_realizable V μ G g₀ g hDensity hg,
      rdiv_density_integrable_of_realizable V μ G g₀ g₀ hDensity hDensity.1,
      (hDensity.2 g hg).2.2, (hDensity.2 g₀ hDensity.1).2.2] with z hi hi₀ hn hn₀
    exact Causalean.Stat.Minimax.hellingerSqDensity_bounds μ _ _ hi hi₀
      (fun x => hg0 x z) (fun x => h₀0 x z) hn hn₀
  have hHi : Integrable (fun z => hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)) ν :=
    (integrable_const 2).mono' hHmeas (hHbounds.mono fun z hz => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hz.1] using hz.2)
  have hcomp : (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z) ∂ν) ≤
      16 * ∫ z, ∫ x, (f (x, z) - 1) ^ 2 * g₀ x z ∂μ ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono_ae hHi (hint.const_mul 16)
    filter_upwards [hsec,
      rdiv_density_integrable_of_realizable V μ G g₀ g hDensity hg,
      rdiv_density_integrable_of_realizable V μ G g₀ g₀ hDensity hDensity.1]
      with z hi hgi h₀i
    rw [← integral_const_mul]
    apply integral_mono_ae
      (Causalean.Stat.Minimax.integrable_sqrt_sum_sub_sq μ _ _ hgi h₀i
        (fun x => hg0 x z) (fun x => h₀0 x z)).2 (hi.const_mul 16)
    apply ae_of_all
    intro x
    by_cases hz : g₀ x z = 0
    · simp [f, hz, hzero x z hz]
    · simpa only [f, mul_assoc] using rdiv_shifted_sqrt_comparison _ _ (hg0 x z)
        (lt_of_le_of_ne (h₀0 x z) (Ne.symm hz))
  have hmap := integral_map (μ := V.law) (V.measurable_x.prodMk V.measurable_z).aemeasurable
    hem.aestronglyMeasurable
  change (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
    ∂V.law.map V.zOf) ≤ 16 * ∫ z, ∫ x, (f (x, z) - 1) ^ 2 * g₀ x z
      ∂μ ∂V.law.map V.zOf at hcomp
  rw [he, ← hmap] at hcomp
  change (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z) ∂ν) ≤
    16 * inputL2Norm Q (f - fun _ => 1) ^ 2
  rw [inputL2Norm]
  simp only [Pi.sub_apply]
  rw [Real.sq_sqrt (integral_nonneg (fun y => sq_nonneg (f y - 1)))]
  exact hcomp

end Papers.TsAdaptiveEstimationInference
