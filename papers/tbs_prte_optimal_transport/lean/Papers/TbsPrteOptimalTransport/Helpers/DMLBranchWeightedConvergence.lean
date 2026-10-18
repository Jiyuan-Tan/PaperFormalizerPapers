module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIPWConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryBranchRates
/-! L2 convergence of residual corrections multiplied by fitted active branches.
The discrepancy splits into a residual error and a branch error; clipping bounds
the coefficients and the population residual without requiring uniform convergence. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology

-- @node: clipped_weighted_residual_sq_difference_bound
/-- If [the absolute fitted weight is at most its weight bound](hyp:hw) and
[the absolute reference residual is at most its residual bound](hyp:hf), [the
squared error of the weighted residual is at most twice the squared weight bound
times the squared residual error plus twice the squared residual bound times
the squared weight error](goal). -/
lemma clipped_weighted_residual_sq_difference_bound {w wh f fh W R : ℝ}
    (hw : |wh| ≤ W) (hf : |f| ≤ R) :
    (wh * fh - w * f) ^ 2 ≤
      2 * W ^ 2 * (fh - f) ^ 2 + 2 * R ^ 2 * (wh - w) ^ 2 := by
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  have hR : 0 ≤ R := (abs_nonneg _).trans hf
  have hws : wh ^ 2 ≤ W ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg wh) hw 2
  have hfs : f ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg f) hf 2
  calc
    _ = (wh * (fh - f) + (wh - w) * f) ^ 2 := by ring
    _ ≤ 2 * (wh * (fh - f)) ^ 2 + 2 * ((wh - w) * f) ^ 2 := by
      nlinarith [sq_nonneg (wh * (fh - f) - (wh - w) * f)]
    _ ≤ _ := by
      rw [mul_pow, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_right hws (sq_nonneg (fh - f)),
        mul_le_mul_of_nonneg_left hfs (sq_nonneg (wh - w))]

-- L2 differences suffice for integrability of the weighted squared error.
-- @node: clipped_weighted_residual_integrated_sq_bound
/-- For [measurable reference weights](hyp:hw), [measurable fitted weights](hyp:hwh),
[measurable reference residuals](hyp:hf), and [measurable fitted residuals](hyp:hfh), assume [weight
errors have finite second moments](hyp:hew), [residual errors have finite second
moments](hyp:hef), [fitted weights obey an absolute bound almost
everywhere](hyp:hwb), and [reference residuals obey an absolute bound almost
everywhere](hyp:hfb). Then [the squared weighted-residual error is integrable,
and its integral is at most twice the squared weight bound times the integrated
squared residual error plus twice the squared residual bound times the
integrated squared weight error](goal). -/
lemma clipped_weighted_residual_integrated_sq_bound {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (w wh f fh : B → ℝ) (W R : ℝ)
    (hw : Measurable w) (hwh : Measurable wh)
    (hf : Measurable f) (hfh : Measurable fh)
    (hew : MemLp (fun x => wh x - w x) 2 ν)
    (hef : MemLp (fun x => fh x - f x) 2 ν)
    (hwb : ∀ᵐ x ∂ν, |wh x| ≤ W) (hfb : ∀ᵐ x ∂ν, |f x| ≤ R) :
    Integrable (fun x => (wh x * fh x - w x * f x) ^ 2) ν ∧
      (∫ x, (wh x * fh x - w x * f x) ^ 2 ∂ν) ≤
        2 * W ^ 2 * (∫ x, (fh x - f x) ^ 2 ∂ν) +
          2 * R ^ 2 * (∫ x, (wh x - w x) ^ 2 ∂ν) := by
  have hm : Measurable (fun x => (wh x * fh x - w x * f x) ^ 2) := by fun_prop
  have hb : ∀ᵐ x ∂ν, (wh x * fh x - w x * f x) ^ 2 ≤
      2 * W ^ 2 * (fh x - f x) ^ 2 + 2 * R ^ 2 * (wh x - w x) ^ 2 := by
    filter_upwards [hwb, hfb] with x hx hy
    exact clipped_weighted_residual_sq_difference_bound hx hy
  have hd := (hef.integrable_sq.const_mul (2 * W ^ 2)).add
    (hew.integrable_sq.const_mul (2 * R ^ 2))
  have hi := hd.mono' hm.aestronglyMeasurable (by
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (sq_nonneg (wh x * fh x - w x * f x))] using hx)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, 2 * W ^ 2 * (fh x - f x) ^ 2 +
        2 * R ^ 2 * (wh x - w x) ^ 2 ∂ν := integral_mono_ae hi hd hb
    _ = _ := by
      rw [integral_add (hef.integrable_sq.const_mul _) (hew.integrable_sq.const_mul _),
        integral_const_mul, integral_const_mul]

-- The component energies, rather than a score-convergence premise, control
-- the fitted correction. This also applies to continuous boundary indicators.
-- @node: dml_weighted_residual_sq_tendsto_probability_zero
/-- Suppose [reference weights are measurable](hyp:hw), [reference residuals
are measurable](hyp:hf), [all fitted weights are measurable](hyp:hwh), and
[all fitted residuals are measurable](hyp:hfh),
[all weight errors](hyp:hew) and [all residual errors](hyp:hef) have finite
second moments, [fitted weights are uniformly bounded almost everywhere](hyp:hwb),
and [reference residuals are uniformly bounded almost everywhere for every
sample size and training realization](hyp:hfb). If [integrated squared weight
errors tend to zero in probability](hyp:hrw) and [integrated squared residual
errors tend to zero in probability](hyp:hrf), [the integrated squared weighted-residual error tends to zero
in probability](goal). -/
lemma dml_weighted_residual_sq_tendsto_probability_zero {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (w f : B → ℝ)
    (wh fh : ℕ → A → B → ℝ) (W R : ℝ)
    (hw : Measurable w) (hf : Measurable f)
    (hwh : ∀ n a, Measurable (wh n a)) (hfh : ∀ n a, Measurable (fh n a))
    (hew : ∀ n a, MemLp (fun x => wh n a x - w x) 2 ν)
    (hef : ∀ n a, MemLp (fun x => fh n a x - f x) 2 ν)
    (hwb : ∀ n a, ∀ᵐ x ∂ν, |wh n a x| ≤ W)
    (hfb : ∀ (_n : ℕ) (_a : A), ∀ᵐ x ∂ν, |f x| ≤ R)
    (hrw : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (wh n a x - w x) ^ 2 ∂ν) atTop (fun _ _ => 0))
    (hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (fh n a x - f x) ^ 2 ∂ν) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (wh n a x * fh n a x - w x * f x) ^ 2 ∂ν)
      atTop (fun _ _ => 0) := by
  have hcf : Continuous (fun t : ℝ => 2 * W ^ 2 * t) := by fun_prop
  have hcw : Continuous (fun t : ℝ => -(2 * R ^ 2 * t)) := by fun_prop
  have hF := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hcf.continuousAt hrf
  have hW := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hcw.continuousAt hrw
  simp only [mul_zero, neg_zero] at hF hW
  have hs := hF.sub hW
  simp only [sub_neg_eq_add, sub_zero] at hs
  apply probability_zero_of_nonneg_le μ _ _ hs
  intro n
  apply Eventually.of_forall
  intro a
  exact ⟨integral_nonneg (fun x => sq_nonneg _),
    (clipped_weighted_residual_integrated_sq_bound ν w (wh n a) f (fh n a) W R
      hw (hwh n a) hf (hfh n a) (hew n a) (hef n a) (hwb n a) (hfb n a)).2⟩

-- The active coefficient in the binary correction is discontinuous. Its
-- energy is derived from the gap and the three affine-argument rates, while
-- the IPW residual energy is derived from regression and denominator rates.
-- @node: dml_binary_active_ipw_residual_sq_tendsto_probability_zero
/-- Assume [a positive branch separation margin](hyp:hsep), [a positive
denominator bound](hyp:hc), [measurable upper thresholds](hyp:hq),
[measurable lower thresholds](hyp:hl), [measurable boundary arguments](hyp:hb),
[measurable reference denominators](hyp:hp), [measurable reference regressions](hyp:hj),
[measurable outcomes](hyp:hy), [measurable assignment weights](hyp:ha),
[measurable fitted upper thresholds](hyp:hqh), [measurable fitted lower thresholds](hyp:hlh),
[measurable fitted boundary arguments](hyp:hbh), [measurable fitted denominators](hyp:hph),
and [measurable fitted regressions](hyp:hjh). If [upper-threshold errors have
finite second moments](hyp:heq), [lower-threshold errors have finite second moments](hyp:hel),
[boundary-argument errors have finite second moments](hyp:heb),
[denominator errors have finite second moments](hyp:heP),
[regression errors have finite second moments](hyp:heJ),
[the reference thresholds and boundary arguments are
separated almost everywhere](hyp:hgap), [reference and fitted denominators
exceed the positive bound almost everywhere](hyp:hclip), [assignment weights
have absolute value at most one almost everywhere](hyp:hassign), [reference
outcome residuals obey a common absolute bound almost everywhere](hyp:hres),
and [upper-threshold L2 errors are negligible relative to the inverse fourth
root of total sample size](hyp:hrq), [lower-threshold L2 errors obey the same
quarter-rate bound](hyp:hrl), [boundary-argument L2 errors obey that quarter-rate
bound](hyp:hrb), [denominator L2 errors obey that quarter-rate bound](hyp:hrP),
and [regression L2 errors obey that quarter-rate bound](hyp:hrJ), then [the integrated squared error of the
inverse-probability-weighted outcome residual restricted to the active branch,
where the upper threshold exceeds both the lower threshold and boundary
argument, tends to zero in probability](goal). -/
lemma dml_binary_active_ipw_residual_sq_tendsto_probability_zero {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure ν]
    (q l b p j y a : B → ℝ) (qh lh bh ph jh : ℕ → A → B → ℝ)
    (sep c R : ℝ) (hsep : 0 < sep) (hc : 0 < c)
    (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hp : Measurable p) (hj : Measurable j) (hy : Measurable y) (ha : Measurable a)
    (hqh : ∀ n t, Measurable (qh n t)) (hlh : ∀ n t, Measurable (lh n t))
    (hbh : ∀ n t, Measurable (bh n t)) (hph : ∀ n t, Measurable (ph n t))
    (hjh : ∀ n t, Measurable (jh n t))
    (heq : ∀ n t, MemLp (fun x => qh n t x - q x) 2 ν)
    (hel : ∀ n t, MemLp (fun x => lh n t x - l x) 2 ν)
    (heb : ∀ n t, MemLp (fun x => bh n t x - b x) 2 ν)
    (heP : ∀ n t, MemLp (fun x => ph n t x - p x) 2 ν)
    (heJ : ∀ n t, MemLp (fun x => jh n t x - j x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, sep ≤ q x - l x ∧ sep ≤ |b x - l x| ∧ sep ≤ |b x - q x|)
    (hclip : ∀ n t, ∀ᵐ x ∂ν, c ≤ p x ∧ c ≤ ph n t x)
    (hassign : ∀ᵐ x ∂ν, |a x| ≤ 1) (hres : ∀ᵐ x ∂ν, |y x - j x| ≤ R)
    (hrq : Causalean.Stat.IsLittleOp
      (fun n t => Real.sqrt (∫ x, (qh n t x - q x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrl : Causalean.Stat.IsLittleOp
      (fun n t => Real.sqrt (∫ x, (lh n t x - l x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrb : Causalean.Stat.IsLittleOp
      (fun n t => Real.sqrt (∫ x, (bh n t x - b x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrP : Causalean.Stat.IsLittleOp
      (fun n t => Real.sqrt (∫ x, (ph n t x - p x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrJ : Causalean.Stat.IsLittleOp
      (fun n t => Real.sqrt (∫ x, (jh n t x - j x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (indicator (qh n t x > max (lh n t x) (bh n t x)) *
            (a x / ph n t x * (y x - jh n t x)) -
          indicator (q x > max (l x) (b x)) * (a x / p x * (y x - j x))) ^ 2 ∂ν)
      atTop (fun _ _ => 0) := by
  let w := fun x => indicator (q x > max (l x) (b x))
  let wh := fun n t x => indicator (qh n t x > max (lh n t x) (bh n t x))
  have hw : Measurable w := by
    dsimp only [w]
    fun_prop
  have hwh : ∀ n t, Measurable (wh n t) := by
    intro n t
    dsimp only [wh]
    fun_prop
  have hwb : ∀ n t x, |wh n t x| ≤ 1 := by
    intro n t x
    dsimp only [wh, indicator]
    split_ifs <;> norm_num
  have hew : ∀ n t, MemLp (fun x => wh n t x - w x) 2 ν := by
    intro n t
    apply MemLp.of_bound (by fun_prop) 1
    apply Eventually.of_forall
    intro x
    dsimp only [wh, w, indicator]
    split_ifs <;> norm_num
  have hBr := binary_branch_component_energy_isLittleOp μ ν q l b qh lh bh sep
    hsep hq hl hb hqh hlh hbh heq hel heb hgap hrq hrl hrb
  have hBrL2 := dml_half_rate_energy_l2_tendsto_probability_zero μ _
    (fun n t => integral_nonneg fun x =>
      add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) hBr
  have hsquare : Continuous (fun z : ℝ => z ^ 2) := by fun_prop
  have hBrZero := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hsquare.continuousAt hBrL2
  simp only [Real.sq_sqrt (integral_nonneg fun x =>
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)),
    zero_pow (by norm_num : 2 ≠ 0)] at hBrZero
  have hrw : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (wh n t x - w x) ^ 2 ∂ν) atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hBrZero
    intro n
    apply Eventually.of_forall
    intro t
    refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
    apply integral_mono (hew n t).integrable_sq
      (binary_branch_component_energy_bound ν q l b (qh n t) (lh n t) (bh n t) sep
        hsep hq hl hb (hqh n t) (hlh n t) (hbh n t) (heq n t) (hel n t)
        (heb n t) hgap).1
    intro x
    dsimp only [wh, w, binaryBranchSqError]
    linarith [sq_nonneg (indicator (lh n t x < bh n t x ∧ bh n t x < qh n t x) -
      indicator (l x < b x ∧ b x < q x)),
      sq_nonneg (indicator (lh n t x > bh n t x) - indicator (l x > b x))]
  apply dml_weighted_residual_sq_tendsto_probability_zero μ ν w
    (fun x => a x / p x * (y x - j x)) wh
    (fun n t x => a x / ph n t x * (y x - jh n t x)) 1 (R / c)
    hw (by fun_prop) hwh (by intro n t; fun_prop) hew
  · intro n t
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    exact (clipped_ipw_residual_integrated_sq_bound ν p (ph n t) j (jh n t) y a c R
      hc hp (hph n t) hj (hjh n t) hy ha (heJ n t) (heP n t)
      (hclip n t) hassign hres).1
  · exact fun n t => Eventually.of_forall (hwb n t)
  · intro n t
    filter_upwards [hclip n t, hassign, hres] with x hx hax hrx
    have hp0 := hc.trans_le hx.1
    rw [abs_mul, abs_div, abs_of_pos hp0]
    calc
      _ ≤ (1 / p x) * R := by gcongr
      _ ≤ (1 / c) * R := by
        apply mul_le_mul_of_nonneg_right _ ((abs_nonneg _).trans hrx)
        exact div_le_div_of_nonneg_left (by norm_num) hc hx.1
      _ = _ := by ring
  · exact hrw
  · exact dml_clipped_ipw_residual_sq_tendsto_probability_zero μ ν p j y a ph jh c R
      hc hp hj hy ha hph hjh heJ heP hclip hassign hres hrJ hrP

end Papers.TbsPrteOptimalTransport
