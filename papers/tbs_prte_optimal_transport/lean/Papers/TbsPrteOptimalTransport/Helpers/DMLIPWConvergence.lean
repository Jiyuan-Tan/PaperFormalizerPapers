module
public import Papers.TbsPrteOptimalTransport.Helpers.DenominatorOrthogonality
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndicatorRates
/-! Squared-error control for clipped IPW residuals in the DML score.
The same observed outcome and assignment indicator are used in both scores;
only the regression and assignment-probability nuisances change. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology

-- @node: clipped_ipw_residual_difference_bound
/-- If [the denominator lower bound is positive](hyp:hc), [the reference denominator is at least that bound](hyp:hp), [the fitted denominator also is at least that bound](hyp:hph), [the assignment weight has absolute value at most one](hyp:ha), and [the absolute reference outcome residual is at most the residual bound](hyp:hR), then [the absolute change in the inverse-probability-weighted outcome residual is at most the absolute mean error divided by the denominator bound plus the residual bound times the absolute denominator error divided by the square of the denominator bound](goal). -/
lemma clipped_ipw_residual_difference_bound {p ph j jh y a c R : ℝ}
    (hc : 0 < c) (hp : c ≤ p) (hph : c ≤ ph)
    (ha : |a| ≤ 1) (hR : |y - j| ≤ R) :
    |a / ph * (y - jh) - a / p * (y - j)| ≤
      |jh - j| / c + R * |ph - p| / c ^ 2 := by
  have hph0 : 0 < ph := hc.trans_le hph
  have hcoef : |a / ph| ≤ 1 / c := by
    rw [abs_div, abs_of_pos hph0]
    exact (div_le_div_of_nonneg_right ha hph0.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hc hph)
  have hrec := clipped_reciprocal_error_bound hc hph hp
  have hid : a / ph * (y - jh) - a / p * (y - j) =
      -(a / ph * (jh - j)) + a * (ph⁻¹ - p⁻¹) * (y - j) := by
    simp only [div_eq_mul_inv]
    ring
  rw [hid]
  calc
    _ ≤ |a / ph| * |jh - j| + |a| * |ph⁻¹ - p⁻¹| * |y - j| := by
      simpa only [abs_neg, abs_mul] using abs_add_le
        (-(a / ph * (jh - j))) (a * (ph⁻¹ - p⁻¹) * (y - j))
    _ ≤ (1 / c) * |jh - j| + 1 * (|ph - p| / c ^ 2) * R := by
      gcongr
    _ = _ := by ring

-- @node: clipped_ipw_residual_sq_difference_bound
/-- With [a positive denominator lower bound](hyp:hc), [a reference denominator at least that large](hyp:hp), [a fitted denominator at least that large](hyp:hph), [an assignment weight of absolute value at most one](hyp:ha), and [a reference outcome residual bounded in absolute value](hyp:hR), [the squared change in the weighted residual is bounded by twice the squared mean error divided by the squared denominator bound plus twice the squared residual bound times the squared denominator error divided by the fourth power of the denominator bound](goal). -/
lemma clipped_ipw_residual_sq_difference_bound {p ph j jh y a c R : ℝ}
    (hc : 0 < c) (hp : c ≤ p) (hph : c ≤ ph)
    (ha : |a| ≤ 1) (hR : |y - j| ≤ R) :
    (a / ph * (y - jh) - a / p * (y - j)) ^ 2 ≤
      (2 / c ^ 2) * (jh - j) ^ 2 +
        (2 * R ^ 2 / (c ^ 2) ^ 2) * (ph - p) ^ 2 := by
  have hb := clipped_ipw_residual_difference_bound (jh := jh) hc hp hph ha hR
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  have hs := mul_self_le_mul_self (abs_nonneg _) hb
  have hcross := sq_nonneg (|jh - j| / c - R * |ph - p| / c ^ 2)
  have hid : 2 * (|jh - j| / c) ^ 2 + 2 * (R * |ph - p| / c ^ 2) ^ 2 =
      (2 / c ^ 2) * (jh - j) ^ 2 +
        (2 * R ^ 2 / (c ^ 2) ^ 2) * (ph - p) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, sq_abs, sq_abs]
    ring
  rw [← hid]
  nlinarith [sq_abs (a / ph * (y - jh) - a / p * (y - j))]

-- L2 nuisance errors provide integrability of the squared score error.
-- @node: clipped_ipw_residual_integrated_sq_bound
/-- Suppose [the denominator lower bound is positive](hyp:hc), [the reference probability](hyp:hp), [fitted probability](hyp:hph), [reference mean](hyp:hj), [fitted mean](hyp:hjh), [outcome](hyp:hy), and [assignment weight](hyp:ha) are measurable, and [the mean error](hyp:heJ) and [probability error](hyp:heP) are square integrable. If [both probabilities are at least the denominator bound almost everywhere](hyp:hclip), [the assignment weight has absolute value at most one almost everywhere](hyp:hassign), and [the reference outcome residual is bounded in absolute value almost everywhere](hyp:hres), then [the squared weighted-residual difference is integrable, and its integral is at most twice the integrated squared mean error divided by the squared denominator bound plus twice the squared residual bound times the integrated squared probability error divided by the fourth power of the denominator bound](goal). -/
lemma clipped_ipw_residual_integrated_sq_bound {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (p ph j jh y a : B → ℝ) (c R : ℝ)
    (hc : 0 < c) (hp : Measurable p) (hph : Measurable ph)
    (hj : Measurable j) (hjh : Measurable jh)
    (hy : Measurable y) (ha : Measurable a)
    (heJ : MemLp (fun x => jh x - j x) 2 ν)
    (heP : MemLp (fun x => ph x - p x) 2 ν)
    (hclip : ∀ᵐ x ∂ν, c ≤ p x ∧ c ≤ ph x)
    (hassign : ∀ᵐ x ∂ν, |a x| ≤ 1)
    (hres : ∀ᵐ x ∂ν, |y x - j x| ≤ R) :
    let E := fun x => (a x / ph x * (y x - jh x) - a x / p x * (y x - j x)) ^ 2
    Integrable E ν ∧ (∫ x, E x ∂ν) ≤
      (2 / c ^ 2) * (∫ x, (jh x - j x) ^ 2 ∂ν) +
        (2 * R ^ 2 / (c ^ 2) ^ 2) * (∫ x, (ph x - p x) ^ 2 ∂ν) := by
  dsimp only
  have hm : Measurable (fun x =>
      (a x / ph x * (y x - jh x) - a x / p x * (y x - j x)) ^ 2) := by
    fun_prop
  have hb : ∀ᵐ x ∂ν,
      (a x / ph x * (y x - jh x) - a x / p x * (y x - j x)) ^ 2 ≤
        (2 / c ^ 2) * (jh x - j x) ^ 2 +
          (2 * R ^ 2 / (c ^ 2) ^ 2) * (ph x - p x) ^ 2 := by
    filter_upwards [hclip, hassign, hres] with x hx hax hrx
    exact clipped_ipw_residual_sq_difference_bound hc hx.1 hx.2 hax hrx
  have hd := (heJ.integrable_sq.const_mul (2 / c ^ 2)).add
    (heP.integrable_sq.const_mul (2 * R ^ 2 / (c ^ 2) ^ 2))
  have hi := hd.mono' hm.aestronglyMeasurable (by
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, Pi.add_apply, abs_of_nonneg (sq_nonneg
      (a x / ph x * (y x - jh x) - a x / p x * (y x - j x)))] using hx)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, (2 / c ^ 2) * (jh x - j x) ^ 2 +
        (2 * R ^ 2 / (c ^ 2) ^ 2) * (ph x - p x) ^ 2 ∂ν := integral_mono_ae hi hd hb
    _ = _ := by
      rw [integral_add (heJ.integrable_sq.const_mul _) (heP.integrable_sq.const_mul _),
        integral_const_mul, integral_const_mul]

-- The conditional squared score discrepancy vanishes using the stated
-- nuisance rates; no rate for the score itself is imposed.
-- @node: dml_clipped_ipw_residual_sq_tendsto_probability_zero
/-- Assume [a positive denominator lower bound](hyp:hc), measurable [reference probabilities](hyp:hp), [reference means](hyp:hj), [outcomes](hyp:hy), and [assignment weights](hyp:ha), and [measurable fitted probabilities](hyp:hph) and [fitted means](hyp:hjh) at every sample index and training realization. If [every fitted mean error is square integrable](hyp:heJ), [every fitted probability error is square integrable](hyp:heP), [reference and fitted probabilities are at least the denominator bound almost everywhere](hyp:hclip), [assignment weights have absolute value at most one almost everywhere](hyp:hassign), [reference outcome residuals are bounded almost everywhere](hyp:hres), and [the L2 mean error](hyp:hrJ) and [L2 probability error](hyp:hrP) are of smaller order in probability than the inverse fourth root of twice one plus the sample index, then [the observation-integrated squared difference between fitted and reference inverse-probability-weighted outcome residuals converges in probability to zero](goal). -/
lemma dml_clipped_ipw_residual_sq_tendsto_probability_zero {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (p j y a : B → ℝ)
    (ph jh : ℕ → A → B → ℝ) (c R : ℝ)
    (hc : 0 < c) (hp : Measurable p) (hj : Measurable j)
    (hy : Measurable y) (ha : Measurable a)
    (hph : ∀ n t, Measurable (ph n t)) (hjh : ∀ n t, Measurable (jh n t))
    (heJ : ∀ n t, MemLp (fun x => jh n t x - j x) 2 ν)
    (heP : ∀ n t, MemLp (fun x => ph n t x - p x) 2 ν)
    (hclip : ∀ n t, ∀ᵐ x ∂ν, c ≤ p x ∧ c ≤ ph n t x)
    (hassign : ∀ᵐ x ∂ν, |a x| ≤ 1)
    (hres : ∀ᵐ x ∂ν, |y x - j x| ≤ R)
    (hrJ : Causalean.Stat.IsLittleOp
      (fun n t => Real.sqrt (∫ x, (jh n t x - j x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrP : Causalean.Stat.IsLittleOp
      (fun n t => Real.sqrt (∫ x, (ph n t x - p x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (a x / ph n t x * (y x - jh n t x) - a x / p x * (y x - j x)) ^ 2 ∂ν)
      atTop (fun _ _ => 0) := by
  have hcontJ : Continuous (fun z : ℝ => (2 / c ^ 2) * z ^ 2) := by fun_prop
  have hcontP : Continuous (fun z : ℝ => -(2 * R ^ 2 / (c ^ 2) ^ 2 * z ^ 2)) := by
    fun_prop
  have hJ := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hcontJ.continuousAt (dml_quarter_rate_tendsto_probability_zero μ _ hrJ)
  have hP := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hcontP.continuousAt (dml_quarter_rate_tendsto_probability_zero μ _ hrP)
  simp only [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, neg_zero] at hJ hP
  have hsum := hJ.sub hP
  simp only [sub_neg_eq_add, sub_zero] at hsum
  apply probability_zero_of_nonneg_le μ _ _ hsum
  intro n
  apply Eventually.of_forall
  intro t
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  exact (clipped_ipw_residual_integrated_sq_bound ν p (ph n t) j (jh n t) y a c R
    hc hp (hph n t) hj (hjh n t) hy ha (heJ n t) (heP n t)
    (hclip n t) hassign hres).2

universe v

-- The positive-level treated-success residual in the actual binary score.
-- @node: RP_clipped_sq_difference_bound
/-- At [a nonzero population level](hyp:hk), suppose [the denominator lower bound is positive](hyp:hc), [the reference baseline probability is at least that bound](hyp:hp), [the fitted baseline probability is at least that bound](hyp:hph), and [the treated-outcome residual relative to the reference treated-success mean is bounded in absolute value](hyp:hres). Then [the squared change in the treated-success residual is bounded by twice the squared treated-success mean error divided by the squared denominator bound plus twice the squared residual bound times the squared baseline-probability error divided by the fourth power of the denominator bound](goal). -/
lemma RP_clipped_sq_difference_bound {X Z : Type v}
    (L : LevelData Z X) (e eh : NuisanceBin L) (k : ℕ) (o : Obs X Z) (c R : ℝ)
    (hk : k ≠ 0) (hc : 0 < c)
    (hp : c ≤ positiveValue e.piLev k o.1)
    (hph : c ≤ positiveValue eh.piLev k o.1)
    (hres : |o.2.2.2 * o.2.2.1 - positiveValue e.P1 k o.1| ≤ R) :
    (RP L eh k o - RP L e k o) ^ 2 ≤
      (2 / c ^ 2) * (positiveValue eh.P1 k o.1 - positiveValue e.P1 k o.1) ^ 2 +
        (2 * R ^ 2 / (c ^ 2) ^ 2) *
          (positiveValue eh.piLev k o.1 - positiveValue e.piLev k o.1) ^ 2 := by
  have ha : |indicator (o.2.1 ∈ L.S k)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  simpa only [RP, if_neg hk] using
    clipped_ipw_residual_sq_difference_bound
      (jh := positiveValue eh.P1 k o.1) hc hp hph ha hres

-- The propensity residual has exactly the same estimate with W as outcome.
-- @node: Rp_clipped_sq_difference_bound
/-- For [a nonzero population level](hyp:hk), if [the denominator lower bound is positive](hyp:hc), [the reference baseline probability is at least that bound](hyp:hp), [the fitted baseline probability is at least that bound](hyp:hph), and [treatment minus the reference level propensity is bounded in absolute value](hyp:hres), then [the squared change in the propensity residual is at most twice the squared level-propensity error divided by the squared denominator bound plus twice the squared residual bound times the squared baseline-probability error divided by the fourth power of the denominator bound](goal). -/
lemma Rp_clipped_sq_difference_bound {X Z : Type v}
    (L : LevelData Z X) (e eh : NuisanceBin L) (k : ℕ) (o : Obs X Z) (c R : ℝ)
    (hk : k ≠ 0) (hc : 0 < c)
    (hp : c ≤ positiveValue e.piLev k o.1)
    (hph : c ≤ positiveValue eh.piLev k o.1)
    (hres : |o.2.2.1 - positiveValue e.pLev k o.1| ≤ R) :
    (Rp L eh k o - Rp L e k o) ^ 2 ≤
      (2 / c ^ 2) * (positiveValue eh.pLev k o.1 - positiveValue e.pLev k o.1) ^ 2 +
        (2 * R ^ 2 / (c ^ 2) ^ 2) *
          (positiveValue eh.piLev k o.1 - positiveValue e.piLev k o.1) ^ 2 := by
  have ha : |indicator (o.2.1 ∈ L.S k)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  simpa only [Rp, if_neg hk] using
    clipped_ipw_residual_sq_difference_bound
      (jh := positiveValue eh.pLev k o.1) hc hp hph ha hres

end Papers.TbsPrteOptimalTransport
