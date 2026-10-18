module
public import Papers.TbsPrteOptimalTransport.Helpers.DenominatorOrthogonality
public import Papers.TbsPrteOptimalTransport.Helpers.ProductScoreMoments
public import Causalean.Stat.Limit.StochasticOrderEnvelope
/-! Integrated second-order regression and clipped inverse-weight remainders. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory

-- @node: ipw_regression_bias_algebra
/-- [The fitted regression plus the true-to-fitted probability ratio times the
regression correction, minus the true regression, equals one minus that ratio
times the fitted-minus-true regression error](goal). -/
lemma ipw_regression_bias_algebra (p q j jhat : ℝ) :
    jhat + p / q * (j - jhat) - j = (1 - p / q) * (jhat - j) := by
  ring

-- The denominator clipping alone bounds the normalized assignment error.
-- No lower bound on the true assignment probability is needed for this step.
-- @node: clipped_assignment_regression_remainder_bound
/-- If [the clipping threshold is positive](hyp:hc) and [the fitted assignment
probability is at least that threshold](hyp:hq), then [the absolute regression
error multiplied by one minus the true-to-fitted probability ratio is bounded
by the absolute assignment error times the absolute regression error divided
by the clipping threshold](goal). -/
lemma clipped_assignment_regression_remainder_bound {p q c e : ℝ}
    (hc : 0 < c) (hq : c ≤ q) :
    |(1 - p / q) * e| ≤ |q - p| * |e| / c := by
  have hq0 : 0 < q := hc.trans_le hq
  have hid : 1 - p / q = (q - p) / q := by
    field_simp
  rw [hid, abs_mul, abs_div, abs_of_pos hq0]
  calc
    _ = (|q - p| * |e|) / q := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hc hq

-- This is the conditional regression-bias term in the full score expansion.
-- L2 errors supply integrability, rather than an extra integrability premise.
-- @node: clipped_assignment_regression_L2_remainder
/-- Suppose [the clipping threshold is positive](hyp:hc), [the true assignment
function is measurable](hyp:hp), [the fitted assignment function is measurable](hyp:hq),
[the fitted assignment function is at least the threshold almost everywhere](hyp:hclip),
[the assignment error is square-integrable](hyp:hprob), and [the regression
error is square-integrable](hyp:he). Then [the regression error multiplied by
one minus the true-to-fitted assignment ratio is integrable, and its absolute
integral is bounded by the product of the two error norms in mean square divided
by the clipping threshold](goal). -/
lemma clipped_assignment_regression_L2_remainder {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (p q e : B → ℝ) (c : ℝ)
    (hc : 0 < c) (hp : Measurable p) (hq : Measurable q)
    (hclip : ∀ᵐ x ∂ν, c ≤ q x)
    (hprob : MemLp (fun x => q x - p x) 2 ν) (he : MemLp e 2 ν) :
    Integrable (fun x => (1 - p x / q x) * e x) ν ∧
      |∫ x, (1 - p x / q x) * e x ∂ν| ≤
        (eLpNorm (fun x => q x - p x) 2 ν).toReal * (eLpNorm e 2 ν).toReal / c := by
  have hprod : Integrable (fun x => (q x - p x) * e x) ν := hprob.integrable_mul he
  have hdom : Integrable (fun x => |(q x - p x) * e x| / c) ν := hprod.abs.div_const c
  have hmeas : AEStronglyMeasurable (fun x => (1 - p x / q x) * e x) ν := by
    first | fun_prop
          | exact (measurable_const.sub (hp.div hq)).aestronglyMeasurable.mul
              he.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂ν, |(1 - p x / q x) * e x| ≤ |(q x - p x) * e x| / c := by
    filter_upwards [hclip] with x hx
    simpa only [abs_mul] using clipped_assignment_regression_remainder_bound hc hx (e := e x)
  have hi := hdom.mono' hmeas (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |(1 - p x / q x) * e x| ∂ν := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => (1 - p x / q x) * e x)
    _ ≤ ∫ x, |(q x - p x) * e x| / c ∂ν := integral_mono_ae hi.abs hdom hbound
    _ = (∫ x, |(q x - p x) * e x| ∂ν) / c := integral_div c _
    _ ≤ _ := div_le_div_of_nonneg_right
      (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hprob he) hc.le

-- The reciprocal error occurs when a centered numerator has a regression error.
-- @node: clipped_reciprocal_regression_L2_remainder
/-- Suppose [the clipping threshold is positive](hyp:hc), [the true assignment
function is measurable](hyp:hp), [the fitted assignment function is measurable](hyp:hq),
[both assignment functions are at least the threshold almost everywhere](hyp:hclip),
[their difference is square-integrable](hyp:hprob), and [the regression error
is square-integrable](hyp:he). Then [the difference of reciprocal assignments
times the regression error is integrable, and its absolute integral is bounded
by the product of the assignment and regression error norms in mean square
divided by the squared clipping threshold](goal). -/
lemma clipped_reciprocal_regression_L2_remainder {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (p q e : B → ℝ) (c : ℝ)
    (hc : 0 < c) (hp : Measurable p) (hq : Measurable q)
    (hclip : ∀ᵐ x ∂ν, c ≤ p x ∧ c ≤ q x)
    (hprob : MemLp (fun x => p x - q x) 2 ν) (he : MemLp e 2 ν) :
    Integrable (fun x => ((p x)⁻¹ - (q x)⁻¹) * e x) ν ∧
      |∫ x, ((p x)⁻¹ - (q x)⁻¹) * e x ∂ν| ≤
        (eLpNorm (fun x => p x - q x) 2 ν).toReal * (eLpNorm e 2 ν).toReal / c ^ 2 := by
  have hprod : Integrable (fun x => (p x - q x) * e x) ν := hprob.integrable_mul he
  have hdom : Integrable (fun x => |(p x - q x) * e x| / c ^ 2) ν :=
    hprod.abs.div_const _
  have hmeas : AEStronglyMeasurable (fun x => ((p x)⁻¹ - (q x)⁻¹) * e x) ν := by
    first | fun_prop | exact (hp.inv.sub hq.inv).aestronglyMeasurable.mul he.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂ν, |((p x)⁻¹ - (q x)⁻¹) * e x| ≤ |(p x - q x) * e x| / c ^ 2 := by
    filter_upwards [hclip] with x hx
    simpa only [abs_mul] using clipped_ipw_regression_remainder_bound hc hx.1 hx.2 (e := e x)
  have hi := hdom.mono' hmeas (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |((p x)⁻¹ - (q x)⁻¹) * e x| ∂ν := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => ((p x)⁻¹ - (q x)⁻¹) * e x)
    _ ≤ ∫ x, |(p x - q x) * e x| / c ^ 2 ∂ν := integral_mono_ae hi.abs hdom hbound
    _ = (∫ x, |(p x - q x) * e x| ∂ν) / c ^ 2 := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right
      (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hprob he) (sq_nonneg c)

-- r is the selected outcome residual before division by the fitted probability.
-- Its conditional mean comes from the two population regression identities.
-- @node: ipw_regression_exact_bias
/-- Suppose [the conditioning information is contained in the ambient information](hyp:hm),
[the fitted inverse assignment weight is measurable with respect to the conditioning
information](hyp:hw), and [the true assignment times the true-minus-fitted regression
is measurable with respect to that information](hyp:hmean). If [the residual is
integrable](hyp:hr), [its proposed conditional mean is integrable](hyp:hpr),
[the inverse-weighted residual is integrable](hyp:hrq), [the inverse-weighted
proposed conditional mean is integrable](hyp:hprq), [the true regression is
integrable](hyp:hj), [the fitted regression is integrable](hyp:hjhat), and
[the residual's conditional mean equals the true assignment times the
true-minus-fitted regression almost everywhere](hyp:hcond), then [the integrated
fitted regression plus inverse-weighted residual minus the integrated true
regression equals the integral of one minus the true-to-fitted assignment ratio
times the fitted-minus-true regression error](goal). -/
lemma ipw_regression_exact_bias {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (p q j jhat r : B → ℝ)
    (hw : StronglyMeasurable[m] (fun x => (q x)⁻¹))
    (hmean : StronglyMeasurable[m] (fun x => p x * (j x - jhat x)))
    (hr : Integrable r ν) (hpr : Integrable (fun x => p x * (j x - jhat x)) ν)
    (hrq : Integrable (fun x => (q x)⁻¹ * r x) ν)
    (hprq : Integrable (fun x => (q x)⁻¹ * (p x * (j x - jhat x))) ν)
    (hj : Integrable j ν) (hjhat : Integrable jhat ν)
    (hcond : ν[r | m] =ᵐ[ν] (fun x => p x * (j x - jhat x))) :
    (∫ x, jhat x + (q x)⁻¹ * r x ∂ν) - (∫ x, j x ∂ν) =
      ∫ x, (1 - p x / q x) * (jhat x - j x) ∂ν := by
  let : MeasurableSpace B := mB
  have htower := score_weighted_conditional_integral ν m hm
    (fun x => (q x)⁻¹) r (fun x => p x * (j x - jhat x))
    hw hr hpr hrq hprq hcond hmean
  rw [integral_add hjhat hrq, htower, ← integral_add hjhat hprq]
  have hsum : Integrable (fun x => jhat x + (q x)⁻¹ * (p x * (j x - jhat x))) ν :=
    hjhat.add hprq
  calc
    _ = ∫ x, (jhat x + (q x)⁻¹ * (p x * (j x - jhat x))) - j x ∂ν :=
      (integral_sub hsum hj).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ipw_regression_bias_algebra (p x) (q x) (j x) (jhat x)

-- Combine the exact score expansion with clipping and Cauchy--Schwarz.
-- @node: ipw_regression_score_bias_L2_bound
/-- Suppose [the conditioning information is contained in the ambient information](hyp:hm),
[the clipping threshold is positive](hyp:hc), [the true assignment function is
measurable](hyp:hp), [the fitted assignment function is measurable](hyp:hq),
[the fitted assignment is at least the threshold almost everywhere](hyp:hclip),
[the assignment error is square-integrable](hyp:hprob), and [the fitted-minus-true
regression error is square-integrable](hyp:he). If [the fitted inverse assignment
weight is measurable given the conditioning information](hyp:hw), [the true
assignment times the true-minus-fitted regression is measurable given that
information](hyp:hmean), [the residual is integrable](hyp:hr), [its proposed
conditional mean is integrable](hyp:hpr), [the inverse-weighted residual is
integrable](hyp:hrq), [the inverse-weighted proposed conditional mean is
integrable](hyp:hprq), [the true regression is integrable](hyp:hj), [the fitted
regression is integrable](hyp:hjhat), and [the residual's conditional mean is
the true assignment times the true-minus-fitted regression almost everywhere](hyp:hcond),
then [the absolute bias of the integrated fitted regression plus inverse-weighted
residual is bounded by the product of the assignment and regression error norms
in mean square divided by the clipping threshold](goal). -/
lemma ipw_regression_score_bias_L2_bound {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (p q j jhat r : B → ℝ) (c : ℝ)
    (hc : 0 < c) (hp : Measurable[mB] p) (hq : Measurable[mB] q)
    (hclip : ∀ᵐ x ∂ν, c ≤ q x)
    (hprob : MemLp (fun x => q x - p x) 2 ν)
    (he : MemLp (fun x => jhat x - j x) 2 ν)
    (hw : StronglyMeasurable[m] (fun x => (q x)⁻¹))
    (hmean : StronglyMeasurable[m] (fun x => p x * (j x - jhat x)))
    (hr : Integrable r ν) (hpr : Integrable (fun x => p x * (j x - jhat x)) ν)
    (hrq : Integrable (fun x => (q x)⁻¹ * r x) ν)
    (hprq : Integrable (fun x => (q x)⁻¹ * (p x * (j x - jhat x))) ν)
    (hj : Integrable j ν) (hjhat : Integrable jhat ν)
    (hcond : ν[r | m] =ᵐ[ν] (fun x => p x * (j x - jhat x))) :
    |(∫ x, jhat x + (q x)⁻¹ * r x ∂ν) - (∫ x, j x ∂ν)| ≤
      (eLpNorm (fun x => q x - p x) 2 ν).toReal *
        (eLpNorm (fun x => jhat x - j x) 2 ν).toReal / c := by
  let : MeasurableSpace B := mB
  rw [ipw_regression_exact_bias ν m hm p q j jhat r
    hw hmean hr hpr hrq hprq hj hjhat hcond]
  exact (clipped_assignment_regression_L2_remainder ν p q
    (fun x => jhat x - j x) c hc hp hq hclip hprob he).2

end Papers.TbsPrteOptimalTransport
