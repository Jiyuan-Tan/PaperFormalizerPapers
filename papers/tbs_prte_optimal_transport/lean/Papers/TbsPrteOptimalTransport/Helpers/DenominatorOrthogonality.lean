module
public import Papers.TbsPrteOptimalTransport.Helpers.Orthogonality
/-! Conditional centering under denominator paths and clipped reciprocal errors. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology
universe v

-- Pulling out a covariate weight preserves conditional centering, even when
-- that weight is a perturbed reciprocal rather than its population value.
-- @node: score_weighted_conditional_centering
/-- If [the conditioning information is contained in the ambient information](hyp:hm),
[the weight is measurable with respect to that information](hyp:hw),
[the residual is integrable](hyp:hr), [its product with the weight is integrable](hyp:hwr), and
[the residual has conditional mean zero](hyp:hzero), then [the weighted residual
also has conditional mean zero almost everywhere](goal). -/
lemma score_weighted_conditional_centering {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (w r : B → ℝ)
    (hw : StronglyMeasurable[m] w) (hr : Integrable r ν)
    (hwr : Integrable (w * r) ν) (hzero : ν[r | m] =ᵐ[ν] 0) :
    ν[w * r | m] =ᵐ[ν] 0 := by
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hw hwr hr, hzero]
    with b hb hz
  simpa only [Pi.mul_apply, hz, Pi.zero_apply, mul_zero] using hb

-- @node: score_denominator_residual_mean_zero
/-- If [the conditioning information is contained in the ambient information](hyp:hm),
[the numerator weight](hyp:ha) and [denominator are measurable with respect to it](hyp:hp),
[the residual is integrable](hyp:hr), [the residual times the weight-to-denominator
ratio is integrable](hyp:hwr), and [the residual has conditional mean zero](hyp:hzero),
then [the integral of that weighted residual is zero](goal). -/
lemma score_denominator_residual_mean_zero {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (a p r : B → ℝ)
    (ha : StronglyMeasurable[m] a) (hp : StronglyMeasurable[m] p)
    (hr : Integrable r ν)
    (hwr : Integrable (fun b => a b / p b * r b) ν)
    (hzero : ν[r | m] =ᵐ[ν] 0) :
    (∫ b, a b / p b * r b ∂ν) = 0 := by
  let : MeasurableSpace B := mB
  have hw : StronglyMeasurable[m] (fun b => a b / p b) := by fun_prop
  have hc := score_weighted_conditional_centering ν m hm
    (fun b => a b / p b) r hw hr hwr hzero
  calc
    _ = ∫ b, ν[(fun b => a b / p b) * r | m] b ∂ν :=
      (integral_condExp hm).symm
    _ = ∫ b, (0 : ℝ) ∂ν := integral_congr_ae hc
    _ = 0 := by simp

-- Exact zero means throughout the admissible neighborhood avoid having to
-- exchange differentiation and integration for denominator directions.
-- @node: score_denominator_path_orthogonality
/-- Suppose [the conditioning information is contained in the ambient information](hyp:hm),
[the path radius is positive](hyp:hradius), and [the numerator weight](hyp:ha),
[initial denominator](hyp:hp), and [denominator direction are measurable with respect
to the conditioning information](hyp:hd). If [the residual is integrable](hyp:hr),
[the weighted residual is integrable at every path displacement smaller in absolute
value than the radius](hyp:hwr), and [the residual has conditional mean zero](hyp:hzero),
then [the integral of the weighted residual has derivative zero at zero along the
linear denominator path](goal). -/
lemma score_denominator_path_orthogonality {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (a p d r : B → ℝ) (radius : ℝ)
    (hradius : 0 < radius)
    (ha : StronglyMeasurable[m] a) (hp : StronglyMeasurable[m] p)
    (hd : StronglyMeasurable[m] d) (hr : Integrable r ν)
    (hwr : ∀ t : ℝ, |t| < radius →
      Integrable (fun b => a b / (p b + t * d b) * r b) ν)
    (hzero : ν[r | m] =ᵐ[ν] 0) :
    HasDerivAt (fun t : ℝ => ∫ b, a b / (p b + t * d b) * r b ∂ν) 0 0 := by
  let : MeasurableSpace B := mB
  apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < radius :=
    (continuousAt_id.abs.eventually_lt_const (by simpa using hradius))
  filter_upwards [hnear] with t ht
  have hpt : StronglyMeasurable[m] (fun b => p b + t * d b) := by fun_prop
  exact score_denominator_residual_mean_zero ν m hm a
    (fun b => p b + t * d b) r ha hpt hr (hwr t ht) hzero

-- These identities expose the fixed numerators of the binary IPW terms.
-- The structural k=0 residual stays zero under every denominator update.
-- @node: RP_denominator_update
/-- After replacing the level-probability denominators, [the outcome residual equals
the reciprocal of the updated level probability times the unchanged numerator:
zero at level zero, and otherwise the level-membership indicator times the difference
between treatment times outcome and its nuisance conditional mean](goal). -/
lemma RP_denominator_update {X Z : Type v} [DecidableEq Z]
    (L : LevelData Z X) (e : NuisanceBin L)
    (pi : PositiveIndex L.K → X → ℝ) (k : ℕ) (o : Obs X Z) :
    RP L {e with piLev := pi} k o =
      (positiveValue pi k o.1)⁻¹ *
        (if k = 0 then 0 else indicator (o.2.1 ∈ L.S k) *
          (o.2.2.2 * o.2.2.1 - positiveValue e.P1 k o.1)) := by
  by_cases hk : k = 0
  · simp [RP, hk]
  · simp only [RP, if_neg hk, div_eq_mul_inv]
    ring

-- @node: Rp_denominator_update
/-- After replacing the level-probability denominators, [the treatment residual equals
the reciprocal of the updated level probability times the unchanged numerator:
zero at level zero, and otherwise the level-membership indicator times the difference
between treatment and its nuisance conditional probability](goal). -/
lemma Rp_denominator_update {X Z : Type v} [DecidableEq Z]
    (L : LevelData Z X) (e : NuisanceBin L)
    (pi : PositiveIndex L.K → X → ℝ) (k : ℕ) (o : Obs X Z) :
    Rp L {e with piLev := pi} k o =
      (positiveValue pi k o.1)⁻¹ *
        (if k = 0 then 0 else indicator (o.2.1 ∈ L.S k) *
          (o.2.2.1 - positiveValue e.pLev k o.1)) := by
  by_cases hk : k = 0
  · simp [Rp, hk]
  · simp only [Rp, if_neg hk, div_eq_mul_inv]
    ring

-- @node: RqBin_denominator_update
/-- After replacing the policy-class denominators, [the binary policy residual equals
the reciprocal of the updated class denominator times the unchanged sum over that
class of policy derivatives times instrument indicators times treatment propensity
residuals; the numerator is zero for class zero or an index beyond the bin's classes](goal). -/
lemma RqBin_denominator_update {X Z : Type v} [Fintype Z] [DecidableEq Z]
    (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (tau : RegularIndex L → X → ℝ) (k j : ℕ) (o : Obs X Z) :
    RqBin dphi L {e with tauLev := tau} k j o =
      (regularValue tau k j o.1)⁻¹ *
        (if j = 0 ∨ L.l k < j then 0 else
          ∑ z ∈ L.T k j, dphi z o.1 (e.prop z o.1) *
            indicator (o.2.1 = z) * (o.2.2.1 - e.prop z o.1)) := by
  unfold RqBin
  split_ifs <;> simp

-- @node: clipped_reciprocal_error_bound
/-- If [the clipping floor is positive](hyp:hc) and [the first denominator](hyp:hp)
and [the second denominator are at least that floor](hyp:hq), then [the absolute
difference of their reciprocals is at most their absolute difference divided by
the squared clipping floor](goal). -/
lemma clipped_reciprocal_error_bound {p q c : ℝ}
    (hc : 0 < c) (hp : c ≤ p) (hq : c ≤ q) :
    |p⁻¹ - q⁻¹| ≤ |p - q| / c ^ 2 := by
  have hp0 : 0 < p := hc.trans_le hp
  have hq0 : 0 < q := hc.trans_le hq
  rw [inv_sub_inv (ne_of_gt hp0) (ne_of_gt hq0), abs_div,
    abs_of_pos (mul_pos hp0 hq0), abs_sub_comm q p]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hc)
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)]

-- The IPW regression remainder is a product of the two nuisance errors.
-- @node: clipped_ipw_regression_remainder_bound
/-- If [the clipping floor is positive](hyp:hc) and [the first denominator](hyp:hp)
and [the second denominator are at least that floor](hyp:hq), then [the absolute
product of the reciprocal error and a regression error is at most the product of
the absolute denominator and regression errors divided by the squared clipping floor](goal). -/
lemma clipped_ipw_regression_remainder_bound {p q c e : ℝ}
    (hc : 0 < c) (hp : c ≤ p) (hq : c ≤ q) :
    |(p⁻¹ - q⁻¹) * e| ≤ |p - q| * |e| / c ^ 2 := by
  rw [abs_mul]
  calc
    _ ≤ (|p - q| / c ^ 2) * |e| :=
      mul_le_mul_of_nonneg_right (clipped_reciprocal_error_bound hc hp hq) (abs_nonneg e)
    _ = _ := by ring

end Papers.TbsPrteOptimalTransport
