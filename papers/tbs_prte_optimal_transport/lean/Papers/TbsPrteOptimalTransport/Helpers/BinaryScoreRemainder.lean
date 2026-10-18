module
public import Papers.TbsPrteOptimalTransport.Helpers.BinaryBranches
public import Mathlib.MeasureTheory.Function.L2Space
/-! Binary score bias with fitted active-branch coefficients. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory
universe v

-- Strict branches agree whenever every affine-argument error is below half
-- the population separation. This also covers the fixed zero lower boundary.
-- @node: binary_hinge_fitted_branches_stable
/-- If [the gap constant is positive](hyp:hc), [the upper-minus-lower gap is
at least that constant](hyp:hlq), [the boundary is separated from the
lower](hyp:hbl) and [upper values by that constant](hyp:hbq), [the upper](hyp:hq),
[lower](hyp:hl), and [boundary perturbations have absolute size at most
e](hyp:hb), and [e is less than half the gap constant](hyp:he), then [the
active-hinge, intermediate-boundary, and lower-dominance indicators are
unchanged by the perturbations](goal). -/
lemma binary_hinge_fitted_branches_stable {q l b dq dl db e c : ℝ}
    (hc : 0 < c) (hlq : c ≤ q - l) (hbl : c ≤ |b - l|) (hbq : c ≤ |b - q|)
    (hq : |dq| ≤ e) (hl : |dl| ≤ e) (hb : |db| ≤ e) (he : e < c / 2) :
    indicator (q + dq > max (l + dl) (b + db)) = indicator (q > max l b) ∧
    indicator (l + dl < b + db ∧ b + db < q + dq) = indicator (l < b ∧ b < q) ∧
    indicator (l + dl > b + db) = indicator (l > b) := by
  obtain ⟨hdq₁, hdq₂⟩ := abs_le.mp hq
  obtain ⟨hdl₁, hdl₂⟩ := abs_le.mp hl
  obtain ⟨hdb₁, hdb₂⟩ := abs_le.mp hb
  have horder : l < q := by linarith
  have horder' : l + dl < q + dq := by linarith
  by_cases h : l < b
  · have hsep : c ≤ b - l := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr h.le)] using hbl
    have h' : l + dl < b + db := by linarith
    rw [max_eq_right h.le, max_eq_right h'.le]
    by_cases hqb : b < q
    · have hsepq : c ≤ q - b := by
        simpa only [abs_of_nonpos (sub_nonpos.mpr hqb.le), neg_sub] using hbq
      have hqb' : b + db < q + dq := by linarith
      simp [indicator, h, h', hqb, hqb', not_lt_of_ge h.le, not_lt_of_ge h'.le]
    · have hsepq : c ≤ b - q := by
        simpa only [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hqb))] using hbq
      have hqb' : ¬ b + db < q + dq := by linarith
      simp [indicator, h, h', hqb, hqb', not_lt_of_ge h.le, not_lt_of_ge h'.le]
  · have hsep : c ≤ l - b := by
      simpa only [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h)), neg_sub] using hbl
    have hlt : b < l := by linarith
    have hlt' : b + db < l + dl := by linarith
    simp [indicator, max_eq_left hlt.le, max_eq_left hlt'.le,
      horder, horder', hlt, hlt', h, not_lt_of_ge hlt'.le]

-- The residual corrections use fitted indicators, including at fitted ties.
-- On the good event their linear term is exact; on the bad event Lipschitz
-- control and the margin turn the linear error into a quadratic bound.
-- @node: binary_hinge_fitted_score_remainder
/-- Given [a positive gap constant](hyp:hc), [an upper-minus-lower gap at
least that constant](hyp:hlq), [boundary separation from the lower](hyp:hbl)
and [upper values by that constant](hyp:hbq), and [upper](hyp:hq), [lower](hyp:hl),
and [boundary perturbations of absolute size at most e](hyp:hb), [the hinge
change after subtracting the upper perturbation weighted by the fitted active
indicator, adding the boundary perturbation weighted by the fitted intermediate
indicator, and adding the lower perturbation weighted by the fitted dominance
and active indicators is bounded in absolute value by twenty-six times e
squared divided by the gap constant](goal). -/
lemma binary_hinge_fitted_score_remainder {q l b dq dl db e c : ℝ}
    (hc : 0 < c) (hlq : c ≤ q - l) (hbl : c ≤ |b - l|) (hbq : c ≤ |b - q|)
    (hq : |dq| ≤ e) (hl : |dl| ≤ e) (hb : |db| ≤ e) :
    |max 0 (q + dq - max (l + dl) (b + db)) - max 0 (q - max l b) -
      (indicator (q + dq > max (l + dl) (b + db)) * dq -
        indicator (l + dl < b + db ∧ b + db < q + dq) * db -
        indicator (l + dl > b + db) *
          indicator (q + dq > max (l + dl) (b + db)) * dl)| ≤
      (26 / c) * e ^ 2 := by
  have he0 : 0 ≤ e := (abs_nonneg dq).trans hq
  by_cases he : e < c / 2
  · obtain ⟨hI, hD, hE⟩ := binary_hinge_fitted_branches_stable
      hc hlq hbl hbq hq hl hb he
    rw [hI, hD, hE]
    exact (binary_hinge_indicator_quadratic_remainder hc hlq hbl hbq hq hl hb).trans
      (mul_le_mul_of_nonneg_right (by
        apply (div_le_div_iff_of_pos_right hc).mpr
        norm_num : (20 : ℝ) / c ≤ 26 / c) (sq_nonneg e))
  · have hm : |max (l + dl) (b + db) - max l b| ≤ e := by
      have h := abs_max_sub_max_le_max (l + dl) (b + db) l b
      simp only [add_sub_cancel_left] at h
      exact h.trans (max_le hl hb)
    have harg : |(q + dq - max (l + dl) (b + db)) - (q - max l b)| ≤ 2 * e := by
      have hid : (q + dq - max (l + dl) (b + db)) - (q - max l b) =
          dq - (max (l + dl) (b + db) - max l b) := by ring
      rw [hid]
      exact (abs_sub _ _).trans (by linarith)
    have hh : |max 0 (q + dq - max (l + dl) (b + db)) - max 0 (q - max l b)| ≤
        2 * e := by
      exact (abs_max_sub_max_le_max 0 _ 0 _).trans
        (max_le (by simpa using (by linarith : 0 ≤ 2 * e)) harg)
    have hcoeff : |indicator (q + dq > max (l + dl) (b + db)) * dq -
        indicator (l + dl < b + db ∧ b + db < q + dq) * db -
        indicator (l + dl > b + db) *
          indicator (q + dq > max (l + dl) (b + db)) * dl| ≤ 3 * e := by
      have hI : |indicator (q + dq > max (l + dl) (b + db)) * dq| ≤ e := by
        unfold indicator
        split_ifs
        · simpa using hq
        · simpa using he0
      have hD : |indicator (l + dl < b + db ∧ b + db < q + dq) * db| ≤ e := by
        unfold indicator
        split_ifs <;> simp_all
      have hE : |indicator (l + dl > b + db) *
          indicator (q + dq > max (l + dl) (b + db)) * dl| ≤ e := by
        unfold indicator
        split_ifs <;> simp_all
      exact (abs_sub _ _).trans (by
        have hfirst := (abs_sub _ _).trans (add_le_add hI hD)
        linarith)
    have hlin := (abs_sub _ _).trans (add_le_add hh hcoeff)
    have hlarge : c / 2 ≤ e := le_of_not_gt he
    have hquad : 5 * e ≤ (26 / c) * e ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).mpr
      nlinarith [mul_nonneg he0 (show 0 ≤ 2 * e - c by linarith)]
    exact hlin.trans (by linarith)

-- Specialize to the fitted coefficients actually appearing in binScoreComponents.
-- @node: hMinus_fitted_score_remainder
/-- Suppose [the gap constant is positive](hyp:hc), [the adjacent original
pooled values have at least that gap](hyp:hlq), [the original adjusted boundary
is separated from the lower](hyp:hbl) and [upper pooled values by that
constant](hyp:hbq), and [the upper pooled value](hyp:hq), [lower pooled
value](hyp:hl), and [adjusted boundary each change by at most the error
envelope](hyp:hb). Then [the binary hinge change minus the linear correction
using the fitted active, intermediate-boundary, and lower-dominance indicators
has absolute value at most twenty-six times the squared envelope divided by
the gap](goal). -/
lemma hMinus_fitted_score_remainder {X Z : Type v}
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 e1 : NuisanceBin L) (k j : ℕ) (x : X) (err c : ℝ)
    (hc : 0 < c)
    (hlq : c ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j - 1) x)
    (hbl : c ≤ |positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x -
      pooledQBin phi L e0 k (j - 1) x|)
    (hbq : c ≤ |positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x -
      pooledQBin phi L e0 k j x|)
    (hq : |pooledQBin phi L e1 k j x - pooledQBin phi L e0 k j x| ≤ err)
    (hl : |pooledQBin phi L e1 k (j - 1) x - pooledQBin phi L e0 k (j - 1) x| ≤ err)
    (hb : |(positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x) -
      (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)| ≤ err) :
    |hMinus phi L e1 k j x - hMinus phi L e0 k j x -
      (Iact phi L e1 k j x * (pooledQBin phi L e1 k j x - pooledQBin phi L e0 k j x) -
        Dbd phi L e1 k j x * ((positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x) -
          (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)) -
        Edom phi L e1 k j x * Iact phi L e1 k j x *
          (pooledQBin phi L e1 k (j - 1) x - pooledQBin phi L e0 k (j - 1) x))| ≤
      (26 / c) * err ^ 2 := by
  have h := binary_hinge_fitted_score_remainder hc hlq hbl hbq hq hl hb
  simpa only [hMinus, Iact, Dbd, Edom, add_sub_cancel] using h

-- Square integrability of the nuisance envelope supplies integrability of the
-- debiased branch remainder; no bounded-outcome premise is needed here.
-- @node: binary_hinge_fitted_score_integrated_remainder
/-- Suppose [the gap constant is positive](hyp:hc), [the upper](hyp:hq),
[lower](hyp:hl), and [boundary functions](hyp:hb) and [their upper](hyp:hdq),
[lower](hyp:hdl), and [boundary perturbations are measurable](hyp:hdb), and
[the error envelope is square integrable](hyp:herr). If [the upper-minus-lower
gap and both boundary distances are at least the gap constant almost
everywhere](hyp:hgap) and [all three perturbations are bounded in absolute
value by the envelope almost everywhere](hyp:herrors), then [the hinge change
minus its linear correction using fitted branch indicators is integrable,
and the absolute value of its integral is at most twenty-six divided by the
gap constant times the integral of the squared envelope](goal). -/
lemma binary_hinge_fitted_score_integrated_remainder {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q l b dq dl db err : X → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hdq : Measurable dq) (hdl : Measurable dl) (hdb : Measurable db)
    (herr : MemLp err 2 μ)
    (hgap : ∀ᵐ x ∂μ, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|)
    (herrors : ∀ᵐ x ∂μ, |dq x| ≤ err x ∧ |dl x| ≤ err x ∧ |db x| ≤ err x) :
    let R := fun x => max 0 (q x + dq x - max (l x + dl x) (b x + db x)) -
      max 0 (q x - max (l x) (b x)) -
      (indicator (q x + dq x > max (l x + dl x) (b x + db x)) * dq x -
        indicator (l x + dl x < b x + db x ∧ b x + db x < q x + dq x) * db x -
        indicator (l x + dl x > b x + db x) *
          indicator (q x + dq x > max (l x + dl x) (b x + db x)) * dl x)
    Integrable R μ ∧ |∫ x, R x ∂μ| ≤ (26 / c) * ∫ x, err x ^ 2 ∂μ := by
  dsimp only
  let R := fun x => max 0 (q x + dq x - max (l x + dl x) (b x + db x)) -
      max 0 (q x - max (l x) (b x)) -
      (indicator (q x + dq x > max (l x + dl x) (b x + db x)) * dq x -
        indicator (l x + dl x < b x + db x ∧ b x + db x < q x + dq x) * db x -
        indicator (l x + dl x > b x + db x) *
          indicator (q x + dq x > max (l x + dl x) (b x + db x)) * dl x)
  change Integrable R μ ∧ |∫ x, R x ∂μ| ≤ (26 / c) * ∫ x, err x ^ 2 ∂μ
  have hI : Measurable (fun x =>
      indicator (q x + dq x > max (l x + dl x) (b x + db x))) := by
    unfold indicator
    exact Measurable.ite (measurableSet_lt ((hl.add hdl).max (hb.add hdb))
      (hq.add hdq)) measurable_const measurable_const
  have hD : Measurable (fun x =>
      indicator (l x + dl x < b x + db x ∧ b x + db x < q x + dq x)) := by
    unfold indicator
    exact Measurable.ite ((measurableSet_lt (hl.add hdl) (hb.add hdb)).inter
      (measurableSet_lt (hb.add hdb) (hq.add hdq))) measurable_const measurable_const
  have hE : Measurable (fun x => indicator (l x + dl x > b x + db x)) := by
    unfold indicator
    exact Measurable.ite (measurableSet_lt (hb.add hdb) (hl.add hdl))
      measurable_const measurable_const
  have hR : Measurable R := by
    dsimp only [R]
    fun_prop
  have hbound : ∀ᵐ x ∂μ, |R x| ≤ (26 / c) * err x ^ 2 := by
    filter_upwards [hgap, herrors] with x hg he
    exact binary_hinge_fitted_score_remainder hc hg.1 hg.2.1 hg.2.2 he.1 he.2.1 he.2.2
  have hdom : Integrable (fun x => (26 / c) * err x ^ 2) μ :=
    herr.integrable_sq.const_mul _
  have hi : Integrable R μ := hdom.mono' hR.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |R x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ x, (26 / c) * err x ^ 2 ∂μ := integral_mono_ae hi.abs hdom hbound
    _ = _ := integral_const_mul _ _

end Papers.TbsPrteOptimalTransport
