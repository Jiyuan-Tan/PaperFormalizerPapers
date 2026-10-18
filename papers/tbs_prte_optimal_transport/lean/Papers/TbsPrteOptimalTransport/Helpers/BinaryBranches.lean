module
public import Papers.TbsPrteOptimalTransport.Helpers.ScoresBinary
/-! Local active-branch derivatives for the binary orthogonal score. -/
public section

namespace Papers.TbsPrteOptimalTransport
open Filter
open scoped Topology
universe v

-- @node: binary_max_hasDerivAt_of_ne
/-- If [the first function has derivative df](hyp:hf) and [the second has
derivative dg at the evaluation point](hyp:hg), and [their values there
differ](hyp:hne), then [their maximum has the derivative of whichever
function has the larger value there](goal). -/
lemma binary_max_hasDerivAt_of_ne {f g : ℝ → ℝ} {df dg t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) (hne : f t ≠ g t) :
    HasDerivAt (fun s => max (f s) (g s)) (if f t < g t then dg else df) t := by
  by_cases hlt : f t < g t
  · rw [if_pos hlt]
    apply hg.congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually_lt hg.continuousAt hlt] with s hs
    exact max_eq_right hs.le
  · rw [if_neg hlt]
    have hgt : g t < f t := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    apply hf.congr_of_eventuallyEq
    filter_upwards [hg.continuousAt.eventually_lt hf.continuousAt hgt] with s hs
    exact max_eq_left hs.le

-- @node: binary_hinge_hasDerivAt
/-- Suppose [the upper](hyp:hq), [lower](hyp:hl), and [boundary paths have
derivatives dq, dl, and db at the evaluation point](hyp:hb), [the lower value
is below the upper](hyp:horder), and [the boundary differs from the
lower](hyp:hbl) and [upper values](hyp:hbq). Then [the positive part of the
upper value minus the maximum of the lower and boundary values has derivative
dq on the active branch, minus db when the boundary lies between the two
values, minus dl when the lower value dominates the boundary and the hinge
is active](goal). -/
lemma binary_hinge_hasDerivAt {q l b : ℝ → ℝ} {dq dl db t : ℝ}
    (hq : HasDerivAt q dq t) (hl : HasDerivAt l dl t) (hb : HasDerivAt b db t)
    (horder : l t < q t) (hbl : b t ≠ l t) (hbq : b t ≠ q t) :
    HasDerivAt (fun s => max 0 (q s - max (l s) (b s)))
      (indicator (q t > max (l t) (b t)) * dq -
        indicator (l t < b t ∧ b t < q t) * db -
        indicator (l t > b t) * indicator (q t > max (l t) (b t)) * dl) t := by
  have hi := binary_max_hasDerivAt_of_ne hl hb hbl.symm
  have hout : (0 : ℝ) ≠ q t - max (l t) (b t) := by
    by_cases h : l t ≤ b t
    · rw [max_eq_right h]
      intro heq
      apply hbq
      linarith
    · rw [max_eq_left (le_of_not_ge h)]
      linarith
  have hh := binary_max_hasDerivAt_of_ne (hasDerivAt_const t (0 : ℝ))
    (hq.sub hi) hout
  apply hh.congr_deriv
  by_cases h : l t < b t
  · have hmax : max (l t) (b t) = b t := max_eq_right h.le
    by_cases ha : b t < q t
    · simp [indicator, hmax, h, ha, not_lt_of_ge h.le, sub_pos.mpr ha]
    · have hn : ¬ 0 < q t - b t := by linarith
      simp [indicator, hmax, h, ha, not_lt_of_ge h.le, hn]
  · have hlt : b t < l t := lt_of_le_of_ne (le_of_not_gt h) hbl
    have hmax : max (l t) (b t) = l t := max_eq_left hlt.le
    simp [indicator, hmax, h, hlt, horder, sub_pos.mpr horder]

-- @node: hMinus_path_hasDerivAt
/-- Suppose [the upper](hyp:hq) and [lower pooled policy paths have derivatives
dq and dl at zero](hyp:hl), [the upper propensity path has derivative dp](hyp:hp),
and [the upper](hyp:hPplus) and [lower treated regression paths have derivatives
dPplus and dPminus](hyp:hPminus). If [the lower pooled value is below the
upper](hyp:horder) and [the adjusted boundary differs from the lower](hyp:hbl)
and [upper pooled values at zero](hyp:hbq), then [the binary hinge path has
derivative equal to the active indicator times dq, minus the boundary
indicator times dp minus the regression increment derivative, minus the
lower-dominance and active indicators times dl](goal). -/
lemma hMinus_path_hasDerivAt {X Z : Type v}
    (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : ℝ → NuisanceBin L) (k j : ℕ) (x : X)
    (dq dl dp dPplus dPminus : ℝ)
    (hq : HasDerivAt (fun t => pooledQBin phi L (e t) k j x) dq 0)
    (hl : HasDerivAt (fun t => pooledQBin phi L (e t) k (j - 1) x) dl 0)
    (hp : HasDerivAt (fun t => positiveValue (e t).pLev (k + 1) x) dp 0)
    (hPplus : HasDerivAt (fun t => positiveValue (e t).P1 (k + 1) x) dPplus 0)
    (hPminus : HasDerivAt (fun t => positiveValue (e t).P1 k x) dPminus 0)
    (horder : pooledQBin phi L (e 0) k (j - 1) x < pooledQBin phi L (e 0) k j x)
    (hbl : positiveValue (e 0).pLev (k + 1) x - binFullJ L (e 0) k x ≠
      pooledQBin phi L (e 0) k (j - 1) x)
    (hbq : positiveValue (e 0).pLev (k + 1) x - binFullJ L (e 0) k x ≠
      pooledQBin phi L (e 0) k j x) :
    HasDerivAt (fun t => hMinus phi L (e t) k j x)
      (Iact phi L (e 0) k j x * dq -
        Dbd phi L (e 0) k j x * (dp - (dPplus - dPminus)) -
        Edom phi L (e 0) k j x * Iact phi L (e 0) k j x * dl) 0 := by
  exact binary_hinge_hasDerivAt hq hl (hp.sub (hPplus.sub hPminus)) horder hbl hbq

-- @node: binary_strict_indicator_eventually_constant
/-- If [the first](hyp:hf) and [second functions are continuous at the
evaluation point](hyp:hg) and [their values there differ](hyp:hne), then
[the indicator that the first is strictly below the second is constant
throughout some neighborhood of that point](goal). -/
lemma binary_strict_indicator_eventually_constant {f g : ℝ → ℝ} {t : ℝ}
    (hf : ContinuousAt f t) (hg : ContinuousAt g t) (hne : f t ≠ g t) :
    (fun s => indicator (f s < g s)) =ᶠ[𝓝 t] (fun _ => indicator (f t < g t)) := by
  by_cases hlt : f t < g t
  · filter_upwards [hf.eventually_lt hg hlt] with s hs
    simp only [indicator, if_pos hs, if_pos hlt]
  · have hgt : g t < f t := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    filter_upwards [hg.eventually_lt hf hgt] with s hs
    simp only [indicator, if_neg (not_lt_of_ge hs.le), if_neg hlt]

-- The three indicators are locally fixed under the binary outcome gap.
-- @node: binary_branch_indicators_eventually_constant
/-- If [the upper](hyp:hq), [lower](hyp:hl), and [boundary paths are continuous
at the evaluation point](hyp:hb), [the lower value is below the upper](hyp:horder),
and [the boundary differs from the lower](hyp:hbl) and [upper values](hyp:hbq),
then [all three indicators, for an active hinge, an intermediate boundary,
and lower-value dominance, equal their values at that point throughout
some neighborhood](goal). -/
lemma binary_branch_indicators_eventually_constant {q l b : ℝ → ℝ} {t : ℝ}
    (hq : ContinuousAt q t) (hl : ContinuousAt l t) (hb : ContinuousAt b t)
    (horder : l t < q t) (hbl : b t ≠ l t) (hbq : b t ≠ q t) :
    ∀ᶠ s in 𝓝 t,
      indicator (q s > max (l s) (b s)) = indicator (q t > max (l t) (b t)) ∧
      indicator (l s < b s ∧ b s < q s) = indicator (l t < b t ∧ b t < q t) ∧
      indicator (l s > b s) = indicator (l t > b t) := by
  have hmax : max (l t) (b t) ≠ q t := by
    by_cases h : l t ≤ b t
    · simpa only [max_eq_right h] using hbq
    · rw [max_eq_left (le_of_not_ge h)]
      exact horder.ne
  have hi := binary_strict_indicator_eventually_constant (hl.max hb) hq hmax
  have hlb := binary_strict_indicator_eventually_constant hl hb hbl.symm
  have hbq' := binary_strict_indicator_eventually_constant hb hq hbq
  have hbl' := binary_strict_indicator_eventually_constant hb hl hbl
  filter_upwards [hi, hlb, hbq', hbl'] with s hs hslb hsbq hsbl
  refine ⟨hs, ?_, hsbl⟩
  have hand : ∀ a c : Prop, indicator (a ∧ c) = indicator a * indicator c := by
    intro a c
    classical
    by_cases ha : a <;> by_cases hc : c <;> simp [indicator, ha, hc]
  rw [hand, hand, hslb, hsbq]

-- This is the conditional-score cancellation: the boundary residual derivative
-- is db, while the upper and lower policy residual derivatives are -dq and -dl.
-- @node: binary_hinge_residual_orthogonality
/-- Suppose [the upper](hyp:hq), [lower](hyp:hl), and [boundary paths have
derivatives dq, dl, and db](hyp:hb), while [the boundary residual has derivative
db](hyp:hrB), [the lower residual has derivative minus dl](hyp:hrL), and
[the upper residual has derivative minus dq](hyp:hrQ) at the evaluation point.
If [the lower value is below the upper](hyp:horder) and [the boundary differs
from the lower](hyp:hbl) and [upper values](hyp:hbq), then [the hinge plus the
boundary-indicator-weighted boundary residual, minus the lower-dominance
and active-indicator-weighted lower residual, plus the active-indicator-weighted
upper residual has derivative zero](goal). -/
lemma binary_hinge_residual_orthogonality {q l b rB rL rQ : ℝ → ℝ}
    {dq dl db t : ℝ}
    (hq : HasDerivAt q dq t) (hl : HasDerivAt l dl t) (hb : HasDerivAt b db t)
    (hrB : HasDerivAt rB db t) (hrL : HasDerivAt rL (-dl) t)
    (hrQ : HasDerivAt rQ (-dq) t)
    (horder : l t < q t) (hbl : b t ≠ l t) (hbq : b t ≠ q t) :
    HasDerivAt (fun s => max 0 (q s - max (l s) (b s)) +
      indicator (l s < b s ∧ b s < q s) * rB s -
      indicator (l s > b s) * indicator (q s > max (l s) (b s)) * rL s +
      indicator (q s > max (l s) (b s)) * rQ s) 0 t := by
  have hh := binary_hinge_hasDerivAt hq hl hb horder hbl hbq
  have hder := ((hh.add (hrB.const_mul (indicator (l t < b t ∧ b t < q t)))).sub
    (hrL.const_mul (indicator (l t > b t) * indicator (q t > max (l t) (b t))))).add
    (hrQ.const_mul (indicator (q t > max (l t) (b t))))
  have hzero : HasDerivAt _ (0 : ℝ) t := hder.congr_deriv (by ring)
  apply hzero.congr_of_eventuallyEq
  filter_upwards [binary_branch_indicators_eventually_constant
    hq.continuousAt hl.continuousAt hb.continuousAt horder hbl hbq] with s hs
  rw [hs.1, hs.2.1, hs.2.2]
  rfl

-- The functions rP, rp and rq here are conditional residual means along a path.
-- At j = 1 the lower policy boundary is p_k and uses its propensity residual.
-- @node: binary_component_conditional_path_orthogonality
/-- Suppose [the upper](hyp:hq) and [lower pooled paths have derivatives dq
and dl](hyp:hl), [the upper propensity has derivative dp](hyp:hp), and
[the upper](hyp:hPplus) and [lower treated regressions have derivatives dPplus
and dPminus at zero](hyp:hPminus). If [the upper](hyp:hrPplus) and [lower
regression residual derivatives are minus dPplus and minus dPminus](hyp:hrPminus),
[the upper propensity residual derivative is minus dp](hyp:hrpplus), [the
upper policy residual derivative is minus dq](hyp:hrqplus), [the lower
propensity residual for the first band, or lower policy residual otherwise,
has derivative minus dl](hyp:hrlower), and [the lower policy residual vanishes
along the whole path in the first band](hyp:hrqzero), then, provided [the
pooled values are strictly ordered](hyp:horder) and [the adjusted boundary
differs from the lower](hyp:hbl) and [upper values at zero](hyp:hbq), [the
binary hinge with its branch-weighted regression, propensity, and policy
residual corrections has derivative zero at zero](goal). -/
lemma binary_component_conditional_path_orthogonality {X Z : Type v}
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : ℝ → NuisanceBin L)
    (k j : ℕ) (x : X) (rPplus rPminus rpplus rpminus rqplus rqminus : ℝ → ℝ)
    (dq dl dp dPplus dPminus : ℝ)
    (hq : HasDerivAt (fun t => pooledQBin phi L (e t) k j x) dq 0)
    (hl : HasDerivAt (fun t => pooledQBin phi L (e t) k (j - 1) x) dl 0)
    (hp : HasDerivAt (fun t => positiveValue (e t).pLev (k + 1) x) dp 0)
    (hPplus : HasDerivAt (fun t => positiveValue (e t).P1 (k + 1) x) dPplus 0)
    (hPminus : HasDerivAt (fun t => positiveValue (e t).P1 k x) dPminus 0)
    (hrPplus : HasDerivAt rPplus (-dPplus) 0)
    (hrPminus : HasDerivAt rPminus (-dPminus) 0)
    (hrpplus : HasDerivAt rpplus (-dp) 0)
    (hrqplus : HasDerivAt rqplus (-dq) 0)
    (hrlower : HasDerivAt (fun t => if j = 1 then rpminus t else rqminus t) (-dl) 0)
    (hrqzero : j = 1 → ∀ t, rqminus t = 0)
    (horder : pooledQBin phi L (e 0) k (j - 1) x < pooledQBin phi L (e 0) k j x)
    (hbl : positiveValue (e 0).pLev (k + 1) x - binFullJ L (e 0) k x ≠
      pooledQBin phi L (e 0) k (j - 1) x)
    (hbq : positiveValue (e 0).pLev (k + 1) x - binFullJ L (e 0) k x ≠
      pooledQBin phi L (e 0) k j x) :
    HasDerivAt (fun t => hMinus phi L (e t) k j x +
      Dbd phi L (e t) k j x * (rPplus t - rPminus t) -
      Dbd phi L (e t) k j x * rpplus t -
      (if j = 1 then Edom phi L (e t) k j x * Iact phi L (e t) k j x * rpminus t else 0) +
      Iact phi L (e t) k j x * rqplus t -
      Edom phi L (e t) k j x * Iact phi L (e t) k j x * rqminus t) 0 0 := by
  have hrB : HasDerivAt (fun t => rPplus t - rPminus t - rpplus t)
      (dp - (dPplus - dPminus)) 0 :=
    ((hrPplus.sub hrPminus).sub hrpplus).congr_deriv (by ring)
  have hh := binary_hinge_residual_orthogonality hq hl (hp.sub (hPplus.sub hPminus))
    hrB hrlower hrqplus horder hbl hbq
  convert hh using 1
  funext t
  dsimp only [hMinus, Dbd, Iact, Edom, binFullJ, Pi.sub_apply]
  by_cases hj : j = 1
  · simp only [if_pos hj, hrqzero hj t]
    ring
  · simp only [if_neg hj]
    ring


-- The gap keeps the population branch fixed on the small-error event.
-- @node: binary_separated_max_branch_stable
/-- If [the separation constant is positive](hyp:_hc), [the two values are
separated by at least that constant](hyp:hgap), [the first](hyp:ha) and
[second perturbations have absolute size at most e](hyp:hb), and [e is less
than half the separation constant](hyp:he), then [the change in their maximum
equals the perturbation of the originally larger value, choosing the first
when it is not smaller](goal). -/
lemma binary_separated_max_branch_stable {a b da db e c : ℝ}
    (_hc : 0 < c) (hgap : c ≤ |a - b|)
    (ha : |da| ≤ e) (hb : |db| ≤ e) (he : e < c / 2) :
    max (a + da) (b + db) - max a b = if a < b then db else da := by
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  by_cases hab : a < b
  · have hsep : c ≤ b - a := by
      simpa only [abs_of_neg (sub_neg.mpr hab), neg_sub] using hgap
    have hnew : a + da ≤ b + db := by linarith
    rw [max_eq_right hnew, max_eq_right hab.le, if_pos hab]
    ring
  · have hsep : c ≤ a - b := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hab))] using hgap
    have hnew : b + db ≤ a + da := by linarith
    rw [max_eq_left hnew, max_eq_left (le_of_not_gt hab), if_neg hab]
    ring

-- Outside the small-error event, Lipschitz control turns the first-order
-- bound into a quadratic one. This does not assume the fitted branch is right.
-- @node: binary_separated_max_quadratic_remainder
/-- If [the separation constant is positive](hyp:hc), [the two values differ
by at least that constant in absolute value](hyp:hgap), and [the first](hyp:ha)
and [second perturbations have absolute size at most e](hyp:hb), then [the
absolute change in their maximum after subtracting the perturbation of the
originally larger value is at most four times e squared divided by the
separation constant](goal). -/
lemma binary_separated_max_quadratic_remainder {a b da db e c : ℝ}
    (hc : 0 < c) (hgap : c ≤ |a - b|) (ha : |da| ≤ e) (hb : |db| ≤ e) :
    |max (a + da) (b + db) - max a b - (if a < b then db else da)| ≤
      (4 / c) * e ^ 2 := by
  have he0 : 0 ≤ e := (abs_nonneg da).trans ha
  by_cases he : e < c / 2
  · rw [binary_separated_max_branch_stable hc hgap ha hb he, sub_self, abs_zero]
    positivity
  · have hm : |max (a + da) (b + db) - max a b| ≤ e := by
      have h := abs_max_sub_max_le_max (a + da) (b + db) a b
      simp only [add_sub_cancel_left] at h
      exact h.trans (max_le ha hb)
    have hd : |if a < b then db else da| ≤ e := by
      split_ifs <;> assumption
    have hlin := (abs_sub _ _).trans (add_le_add hm hd)
    have hquad : 2 * e ≤ (4 / c) * e ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).mpr
      have hlarge : c / 2 ≤ e := le_of_not_gt he
      have hprod : 0 ≤ e * (2 * e - c) := mul_nonneg he0 (by linarith)
      nlinarith
    exact hlin.trans (by linarith)

-- The outer hinge is also separated: q differs from max l b by at least c.
-- @node: binary_hinge_quadratic_remainder
/-- If [the gap constant is positive](hyp:hc), [the upper value exceeds the
lower by at least that constant](hyp:hlq), [the boundary is separated from
the lower](hyp:hbl) and [upper values by that constant](hyp:hbq), and
[the upper](hyp:hq), [lower](hyp:hl), and [boundary perturbations have absolute
size at most e](hyp:hb), then [the hinge change minus its active-indicator-weighted
linear change, using the perturbation of the larger inner argument, has
absolute value at most twenty times e squared divided by the gap](goal). -/
lemma binary_hinge_quadratic_remainder {q l b dq dl db e c : ℝ}
    (hc : 0 < c) (hlq : c ≤ q - l) (hbl : c ≤ |b - l|) (hbq : c ≤ |b - q|)
    (hq : |dq| ≤ e) (hl : |dl| ≤ e) (hb : |db| ≤ e) :
    |max 0 (q + dq - max (l + dl) (b + db)) - max 0 (q - max l b) -
      indicator (q > max l b) * (dq - (if l < b then db else dl))| ≤
      (20 / c) * e ^ 2 := by
  have he0 : 0 ≤ e := (abs_nonneg dq).trans hq
  let dm := max (l + dl) (b + db) - max l b
  have hdm : |dm| ≤ e := by
    have h := abs_max_sub_max_le_max (l + dl) (b + db) l b
    simp only [add_sub_cancel_left] at h
    exact h.trans (max_le hl hb)
  have hinner := binary_separated_max_quadratic_remainder hc
    (by simpa only [abs_sub_comm] using hbl) hl hb
  have houtergap : c ≤ |0 - (q - max l b)| := by
    by_cases h : l ≤ b
    · simpa only [max_eq_right h, zero_sub, neg_sub] using hbq
    · rw [max_eq_left (le_of_not_ge h), zero_sub, abs_neg,
        abs_of_nonneg (by linarith : 0 ≤ q - l)]
      exact hlq
  have harg : |dq - dm| ≤ 2 * e := (abs_sub _ _).trans (by linarith)
  have hout := binary_separated_max_quadratic_remainder hc houtergap
    (show |(0 : ℝ)| ≤ 2 * e by simpa using (by linarith : 0 ≤ 2 * e)) harg
  have hind : (if (0 : ℝ) < q - max l b then dq - dm else 0) =
      indicator (q > max l b) * (dq - dm) := by
    by_cases h : q > max l b
    · simp [indicator, h, sub_pos.mpr h]
    · simp [indicator, h, show ¬ 0 < q - max l b by simpa only [sub_pos] using h]
  have hid : q - max l b + (dq - dm) = q + dq - max (l + dl) (b + db) := by
    dsimp [dm]
    ring
  rw [zero_add, hid, hind] at hout
  have hweight : |indicator (q > max l b) *
      (dm - (if l < b then db else dl))| ≤ (4 / c) * e ^ 2 := by
    by_cases h : q > max l b
    · simpa only [indicator, if_pos h, one_mul, dm] using hinner
    · simp only [indicator, if_neg h, zero_mul, abs_zero]
      positivity
  have htriangle := abs_sub_le
    (max 0 (q + dq - max (l + dl) (b + db)) - max 0 (q - max l b))
    (indicator (q > max l b) * (dq - dm))
    (indicator (q > max l b) * (dq - (if l < b then db else dl)))
  have hdiff : indicator (q > max l b) * (dq - dm) -
      indicator (q > max l b) * (dq - (if l < b then db else dl)) =
      -(indicator (q > max l b) * (dm - (if l < b then db else dl))) := by ring
  rw [hdiff, abs_neg] at htriangle
  calc
    _ ≤ (4 / c) * (2 * e) ^ 2 + (4 / c) * e ^ 2 :=
      htriangle.trans (add_le_add hout hweight)
    _ = (20 / c) * e ^ 2 := by ring


-- Put the bound in exactly the Riesz-coefficient form used by the score.
-- @node: binary_hinge_indicator_quadratic_remainder
/-- Under [a positive gap constant](hyp:hc), [an upper-minus-lower gap at
least that constant](hyp:hlq), [boundary separation from the lower](hyp:hbl)
and [upper values by that constant](hyp:hbq), and [upper](hyp:hq), [lower](hyp:hl),
and [boundary perturbations bounded in absolute value by e](hyp:hb), [the
hinge change minus the upper perturbation on the active branch, plus the
boundary perturbation on the intermediate branch, plus the lower perturbation
on the active lower-dominant branch has absolute value at most twenty times
e squared divided by the gap](goal). -/
lemma binary_hinge_indicator_quadratic_remainder {q l b dq dl db e c : ℝ}
    (hc : 0 < c) (hlq : c ≤ q - l) (hbl : c ≤ |b - l|) (hbq : c ≤ |b - q|)
    (hq : |dq| ≤ e) (hl : |dl| ≤ e) (hb : |db| ≤ e) :
    |max 0 (q + dq - max (l + dl) (b + db)) - max 0 (q - max l b) -
      (indicator (q > max l b) * dq - indicator (l < b ∧ b < q) * db -
        indicator (l > b) * indicator (q > max l b) * dl)| ≤
      (20 / c) * e ^ 2 := by
  have hcoeff : indicator (q > max l b) * dq - indicator (l < b ∧ b < q) * db -
      indicator (l > b) * indicator (q > max l b) * dl =
      indicator (q > max l b) * (dq - (if l < b then db else dl)) := by
    by_cases h : l < b
    · rw [max_eq_right h.le]
      by_cases hq' : b < q <;> simp [indicator, h, hq', not_lt_of_ge h.le]
    · have hb' : b < l := by
        have hle : b ≤ l := le_of_not_gt h
        have hsep : c ≤ l - b := by
          simpa only [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub] using hbl
        linarith
      rw [max_eq_left hb'.le]
      have hlq' : l < q := by linarith
      simp [indicator, h, hb', hlq']
  rw [hcoeff]
  exact binary_hinge_quadratic_remainder hc hlq hbl hbq hq hl hb

-- Apply the finite-perturbation bound to the actual binary gap functional.
-- @node: hMinus_quadratic_remainder
/-- Suppose [the gap constant is positive](hyp:hc), [the adjacent pooled
values are separated by that constant](hyp:hlq), [the adjusted boundary is
that far from the lower](hyp:hbl) and [upper pooled values](hyp:hbq), and
[the upper pooled value](hyp:hq), [lower pooled value](hyp:hl), and [adjusted
boundary change by at most the error envelope](hyp:hb). Then [the binary
hinge change after subtracting its linear correction weighted by the original
active, intermediate-boundary, and lower-dominance indicators is bounded in
absolute value by twenty times the squared envelope divided by the gap](goal). -/
lemma hMinus_quadratic_remainder {X Z : Type v}
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
      (Iact phi L e0 k j x * (pooledQBin phi L e1 k j x - pooledQBin phi L e0 k j x) -
        Dbd phi L e0 k j x * ((positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x) -
          (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)) -
        Edom phi L e0 k j x * Iact phi L e0 k j x *
          (pooledQBin phi L e1 k (j - 1) x - pooledQBin phi L e0 k (j - 1) x))| ≤
      (20 / c) * err ^ 2 := by
  have h := binary_hinge_indicator_quadratic_remainder hc hlq hbl hbq hq hl hb
  simpa only [hMinus, Iact, Dbd, Edom, add_sub_cancel] using h

end Papers.TbsPrteOptimalTransport
