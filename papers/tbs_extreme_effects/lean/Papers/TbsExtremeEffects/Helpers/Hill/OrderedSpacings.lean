module
public import Papers.TbsExtremeEffects.Helpers.Hill.SurvivalCoordinate

/-! Explicit finite exponential spacings and their tail-prefix agreement. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Set

/-- [The ordered spacing](goal) for [the sample functions](hyp:V), at [the index](hyp:j)
and [sample point](hyp:w), is its rank times the gap to the next decreasing order statistic. -/
-- @node: hillOrderedSpacing
noncomputable def hillOrderedSpacing {Ω : Type*} {n : ℕ}
    (V : Fin n → Ω → ℝ) (j : Fin n) (w : Ω) : ℝ :=
  ((j : ℕ) + 1 : ℝ) * (hillDecreasingOrder V w j -
    if h : j.val + 1 < n then hillDecreasingOrder V w ⟨j.val + 1, h⟩ else 0)

/-- If [every sample function is measurable](hyp:hV), then [the corresponding ordered spacing](goal) is measurable. -/
@[fun_prop]
-- @node: hill_ordered_spacing_measurable
lemma hill_ordered_spacing_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (V : Fin n → Ω → ℝ) (hV : ∀ i, Measurable (V i)) (j : Fin n) :
    Measurable (hillOrderedSpacing V j) := by
  unfold hillOrderedSpacing
  split_ifs <;> fun_prop

/-- When [the tail length is below the sample size](hyp:hk), [the decreasing order statistics agree with the sequence `Y`](hyp:hY), and
[the spacing index lies before that tail length](hyp:hj), [the ordered spacing](goal) equals its rank times the adjacent gap in `Y`. -/
-- @node: hill_ordered_spacing_agreement
lemma hill_ordered_spacing_agreement {Ω : Type*} {n k : ℕ}
    (V : Fin n → Ω → ℝ) (Y : ℕ → ℝ) (w : Ω) (hk : k < n)
    (hY : ∀ i : Fin n, hillDecreasingOrder V w i = Y (i.val + 1))
    (j : Fin n) (hj : j.val < k) :
    hillOrderedSpacing V j w = ((j : ℕ) + 1 : ℝ) *
      (Y (j.val + 1) - Y (j.val + 2)) := by
  have hnext : j.val + 1 < n := by omega
  simp only [hillOrderedSpacing, dif_pos hnext, hY]

/-- If [survival is antitone](hyp:hS), [strictly decreases from `a` onward](hyp:hStrict), and [is positive everywhere](hyp:hpos), then [a tail reference radius lies above the cutoff](hyp:har), [has reciprocal survival `v⁻¹`](hyp:hInv), and [the logarithmic survival threshold holds at `x`](hyp:hlog) imply [that `x` is at least that reference radius](goal).

The strictness is needed only on the tail ray, not on the entire radial law. -/
-- @node: hill_radius_above_quantile_of_log_survival
lemma hill_radius_above_quantile_of_log_survival (S : ℝ → ℝ)
    {a r v x : ℝ} (hS : Antitone S) (hStrict : StrictAntiOn S (Ici a))
    (hpos : ∀ z, 0 < S z) (har : a < r) (hInv : S r = v⁻¹)
    (hlog : Real.log v ≤ -Real.log (S x)) : r ≤ x := by
  by_contra h
  have hxr : x < r := lt_of_not_ge h
  have hmax : max a x < r := max_lt har hxr
  have hlt : S r < S x :=
    (hStrict (le_max_left a x) har.le hmax).trans_le
      (hS (le_max_right a x))
  have hlogs := Real.log_lt_log (hpos r) hlt
  rw [hInv, Real.log_inv] at hlogs
  linarith

end Papers.TbsExtremeEffects
