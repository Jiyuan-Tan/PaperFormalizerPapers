module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Extr
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.Lattice
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Closure properties of absolutely continuous functions on an interval

Composition with a map that is Lipschitz on the image of an interval preserves
absolute continuity. In particular, the square root of a strictly positive
absolutely continuous real function is absolutely continuous: continuity on the
compact interval places its range inside a compact interval bounded away from zero.

## Main results

* `absolutelyContinuousOnInterval_comp_of_lipschitzOnWith`: a map that is Lipschitz
  on the image of the interval, composed with an absolutely continuous function, is
  absolutely continuous.
* `absolutelyContinuousOnInterval_sqrt_of_pos`: the square root of a strictly
  positive absolutely continuous function is absolutely continuous.

Reference: Royden and Fitzpatrick, *Real Analysis*, fourth edition, §6.4,
Problem 44, p. 124, states the Lipschitz composition principle. Here the
Lipschitz condition is needed only on the image of the interval.
-/

public section

namespace Toolkit.Foundations.Analysis.Calculus

/-- If [a function is absolutely continuous on the interval between two real
endpoints](hyp:hf) and [a second map is Lipschitz on its image of that
interval](hyp:hg), then [their composition is absolutely continuous on the same
interval](goal).

The first function may take values in any pseudometric space, and the second map
needs no regularity away from the image of the interval.
-/
theorem absolutelyContinuousOnInterval_comp_of_lipschitzOnWith
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (a b : ℝ) (f : ℝ → X) (g : X → Y) {K : NNReal}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : LipschitzOnWith K g (f '' Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  -- Use absolutelyContinuousOnInterval_iff with epsilon / (K + 1), which
  -- also handles K = 0. For E in disjWithin a b, both endpoints belong
  -- to the interval, so their f-images are in the Lipschitz domain.
  -- Apply hg.dist_le_mul to each increment and Finset.sum_le_sum,
  -- then Finset.mul_sum. The resulting sum is bounded by K times
  -- the increment sum for f. No regularity of f outside the interval is needed.
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  have hK : 0 < (K : ℝ) + 1 := add_pos_of_nonneg_of_pos K.coe_nonneg zero_lt_one
  obtain ⟨δ, hδ, hδf⟩ := hf (ε / ((K : ℝ) + 1)) (div_pos hε hK)
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlength
  have hsum := hδf E hE hlength
  have hnonneg : 0 ≤ ∑ i ∈ Finset.range E.1,
      dist (f (E.2 i).1) (f (E.2 i).2) :=
    Finset.sum_nonneg (fun _ _ => dist_nonneg)
  calc
    ∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) *
            dist (f (E.2 i).1) (f (E.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hg.dist_le_mul (f (E.2 i).1)
        ⟨(E.2 i).1, (hE.1 i hi).1, rfl⟩ (f (E.2 i).2)
        ⟨(E.2 i).2, (hE.1 i hi).2, rfl⟩
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1,
        dist (f (E.2 i).1) (f (E.2 i).2) := (Finset.mul_sum ..).symm
    _ ≤ ((K : ℝ) + 1) * ∑ i ∈ Finset.range E.1,
        dist (f (E.2 i).1) (f (E.2 i).2) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hnonneg
    _ < ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) :=
      mul_lt_mul_of_pos_left hsum hK
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hK)

/-- If [a real function is absolutely continuous on the interval between two real
endpoints](hyp:hr) and [is strictly positive at every point of that
interval](hyp:hpos), then [its square root is absolutely continuous on the same
interval](goal).

By continuity on the compact interval the function is bounded below by a positive
constant there, and the square root is Lipschitz on the resulting compact range.
-/
theorem absolutelyContinuousOnInterval_sqrt_of_pos
    (a b : ℝ) (r : ℝ → ℝ)
    (hr : AbsolutelyContinuousOnInterval r a b)
    (hpos : ∀ x ∈ Set.uIcc a b, 0 < r x) :
    AbsolutelyContinuousOnInterval (fun x => √(r x)) a b := by
  obtain ⟨xmin, hxmin, hmin⟩ :=
    isCompact_uIcc.exists_isMinOn Set.nonempty_uIcc hr.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    isCompact_uIcc.exists_isMaxOn Set.nonempty_uIcc hr.continuousOn
  have hsqrt : ContDiffOn ℝ 1 Real.sqrt (Set.Icc (r xmin) (r xmax)) := by
    exact contDiffOn_id.sqrt (fun x hx => ne_of_gt (lt_of_lt_of_le (hpos xmin hxmin) hx.1))
  obtain ⟨K, hK⟩ := hsqrt.exists_lipschitzOnWith (by decide)
    (convex_Icc _ _) isCompact_Icc
  apply absolutelyContinuousOnInterval_comp_of_lipschitzOnWith a b r Real.sqrt hr
  apply hK.mono
  rintro y ⟨x, hx, rfl⟩
  exact ⟨hmin hx, hmax hx⟩

end Toolkit.Foundations.Analysis.Calculus
