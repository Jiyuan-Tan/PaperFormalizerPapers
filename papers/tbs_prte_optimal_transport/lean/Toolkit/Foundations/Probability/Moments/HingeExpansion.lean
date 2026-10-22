module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.MinMax
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

/-!
# Second-order expansion of the expected hinge at a point of bounded density

The expected hinge (check-loss) `t ↦ ∫ (t - y)₊ dν(y)` has derivative `ν((-∞, t])`
at a threshold `a`. This module bounds the remainder of that linearization by a
quadratic in the threshold displacement, assuming only that interval masses near
`a` are controlled by a constant times their length; finite total mass extends the
bound to all displacements. The combined remainder is integrated directly, so no
first moment of the measure is needed.

* `abs_posPart_sub_sub_mul_indicator_le_indicator`: the pointwise remainder is
  supported on the interval between the two thresholds and bounded by the
  displacement there.
* `measureReal_Ioc_min_max_le_of_local_bound`: a local density bound plus finite
  total mass bounds the mass between the thresholds linearly in the displacement.
* `abs_integral_posPart_sub_sub_mul_indicator_le_mul_measureReal_Ioc`: the
  integrated remainder is at most displacement times interval mass.
* `abs_integral_posPart_sub_sub_mul_indicator_le`: the quadratic remainder bound.

Typical uses are the orthogonality remainders of quantile, expected-shortfall
(CVaR) and Lorentz-type scores whose threshold is estimated.
-/

public section

open MeasureTheory Set

namespace Toolkit.Foundations.Probability.Moments

/-- [For every outcome, moving a hinge threshold from one value to another changes
the positive part of threshold minus outcome by the displacement times the
indicator that the outcome is at most the old threshold, up to an error whose
absolute value is at most the absolute displacement when the outcome lies strictly
above the smaller and at or below the larger threshold, and zero
otherwise](goal).

Split according to the order of the thresholds and whether the outcome is below
each threshold. The upper endpoint must be included: when the threshold moves
downward, an outcome exactly at the old threshold has a nonzero remainder. -/
theorem abs_posPart_sub_sub_mul_indicator_le_indicator (a b y : ℝ) :
    |max (b - y) 0 - max (a - y) 0 -
      (b - a) * (Set.Iic a).indicator (fun _ : ℝ => (1 : ℝ)) y| ≤
    (Set.Ioc (min a b) (max a b)).indicator (fun _ : ℝ => |b - a|) y := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
    by_cases hya : y ≤ a <;> by_cases hyb : y ≤ b <;>
      simp [Set.indicator, max_def, abs_le, ← not_le, hya, hyb,
        abs_of_nonneg (sub_nonneg.mpr hab)] <;>
      split_ifs <;> constructor <;> linarith
  · rw [min_eq_right hab, max_eq_left hab]
    by_cases hya : y ≤ a <;> by_cases hyb : y ≤ b <;>
      simp [Set.indicator, max_def, abs_le, ← not_le, hya, hyb,
        abs_of_nonpos (sub_nonpos.mpr hab)] <;>
      split_ifs <;> constructor <;> linarith

/-- For a finite measure on the real line, if [the radius is positive](hyp:hr),
[the density cap is nonnegative](hyp:hC), and [every left-open, right-closed
interval within that radius of the center has mass at most the cap times its
length](hyp:hdensity), then [the mass of the interval between the center and any
other point is at most their distance times the cap plus total mass over the
radius](goal).

When the point is within the radius the local bound applies directly; otherwise
the interval mass is at most the total mass, which is at most total mass over the
radius times the distance. -/
theorem measureReal_Ioc_min_max_le_of_local_bound
    (ν : Measure ℝ) [IsFiniteMeasure ν] (a b r C : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ (u v : ℝ), a - r ≤ u → u ≤ v → v ≤ a + r →
      (ν (Ioc u v)).toReal ≤ C * (v - u)) :
    (ν (Ioc (min a b) (max a b))).toReal ≤
      (C + (ν univ).toReal / r) * |b - a| := by
  have hmass : 0 ≤ (ν univ).toReal := ENNReal.toReal_nonneg
  have hquot : 0 ≤ (ν univ).toReal / r := div_nonneg hmass hr.le
  have hlength : max a b - min a b = |b - a| := by
    rw [max_sub_min_eq_abs', abs_sub_comm]
  by_cases hnear : |b - a| ≤ r
  · have hab := abs_le.mp hnear
    have hlower : a - r ≤ min a b := le_min (by linarith) (by linarith)
    have hupper : max a b ≤ a + r := max_le (by linarith) (by linarith)
    calc
      (ν (Ioc (min a b) (max a b))).toReal ≤ C * |b - a| := by
        simpa only [hlength] using
          hdensity (min a b) (max a b) hlower min_le_max hupper
      _ ≤ (C + (ν univ).toReal / r) * |b - a| :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hquot) (abs_nonneg _)
  · have hfar : r ≤ |b - a| := (lt_of_not_ge hnear).le
    calc
      (ν (Ioc (min a b) (max a b))).toReal ≤ (ν univ).toReal :=
        measureReal_mono (subset_univ _)
      _ = ((ν univ).toReal / r) * r := (div_mul_cancel₀ _ hr.ne').symm
      _ ≤ ((ν univ).toReal / r) * |b - a| :=
        mul_le_mul_of_nonneg_left hfar hquot
      _ ≤ (C + (ν univ).toReal / r) * |b - a| :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (abs_nonneg _)

/-- For a finite measure on the real line and any two thresholds, [the absolute
value of the expected change in the hinge loss, minus the threshold displacement
times the probability mass at or below the old threshold, is at most the absolute
displacement times the mass of the interval between the two thresholds](goal).

Integrate the pointwise bound against the integrable indicator of that interval.
The combined remainder is bounded, so no moment of the measure is needed. -/
theorem abs_integral_posPart_sub_sub_mul_indicator_le_mul_measureReal_Ioc
    (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) :
    |∫ y : ℝ, max (b - y) 0 - max (a - y) 0 -
      (b - a) * (Iic a).indicator (fun _ : ℝ => (1 : ℝ)) y ∂ν| ≤
      |b - a| * (ν (Ioc (min a b) (max a b))).toReal := by
  have hg : Integrable
      ((Ioc (min a b) (max a b)).indicator (fun _ : ℝ => |b - a|)) ν :=
    (integrable_const _).indicator measurableSet_Ioc
  have hbound := norm_integral_le_of_norm_le
    (f := fun y : ℝ => max (b - y) 0 - max (a - y) 0 -
      (b - a) * (Iic a).indicator (fun _ : ℝ => (1 : ℝ)) y) hg
    (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs] using
        abs_posPart_sub_sub_mul_indicator_le_indicator a b y))
  rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul] at hbound
  simpa only [Real.norm_eq_abs, measureReal_def, mul_comm] using hbound

/-- **Second-order expansion of the expected hinge.** Let a finite measure on the
real line have, around a threshold, [a positive radius](hyp:hr), [a nonnegative
density cap](hyp:hC), and [mass at most the cap times length on every left-open,
right-closed interval within that radius](hyp:hdensity). Then for any new
threshold, [the expected change in the hinge loss, minus the threshold
displacement times the mass at or below the old threshold, is in absolute value at
most the squared displacement times the cap plus total mass over the
radius](goal).

Here the hinge loss of an outcome at a threshold is the positive part of threshold
minus outcome, and the linear term is its derivative, the distribution function at
the old threshold. The bound holds for all new thresholds, including those outside
the density-controlled neighborhood, and needs no first moment. -/
theorem abs_integral_posPart_sub_sub_mul_indicator_le
    (ν : Measure ℝ) [IsFiniteMeasure ν] (a b r C : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ (u v : ℝ), a - r ≤ u → u ≤ v → v ≤ a + r →
      (ν (Ioc u v)).toReal ≤ C * (v - u)) :
    |∫ y : ℝ, max (b - y) 0 - max (a - y) 0 -
      (b - a) * (Iic a).indicator (fun _ : ℝ => (1 : ℝ)) y ∂ν| ≤
      (C + (ν univ).toReal / r) * (b - a) ^ 2 := by
  calc
    _ ≤ |b - a| * (ν (Ioc (min a b) (max a b))).toReal :=
      abs_integral_posPart_sub_sub_mul_indicator_le_mul_measureReal_Ioc ν a b
    _ ≤ |b - a| * ((C + (ν univ).toReal / r) * |b - a|) :=
      mul_le_mul_of_nonneg_left
        (measureReal_Ioc_min_max_le_of_local_bound ν a b r C hr hC hdensity)
        (abs_nonneg _)
    _ = (C + (ν univ).toReal / r) * (b - a) ^ 2 := by
      rw [mul_left_comm, ← pow_two, sq_abs]

end Toolkit.Foundations.Probability.Moments
