module

public import Causalean.Stat.Coupling.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Holder
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Order.MinMax
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Symmetric clipping and convergence of cross moments

Clipping a real value to the interval from minus a radius to that radius, its
elementary bounds and its pointwise convergence as the radius grows; the
integrability of the coordinate product under a coupling whose marginals have
Hölder-conjugate moments; and the convergence of the expected product of the
clipped coordinates to the expected product.

This is the analytic layer of the Hölder-moment extension of the real-line
rearrangement inequality. Dominated convergence uses the already integrable
absolute product, so it treats the endpoint exponents without a separate
Young-inequality argument.
-/

@[expose] public section

namespace Toolkit.Tricks.Probability.Moments

open MeasureTheory Filter
open scoped ENNReal Topology
open Causalean.Stat

/-- For [a nonnegative integer radius](hyp:n) and [a real value](hyp:x),
[symmetric clipping](goal) replaces values outside the interval from minus the
radius to the radius by the nearest endpoint. -/
def symmetricClip (n : ℕ) (x : ℝ) : ℝ := max (-(n : ℝ)) (min (n : ℝ) x)

/-- [Clipping at any integer radius](hyp:n) is [a measurable function of the
real input](goal). -/
theorem measurable_symmetricClip (n : ℕ) : Measurable (symmetricClip n) := by
  exact measurable_const.max (measurable_const.min measurable_id)

/-- For [an integer radius](hyp:n) and [a real value](hyp:x), [the absolute
clipped value is at most the absolute original value](goal). -/
theorem abs_symmetricClip_le_abs (n : ℕ) (x : ℝ) :
    |symmetricClip n x| ≤ |x| := by
  rw [abs_le]
  constructor
  · exact le_max_of_le_right (le_min
      ((neg_nonpos.mpr (abs_nonneg x)).trans (Nat.cast_nonneg n)) (neg_abs_le x))
  · exact max_le ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (abs_nonneg x))
      ((min_le_right _ _).trans (le_abs_self x))

/-- For [an integer radius](hyp:n) and [a real value](hyp:x), [the absolute
clipped value is at most the radius](goal). -/
theorem abs_symmetricClip_le (n : ℕ) (x : ℝ) : |symmetricClip n x| ≤ (n : ℝ) := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le
    ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (Nat.cast_nonneg n)) (min_le_left _ _)⟩

/-- For [each real value](hyp:x), [clipping converges to that value as the
integer radius tends to infinity](goal). -/
theorem tendsto_symmetricClip (x : ℝ) :
    Tendsto (fun n : ℕ => symmetricClip n x) atTop (𝓝 x) := by
  -- Eventually the radius is larger than |x|, so clipping is eventually equal to x.
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnx : |x| ≤ (n : ℝ) := hN.le.trans (Nat.cast_le.mpr hn)
  have hb := abs_le.mp hnx
  simp [symmetricClip, min_eq_right hb.2, max_eq_right hb.1]

/-- Under [a coupling of the two real marginals](hyp:hπ), [conjugate Hölder
exponents, including one and infinity](hyp:hpq), and [finite corresponding
absolute moments of the marginals](hyp:hμ,hν), [the coordinate product is
integrable under the coupling](goal). -/
theorem integrable_mul_of_isCoupling {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}
    {p q : ℝ≥0∞} [hpq : p.HolderConjugate q]
    (hπ : IsCoupling π μ ν) (hμ : MemLp (fun x : ℝ => x) p μ)
    (hν : MemLp (fun x : ℝ => x) q ν) :
    Integrable (fun z : ℝ × ℝ => z.1 * z.2) π := by
  have hfst : MemLp (fun z : ℝ × ℝ => z.1) p π := by
    rw [← hπ.map_fst] at hμ
    simpa [Function.comp_def] using hμ.comp_of_map measurable_fst.aemeasurable
  have hsnd : MemLp (fun z : ℝ × ℝ => z.2) q π := by
    rw [← hπ.map_snd] at hν
    simpa [Function.comp_def] using hν.comp_of_map measurable_snd.aemeasurable
  exact hfst.integrable_mul hsnd

/-- For [a measure on pairs of real values](hyp:π) with [integrable coordinate
product](hyp:hint), [the expectations of the products of the clipped coordinates
converge to the expectation of the original product](goal). -/
theorem tendsto_integral_symmetricClip_mul (π : Measure (ℝ × ℝ))
    (hint : Integrable (fun z : ℝ × ℝ => z.1 * z.2) π) :
    Tendsto (fun n : ℕ => ∫ z, symmetricClip n z.1 * symmetricClip n z.2 ∂π)
      atTop (𝓝 (∫ z, z.1 * z.2 ∂π)) := by
  -- Use hint.norm as the integrable bound; abs_symmetricClip_le_abs bounds
  -- the clipped product, and tendsto_symmetricClip gives pointwise convergence.
  apply tendsto_integral_of_dominated_convergence (fun z : ℝ × ℝ => ‖z.1 * z.2‖)
  · intro n
    exact (((measurable_symmetricClip n).comp measurable_fst).mul
      ((measurable_symmetricClip n).comp measurable_snd)).aestronglyMeasurable
  · exact hint.norm
  · intro n
    exact ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs, abs_mul] using
        mul_le_mul (abs_symmetricClip_le_abs n z.1) (abs_symmetricClip_le_abs n z.2)
          (abs_nonneg _) (abs_nonneg _)
  · exact ae_of_all _ fun z => (tendsto_symmetricClip z.1).mul (tendsto_symmetricClip z.2)

end Toolkit.Tricks.Probability.Moments
