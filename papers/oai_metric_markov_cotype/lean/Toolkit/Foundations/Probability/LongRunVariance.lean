module

public import Batteries.Logic
public import Causalean.Mathlib.Probability.Certified.FiniteKernel
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice
public import Mathlib.Order.Max
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UniformSpace.Defs
public import Toolkit.Foundations.Probability.PoissonEquation

/-!
# Long-run variance of a finite Markov chain without aperiodicity

For a reward with stationary mean zero on a finite irreducible chain, the
Cesàro-weighted sum of the stationary lagged covariances, over lags one through
n minus one, converges, and the resulting long-run variance is the stationary
average of a nonnegative one-step innovation variance.

* `sum_innovationVariance_nonneg`, `sum_innovationVariance_eq`: the stationary
  average innovation variance of a Poisson potential is nonnegative and equals the
  reward's stationary second moment plus twice its pairing with the potential's
  one-step average.
* `sum_weighted_differences`: the summation-by-parts identity for Cesàro-weighted
  consecutive differences.
* `tendsto_weighted_covariances_of_potential`: the Cesàro-weighted covariance sums
  converge to that pairing. A Poisson potential turns the sum into a telescoping
  sum plus a vanishing Cesàro remainder, so periodic chains are included.

Reference: Meyn and Tweedie, Markov Chains and Stochastic Stability, Section 17.4
(the asymptotic variance through the Poisson equation).
-/

public section

open scoped BigOperators Topology
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

namespace Toolkit.Foundations.Probability

/-- For [a matrix with nonnegative entries](hyp:hR) and [nonnegative state weights](hyp:hphi),
[the weighted average of the innovation variances of any state function](hyp:g)
[is nonnegative](goal). -/
theorem sum_innovationVariance_nonneg {T : Type*} [Fintype T]
    {R : Matrix T T ℝ} {phi : T → ℝ}
    (hR : ∀ x y, 0 ≤ R x y) (hphi : ∀ x, 0 ≤ phi x) (g : T → ℝ) :
    0 ≤ ∑ x, phi x * innovationVariance R g x := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hphi x)
    (Finset.sum_nonneg fun y _ => mul_nonneg (hR x y) (sq_nonneg _))

/-- For [a row-stochastic finite matrix](hyp:hR), [a stationary probability vector](hyp:hphi),
and [a Poisson potential for a real reward](hyp:hpoisson), [the stationary average innovation
variance equals the reward's stationary second moment plus twice its stationary pairing
with the potential's one-step average](goal). -/
theorem sum_innovationVariance_eq {T : Type*} [Fintype T]
    {R : Matrix T T ℝ} {phi f g : T → ℝ}
    (hR : IsStochasticMatrix R) (hphi : IsStationary R phi)
    (hpoisson : ∀ x, g x - R.mulVec g x = f x) :
    (∑ x, phi x * innovationVariance R g x) =
      (∑ x, phi x * f x ^ 2) + 2 * ∑ x, phi x * f x * R.mulVec g x := by
  classical
  have hv (x : T) : innovationVariance R g x =
      R.mulVec (fun y => g y ^ 2) x - (R.mulVec g x) ^ 2 := by
    unfold innovationVariance
    simp_rw [show ∀ y, R x y * (g y - R.mulVec g x) ^ 2 =
      R x y * g y ^ 2 - 2 * R.mulVec g x * (R x y * g y) +
        R x y * (R.mulVec g x) ^ 2 by intro y; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hR.2 x]
    change R.mulVec (fun y => g y ^ 2) x -
      2 * R.mulVec g x * R.mulVec g x + 1 * (R.mulVec g x) ^ 2 = _
    ring
  simp_rw [hv, mul_sub]
  rw [Finset.sum_sub_distrib, sum_stationary_mulVec hphi]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← hpoisson x]
  ring

/-- For [a real sequence](hyp:a) and [a positive endpoint](hyp:hn),
[the sum of consecutive differences at indices one through n minus one, weighted
by one minus the index divided by n, equals the first sequence value minus the
average of the values at indices one through n](goal).

This is the finite identity behind the limit of the Cesàro-weighted covariance sums. -/
theorem sum_weighted_differences (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.Ico 1 n, (1 - (k : ℝ) / n) * (a k - a (k + 1))) =
      a 1 - (∑ k ∈ Finset.Ico 1 (n + 1), a k) / n := by
  have ht : ∀ n : ℕ, 1 ≤ n →
      (∑ k ∈ Finset.Ico 1 n, ((n : ℝ) - k) * (a k - a (k + 1))) =
        (n : ℝ) * a 1 - ∑ k ∈ Finset.Ico 1 (n + 1), a k := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
      have hs : (∑ k ∈ Finset.Ico 1 n,
          (((n + 1 : ℕ) : ℝ) - k) * (a k - a (k + 1))) =
          (∑ k ∈ Finset.Ico 1 n, ((n : ℝ) - k) * (a k - a (k + 1))) +
          ∑ k ∈ Finset.Ico 1 n, (a k - a (k + 1)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        ring
      have hd : (∑ k ∈ Finset.Ico 1 n, (a k - a (k + 1))) = a 1 - a n := by
        simpa only [neg_sub_neg] using Finset.sum_Ico_sub (fun k => -a k) hn
      rw [hs, ih, hd]
      push_cast
      ring
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  calc
    _ = (∑ k ∈ Finset.Ico 1 n, ((n : ℝ) - k) * (a k - a (k + 1))) / n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      field_simp
    _ = _ := by rw [ht n hn]; field_simp

/-- For [a row-stochastic finite matrix](hyp:hR) with [positive-power reachability](hyp:hreach),
[a stationary probability vector](hyp:hphi), [a reward with stationary mean zero](hyp:hcenter),
and [a Poisson potential for that reward](hyp:hpoisson), [the Cesàro-weighted sum of
positive-lag covariances converges to the stationary pairing of the reward with the
potential's one-step average](goal). -/
theorem tendsto_weighted_covariances_of_potential
    {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    {R : Matrix T T ℝ} {phi f g : T → ℝ}
    (hR : IsStochasticMatrix R)
    (hreach : ∀ x y, ∃ n : ℕ, 0 < (R ^ n) x y)
    (hphi : IsStationary R phi) (hcenter : ∑ x, phi x * f x = 0)
    (hpoisson : ∀ x, g x - R.mulVec g x = f x) :
    Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.Ico 1 n,
      (1 - (k : ℝ) / n) * ∑ x, ∑ y, phi x * (R ^ k) x y * f x * f y)
      Filter.atTop (nhds (∑ x, phi x * f x * R.mulVec g x)) := by
  classical
  let a : ℕ → ℝ := fun k => ∑ x, phi x * f x * (R ^ k).mulVec g x
  have hf : f = g - R.mulVec g := by
    ext x
    exact (hpoisson x).symm
  have hc (k : ℕ) : (∑ x, ∑ y, phi x * (R ^ k) x y * f x * f y) =
      a k - a (k + 1) := by
    have hm : (R ^ k).mulVec f = (R ^ k).mulVec g - (R ^ (k + 1)).mulVec g := by
      rw [hf, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_succ]
    calc
      _ = ∑ x, phi x * f x * (R ^ k).mulVec f x := by
        apply Finset.sum_congr rfl
        intro x _
        change (∑ y, phi x * (R ^ k) x y * f x * f y) =
          phi x * f x * ∑ y, (R ^ k) x y * f y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by simp [hm, a, mul_sub, Finset.sum_sub_distrib]
  have htel (n : ℕ) (hn : 0 < n) :
      (∑ k ∈ Finset.Ico 1 n,
        (1 - (k : ℝ) / n) * ∑ x, ∑ y, phi x * (R ^ k) x y * f x * f y) =
      a 1 - (∑ k ∈ Finset.Ico 1 (n + 1), a k) / n := by
    simp_rw [hc]
    exact sum_weighted_differences a hn
  let B : ℝ := ∑ y, |g y|
  have hb (y : T) : |g y| ≤ B :=
    Finset.single_le_sum (fun z _ => abs_nonneg (g z)) (Finset.mem_univ y)
  have hshift (x : T) : Filter.Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Ico 1 (n + 1), (R ^ k).mulVec g x) / n)
      Filter.atTop (nhds (∑ y, phi y * g y)) := by
    have he : Filter.Tendsto (fun n : ℕ => ((R ^ n).mulVec g x - g x) / n)
        Filter.atTop (nhds 0) := by
      apply tendsto_bdd_div_atTop_nhds_zero (b := -B - g x) (B := B - g x)
      · exact Filter.Eventually.of_forall fun n => by
          linarith [(abs_le.mp (abs_mulVec_pow_le hR hb n x)).1]
      · exact Filter.Eventually.of_forall fun n => by
          linarith [(abs_le.mp (abs_mulVec_pow_le hR hb n x)).2]
      · exact tendsto_natCast_atTop_atTop
    have hl := (tendsto_average_mulVec_pow hR hreach hphi g x).add he
    apply Filter.Tendsto.congr' _ (by simpa using hl)
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ n + 1), Finset.sum_range_succ]
    simp only [Finset.sum_range_one, pow_zero, Matrix.one_mulVec]
    ring
  have hlim : Filter.Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Ico 1 (n + 1), a k) / n)
      Filter.atTop (nhds 0) := by
    have hl := tendsto_finsetSum Finset.univ (fun x _ =>
      (hshift x).const_mul (phi x * f x))
    have hz : (∑ x, phi x * f x * (∑ y, phi y * g y)) = 0 := by
      rw [← Finset.sum_mul, hcenter, zero_mul]
    rw [hz] at hl
    convert hl using 1
    ext n
    simp only [a, Finset.sum_div, mul_div_assoc]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  apply Filter.Tendsto.congr' _ (by simpa [a] using hlim.const_sub (a 1))
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simpa [a] using (htel n hn).symm

end Toolkit.Foundations.Probability
