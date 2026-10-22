module

public import Causalean.Stat.Concentration.TailBounds.BinomialCount
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Multiplicative Chernoff bounds for sums of independent bounded variables

For a finite family of independent random variables in the unit interval, the
lower tail of their sum has a rate controlled by the sum of the individual
expectations, rather than by the number of summands. No common distribution or
common mean is required, so the bounds stay informative when the mean is small
(counts of rare events).

The module exposes the Chernoff chain one step at a time:

* `mgf_sum_le_exp_of_mem_Icc` — the moment generating function of the sum is at
  most `exp (M * (exp t - 1))`, with `M` the sum of the means, at every tilt `t`;
* `measureReal_sum_le_le_exp_of_mem_Icc_of_nonpos` — the resulting lower-tail
  bound at an arbitrary nonpositive tilt and an arbitrary threshold;
* `measureReal_sum_le_one_sub_mul_le_exp_of_mem_Icc` — the multiplicative
  Chernoff lower-tail bound `ℙ(∑ Xᵢ ≤ (1 - δ) M) ≤ exp (-δ² M / 2)`.

The proof uses the one-variable moment generating function bound
`Causalean.Stat.Concentration.mgf_le_of_mem_Icc_zero_one` together with
Mathlib's factorization for independent sums and its Chernoff inequality. The
tilt is minus the relative deviation: the quadratic bound on the negative
exponential gives the standard constant one half without logarithms or endpoint
limits.

Reference: Mitzenmacher and Upfal, *Probability and Computing*, Theorem 4.5;
Boucheron, Lugosi and Massart, *Concentration Inequalities*, section 2.2.
-/

public section

namespace Toolkit.Foundations.Probability.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- For [measurable random variables](hyp:hXmeas) that are
[mutually independent](hyp:hXindep) and [take values between zero and one](hyp:hXbounded)
on [a probability space](hyp:hP), [the moment generating function of the sum over any finite
set of them, at any real tilt, is at most the exponential of the sum of their means times
the exponential of the tilt minus one](goal).

With M the sum of the expectations and t the tilt, the bound reads
𝔼[exp(t·∑ᵢ Xᵢ)] ≤ exp(M·(exp(t) − 1)); it holds for tilts of either sign. -/
theorem mgf_sum_le_exp_of_mem_Icc
    (P : Measure Ω) [hP : IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X P)
    (hXbounded : ∀ i w, X i w ∈ Set.Icc (0 : ℝ) 1)
    (I : Finset ι) (t : ℝ) :
    mgf (fun w ↦ ∑ i ∈ I, X i w) P t ≤
      Real.exp ((∑ i ∈ I, ∫ w, X i w ∂P) * (Real.exp t - 1)) := by
  -- Rewrite the pointwise sum as a sum of functions, use hXindep.mgf_sum,
  -- and bound each factor with Causalean's mgf_le_of_mem_Icc_zero_one.
  -- Finset.prod_le_prod uses mgf_nonneg; Real.exp_sum and
  -- Finset.sum_mul combine the exponential factors. Include I = empty.
  classical
  have hsum : (fun w ↦ ∑ i ∈ I, X i w) = ∑ i ∈ I, X i := by
    ext w
    simp only [Finset.sum_apply]
  rw [hsum, hXindep.mgf_sum hXmeas]
  calc
    (∏ i ∈ I, mgf (X i) P t) ≤
        ∏ i ∈ I, Real.exp ((∫ w, X i w ∂P) * (Real.exp t - 1)) := by
      exact Finset.prod_le_prod (fun i _ ↦ mgf_nonneg) (fun i _ ↦
        Causalean.Stat.Concentration.mgf_le_of_mem_Icc_zero_one
          (hXmeas i).aemeasurable (ae_of_all _ (hXbounded i)) t)
    _ = Real.exp ((∑ i ∈ I, ∫ w, X i w ∂P) * (Real.exp t - 1)) := by
      rw [← Real.exp_sum, ← Finset.sum_mul]

/-- For [measurable random variables](hyp:hXmeas) that are
[mutually independent](hyp:hXindep) and [take values between zero and one](hyp:hXbounded)
on [a probability space](hyp:hP), let M be the sum of their expectations over a finite
index set. At [any nonpositive tilt t](hyp:ht), [the probability that their sum is at most
a threshold a is bounded by exp(−t·a + M·(exp(t)−1))](goal).

This is the Chernoff lower tail before the tilt is chosen; optimising over the tilt
recovers the usual multiplicative bounds. -/
theorem measureReal_sum_le_le_exp_of_mem_Icc_of_nonpos
    (P : Measure Ω) [hP : IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X P)
    (hXbounded : ∀ i w, X i w ∈ Set.Icc (0 : ℝ) 1)
    (I : Finset ι) (a : ℝ) {t : ℝ} (ht : t ≤ 0) :
    P.real {w | ∑ i ∈ I, X i w ≤ a} ≤
      Real.exp (-t * a + (∑ i ∈ I, ∫ w, X i w ∂P) * (Real.exp t - 1)) := by
  -- The exponential of t times the sum is measurable and bounded by 1:
  -- the sum is nonnegative and t is nonpositive. Derive integrability
  -- with Integrable.of_bound, rather than adding an integrability premise.
  -- Apply ProbabilityTheory.measure_le_le_exp_mul_mgf, the preceding MGF
  -- bound, mul_le_mul_of_nonneg_left, and Real.exp_add.
  classical
  have hsummeas : Measurable (fun w ↦ ∑ i ∈ I, X i w) := by
    exact Finset.measurable_sum I (fun i _ ↦ hXmeas i)
  have hsumnonneg : ∀ w, 0 ≤ ∑ i ∈ I, X i w := fun w ↦
    Finset.sum_nonneg (fun i _ ↦ (hXbounded i w).1)
  have hint : Integrable (fun w ↦ Real.exp (t * ∑ i ∈ I, X i w)) P := by
    refine Integrable.of_bound
      (hsummeas.const_mul t).exp.aestronglyMeasurable 1 (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (t * ∑ i ∈ I, X i w) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg ht (hsumnonneg w))
      _ = 1 := Real.exp_zero
  calc
    P.real {w | ∑ i ∈ I, X i w ≤ a} ≤
        Real.exp (-t * a) * mgf (fun w ↦ ∑ i ∈ I, X i w) P t :=
      measure_le_le_exp_mul_mgf a ht hint
    _ ≤ Real.exp (-t * a) *
        Real.exp ((∑ i ∈ I, ∫ w, X i w ∂P) * (Real.exp t - 1)) :=
      mul_le_mul_of_nonneg_left
        (mgf_sum_le_exp_of_mem_Icc P X hXmeas hXindep hXbounded I t)
        (Real.exp_pos _).le
    _ = Real.exp (-t * a + (∑ i ∈ I, ∫ w, X i w ∂P) * (Real.exp t - 1)) :=
      (Real.exp_add _ _).symm

-- Causalean's SharpBernstein module has a private quadratic lemma, which
-- is unavailable through its public API. This elementary argument uses the
-- public Taylor lower bound at the opposite (nonnegative) argument.
private lemma exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hpoly : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
    have hseries := Real.sum_le_exp_of_nonneg hx 3
    convert hseries using 1; norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
  have hinv := inv_anti₀ hpos hpoly
  rw [← Real.exp_neg] at hinv
  have hprod : 1 ≤ (1 + x + x ^ 2 / 2) * (1 - x + x ^ 2 / 2) := by
    nlinarith [sq_nonneg (x ^ 2)]
  have hquad : (1 + x + x ^ 2 / 2)⁻¹ ≤ 1 - x + x ^ 2 / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    simpa [mul_comm] using hprod
  exact hinv.trans hquad

/-- **Multiplicative Chernoff lower-tail bound.** Let the random variables be
[measurable](hyp:hXmeas), [mutually independent](hyp:hXindep), and
[valued in the interval from zero to one](hyp:hXbounded) on [a probability space](hyp:hP),
and let M be the sum of their expectations over a finite index set.
For [a relative deviation δ between zero and one](hyp:hδ),
[the probability that their sum is at most (1 − δ) times M is at most exp(−δ² M / 2)](goal).

The variables need not share a distribution or a mean, and the rate depends on the total
mean M rather than on the number of summands (Mitzenmacher and Upfal, Theorem 4.5). -/
theorem measureReal_sum_le_one_sub_mul_le_exp_of_mem_Icc
    (P : Measure Ω) [hP : IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X P)
    (hXbounded : ∀ i w, X i w ∈ Set.Icc (0 : ℝ) 1)
    (I : Finset ι) {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    P.real {w | ∑ i ∈ I, X i w ≤ (1 - δ) * (∑ i ∈ I, ∫ w, X i w ∂P)} ≤
      Real.exp (-(δ ^ 2) * (∑ i ∈ I, ∫ w, X i w ∂P) / 2) := by
  have hM : 0 ≤ ∑ i ∈ I, ∫ w, X i w ∂P :=
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun w ↦ (hXbounded i w).1
  refine (measureReal_sum_le_le_exp_of_mem_Icc_of_nonpos P X hXmeas hXindep
    hXbounded I ((1 - δ) * (∑ i ∈ I, ∫ w, X i w ∂P))
    (t := -δ) (neg_nonpos.mpr hδ.1)).trans (Real.exp_le_exp.mpr ?_)
  have hquad := mul_le_mul_of_nonneg_left (exp_neg_le_quadratic hδ.1) hM
  nlinarith

end Toolkit.Foundations.Probability.Concentration
