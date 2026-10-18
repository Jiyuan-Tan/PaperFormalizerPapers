module

public import Causalean.Mathlib.Probability.StdNormalCDF
public import Causalean.Stat.OrderStatistic.Basic
public import Causalean.Stat.OrderStatistic.CDFTransport
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Laws of CDF and survival transforms of real random variables

The probability-integral transform sends any continuous real distribution to
the uniform law on the unit interval. Composing it with the inverse exponential
CDF gives the standard exponential law for minus the logarithm of the survival
function. No density, strict monotonicity, or full-support hypothesis is needed.

The module provides

* `measureReal_Ioi_eq_one_sub_cdf`: the survival function is one minus the CDF;
* `measurable_neg_log_measureReal_Ioi`: measurability of minus the log survival
  function;
* `map_neg_log_one_sub_uniform01_eq_expMeasure`: minus the log of one minus a
  unit-uniform draw is standard exponential;
* `map_neg_log_one_sub_cdf_eq_expMeasure`: the same law for minus the log of one
  minus a continuous CDF evaluated at a draw from its own distribution;
* `map_neg_log_measureReal_Ioi_eq_expMeasure`: minus the log survival function of
  an atomless real distribution, evaluated at a draw from it, is standard
  exponential.

The uniform law of the CDF transform and the continuity of an atomless CDF are
reused from Causalean (`Causalean.Stat.OrderStatistic.cdf_pushforward_of_continuous`,
`Causalean.Mathlib.cdf_continuous_of_noAtoms`); the only additional distribution
calculation is the inverse exponential transform of the unit-uniform law.

## References

Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events*, §4.1;
de Haan and Ferreira, *Extreme Value Theory*, §3.2.
-/

public section

namespace Toolkit.Foundations.Probability.Distributions

open MeasureTheory ProbabilityTheory

/-- For [a probability distribution on the real line](hyp:mu,hprob) and [a real
threshold](hyp:x), [the probability of strictly exceeding the threshold equals one
minus the cumulative distribution function at that threshold](goal). -/
theorem measureReal_Ioi_eq_one_sub_cdf (mu : Measure ℝ)
    [hprob : IsProbabilityMeasure mu] (x : ℝ) :
    mu.real (Set.Ioi x) = 1 - cdf mu x := by
  rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
    cdf_eq_real]

/-- For [a probability distribution on the real line](hyp:mu,hprob), [minus the
logarithm of its survival function is a measurable function of the
threshold](goal).

The survival function at a threshold is the probability of strictly exceeding it. -/
theorem measurable_neg_log_measureReal_Ioi (mu : Measure ℝ)
    [hprob : IsProbabilityMeasure mu] :
    Measurable (fun x => -Real.log (mu.real (Set.Ioi x))) := by
  have hm : Measurable (fun x : ℝ => -Real.log (1 - cdf mu x)) :=
    (Real.measurable_log.comp
      (measurable_const.sub (monotone_cdf mu).measurable)).neg
  simpa only [measureReal_Ioi_eq_one_sub_cdf] using hm

/-- [If U is uniformly distributed on the unit interval, then minus the logarithm
of one minus U has the exponential distribution with rate one](goal). -/
theorem map_neg_log_one_sub_uniform01_eq_expMeasure :
    Measure.map (fun u : ℝ => -Real.log (1 - u))
      Causalean.Stat.OrderStatistic.uniform01 = expMeasure 1 := by
  have hg : Measurable (fun u : ℝ => -Real.log (1 - u)) :=
    (Real.measurable_log.comp (measurable_const.sub measurable_id)).neg
  have : IsProbabilityMeasure Causalean.Stat.OrderStatistic.uniform01 :=
    ⟨by simp [Causalean.Stat.OrderStatistic.uniform01, Real.volume_Icc]⟩
  have : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have : IsProbabilityMeasure
      (Measure.map (fun u : ℝ => -Real.log (1 - u))
        Causalean.Stat.OrderStatistic.uniform01) := Measure.isProbabilityMeasure_map hg.aemeasurable
  apply Measure.eq_of_cdf
  ext t
  rw [cdf_eq_real, map_measureReal_apply hg measurableSet_Iic,
    cdf_expMeasure_eq zero_lt_one]
  unfold Causalean.Stat.OrderStatistic.uniform01
  rw [← restrict_Ioo_eq_restrict_Icc]
  simp only [measureReal_def, Measure.restrict_apply (hg measurableSet_Iic)]
  by_cases ht : 0 ≤ t
  · have hb : 1 - Real.exp (-t) < 1 := by linarith [Real.exp_pos (-t)]
    have hs : (fun u : ℝ => -Real.log (1 - u)) ⁻¹' Set.Iic t ∩
        Set.Ioo 0 1 = Set.Ioc 0 (1 - Real.exp (-t)) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic,
        Set.mem_Ioo, Set.mem_Ioc]
      constructor
      · rintro ⟨h, hu0, hu1⟩
        have he : Real.exp (-t) ≤ 1 - u :=
          (Real.le_log_iff_exp_le (by linarith : 0 < 1 - u)).1 (by linarith)
        exact ⟨hu0, by linarith⟩
      · rintro ⟨hu0, hu⟩
        have hu1 : u < 1 := hu.trans_lt hb
        have hl : -t ≤ Real.log (1 - u) :=
          (Real.le_log_iff_exp_le (by linarith : 0 < 1 - u)).2 (by linarith)
        exact ⟨by linarith, hu0, hu1⟩
    rw [hs, Real.volume_Ioc]
    have hn : 0 ≤ 1 - Real.exp (-t) := by
      have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
      linarith
    simp [ht, ENNReal.toReal_ofReal, hn]
  · have hs : (fun u : ℝ => -Real.log (1 - u)) ⁻¹' Set.Iic t ∩
        Set.Ioo 0 1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      rcases hu with ⟨h, hu0, hu1⟩
      have hl : Real.log (1 - u) ≤ 0 :=
        Real.log_nonpos (by linarith) (by linarith)
      change -Real.log (1 - u) ≤ t at h
      linarith
    simp [hs, ht]

/-- If X is drawn from [a probability distribution on the real line](hyp:mu,hprob)
[whose cumulative distribution function F is continuous](hyp:hcont), then [minus
the logarithm of one minus F(X) has the exponential distribution with rate
one](goal). -/
theorem map_neg_log_one_sub_cdf_eq_expMeasure (mu : Measure ℝ)
    [hprob : IsProbabilityMeasure mu]
    (hcont : Continuous (fun x => cdf mu x)) :
    Measure.map (fun x => -Real.log (1 - cdf mu x)) mu = expMeasure 1 := by
  have hg : Measurable (fun u : ℝ => -Real.log (1 - u)) :=
    (Real.measurable_log.comp (measurable_const.sub measurable_id)).neg
  change mu.map ((fun u : ℝ => -Real.log (1 - u)) ∘ (fun x => cdf mu x)) = _
  rw [← Measure.map_map hg hcont.measurable,
    Causalean.Stat.OrderStatistic.cdf_pushforward_of_continuous mu hcont]
  exact map_neg_log_one_sub_uniform01_eq_expMeasure

/-- **Minus the log survival function of an atomless variable is standard
exponential.** If X is drawn from [a probability distribution on the real
line](hyp:mu,hprob) [that puts zero probability on every single point](hyp:hatom),
and S is its survival function, then [minus the logarithm of S(X) has the
exponential distribution with rate one](goal).

The survival function at a threshold is the probability of strictly exceeding that
threshold. Atomlessness supplies continuity of the cumulative distribution
function; no density or strict monotonicity is required. Points where the survival
function vanishes carry no probability, so the convention for the logarithm of
zero does not affect the image law. -/
theorem map_neg_log_measureReal_Ioi_eq_expMeasure (mu : Measure ℝ)
    [hprob : IsProbabilityMeasure mu] [hatom : NullSingletonClass mu] :
    Measure.map (fun x => -Real.log (mu.real (Set.Ioi x))) mu = expMeasure 1 := by
  simpa only [measureReal_Ioi_eq_one_sub_cdf] using
    map_neg_log_one_sub_cdf_eq_expMeasure mu
      (Causalean.Mathlib.cdf_continuous_of_noAtoms mu)

end Toolkit.Foundations.Probability.Distributions
