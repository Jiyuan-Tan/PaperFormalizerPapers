module

public import Causalean.Experimentation.Sequential.Ville
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

/-!
# Toolkit.Foundations.Probability.Concentration.ExponentialSupermartingale

Maximal tail bounds for partial sums through exponential supermartingales
-/

public section

namespace Toolkit.Foundations.Probability.Concentration

section

open MeasureTheory
open scoped ENNReal Topology

/-- If [the exponential tilt is positive](hyp:hlam), [the compensation is nonnegative](hyp:hc), [the process starts at zero](hyp:hzero), and [its compensated exponential is a supermartingale](hyp:hSuper), then [the probability that the process crosses the level by the stated horizon is bounded by the exponential envelope](goal).
-/
-- @node: hill_exponential_crossing_bound
lemma measureReal_exists_le_lt_le_exp_of_supermartingale_exp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) {lam c a : ℝ}
    (hlam : 0 < lam) (hc : 0 ≤ c) (hzero : ∀ w, B 0 w = 0)
    (hSuper : Supermartingale (fun i w => Real.exp (lam * B i w - (i : ℝ) * c)) ℱ P)
    (m : ℕ) :
    P.real {w | ∃ i ≤ m, a < B i w} ≤ Real.exp (-lam * a + (m : ℝ) * c) := by
  classical
  let L := Real.exp (lam * a - (m : ℝ) * c)
  have hVille := Causalean.Experimentation.Sequential.supermartingale_maximal_ineq
    hSuper (fun i w => (Real.exp_pos _).le) (Real.exp_pos (lam * a - (m : ℝ) * c)) m
  have hinit : (∫ w, Real.exp (lam * B 0 w - (0 : ℝ) * c) ∂P) = 1 := by
    simp only [hzero, mul_zero, zero_mul, sub_zero, Real.exp_zero]
    simp
  simp only [Nat.cast_zero] at hVille
  rw [hinit] at hVille
  have hsub : {w | ∃ i ≤ m, a < B i w} ⊆
      {w | L ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
        (fun i => Real.exp (lam * B i w - (i : ℝ) * c))} := by
    rintro w ⟨i, hi, hcross⟩
    apply Finset.le_sup'_of_le (fun j => Real.exp (lam * B j w - (j : ℝ) * c))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    apply Real.exp_le_exp.mpr
    have hic : (i : ℝ) * c ≤ (m : ℝ) * c :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hc
    have hab := mul_le_mul_of_nonneg_left hcross.le hlam.le
    linarith
  have hmeasure := (measure_mono hsub).trans hVille
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / L)] at hreal
  have heq : 1 / L = Real.exp (-lam * a + (m : ℝ) * c) := by
    dsimp [L]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  exact hreal.trans_eq heq

end

end Toolkit.Foundations.Probability.Concentration

namespace Toolkit.Foundations.Probability.Concentration

section

open MeasureTheory
open scoped ENNReal Topology

/-- If [the partial-sum process is strongly adapted](hyp:hB), [each compensated exponential is integrable](hyp:hInt), [each exponential increment is integrable](hyp:hInc), and [its conditional exponential moment is bounded by the compensation factor](hyp:hMoment), then [the compensated exponential process is a supermartingale](goal).
-/
-- @node: hill_supermartingale_of_increment_moment
lemma supermartingale_exp_mul_sub_of_condExp_exp_increment_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (lam c : ℝ)
    (hB : StronglyAdapted ℱ B)
    (hInt : ∀ i, Integrable (fun w => Real.exp (lam * B i w - (i : ℝ) * c)) P)
    (hInc : ∀ i, Integrable (fun w => Real.exp (lam * (B (i + 1) w - B i w))) P)
    (hMoment : ∀ i, P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
      ≤ᵐ[P] fun _ => Real.exp c) :
    Supermartingale (fun i w => Real.exp (lam * B i w - (i : ℝ) * c)) ℱ P := by
  apply supermartingale_nat
  · intro i
    have hb := (hB i).measurable
    apply Measurable.stronglyMeasurable
    fun_prop
  · exact hInt
  · intro i
    let f : Ω → ℝ := fun w => Real.exp (lam * B i w - (i : ℝ) * c - c)
    let g : Ω → ℝ := fun w => Real.exp (lam * (B (i + 1) w - B i w))
    have hprod : (fun w => Real.exp (lam * B (i + 1) w - ((i + 1 : ℕ) : ℝ) * c)) =
        f * g := by
      funext w
      dsimp [f, g]
      rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    have hf : StronglyMeasurable[ℱ i] f := by
      have hb := (hB i).measurable
      apply Measurable.stronglyMeasurable
      fun_prop
    have hp : Integrable (f * g) P := by rw [← hprod]; exact hInt (i + 1)
    have hpull := condExp_mul_of_stronglyMeasurable_left hf hp (hInc i)
    rw [hprod]
    filter_upwards [hpull, hMoment i] with w hw hm
    calc
      _ = f w * P[g | ℱ i] w := hw
      _ ≤ f w * Real.exp c := mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
      _ = _ := by
        dsimp [f]
        rw [← Real.exp_add]
        congr 1
        ring

end

end Toolkit.Foundations.Probability.Concentration
