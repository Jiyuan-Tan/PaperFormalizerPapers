module

public import Batteries.Logic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
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
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.RelClasses
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

/-!
# Expectation recursions and telescoping bounds

From a conditional drift inequality `𝔼[V (t+1) | ℱ t] ≤ (1 - a t) V t + b t` the expectations
obey the same one-step recursion and hence the product-and-forcing bound; from
`𝔼[V (t+1) | ℱ t] ≤ V t - c t e t + b t` with `V ≥ 0` the weighted expected errors telescope:
`∑ c t 𝔼 e t ≤ 𝔼 V 0 + ∑ b t`. The observables are any integrable processes on any filtered
probability space, in particular arbitrary functions of a full history, not only Markov
statistics; the contraction coefficients may vary with time.
-/

public section

namespace Toolkit.Foundations.Probability.Processes

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If [the potential is integrable at every time](hyp:hV) and
[its conditional expected next value obeys the affine drift inequality](hyp:hdrift),
then [its unconditional expectation obeys the same one-step recursion](goal). -/
theorem expectation_recursion (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (V : ℕ → Ω → ℝ)
    (a b : ℕ → ℝ) (hV : ∀ t, Integrable (V t) μ)
    (hdrift : ∀ t, μ[V (t + 1) | ℱ t] ≤ᵐ[μ] fun ω => (1 - a t) * V t ω + b t)
    (t : ℕ) :
    (∫ ω, V (t + 1) ω ∂μ) ≤ (1 - a t) * (∫ ω, V t ω ∂μ) + b t := by
  have h := integral_mono_ae integrable_condExp
    (((hV t).const_mul (1 - a t)).add (integrable_const (b t))) (hdrift t)
  rw [integral_condExp (ℱ.le t),
    integral_add' ((hV t).const_mul (1 - a t)) (integrable_const (b t)),
    integral_const_mul] at h
  simpa using h

/-- If [a scalar sequence obeys an affine recursion](hyp:hrec) with
[nonnegative multiplicative coefficients](hyp:hq), then
[its value is bounded by the initial value and the accumulated weighted forcing terms](goal).

Coefficients greater than one and signed forcing terms are allowed.
-/
theorem affine_recursion_bound (v q b : ℕ → ℝ) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, v (t + 1) ≤ q t * v t + b t) (T : ℕ) :
    v T ≤ (∏ t ∈ Finset.range T, q t) * v 0 +
      ∑ i ∈ Finset.range T, b i * ∏ j ∈ Finset.Ico (i + 1) T, q j := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hsum :
        (∑ i ∈ Finset.range (T + 1), b i * ∏ j ∈ Finset.Ico (i + 1) (T + 1), q j) =
          q T * (∑ i ∈ Finset.range T, b i * ∏ j ∈ Finset.Ico (i + 1) T, q j) + b T := by
      rw [Finset.sum_range_succ]
      simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hi))]
      ring
    calc
      v (T + 1) ≤ q T * v T + b T := hrec T
      _ ≤ q T * ((∏ t ∈ Finset.range T, q t) * v 0 +
          ∑ i ∈ Finset.range T, b i * ∏ j ∈ Finset.Ico (i + 1) T, q j) + b T :=
        add_le_add (mul_le_mul_of_nonneg_left ih (hq T)) (le_refl (b T))
      _ = _ := by rw [Finset.prod_range_succ, hsum]; ring

/-- If [the potential is integrable](hyp:hV), [the conditional drift inequality holds](hyp:hdrift),
and [each contraction coefficient is at most one](hyp:ha), then
[the expected potential obeys the time-varying product-and-forcing bound](goal). -/
theorem expectation_product_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (V : ℕ → Ω → ℝ)
    (a b : ℕ → ℝ) (hV : ∀ t, Integrable (V t) μ) (ha : ∀ t, a t ≤ 1)
    (hdrift : ∀ t, μ[V (t + 1) | ℱ t] ≤ᵐ[μ] fun ω => (1 - a t) * V t ω + b t)
    (T : ℕ) :
    (∫ ω, V T ω ∂μ) ≤ (∏ t ∈ Finset.range T, (1 - a t)) * (∫ ω, V 0 ω ∂μ) +
      ∑ i ∈ Finset.range T, b i * ∏ j ∈ Finset.Ico (i + 1) T, (1 - a j) := by
  exact affine_recursion_bound (fun t => ∫ ω, V t ω ∂μ) (fun t => 1 - a t) b
    (fun t => sub_nonneg.mpr (ha t))
    (expectation_recursion μ ℱ V a b hV hdrift) T

/-- For [integrable potentials and errors](hyp:hV,he), if
[the potential is nonnegative](hyp:hVnonneg) and
[the conditional drift pays for the error](hyp:hdrift),
then [the total expected weighted error is at most the initial expected potential plus
the accumulated forcing terms](goal). -/
theorem expectation_telescoping_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (V e : ℕ → Ω → ℝ)
    (c b : ℕ → ℝ) (hV : ∀ t, Integrable (V t) μ) (he : ∀ t, Integrable (e t) μ)
    (hVnonneg : ∀ t, 0 ≤ᵐ[μ] V t)
    (hdrift : ∀ t, μ[V (t + 1) | ℱ t] ≤ᵐ[μ] fun ω => V t ω - c t * e t ω + b t)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, c t * ∫ ω, e t ω ∂μ) ≤
      (∫ ω, V 0 ω ∂μ) + ∑ t ∈ Finset.range T, b t := by
  have hstep : ∀ t, (∫ ω, V (t + 1) ω ∂μ) ≤
      (∫ ω, V t ω ∂μ) - c t * (∫ ω, e t ω ∂μ) + b t := by
    intro t
    have h := integral_mono_ae integrable_condExp
      (((hV t).sub ((he t).const_mul (c t))).add (integrable_const (b t)))
      (hdrift t)
    rw [integral_condExp (ℱ.le t),
      integral_add' ((hV t).sub ((he t).const_mul (c t))) (integrable_const (b t)),
      integral_sub' (hV t) ((he t).const_mul (c t)), integral_const_mul] at h
    simpa using h
  have htel : ∀ n, (∑ t ∈ Finset.range n, c t * ∫ ω, e t ω ∂μ) +
      (∫ ω, V n ω ∂μ) ≤ (∫ ω, V 0 ω ∂μ) + ∑ t ∈ Finset.range n, b t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hn := hstep n
      linarith
  have hterminal : 0 ≤ ∫ ω, V T ω ∂μ := integral_nonneg_of_ae (hVnonneg T)
  linarith [htel T]

end Toolkit.Foundations.Probability.Processes

namespace Toolkit.Foundations.Probability.Processes

section

set_option warn.classDefReducibility false
open scoped BigOperators Topology ENNReal

-- @node: lem:lem2
/-- If [γ is nonnegative](hyp:hγ), [every term of p lies between zero and one](hyp:hp),
and [each next term is at most p − γp²](hyp:hrec), then
[p at time t is at most 1 / (1 + γt)](goal). -/
lemma le_one_div_one_add_mul_of_le_sub_mul_sq (p : ℕ → ℝ) (γ : ℝ) (hγ : 0 ≤ γ) (hp : ∀ t, p t ∈ Set.Icc 0 1)
    (hrec : ∀ t, p (t+1) ≤ p t - γ * p t ^ 2) (t : ℕ) :
    p t ≤ 1 / (1 + γ * t) := by
  have hmono : Antitone p := antitone_nat_of_succ_le fun n => by
    nlinarith [hrec n, mul_nonneg hγ (sq_nonneg (p n))]
  have hden : 0 < 1 + γ * t := by positivity
  by_cases ht : p t = 0
  · rw [ht]
    exact le_of_lt (one_div_pos.mpr hden)
  have htpos : 0 < p t := lt_of_le_of_ne (hp t).1 (Ne.symm ht)
  have hpos (n : ℕ) (hn : n ≤ t) : 0 < p n := lt_of_lt_of_le htpos (hmono hn)
  -- On a positive prefix, each reciprocal increment is at least γ.
  have hstep (n : ℕ) (hn : n < t) : 1 / p n + γ ≤ 1 / p (n + 1) := by
    have hnpos := hpos n (Nat.le_of_lt hn)
    have hnextpos := hpos (n + 1) hn
    have hcross : γ * p n * p (n + 1) ≤ γ * p n ^ 2 := by
      nlinarith [mul_nonneg hγ (le_of_lt hnpos), hmono (Nat.le_succ n)]
    apply (le_div_iff₀ hnextpos).2
    calc
      (1 / p n + γ) * p (n + 1) =
          ((1 + γ * p n) * p (n + 1)) / p n := by
            field_simp [ne_of_gt hnpos]
      _ ≤ 1 := (div_le_iff₀ hnpos).2 (by nlinarith [hrec n])
  -- Induction telescopes the reciprocal increments up to the fixed horizon.
  have hsum (n : ℕ) (hn : n ≤ t) : 1 / p 0 + γ * n ≤ 1 / p n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hi := ih (Nat.le_trans (Nat.le_succ n) hn)
      have hs := hstep n hn
      push_cast
      linarith
  have hinit : 1 ≤ 1 / p 0 := (le_div_iff₀ (hpos 0 (Nat.zero_le t))).2 (by
    simpa using (hp 0).2)
  have hbound : 1 + γ * t ≤ 1 / p t := by linarith [hsum t le_rfl]
  exact (le_div_iff₀ hden).2 (by
    have := (le_div_iff₀ htpos).1 hbound
    nlinarith)

end

end Toolkit.Foundations.Probability.Processes
