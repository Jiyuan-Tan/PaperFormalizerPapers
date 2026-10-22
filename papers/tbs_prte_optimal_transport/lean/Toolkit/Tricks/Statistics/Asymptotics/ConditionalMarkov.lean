module

public import Batteries.Logic
public import Causalean.Stat.Limit.Modes
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
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
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.Prop
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

/-!
# Convergence in probability from conditional moment bounds

Conditional Markov bounds turn conditional moment control into unconditional
convergence in probability, allowing the conditioning sigma algebra to vary with
the sample size. This is the conditioning step in sample splitting arguments.

The reference is Chernozhukov, Chetverikov, Demirer, Duflo, Hansen, Newey and
Robins (2018), *Double/debiased machine learning*, Lemma 6.1 (conditional
convergence implies unconditional). The moment version follows by conditional
Markov's inequality. The original TeX source is available at
https://arxiv.org/src/1608.00060v5, `Post-ML-28-noectj.tex`, lines 1846–1854.

The bound need only be measurable for the ambient sigma algebra. In particular,
it need not be measurable for the conditioning sigma algebra: the good event
used for the conditional integral is a sublevel set of the conditional
expectation itself. No integrability or almost sure nonnegativity of the bound
is assumed.

## Main results

* `measureReal_ge_le_of_condExp_le`: the single-index conditional Markov tail
  bound.
* `tendstoInProbability_zero_of_condExp_le_of_tendstoInProbability_zero`:
  conditional convergence to zero implies convergence in probability.
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace Toolkit.Tricks.Statistics.Asymptotics

/-- On a probability space, suppose [the conditioning sigma algebra is contained
in the ambient one](hyp:hm) and has a sigma-finite restricted measure. If
[a real quantity is integrable](hyp:hE), [is nonnegative almost surely](hyp:hEnonneg),
and [its conditional expectation is bounded almost surely by a real
quantity](hyp:hcond) that [is measurable for the ambient sigma algebra](hyp:hV),
then for [a positive tail
threshold](hyp:hε) and [a positive bound cutoff](hyp:hδ), [its upper-tail
probability is at most the probability that the absolute bound exceeds the
cutoff, plus the cutoff divided by the tail threshold](goal).

The tail probabilities include equality at their thresholds. -/
theorem measureReal_ge_le_of_condExp_le
    {A : Type*} [mA : MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (m : MeasurableSpace A) (hm : m ≤ mA) [SigmaFinite (μ.trim hm)]
    (E V : A → ℝ) (hV : Measurable[mA] V)
    (hE : Integrable E μ) (hEnonneg : 0 ≤ᵐ[μ] E)
    (hcond : μ[E | m] ≤ᵐ[μ] V)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    μ.real {ω | ε ≤ E ω} ≤ μ.real {ω | δ ≤ |V ω|} + δ / ε := by
  /- Proof plan: put C = μ[E | m], S = {C ≤ δ}, B = {δ ≤ |V|}.
  The set S is m-measurable by stronglyMeasurable_condExp. Use
  setIntegral_condExp hm hE on S to identify the restricted integral of E
  with that of C, which is at most δ * μ.real S ≤ δ. Apply
  mul_meas_ge_le_integral_of_nonneg to E under μ.restrict S, using
  hE.integrableOn and hEnonneg restricted to S. This bounds the part of
  the E tail inside S by δ / ε. The set B is ambient measurable by hV;
  partition the E tail against B using measureReal_inter_add_sdiff₀.
  On Bᶜ, hcond implies C ≤ V ≤ |V| < δ almost surely, so the remaining
  tail is contained in S up to a null set. No m-measurability of V is used.
  All real-measure monotonicity steps use finiteness of μ, never toReal
  monotonicity without a finite upper endpoint. -/
  let : MeasurableSpace A := mA
  let S := {ω | μ[E | m] ω ≤ δ}
  let B := {ω | δ ≤ |V ω|}
  let T := {ω | ε ≤ E ω}
  have hSm : MeasurableSet[m] S :=
    measurableSet_le stronglyMeasurable_condExp.measurable measurable_const
  have hS : @MeasurableSet A mA S := hm _ hSm
  have hB : @MeasurableSet A mA B := by
    change @MeasurableSet A mA {ω | δ ≤ |V ω|}
    exact measurableSet_le measurable_const (by simpa only [Real.norm_eq_abs] using hV.norm)
  have hint : ∫ ω in S, E ω ∂μ ≤ δ := by
    rw [← setIntegral_condExp hm hE hSm]
    calc
      ∫ ω in S, μ[E | m] ω ∂μ ≤ ∫ _ in S, δ ∂μ :=
        setIntegral_mono_on integrable_condExp.integrableOn
          (integrable_const δ).integrableOn hS (fun _ hω => hω)
      _ = μ.real S * δ := by simp
      _ ≤ 1 * δ := mul_le_mul_of_nonneg_right (measureReal_le_one) hδ.le
      _ = δ := one_mul δ
  have hmark : μ.real (T ∩ S) ≤ δ / ε := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (ae_restrict_of_ae hEnonneg) hE.integrableOn ε (μ := μ.restrict S)
    rw [measureReal_restrict_apply' hS] at h
    exact (le_div_iff₀ hε).mpr (by simpa [mul_comm] using h.trans hint)
  have hsub : (T \ B : Set A) ≤ᵐ[μ] (T ∩ S : Set A) := by
    filter_upwards [hcond] with ω hω
    intro h
    exact ⟨h.1, hω.trans ((le_abs_self _).trans (not_le.mp h.2).le)⟩
  calc
    μ.real T = μ.real (T ∩ B) + μ.real (T \ B) :=
      (measureReal_inter_add_sdiff₀ (s := T) hB.nullMeasurableSet).symm
    _ ≤ μ.real B + μ.real (T ∩ S) := add_le_add
      (measureReal_mono Set.inter_subset_right)
      (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub))
    _ ≤ μ.real B + δ / ε := add_le_add_right hmark _

/-- Conditional convergence to zero implies convergence in probability: on a
probability space, let [the conditioning sigma algebras be contained in the
ambient one](hyp:hm), with sigma-finite restricted measures. If [the real
bounds are measurable](hyp:hV), [the real errors are integrable](hyp:hE) and
[nonnegative almost surely](hyp:hEnonneg), [their conditional expectations are
bounded almost surely by those bounds](hyp:hcond), and [the bounds converge
to zero in probability](hyp:hlim), then [the errors converge to zero in
probability](goal).

Both the conditioning sigma algebra and the bound may vary with the index.
Only ambient measurability of the bounds is required, so this also applies
directly when they are measurable for their respective conditioning sigma
algebras. -/
theorem tendstoInProbability_zero_of_condExp_le_of_tendstoInProbability_zero
    {A : Type*} [mA : MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace A) (hm : ∀ n, m n ≤ mA)
    [∀ n, SigmaFinite (μ.trim (hm n))]
    (E V : ℕ → A → ℝ) (hV : ∀ n, Measurable (V n))
    (hE : ∀ n, Integrable (E n) μ)
    (hEnonneg : ∀ n, 0 ≤ᵐ[μ] E n)
    (hcond : ∀ n, μ[E n | m n] ≤ᵐ[μ] V n)
    (hlim : Causalean.Stat.Modes.TendstoInProbability
      (fun _ => μ) V atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability
      (fun _ => μ) E atTop (fun _ _ => 0) := by
  /- Proof plan: use Modes.tendstoInProbability_iff_measureReal_norm for
  both hlim and the goal, reducing to real norm-tail probabilities.
  Fix ε > 0 and a desired probability tolerance η > 0. Choose
  δ = η * ε / 2 > 0. The preceding bound controls each E upper tail by
  the V absolute tail at δ plus η / 2. The V tail is eventually < η / 2
  by hlim. For E, use hEnonneg to replace |E n| by E n almost surely;
  ambient measurability of E is not required (integrability supplies
  a.e. measurability). Conclude using the real metric or order criterion
  for convergence to zero. Do not interchange limits in n and δ or
  assume convergence of the unconditional expectations. -/
  apply (Causalean.Stat.Modes.tendstoInProbability_iff_measureReal_norm
    (fun _ : ℕ => μ) E atTop (fun _ _ => 0)).mpr
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (measureReal_nonneg))
  · intro η hη
    let δ := η * ε / 2
    have hδ : 0 < δ := div_pos (mul_pos hη hε) (by norm_num)
    have htail := (Causalean.Stat.Modes.tendstoInProbability_iff_measureReal_norm
      (fun _ : ℕ => μ) V atTop (fun _ _ => 0)).mp hlim δ hδ
    have hevent := (tendsto_order.mp htail).2 (η / 2) (half_pos hη)
    filter_upwards [hevent] with n hn
    have heq : μ.real {ω | ε ≤ ‖E n ω - 0‖} = μ.real {ω | ε ≤ E n ω} := by
      apply measureReal_congr
      filter_upwards [hEnonneg n] with ω hω
      change (ε ≤ ‖E n ω - 0‖) = (ε ≤ E n ω)
      simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hω]
    rw [heq]
    have hbound := measureReal_ge_le_of_condExp_le μ (m n) (hm n)
      (E n) (V n) (hV n) (hE n) (hEnonneg n) (hcond n) hε hδ
    have hratio : δ / ε = η / 2 := by dsimp [δ]; field_simp
    simp only [sub_zero, Real.norm_eq_abs] at hn
    rw [hratio] at hbound
    linarith

end Toolkit.Tricks.Statistics.Asymptotics
