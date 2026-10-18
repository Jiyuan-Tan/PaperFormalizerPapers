module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

/-!
# Conditional expectations of functions of a finite-valued random variable

A random choice from a finite set selects one of a family of real-valued functions
measurable with respect to the conditioning sigma-algebra. Its conditional mean is
the sum of those functions weighted by the conditional probabilities of the choices.
Only the products with the choice indicators need to be integrable; the functions
themselves need not be bounded or integrable.

The finite value space has measurable singletons, the usual discrete measurable
structure for a finite random element. An indicator is written directly as a real
valued if-then-else, so no auxiliary indicator definition is needed.

## Main results

* `Toolkit.Foundations.Probability.Conditioning.condExp_apply_eq_sum_mul_condExp_indicator`:
  the conditional expectation of `ω ↦ g (X ω) ω` given `G` is almost everywhere
  `∑ z, g z ω * μ[1{X = z} | G] ω`.

Reference: Durrett, *Probability: Theory and Examples*, fifth edition, Section 4.1,
Theorem 4.1.14 (taking out a measurable factor), together with finite-sum linearity.
-/

public section

namespace Toolkit.Foundations.Probability.Conditioning

open MeasureTheory

/-- The conditional expectation of a function of [a random element measurable with
respect to the ambient events](hyp:hX), taking values in [a finite discrete
measurable space](hyp:finiteS,hS), under [a finite measure](hyp:hμ) and given
[a sub-sigma-algebra of the ambient events](hyp:hG), is
[the sum over its values of each function times the conditional probability of that
value, almost everywhere](goal), provided [each real-valued function is measurable
with respect to the conditioning sigma-algebra](hyp:hg) and [its product with the
indicator of the corresponding value is integrable](hyp:h_int).

Neither boundedness nor integrability of the individual functions is assumed.
-/
theorem condExp_apply_eq_sum_mul_condExp_indicator
    {Ω S : Type*} [mΩ : MeasurableSpace Ω]
    [finiteS : Fintype S] [DecidableEq S] [MeasurableSpace S]
    [hS : MeasurableSingletonClass S]
    (μ : Measure Ω) [hμ : IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    (X : Ω → S) (hX : Measurable[mΩ] X) (g : S → Ω → ℝ)
    (hg : ∀ z, Measurable[G] (g z))
    (h_int : ∀ z, Integrable (fun ω => g z ω * if X ω = z then 1 else 0) μ) :
    μ[fun ω => g (X ω) ω | G] =ᵐ[μ]
      fun ω => ∑ z, g z ω * (μ[fun ω => if X ω = z then (1 : ℝ) else 0 | G]) ω := by
  -- The measure restricted to the conditioning sigma-algebra is finite, so the
  -- conditional expectations below are genuine ones, not the zero fallback.
  have : IsFiniteMeasure (μ.trim hG) := inferInstance
  -- Decompose the function over the finitely many values of `X`.
  have h_decomp : (fun ω => g (X ω) ω) =
      ∑ z : S, (fun ω => g z ω * if X ω = z then 1 else 0) := by
    funext ω
    simp [Finset.sum_apply, mul_ite]
  -- Pull the `G`-measurable factor out of each summand.
  have h_pull : ∀ z : S,
      μ[fun ω => g z ω * if X ω = z then 1 else 0 | G] =ᵐ[μ]
        fun ω => g z ω * (μ[fun ω => if X ω = z then (1 : ℝ) else 0 | G]) ω := by
    intro z
    have h_set : @MeasurableSet Ω mΩ {ω | X ω = z} :=
      hX (measurableSet_singleton z)
    have h_indicator : Integrable (fun ω => if X ω = z then (1 : ℝ) else 0) μ := by
      have h_eq : {ω | X ω = z}.indicator (fun _ : Ω => (1 : ℝ)) =
          (fun ω => if X ω = z then (1 : ℝ) else 0) := by
        funext ω
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [← h_eq]
      exact (integrable_const (1 : ℝ) (μ := μ)).indicator h_set
    exact condExp_mul_of_stronglyMeasurable_left (hg z).stronglyMeasurable
      (h_int z) h_indicator
  rw [h_decomp]
  refine (condExp_finsetSum (fun z _ => h_int z) G).trans ?_
  filter_upwards [ae_all_iff.mpr h_pull] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun z _ => hω z)

end Toolkit.Foundations.Probability.Conditioning
