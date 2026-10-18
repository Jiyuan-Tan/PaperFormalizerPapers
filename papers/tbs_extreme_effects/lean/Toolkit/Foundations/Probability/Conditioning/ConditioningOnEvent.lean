module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Order.Basic

/-!
# Toolkit.Foundations.Probability.Conditioning.ConditioningOnEvent

Conditional expectations under a law conditioned on an event
-/

public section

namespace Toolkit.Foundations.Probability.Conditioning

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- If [the conditioning sigma-algebra is contained in the ambient one](hyp:hG), [the conditioning event is measurable for it](hyp:hA), [that event has positive measure](hyp:hpos), and [the outcome is integrable](hyp:hf), then [conditioning first on the event leaves its conditional expectation unchanged almost everywhere under the conditional law](goal).

Conditioning on an event already in the conditioning sigma algebra preserves the conditional expectation. The normalization of the restricted measure cancels in every defining set integral. -/
-- @node: condExp_cond_on_measurable_event
lemma condExp_cond_ae_eq_condExp_of_measurableSet {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[G] A) (hpos : μ A ≠ 0)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    (μ[|A])[f | G] =ᵐ[μ[|A]] μ[f | G] := by
  have hc : (μ A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hpos
  have hfcond : Integrable f (μ[|A]) := hf.integrableOn.smul_measure hc
  have hgcond : Integrable (μ[f | G]) (μ[|A]) :=
    (integrable_condExp (μ := μ) (f := f) (m := G)).integrableOn.smul_measure hc
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hG hfcond
  · intro s hs _
    exact hgcond.integrableOn
  · intro s hs _
    simp only [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure]
    rw [Measure.restrict_restrict (hG _ hs)]
    rw [setIntegral_condExp hG hf (hs.inter hA)]
  · exact stronglyMeasurable_condExp.aestronglyMeasurable

end

end Toolkit.Foundations.Probability.Conditioning

namespace Toolkit.Foundations.Probability.Conditioning

noncomputable section

open scoped BigOperators Topology
open MeasureTheory

-- @node: reduction_map_cond_preimage
/-- For [a measurable transformation f](hyp:hf) and [a measurable target event A](hyp:hA),
[the distribution of f after conditioning on its value belonging to A equals its
unconditional distribution conditioned on A](goal). -/
lemma map_cond_preimage {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (f : Ω → α) (hf : Measurable f) (A : Set α) (hA : MeasurableSet A) :
    (ProbabilityTheory.cond μ (f ⁻¹' A)).map f = ProbabilityTheory.cond (μ.map f) A := by
  simp only [ProbabilityTheory.cond, Measure.map_smul,
    ← Measure.restrict_map hf hA, Measure.map_apply hf hA]

end

end Toolkit.Foundations.Probability.Conditioning
