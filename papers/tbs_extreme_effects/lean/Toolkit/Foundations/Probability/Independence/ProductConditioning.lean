module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Prod
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.Real

/-!
# Toolkit.Foundations.Probability.Independence.ProductConditioning

Conditioning product laws on coordinate rectangles
-/

public section

namespace Toolkit.Foundations.Probability.Independence

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

-- @node: sample_cond_pi_rectangle
/-- Given [measurable coordinate conditioning sets](hyp:hs) with [positive probability in every coordinate](hyp:hpos), [conditioning a product law on their rectangle equals the product of the coordinatewise conditional laws](goal). -/
lemma cond_pi_univ_pi {I Z : Type*} [Fintype I] [MeasurableSpace Z]
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)]
    (s : I → Set Z) (hs : ∀ i, MeasurableSet (s i))
    (hpos : ∀ i, μ i (s i) ≠ 0) :
    cond (Measure.pi μ) (Set.univ.pi s) = Measure.pi (fun i => cond (μ i) (s i)) := by
  letI (i : I) : IsProbabilityMeasure (cond (μ i) (s i)) := cond_isProbabilityMeasure (hpos i)
  apply (Measure.pi_eq fun u hu => ?_).symm
  rw [cond_apply (MeasurableSet.univ_pi hs), ← Set.pi_inter_distrib,
    Measure.pi_pi, Measure.pi_pi]
  simp_rw [cond_apply (hs _)]
  rw [ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inr (measure_ne_top (μ j) (s j))),
    ← Finset.prod_mul_distrib]

end

end Toolkit.Foundations.Probability.Independence

namespace Toolkit.Foundations.Probability.Independence

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- If [the nuisance map is measurable](hyp:hg), [the nuisance and sample have the stated product joint law](hyp:hjoint), [the joint bad event is measurable](hyp:hE), [the probability bound is delta](hyp:delta), and [almost every nuisance-specific section of that event has probability at most delta](hyp:hsections), then [the realized joint bad event has probability at most delta](goal). -/
-- @node: excess_independent_event_probability_le
lemma measure_prodMk_mem_le_of_ae_measure_section_le
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (Q : Measure B) [SFinite Q]
    (g : Ω → A) (sample : Ω → B) (hg : Measurable g)
    (hjoint : MeasurePreserving (fun w => (g w, sample w)) mu ((mu.map g).prod Q))
    (E : Set (A × B)) (hE : MeasurableSet E) (delta : ℝ≥0∞)
    (hsections : ∀ᵐ w ∂mu, Q {b | (g w, b) ∈ E} ≤ delta) :
    mu {w | (g w, sample w) ∈ E} ≤ delta := by
  have hsec : ∀ᵐ a ∂mu.map g, Q (Prod.mk a ⁻¹' E) ≤ delta := by
    apply (ae_map_iff hg.aemeasurable
      (measurableSet_le (measurable_measure_prodMk_left hE) measurable_const)).2
    exact hsections
  calc
    mu {w | (g w, sample w) ∈ E} = ((mu.map g).prod Q) E := by
      rw [← hjoint.map_eq, Measure.map_apply hjoint.measurable hE]
      rfl
    _ = ∫⁻ a, Q (Prod.mk a ⁻¹' E) ∂mu.map g := Measure.prod_apply hE
    _ ≤ ∫⁻ _a, delta ∂mu.map g := lintegral_mono_ae hsec
    _ = delta := by simp [Measure.map_apply hg MeasurableSet.univ]

end

end Toolkit.Foundations.Probability.Independence
