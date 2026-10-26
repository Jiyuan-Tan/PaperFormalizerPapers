module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.Restriction
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs
public import Toolkit.Foundations.Probability.Processes.PathLaw

/-!
# Information available from a finite history

The natural filtration of a process with changing state spaces is Mathlib's `Filtration.piLE`,
including the coordinate at the current time. This module proves that every coordinate and
every measurable function of the history is adapted, that history statistics depend only on
past coordinates, and that running sums, running averages, best-so-far maxima and indicators
of history events are measurable at the current time.
-/

@[expose] public section

namespace Toolkit.Foundations.Probability.Processes

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable (X : ℕ → Type*) [∀ t, MeasurableSpace (X t)]

/-- The [natural filtration](goal) reveals the coordinates through each time in
[the changing state spaces](hyp:X). -/
def naturalFiltration : Filtration ℕ (inferInstance : MeasurableSpace (Path X)) :=
  Filtration.piLE

/-- [The finite history is measurable with the information available at that time](goal). -/
theorem measurable_history (t : ℕ) :
    Measurable[naturalFiltration X t] (history X t) := by
  rw [naturalFiltration, Filtration.piLE_eq_comap_frestrictLe]
  exact measurable_iff_comap_le.mpr le_rfl

/-- [Every coordinate of the changing-state process is adapted](goal). -/
theorem adapted_coordinate : Adapted (naturalFiltration X) (coordinate X) := by
  intro t
  exact (measurable_pi_apply ⟨t, Finset.mem_Iic.mpr le_rfl⟩).comp (measurable_history X t)

variable {X}

/-- [A measurable function of the finite history](hyp:hf) is
[measurable with the information available at that time](goal). -/
theorem measurable_history_function {Y : Type*} [MeasurableSpace Y] (t : ℕ)
    (f : History X t → Y) (hf : Measurable f) :
    Measurable[naturalFiltration X t] (fun ω => f (history X t ω)) :=
  hf.comp (measurable_history X t)

/-- [Measurable time-dependent history statistics](hyp:hf) form [an adapted process](goal). -/
theorem adapted_history_function {Y : ℕ → Type*} [∀ t, MeasurableSpace (Y t)]
    (f : (t : ℕ) → History X t → Y t) (hf : ∀ t, Measurable (f t)) :
    Adapted (naturalFiltration X) (fun t ω => f t (history X t ω)) :=
  fun t => measurable_history_function t (f t) (hf t)

omit [∀ t, MeasurableSpace (X t)] in
/-- [A statistic formed from the finite history depends only on coordinates
through that time](goal). -/
theorem dependsOn_history_function {Y : Type*} (t : ℕ) (f : History X t → Y) :
    DependsOn (fun ω => f (history X t ω)) (Set.Iic t) := by
  intro ω ω' h
  apply congrArg f
  funext (i : Finset.Iic t)
  exact h i (Finset.mem_Iic.mp i.property)

/-- [Measurable coordinate statistics](hyp:hf) have [a measurable finite running sum](goal). -/
theorem measurable_running_sum (f : (i : ℕ) → X i → ℝ) (hf : ∀ i, Measurable (f i))
    (t : ℕ) : Measurable[naturalFiltration X t]
      (fun ω => ∑ i : Finset.Iic t, f i (coordinate X i ω)) := by
  exact measurable_history_function t
    (fun h => ∑ i : Finset.Iic t, f i (h i))
    (Finset.measurable_sum _ (fun i _ => (hf i).comp (measurable_pi_apply i)))

/-- [Measurable coordinate statistics](hyp:hf) have [a measurable running average](goal). -/
theorem measurable_running_average (f : (i : ℕ) → X i → ℝ) (hf : ∀ i, Measurable (f i))
    (t : ℕ) : Measurable[naturalFiltration X t]
      (fun ω => (∑ i : Finset.Iic t, f i (coordinate X i ω)) / (t + 1 : ℝ)) := by
  exact (measurable_running_sum f hf t).div_const _

/-- [Measurable coordinate statistics](hyp:hf) have [a measurable best-so-far maximum](goal). -/
theorem measurable_running_max (f : (i : ℕ) → X i → ℝ) (hf : ∀ i, Measurable (f i))
    (t : ℕ) : Measurable[naturalFiltration X t]
      (fun ω => (Finset.univ : Finset (Finset.Iic t)).sup'
        ⟨⟨t, Finset.mem_Iic.mpr le_rfl⟩, Finset.mem_univ _⟩
        (fun i => f i (coordinate X i ω))) := by
  classical
  apply measurable_history_function t
    (fun h => (Finset.univ : Finset (Finset.Iic t)).sup'
      ⟨⟨t, Finset.mem_Iic.mpr le_rfl⟩, Finset.mem_univ _⟩ (fun i => f i (h i)))
  convert
    (Finset.measurable_sup'
      (s := (Finset.univ : Finset (Finset.Iic t)))
      (f := fun i (h : History X t) => f i (h i))
      ⟨⟨t, Finset.mem_Iic.mpr le_rfl⟩, Finset.mem_univ _⟩
      (fun i _ => (hf i).comp (measurable_pi_apply i))) using 1
  funext h
  symm
  apply Finset.sup'_apply

/-- [A measurable set of finite histories](hyp:hA) gives
[an event measurable at the observation time](goal). -/
theorem measurableSet_history_event (t : ℕ) (A : Set (History X t))
    (hA : MeasurableSet A) :
    MeasurableSet[naturalFiltration X t] {ω | history X t ω ∈ A} :=
  (measurable_history X t) hA

/-- [A measurable history event](hyp:hA) has [a measurable real indicator at that time](goal). -/
theorem measurable_history_indicator (t : ℕ) (A : Set (History X t))
    (hA : MeasurableSet A) : Measurable[naturalFiltration X t]
      ({ω | history X t ω ∈ A}.indicator (fun _ => (1 : ℝ))) := by
  exact measurable_const.indicator (measurableSet_history_event t A hA)

end Toolkit.Foundations.Probability.Processes
