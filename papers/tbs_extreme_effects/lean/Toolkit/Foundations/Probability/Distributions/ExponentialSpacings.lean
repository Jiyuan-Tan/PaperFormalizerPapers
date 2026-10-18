module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.Basic
public import Toolkit.Foundations.Probability.Distributions.DescendingOrderStatistics
public import Toolkit.Foundations.Probability.Distributions.DescendingSortMeasure
public import Toolkit.Foundations.Probability.Distributions.ExponentialOrderedDensity

/-!
# Rényi's representation of exponential order statistics

For independent measurable real random variables with common exponential rate r > 0,
sort descending, put zero after the smallest observation, and multiply each consecutive
gap by its one-based rank. These spacings are again independent exponential variables
of rate r. The theorem includes the empty sample and arbitrary probability spaces.

The module provides the normalized ordered spacings of a family of random variables
(`normalizedSpacing`), their measurability, and Rényi's representation
(`iIndepFun_normalizedSpacing_and_map_eq_expMeasure`). A different choice of descending
sorting permutation gives the same values by `Tuple.unique_antitone`.

References: A. Rényi (1953), *On the theory of order statistics*, Section 1;
Arnold, Balakrishnan & Nagaraja, *A First Course in Order Statistics*, Theorem 4.6.1.
-/

@[expose] public section

namespace Toolkit.Foundations.Probability.Distributions

open MeasureTheory ProbabilityTheory

noncomputable section

/-- For [a finite family of real random variables](hyp:V), [the normalized ordered spacings](goal)
are computed separately at each sample point by sorting the observations in descending order and
applying the normalized spacing map. -/
def normalizedSpacing {Ω : Type*} {n : ℕ} (V : Fin n → Ω → ℝ) : Fin n → Ω → ℝ :=
  fun j ω => normalizedSpacingMap (sortDescending (fun i => V i ω)) j

/-- If [every member of a finite family of real random variables is measurable](hyp:hV), [each of
its normalized descending spacings is measurable](goal). -/
theorem measurable_normalizedSpacing {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (V : Fin n → Ω → ℝ) (hV : ∀ j, Measurable (V j)) (j : Fin n) :
    Measurable (normalizedSpacing V j) := by
  exact (measurable_pi_apply j).comp
    (measurable_normalizedSpacingMap.comp
      (measurable_sortDescending.comp (measurable_pi_lambda _ hV)))

/-- **Rényi's representation.** Let the observations be [measurable real random
variables](hyp:hV) on a probability space, [mutually independent](hyp:h_indep), and [each
exponential with the same rate](hyp:h_law), where [the rate is positive](hyp:hr). After sorting
their values in decreasing order and placing zero after the smallest value, [the consecutive gaps
multiplied by their one-based ranks are mutually independent and each exponential with that same
rate](goal). -/
theorem iIndepFun_normalizedSpacing_and_map_eq_expMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {r : ℝ} (V : Fin n → Ω → ℝ) (hr : 0 < r)
    (hV : ∀ j, Measurable (V j)) (h_indep : iIndepFun V P)
    (h_law : ∀ j, P.map (V j) = expMeasure r) :
    iIndepFun (normalizedSpacing V) P ∧
      ∀ j, P.map (normalizedSpacing V j) = expMeasure r := by
  have hsample : P.map (fun ω j => V j ω) =
      Measure.pi (fun _ : Fin n => expMeasure r) := by
    rw [h_indep.map_fun_eq_pi_map (fun j => (hV j).aemeasurable)]
    congr 1
    funext j
    exact h_law j
  have hmeas : Measurable (fun ω j => normalizedSpacing V j ω) :=
    measurable_pi_lambda _ (measurable_normalizedSpacing V hV)
  have hjoint : P.map (fun ω j => normalizedSpacing V j ω) =
      Measure.pi (fun _ : Fin n => expMeasure r) := by
    change P.map ((normalizedSpacingMap ∘ sortDescending) ∘
      (fun ω j => V j ω)) = _
    rw [← Measure.map_map (measurable_normalizedSpacingMap.comp measurable_sortDescending)
      (measurable_pi_lambda _ hV), hsample]
    exact map_normalizedSpacing_sortDescending_pi_expMeasure n hr
  let : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hmarginal : ∀ j, P.map (normalizedSpacing V j) = expMeasure r := by
    intro j
    calc
      P.map (normalizedSpacing V j) =
          (P.map (fun ω k => normalizedSpacing V k ω)).map (fun x => x j) := by
        rw [Measure.map_map (measurable_pi_apply j) hmeas]
        rfl
      _ = (Measure.pi (fun _ : Fin n => expMeasure r)).map (fun x => x j) := by
        rw [hjoint]
      _ = expMeasure r := (measurePreserving_eval (fun _ : Fin n => expMeasure r) j).map_eq
  refine ⟨(iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_normalizedSpacing V hV j).aemeasurable)).2 ?_, hmarginal⟩
  simpa only [hmarginal] using hjoint

end
end Toolkit.Foundations.Probability.Distributions
