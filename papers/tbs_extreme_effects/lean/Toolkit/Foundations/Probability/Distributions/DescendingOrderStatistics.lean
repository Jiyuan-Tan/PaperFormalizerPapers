module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

/-!
# Descending order statistics and normalized spacings

Finite real samples are sorted in decreasing order. Coordinate `j : Fin n` denotes
rank `j.val + 1`; the value following the last rank is zero. Thus the normalized
spacing is `(j.val + 1)` times the difference of consecutive descending values.
These definitions allow empty samples and do not impose nonnegativity on inputs.

The module provides the descending sort `sortDescending`, the normalized spacing
transformation as a linear map (`normalizedSpacingLinear`) and as a function
(`normalizedSpacingMap`), and their elementary order and measurability facts.
-/

@[expose] public section

namespace Toolkit.Foundations.Probability.Distributions

open MeasureTheory

noncomputable section

/-- For [a finite real sample](hyp:x), [its descending order statistics](goal) are the sample
values rearranged from largest to smallest.

They are obtained by reversing the increasing tuple sort. -/
def sortDescending {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  (x ∘ Tuple.sort x) ∘ Fin.revPerm

/-- For [a sample size](hyp:n), [the normalized spacing linear map](goal) multiplies each
consecutive descending-coordinate difference by its one-based rank, using zero after the last
coordinate. -/
def normalizedSpacingLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun j : Fin n =>
    ((j.val + 1 : ℕ) : ℝ) •
      ((LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ) -
        if h : j.val + 1 < n then LinearMap.proj ⟨j.val + 1, h⟩ else 0)

/-- For [a real coordinate vector](hyp:y), [its normalized spacing vector](goal) consists of each
one-based rank times the gap to the next coordinate, with zero following the last coordinate. -/
def normalizedSpacingMap {n : ℕ} (y : Fin n → ℝ) : Fin n → ℝ :=
  normalizedSpacingLinear n y

/-- For [a real coordinate vector](hyp:y) and [a zero-based rank](hyp:j), [the normalized spacing
is the one-based rank times the next-coordinate difference, or times the final coordinate at the
last rank](goal). -/
theorem normalizedSpacingMap_apply {n : ℕ} (y : Fin n → ℝ) (j : Fin n) :
    normalizedSpacingMap y j = ((j.val + 1 : ℕ) : ℝ) *
      (y j - if h : j.val + 1 < n then y ⟨j.val + 1, h⟩ else 0) := by
  classical
  by_cases h : j.val + 1 < n <;>
    simp [normalizedSpacingMap, normalizedSpacingLinear, h]

/-- [The normalized spacing map is measurable](goal) for any finite sample size. -/
theorem measurable_normalizedSpacingMap {n : ℕ} :
    Measurable (normalizedSpacingMap (n := n)) :=
  (normalizedSpacingLinear n).continuous_of_finiteDimensional.measurable

/-- For [a finite real sample](hyp:x), [its descending order statistics are nonincreasing](goal).
-/
theorem antitone_sortDescending {n : ℕ} (x : Fin n → ℝ) :
    Antitone (sortDescending x) := by
  intro i j hij
  exact Tuple.monotone_sort x (Fin.rev_le_rev.mpr hij)

/-- For [a finite real sample](hyp:x) and [a permutation of its coordinates](hyp:σ), [permuting
before sorting leaves the descending order statistics unchanged](goal). -/
theorem sortDescending_comp_perm {n : ℕ} (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : sortDescending (x ∘ σ) = sortDescending x := by
  unfold sortDescending
  rw [Tuple.comp_perm_comp_sort_eq_comp_sort]

/-- If [a real sample](hyp:x) rearranged by [a permutation of its coordinates](hyp:σ)
[is nonincreasing](hyp:h), then [its descending order statistics are exactly that rearranged
sample](goal). -/
theorem sortDescending_eq_comp_of_antitone {n : ℕ} (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (h : Antitone (x ∘ σ)) :
    sortDescending x = x ∘ σ := by
  change x ∘ (Fin.revPerm.trans (Tuple.sort x)) = x ∘ σ
  exact Tuple.unique_antitone (antitone_sortDescending x) h

end
end Toolkit.Foundations.Probability.Distributions
