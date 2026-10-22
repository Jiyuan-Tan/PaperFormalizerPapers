module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.MinMax
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
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
# Toolkit.Foundations.Probability.Conditioning.ConditionalIntegrability

Integrability criteria obtained through conditional expectations
-/

public section

namespace Toolkit.Foundations.Probability.Conditioning

section

open MeasureTheory
open scoped ENNReal Topology
variable {Z : Type*} [mZ : MeasurableSpace Z]

/-- If [the nonnegative variable `D` is integrable](hyp:hD,hD0), [the conditioning sigma-algebra is contained in the ambient one](hyp:hm), [the nonnegative multiplier is strongly measurable relative to it](hyp:hH,hH0), and [its product with the conditional expectation of `D` is integrable](hyp:hI), then [the product of `D` and the multiplier is integrable](goal). -/
-- @node: hill_integrable_mul_of_condExp_mul
lemma integrable_mul_of_integrable_condExp_mul (Q : Measure Z) [IsFiniteMeasure Q] {D H : Z → ℝ}
    (hD : Integrable D Q) (hD0 : ∀ z, 0 ≤ D z) {m : MeasurableSpace Z} (hm : m ≤ mZ)
    (hH : StronglyMeasurable[m] H) (hH0 : ∀ z, 0 ≤ H z)
    (hI : Integrable (fun z => Q[D | m] z * H z) Q) :
    Integrable (fun z => D z * H z) Q := by
  have hHm : StronglyMeasurable[mZ] H := hH.mono hm
  let Hn : ℕ → Z → ℝ := fun n z => min (H z) n
  have hHn : ∀ n, StronglyMeasurable[m] (Hn n) := fun n =>
    (hH.measurable.min measurable_const).stronglyMeasurable
  have hbound : ∀ n, (∫ z, D z * Hn n z ∂Q) ≤ ∫ z, Q[D | m] z * H z ∂Q := by
    intro n
    have hpull := condExp_stronglyMeasurable_mul_of_bound hm (hHn n) hD (n : ℝ)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hH0 z) (Nat.cast_nonneg n))]
        exact min_le_right _ _)
    have h : (∫ z, Hn n z * D z ∂Q) = ∫ z, Hn n z * Q[D | m] z ∂Q :=
      (integral_condExp hm).symm.trans (integral_congr_ae hpull)
    calc (∫ z, D z * Hn n z ∂Q) = ∫ z, Hn n z * D z ∂Q := by
          congr 1; funext z; ring
      _ = ∫ z, Hn n z * Q[D | m] z ∂Q := h
      _ ≤ ∫ z, Q[D | m] z * H z ∂Q := by
          apply integral_mono_ae
          · exact integrable_condExp.bdd_mul (c := n) ((hHn n).mono hm).aestronglyMeasurable
              (ae_of_all _ fun z => by
                rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hH0 z) (Nat.cast_nonneg n))]
                exact min_le_right _ _)
          · exact hI
          · filter_upwards [condExp_nonneg (m := m) (ae_of_all _ hD0)] with z hz
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left (min_le_left _ _) hz
  refine ⟨(hD.aestronglyMeasurable.mul hHm.aestronglyMeasurable), ?_⟩
  rw [HasFiniteIntegral]
  have hmono : Monotone fun n => fun z => ENNReal.ofReal (D z * Hn n z) := by
    intro i j hij z
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (min_le_min_left _ (by exact_mod_cast hij)) (hD0 z)
  have hsup : ∀ z, ⨆ n, ENNReal.ofReal (D z * Hn n z) = ‖D z * H z‖ₑ := by
    intro z
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg (hD0 z) (hH0 z))]
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (hD0 z))
    · obtain ⟨n, hn⟩ := exists_nat_ge (H z)
      exact le_iSup_of_le n (by simp [Hn, min_eq_left hn])
  have hmeas : ∀ n, AEMeasurable (fun z => ENNReal.ofReal (D z * Hn n z)) Q := fun n =>
    (hD.aemeasurable.mul ((hHn n).mono hm).measurable.aemeasurable).ennreal_ofReal
  have hint : ∀ n, Integrable (fun z => D z * Hn n z) Q := fun n =>
    hD.mul_bdd ((hHn n).mono hm).aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hH0 z) (Nat.cast_nonneg n))]
      exact min_le_right _ _)
  calc ∫⁻ z, ‖D z * H z‖ₑ ∂Q = ∫⁻ z, ⨆ n, ENNReal.ofReal (D z * Hn n z) ∂Q := by
        congr 1; funext z; exact (hsup z).symm
    _ = ⨆ n, ∫⁻ z, ENNReal.ofReal (D z * Hn n z) ∂Q :=
        lintegral_iSup' hmeas (ae_of_all _ fun z i j hij => hmono hij z)
    _ ≤ ENNReal.ofReal (∫ z, Q[D | m] z * H z ∂Q) := by
        refine iSup_le fun n => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
          (ae_of_all _ fun z => mul_nonneg (hD0 z) (le_min (hH0 z) (Nat.cast_nonneg n)))]
        exact ENNReal.ofReal_le_ofReal (hbound n)
    _ < ⊤ := ENNReal.ofReal_lt_top

end

end Toolkit.Foundations.Probability.Conditioning
