module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Nat
public import Mathlib.Order.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import StatLean.Bayesian.Sufficiency.Factorization
public import Toolkit.Foundations.Probability.Distributions.DescendingOrderStatistics

/-!
# Geometry of the normalized spacing transformation

The consecutive-difference transformation is upper triangular with diagonal
1, ..., n. Its determinant is n!, its Jacobian rescales Lebesgue measure by
1/n!, and it sends the nonnegative descending cone to the nonnegative orthant.
A weighted telescoping identity controls the exponential density after transport.

The module provides the determinant (`normalizedSpacingLinear_det`), the image of
Lebesgue measure (`map_normalizedSpacingMap_volume`), the cone correspondence
(`normalizedSpacingMap_nonneg_iff`), the sum identity (`sum_normalizedSpacingMap`),
and the change of variables for densities
(`map_normalizedSpacingMap_withDensity_pullback`).
-/

public section

namespace Toolkit.Foundations.Probability.Distributions

open MeasureTheory

/-- For [a sample size](hyp:n), [the determinant of the normalized spacing linear map is the
sample-size factorial](goal). -/
theorem normalizedSpacingLinear_det (n : ℕ) :
    LinearMap.det (normalizedSpacingLinear n) = (n.factorial : ℝ) := by
  -- Use LinearMap.toMatrix' and the upper-triangular determinant formula.
  -- The diagonal product ∏ j : Fin n, (j.val + 1) is n!; this includes n = 0.
  classical
  rw [← LinearMap.det_toMatrix']
  have htri : (LinearMap.toMatrix' (normalizedSpacingLinear n)).IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    rw [LinearMap.toMatrix'_apply]
    change normalizedSpacingMap (Pi.single j 1) i = 0
    rw [normalizedSpacingMap_apply]
    have hij : i ≠ j := ne_of_gt hji
    by_cases h : i.val + 1 < n
    · have hnext : (⟨i.val + 1, h⟩ : Fin n) ≠ j := by
        intro he
        have heval := congrArg Fin.val he
        change i.val + 1 = j.val at heval
        have hlt : j.val < i.val := hji
        omega
      simp [h, hij, hnext]
    · simp [h, hij]
  rw [Matrix.det_of_isUpperTriangular htri]
  have hd : ∀ i : Fin n, LinearMap.toMatrix' (normalizedSpacingLinear n) i i =
      ((i.val + 1 : ℕ) : ℝ) := by
    intro i
    rw [LinearMap.toMatrix'_apply]
    change normalizedSpacingMap (Pi.single i 1) i = _
    rw [normalizedSpacingMap_apply]
    by_cases h : i.val + 1 < n
    · have hnext : (⟨i.val + 1, h⟩ : Fin n) ≠ i := by
        intro he
        have heval := congrArg Fin.val he
        change i.val + 1 = i.val at heval
        omega
      simp [h, hnext]
    · simp [h]
  simp_rw [hd]
  rw [← Nat.cast_prod]
  exact congrArg (fun k : ℕ => (k : ℝ))
    ((Fin.prod_univ_eq_prod_range (fun k : ℕ => k + 1) n).trans
      (Finset.prod_range_add_one_eq_factorial n))

/-- For [a sample size](hyp:n), [the normalized spacing map sends Lebesgue measure to its
reciprocal-factorial multiple](goal). -/
theorem map_normalizedSpacingMap_volume (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).map normalizedSpacingMap =
      ENNReal.ofReal ((n.factorial : ℝ)⁻¹) • volume := by
  have hdet : LinearMap.det (normalizedSpacingLinear n) ≠ 0 := by
    rw [normalizedSpacingLinear_det]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  change (volume : Measure (Fin n → ℝ)).map (normalizedSpacingLinear n) = _
  simpa [normalizedSpacingLinear_det, abs_of_pos
    (inv_pos.mpr (show (0 : ℝ) < n.factorial by positivity))] using
    (Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet)

/-- For [a real coordinate vector](hyp:y), [all normalized spacings are nonnegative exactly when
the original coordinates are nonnegative and nonincreasing](goal). -/
theorem normalizedSpacingMap_nonneg_iff {n : ℕ} (y : Fin n → ℝ) :
    (∀ j, 0 ≤ normalizedSpacingMap y j) ↔ (∀ j, 0 ≤ y j) ∧ Antitone y := by
  -- Divide by each positive rank; backward induction from the final coordinate
  -- gives nonnegativity. Adjacent inequalities give antitonicity on Fin n.
  classical
  cases n with
  | zero => simp [Antitone]
  | succ n =>
    constructor
    · intro h
      have hgap (j : Fin (n + 1)) :
          0 ≤ y j - if h : j.val + 1 < n + 1 then y ⟨j.val + 1, h⟩ else 0 := by
        have hp : (0 : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by positivity
        exact (mul_nonneg_iff_of_pos_left hp).mp (by simpa [normalizedSpacingMap_apply] using h j)
      have ha : Antitone y := Fin.antitone_iff_succ_le.mpr fun i => by
        have hg := hgap i.castSucc
        have hi : i.val + 1 < n + 1 := by omega
        have he : (⟨i.val + 1, hi⟩ : Fin (n + 1)) = i.succ := by
          apply Fin.ext
          rfl
        simpa only [Fin.val_castSucc, dif_pos hi, he] using (sub_nonneg.mp hg)
      refine ⟨fun j => ?_, ha⟩
      have hl : 0 ≤ y (Fin.last n) := by simpa using hgap (Fin.last n)
      exact hl.trans (ha (Fin.le_last j))
    · rintro ⟨hn, ha⟩ j
      rw [normalizedSpacingMap_apply]
      apply mul_nonneg (by positivity)
      split_ifs with h
      · exact sub_nonneg.mpr (ha (by simp only [Fin.le_def]; omega))
      · simpa using hn j

/-- For [a real coordinate vector](hyp:y), [the sum of its normalized spacings equals the sum of
its coordinates](goal). -/
theorem sum_normalizedSpacingMap {n : ℕ} (y : Fin n → ℝ) :
    ∑ j, normalizedSpacingMap y j = ∑ j, y j := by
  -- Expand the differences and shift the successor-index sum; coefficients
  -- telescope, including the zero terminal coordinate. Alternatively induct on n.
  classical
  let x : ℕ → ℝ := fun k => if h : k < n then y ⟨k, h⟩ else 0
  have hx (j : Fin n) : x j.val = y j := by simp [x, j.isLt]
  have hnext (j : Fin n) :
      (if h : j.val + 1 < n then y ⟨j.val + 1, h⟩ else 0) = x (j.val + 1) := rfl
  simp_rw [normalizedSpacingMap_apply, hnext, ← hx]
  change (∑ j : Fin n, (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
    (x k - x (k + 1))) j.val) = ∑ j : Fin n, x j.val
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      (x k - x (k + 1))) n, Fin.sum_univ_eq_sum_range x n]
  have halg (k : ℕ) : ((k + 1 : ℕ) : ℝ) * (x k - x (k + 1)) =
      x k - (((k + 1 : ℕ) : ℝ) * x (k + 1) - (k : ℝ) * x k) := by
    push_cast
    ring
  simp_rw [halg]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => (k : ℝ) * x k) n]
  simp [x]

/-- For [an extended-real density on finite real vectors](hyp:f) that
[is measurable](hyp:hf), [transporting its pullback through the normalized spacing map,
multiplied by the factorial Jacobian, recovers the original Lebesgue-density measure](goal). -/
theorem map_normalizedSpacingMap_withDensity_pullback {n : ℕ}
    (f : (Fin n → ℝ) → ENNReal) (hf : Measurable f) :
    (volume.withDensity (fun y => (n.factorial : ENNReal) * f (normalizedSpacingMap y))).map
        normalizedSpacingMap = volume.withDensity f := by
  -- Prove transport of a pulled-back density by testing measurable sets and
  -- using lintegral_map; apply map_normalizedSpacingMap_volume and cancel n!.
  -- This helper has no exponential or integrability assumptions.
  have hm := measurable_normalizedSpacingMap (n := n)
  rw [StatLean.Bayesian.map_withDensity_comp hm
      (f := fun z => (n.factorial : ENNReal) * f z) (measurable_const.mul hf),
    map_normalizedSpacingMap_volume, withDensity_smul_measure]
  have hc : (n.factorial : ENNReal) * ENNReal.ofReal ((n.factorial : ℝ)⁻¹) = 1 := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
    exact ENNReal.mul_inv_cancel (by simp [Nat.factorial_ne_zero]) (by simp)
  change ENNReal.ofReal ((n.factorial : ℝ)⁻¹) •
    volume.withDensity ((n.factorial : ENNReal) • f) = _
  rw [withDensity_smul (n.factorial : ENNReal) hf, smul_smul, mul_comm, hc, one_smul]

end Toolkit.Foundations.Probability.Distributions
