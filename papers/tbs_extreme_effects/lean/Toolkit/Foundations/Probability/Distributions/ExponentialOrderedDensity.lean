module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Logic.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs
public import StatLean.Bayesian.ForMathlib.PiWithDensity
public import Toolkit.Foundations.Probability.Distributions.DescendingOrderStatistics
public import Toolkit.Foundations.Probability.Distributions.DescendingSortMeasure
public import Toolkit.Foundations.Probability.Distributions.NormalizedSpacingMap

/-!
# Joint density of exponential order statistics

The iid exponential density is symmetric. Sorting restricts it to the descending
chamber and multiplies it by n!. The spacing Jacobian cancels that factorial;
nonnegativity and telescoping then recover the original product density.

The module provides the joint density of an exponential sample
(`pi_expMeasure_eq_withDensity`), the joint density of its descending order statistics
(`map_sortDescending_pi_expMeasure`), and the law of their normalized spacings
(`map_normalizedSpacing_sortDescending_pi_expMeasure`).

Reference: A. Rényi (1953), *On the theory of order statistics*, Section 1,
pp. 192–194, equations (1.6)–(1.9), DOI 10.1007/BF02127580.
The original uses ascending ranks; reversing them yields the descending convention.
-/

@[expose] public section

namespace Toolkit.Foundations.Probability.Distributions

open MeasureTheory ProbabilityTheory

noncomputable section

/-- For [an exponential rate](hyp:r) and [a finite real vector](hyp:x), [the exponential product
density](goal) is the product of the coordinate exponential densities. -/
def exponentialProductDensity {n : ℕ} (r : ℝ) (x : Fin n → ℝ) : ENNReal :=
  ∏ j, exponentialPDF r (x j)

/-- For [an exponential rate](hyp:r) and [a finite real vector](hyp:x), [the ordered exponential
density](goal) is [the factorial times the exponential product density on the descending
chamber](step:1), and [zero outside that chamber](step:2). -/
def orderedExponentialDensity {n : ℕ} (r : ℝ) (x : Fin n → ℝ) : ENNReal :=
  if Antitone x then (n.factorial : ENNReal) * exponentialProductDensity r x else 0

/-- For [a positive exponential rate](hyp:hr) and [a sample size](hyp:n), [the product exponential
law has the exponential product density with respect to Lebesgue measure](goal). -/
theorem pi_expMeasure_eq_withDensity (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Measure.pi (fun _ : Fin n => expMeasure r) =
      volume.withDensity (exponentialProductDensity r) := by
  have hlaw : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  let : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  let : IsProbabilityMeasure (volume.withDensity (exponentialPDF r)) := by
    rw [← hlaw]
    infer_instance
  simp_rw [hlaw]
  exact StatLean.Bayesian.pi_withDensity volume
    (fun _ => (measurable_exponentialPDFReal r).ennreal_ofReal)

/-- For [an exponential rate](hyp:r), [the exponential product density is measurable](goal). -/
theorem measurable_exponentialProductDensity {n : ℕ} (r : ℝ) :
    Measurable (exponentialProductDensity (n := n) r) := by
  change Measurable (fun x : Fin n → ℝ =>
    ∏ j, ENNReal.ofReal (exponentialPDFReal r (x j)))
  exact Finset.measurable_prod _ fun j _ =>
    ((measurable_exponentialPDFReal r).comp (measurable_pi_apply j)).ennreal_ofReal

/-- For [an exponential rate](hyp:r), [a real sample](hyp:x), and [a coordinate
permutation](hyp:σ), [the exponential product density is unchanged by permuting the sample](goal).
-/
theorem exponentialProductDensity_comp_perm {n : ℕ} (r : ℝ) (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    exponentialProductDensity r (x ∘ σ) = exponentialProductDensity r x := by
  exact Equiv.prod_comp σ (fun j => exponentialPDF r (x j))

/-- For [a positive exponential rate](hyp:hr) and [a sample size](hyp:n), [descending sorting of
the product exponential law has the ordered exponential density](goal). -/
theorem map_sortDescending_pi_expMeasure (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (Measure.pi (fun _ : Fin n => expMeasure r)).map sortDescending =
      volume.withDensity (orderedExponentialDensity r) := by
  rw [pi_expMeasure_eq_withDensity n hr,
    map_sortDescending_withDensity _ (measurable_exponentialProductDensity r)
      (fun σ x => exponentialProductDensity_comp_perm r x σ),
    ← withDensity_smul _ (measurable_exponentialProductDensity r),
    ← withDensity_indicator isClosed_antitone.measurableSet]
  congr 1
  funext x
  simp [orderedExponentialDensity, Set.indicator, smul_eq_mul]

/-- For [a positive exponential rate](hyp:hr) and [a real coordinate vector](hyp:y), [the ordered
exponential density equals the factorial times the product exponential density evaluated at its
normalized spacings](goal). -/
theorem orderedExponentialDensity_eq_spacing_pullback {n : ℕ} {r : ℝ}
    (hr : 0 < r) (y : Fin n → ℝ) :
    orderedExponentialDensity r y =
      (n.factorial : ENNReal) * exponentialProductDensity r (normalizedSpacingMap y) := by
  classical
  have hprod (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) :
      exponentialProductDensity r x =
        ENNReal.ofReal (r ^ n * Real.exp (-(r * ∑ j, x j))) := by
    unfold exponentialProductDensity
    simp_rw [exponentialPDF_of_nonneg (hx _)]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ =>
      mul_nonneg hr.le (Real.exp_pos _).le), Finset.prod_mul_distrib, ← Real.exp_sum]
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    simp
  by_cases hs : (∀ j, 0 ≤ y j) ∧ Antitone y
  · have hspacing := (normalizedSpacingMap_nonneg_iff y).2 hs
    rw [orderedExponentialDensity, if_pos hs.2, hprod y hs.1,
      hprod (normalizedSpacingMap y) hspacing, sum_normalizedSpacingMap]
  · have hspacing : ¬ ∀ j, 0 ≤ normalizedSpacingMap y j := by
      simpa only [normalizedSpacingMap_nonneg_iff] using hs
    obtain ⟨j, hj⟩ := not_forall.mp hspacing
    have hz : exponentialProductDensity r (normalizedSpacingMap y) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j)
        (exponentialPDF_of_neg (lt_of_not_ge hj))
    rw [hz, mul_zero]
    by_cases ha : Antitone y
    · have hn : ¬ ∀ j, 0 ≤ y j := fun h => hs ⟨h, ha⟩
      obtain ⟨i, hi⟩ := not_forall.mp hn
      have hy : exponentialProductDensity r y = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i)
          (exponentialPDF_of_neg (lt_of_not_ge hi))
      rw [orderedExponentialDensity, if_pos ha, hy, mul_zero]
    · rw [orderedExponentialDensity, if_neg ha]

/-- For [a positive exponential rate](hyp:hr) and [a sample size](hyp:n), [normalized spacings of
a descending-sorted product exponential sample again have the same product exponential law](goal).
-/
theorem map_normalizedSpacing_sortDescending_pi_expMeasure (n : ℕ) {r : ℝ}
    (hr : 0 < r) :
    (Measure.pi (fun _ : Fin n => expMeasure r)).map
        (fun x => normalizedSpacingMap (sortDescending x)) =
      Measure.pi (fun _ : Fin n => expMeasure r) := by
  change (Measure.pi (fun _ : Fin n => expMeasure r)).map
    (normalizedSpacingMap ∘ sortDescending) = _
  rw [← Measure.map_map measurable_normalizedSpacingMap measurable_sortDescending,
    map_sortDescending_pi_expMeasure n hr]
  have hd : orderedExponentialDensity (n := n) r =
      (fun y => (n.factorial : ENNReal) *
        exponentialProductDensity r (normalizedSpacingMap y)) := by
    funext y
    exact orderedExponentialDensity_eq_spacing_pullback hr y
  rw [hd, map_normalizedSpacingMap_withDensity_pullback
    _ (measurable_exponentialProductDensity r), ← pi_expMeasure_eq_withDensity n hr]

end
end Toolkit.Foundations.Probability.Distributions
