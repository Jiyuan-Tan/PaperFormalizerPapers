module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Lipschitz estimates for simplex normalization

Dividing each coordinate by the total mass controls the resulting change in
the sum of absolute coordinate differences. Only the second vector needs
nonnegative coordinates; both total masses must be positive. In particular,
the estimate applies to the normalization of nonnegative weight vectors
(propensities, softmax numerators, importance weights) to probability vectors.

The finite-set formulation also covers an entire finite index type by taking
the indexing set to be `Finset.univ`.

## Main results

* `sum_abs_div_sum_sub_div_sum_le`: the ℓ¹ distance between the normalized
  vectors is at most `2 / P` times the ℓ¹ distance between the original ones,
  where `P` is the total mass of the first vector.
-/

public section

namespace Toolkit.Foundations.Analysis.Normed

/-- For two real vectors p and q on a finite set, if [q has nonnegative
coordinates on that set](hyp:hq), [p has positive total mass P](hyp:hP), and
[q has positive total mass Q](hyp:hQ), then [the sum over the set of the absolute
differences between the normalized coordinates p(i)/P and q(i)/Q is at most 2/P
times the sum of the absolute differences between the original coordinates](goal).

This is a Lipschitz bound for the map sending a weight vector to the probability
vector proportional to it; no sign condition on p is needed.
-/
theorem sum_abs_div_sum_sub_div_sum_le {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i)
    (hP : 0 < ∑ i ∈ s, p i) (hQ : 0 < ∑ i ∈ s, q i) :
    (∑ i ∈ s, |p i / (∑ j ∈ s, p j) - q i / (∑ j ∈ s, q j)|) ≤
      (2 / (∑ i ∈ s, p i)) * ∑ i ∈ s, |p i - q i| := by
  /-
  Proof plan: abbreviate the masses by P and Q and the original absolute
  difference sum by D. First bound |P - Q| by D using
  `Finset.sum_sub_distrib` and `Finset.abs_sum_le_sum_abs`.
  For each i in s, use the identity
    p i / P - q i / Q = (p i - q i) / P + (q i / Q) * ((Q - P) / P).
  Both denominators are nonzero. The triangle inequality, positivity of P,
  and nonnegativity of q i / Q bound the absolute value by
    |p i - q i| / P + (q i / Q) * (|P - Q| / P).
  Sum this estimate. `Finset.sum_div` and `Finset.sum_mul` give the bound
  D / P + |P - Q| / P since the normalized q coordinates sum to one.
  Monotonicity of division by P finishes with 2 * D / P.
  No nonnegativity of p, finiteness instance on the ambient type, or
  nonemptiness hypothesis is needed.
  -/
  let P := ∑ i ∈ s, p i
  let Q := ∑ i ∈ s, q i
  let D := ∑ i ∈ s, |p i - q i|
  have hP0 : P ≠ 0 := ne_of_gt hP
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  have hmass : |P - Q| ≤ D := by
    simpa only [P, Q, D, Finset.sum_sub_distrib] using
      Finset.abs_sum_le_sum_abs (fun i => p i - q i) s
  have hcoord (i : ι) (hi : i ∈ s) :
      |p i / P - q i / Q| ≤
        |p i - q i| / P + (q i / Q) * (|P - Q| / P) := by
    have hsplit : p i / P - q i / Q =
        (p i - q i) / P + (q i / Q) * ((Q - P) / P) := by
      field_simp
      ring
    rw [hsplit]
    calc
      |(p i - q i) / P + (q i / Q) * ((Q - P) / P)| ≤
          |(p i - q i) / P| + |(q i / Q) * ((Q - P) / P)| :=
        abs_add_le _ _
      _ = |p i - q i| / P + (q i / Q) * (|P - Q| / P) := by
        rw [abs_div, abs_of_pos hP, abs_mul,
          abs_of_nonneg (div_nonneg (hq i hi) (le_of_lt hQ)),
          abs_div, abs_of_pos hP, abs_sub_comm Q P]
  have hnormalized : ∑ i ∈ s, q i / Q = 1 := by
    rw [← Finset.sum_div]
    exact div_self hQ0
  calc
    (∑ i ∈ s, |p i / P - q i / Q|) ≤
        ∑ i ∈ s, (|p i - q i| / P + (q i / Q) * (|P - Q| / P)) :=
      Finset.sum_le_sum hcoord
    _ = D / P + |P - Q| / P := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
        hnormalized, one_mul]
    _ ≤ D / P + D / P :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hmass (le_of_lt hP))
    _ = (2 / P) * D := by ring

end Toolkit.Foundations.Analysis.Normed
