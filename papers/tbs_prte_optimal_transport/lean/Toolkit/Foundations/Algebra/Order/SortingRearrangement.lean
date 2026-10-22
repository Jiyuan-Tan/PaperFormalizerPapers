module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Rearrangement inequalities for sorting finite lists of reals

Sorting a finite real list in nondecreasing order weakly reduces its sum of
absolute deviations from any equally long nondecreasing reference list.

The argument is split from the choice of cost: any real-valued cost satisfying
the two-point Monge (exchange) inequality decreases when the first list is
insertion sorted or merge sorted against a nondecreasing reference, with no sign
restriction on the cost and no initial ordering of the first list. Absolute
deviation satisfies the exchange inequality, which gives the ℓ¹ rearrangement
result `sum_zipWith_abs_sub_mergeSort_le`.

This is the finite-list case of Chernozhukov, Fernández-Val and Galichon (2009),
*Improving point and interval estimators of monotone functions by rearrangement*,
Biometrika 96, Proposition 1, with p = 1; see also Lorentz (1953).
-/

public section

namespace Toolkit.Foundations.Algebra.Order

/-- If [matching two ordered pairs in the same order never costs more than crossing
them](hyp:hcost), [the reference list is nondecreasing](hyp:hq), and [the reference
has one more entry than the input list](hyp:hlen), then [inserting one value by
successive ordered comparisons costs no more than placing it at the front](goal).

The input list need not already be sorted. -/
theorem sum_zipWith_orderedInsert_le_of_monge
    {α β : Type*} [LinearOrder α] [Preorder β] (c : α → β → ℝ)
    (hcost : ∀ a b u v, a ≤ b → u ≤ v →
      c a u + c b v ≤ c b u + c a v)
    (a : α) (l : List α) (q : List β)
    (hq : q.Pairwise (· ≤ ·)) (hlen : q.length = l.length + 1) :
    (List.zipWith c (l.orderedInsert (· ≤ ·) a) q).sum ≤
      (List.zipWith c (a :: l) q).sum := by
  induction l generalizing q with
  | nil => simp
  | cons b bs ih =>
    by_cases hab : a ≤ b
    · rw [List.orderedInsert_cons_of_le (· ≤ ·) bs hab]
    · cases q with
      | nil => simp at hlen
      | cons u q =>
        cases q with
        | nil => simp at hlen
        | cons v qs =>
          have htail : (v :: qs).length = bs.length + 1 := by
            simpa using hlen
          have huv : u ≤ v := (List.pairwise_cons.mp hq).1 v (by simp)
          have hi := ih (v :: qs) hq.of_cons htail
          rw [List.orderedInsert_cons, if_neg hab]
          simp only [List.zipWith_cons_cons, List.sum_cons] at hi ⊢
          calc
            c b u + (List.zipWith c (bs.orderedInsert (· ≤ ·) a) (v :: qs)).sum ≤
                c b u + (c a v + (List.zipWith c bs qs).sum) :=
              add_le_add (le_refl (c b u)) hi
            _ ≤ c a u + (c b v + (List.zipWith c bs qs).sum) := by
              simpa only [add_assoc] using
                add_le_add (hcost b a u v (le_of_not_ge hab) huv)
                  (le_refl (List.zipWith c bs qs).sum)

/-- If [matching ordered pairs costs no more than crossing them](hyp:hcost),
[the reference list is nondecreasing](hyp:hq), and [both lists have the same
length](hyp:hlen), then [insertion sorting the first list weakly reduces the
sum of the paired costs](goal). -/
theorem sum_zipWith_insertionSort_le_of_monge
    {α β : Type*} [LinearOrder α] [Preorder β] (c : α → β → ℝ)
    (hcost : ∀ a b u v, a ≤ b → u ≤ v →
      c a u + c b v ≤ c b u + c a v)
    (l : List α) (q : List β)
    (hq : q.Pairwise (· ≤ ·)) (hlen : q.length = l.length) :
    (List.zipWith c (l.insertionSort (· ≤ ·)) q).sum ≤
      (List.zipWith c l q).sum := by
  induction l generalizing q with
  | nil => simp
  | cons a l ih =>
    cases q with
    | nil => simp at hlen
    | cons b q =>
      have htail : q.length = l.length := by simpa using hlen
      rw [List.insertionSort_cons]
      calc
        (List.zipWith c ((l.insertionSort (· ≤ ·)).orderedInsert (· ≤ ·) a)
            (b :: q)).sum ≤
            (List.zipWith c (a :: l.insertionSort (· ≤ ·)) (b :: q)).sum :=
          sum_zipWith_orderedInsert_le_of_monge c hcost a _ _ hq (by
            simpa using hlen)
        _ ≤ (List.zipWith c (a :: l) (b :: q)).sum := by
          simpa only [List.zipWith_cons_cons, List.sum_cons] using
            add_le_add (le_refl (c a b)) (ih q hq.of_cons htail)

/-- If [matching ordered pairs costs no more than crossing them](hyp:hcost),
[the reference list is nondecreasing](hyp:hq), and [both lists have the same
length](hyp:hlen), then [merge sorting the first list weakly reduces the sum
of the paired costs](goal). -/
theorem sum_zipWith_mergeSort_le_of_monge
    {α β : Type*} [LinearOrder α] [Preorder β] (c : α → β → ℝ)
    (hcost : ∀ a b u v, a ≤ b → u ≤ v →
      c a u + c b v ≤ c b u + c a v)
    (l : List α) (q : List β)
    (hq : q.Pairwise (· ≤ ·)) (hlen : q.length = l.length) :
    (List.zipWith c (l.mergeSort fun a b => decide (a ≤ b)) q).sum ≤
      (List.zipWith c l q).sum := by
  simpa only [List.mergeSort_eq_insertionSort (r := (· ≤ ·))] using
    sum_zipWith_insertionSort_le_of_monge c hcost l q hq hlen

/-- For [two real values in increasing order](hyp:hab) and [two reference values
in increasing order](hyp:huv), [matching them in the same order has no greater
total absolute deviation than matching them in opposite orders](goal).

This is the Monge property of absolute deviation. -/
theorem abs_sub_add_abs_sub_le_of_le
    (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v) :
    |a - u| + |b - v| ≤ |b - u| + |a - v| := by
  rcases le_total 0 (a - u) with hau | hau <;>
    rcases le_total 0 (b - v) with hbv | hbv <;>
    rcases le_total 0 (b - u) with hbu | hbu <;>
    rcases le_total 0 (a - v) with hav | hav <;>
    simp_all only [abs_of_nonneg, abs_of_nonpos] <;> linarith

/-- Sorting reduces the ℓ¹ distance to a nondecreasing target: if [the reference
list is nondecreasing](hyp:hq) and [it has the same length as the input
list](hyp:hlen), then [the sum of absolute deviations after sorting the input
in nondecreasing order is no larger than before sorting](goal).

The finite-list case p = 1 of the rearrangement inequality of Chernozhukov,
Fernández-Val and Galichon (2009, Proposition 1); see also Lorentz (1953). -/
theorem sum_zipWith_abs_sub_mergeSort_le
    (l q : List ℝ) (hq : List.Pairwise (fun x1 x2 => x1 ≤ x2) q)
    (hlen : q.length = l.length) :
    (List.zipWith (fun x y => |x - y|)
      (l.mergeSort fun x1 x2 => decide (x1 ≤ x2)) q).sum ≤
      (List.zipWith (fun x y => |x - y|) l q).sum :=
  sum_zipWith_mergeSort_le_of_monge (fun x y : ℝ => |x - y|)
    abs_sub_add_abs_sub_le_of_le l q hq hlen

end Toolkit.Foundations.Algebra.Order
