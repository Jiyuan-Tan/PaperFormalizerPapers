module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousLearners
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Fin
public import Toolkit.Foundations.Algebra.Order.SortingRearrangement
/-! Sorting contracts the grid error toward a nondecreasing population quantile vector. -/
public section
namespace Papers.TbsPrteOptimalTransport
open Set
open scoped BigOperators
set_option linter.unusedSectionVars false

-- @node: abs_sorted_exchange
/-- If [b is no larger than a](hyp:hab) and [c is no larger than d](hyp:hcd),
[matching b to c and a to d has no greater total absolute error than the crossed matching](goal). -/
lemma abs_sorted_exchange (a b c d : ℝ) (hab : b ≤ a) (hcd : c ≤ d) :
    |b - c| + |a - d| ≤ |a - c| + |b - d| := by
  by_cases hac : a ≤ c
  · rw [abs_of_nonpos (by linarith : b - c ≤ 0),
      abs_of_nonpos (by linarith : a - d ≤ 0),
      abs_of_nonpos (by linarith : a - c ≤ 0),
      abs_of_nonpos (by linarith : b - d ≤ 0)]
    linarith
  by_cases hdb : d ≤ b
  · rw [abs_of_nonneg (by linarith : 0 ≤ b - c),
      abs_of_nonneg (by linarith : 0 ≤ a - d),
      abs_of_nonneg (by linarith : 0 ≤ a - c),
      abs_of_nonneg (by linarith : 0 ≤ b - d)]
    linarith
  rw [abs_of_nonneg (by linarith : 0 ≤ a - c),
    abs_of_nonpos (by linarith : b - d ≤ 0)]
  rcases le_total 0 (b - c) with hbc | hbc <;>
    rcases le_total 0 (a - d) with had | had <;>
    simp_all only [abs_of_nonneg, abs_of_nonpos] <;> linarith

-- @node: ordered_insert_quantile_error_le
/-- If [the reference list is nondecreasing](hyp:hq) and [has one more entry than the original list](hyp:hlen),
[inserting a value at its ordered position has no greater total absolute error against the reference list than prepending that value](goal). -/
lemma ordered_insert_quantile_error_le (a : ℝ) (l q : List ℝ)
    (hq : q.Pairwise (· ≤ ·)) (hlen : q.length = l.length + 1) :
    (List.zipWith (fun x y : ℝ => |x - y|) (l.orderedInsert (· ≤ ·) a) q).sum ≤
      (List.zipWith (fun x y : ℝ => |x - y|) (a :: l) q).sum := by
  induction l generalizing q with
  | nil => simp
  | cons b l ih =>
    by_cases hab : a ≤ b
    · rw [List.orderedInsert_cons, if_pos hab]
    rw [List.orderedInsert_cons, if_neg hab]
    cases q with
    | nil => simp at hlen
    | cons c q =>
      cases q with
      | nil => simp at hlen
      | cons d q =>
        have hcd : c ≤ d := (List.pairwise_cons.mp hq).1 d (by simp)
        have htail := ih (d :: q) hq.of_cons (by simpa using hlen)
        have hex := abs_sorted_exchange a b c d (le_of_not_ge hab) hcd
        simp only [List.zipWith_cons_cons, List.sum_cons] at *
        linarith

-- @node: insertion_sort_quantile_error_le
/-- If [the reference list is nondecreasing](hyp:hq) and [has the same length as the data list](hyp:hlen),
[sorting the data by insertion sort weakly reduces the sum of absolute deviations from the reference entries](goal). -/
lemma insertion_sort_quantile_error_le (l q : List ℝ)
    (hq : q.Pairwise (· ≤ ·)) (hlen : q.length = l.length) :
    (List.zipWith (fun x y : ℝ => |x - y|) (l.insertionSort (· ≤ ·)) q).sum ≤
      (List.zipWith (fun x y : ℝ => |x - y|) l q).sum := by
  induction l generalizing q with
  | nil => simp
  | cons a l ih =>
    rw [List.insertionSort_cons]
    have hinsert := ordered_insert_quantile_error_le a (l.insertionSort (· ≤ ·)) q hq
      (by simpa using hlen)
    apply hinsert.trans
    cases q with
    | nil => simp at hlen
    | cons c q =>
      simpa only [List.zipWith_cons_cons, List.sum_cons] using
        add_le_add_right (ih q hq.of_cons (by simpa using hlen)) |a - c|

-- @node: merge_sort_quantile_error_le
/-- If [the reference list is nondecreasing](hyp:hq) and [has the same length as the data list](hyp:hlen),
[sorting the data by merge sort weakly reduces the sum of absolute deviations from the reference entries](goal). -/
lemma merge_sort_quantile_error_le (l q : List ℝ)
    (hq : q.Pairwise (· ≤ ·)) (hlen : q.length = l.length) :
    (List.zipWith (fun x y : ℝ => |x - y|) (l.mergeSort (· ≤ ·)) q).sum ≤
      (List.zipWith (fun x y : ℝ => |x - y|) l q).sum := by
  exact Toolkit.Foundations.Algebra.Order.sum_zipWith_abs_sub_mergeSort_le l q hq hlen

-- @node: list_grid_error_sum
/-- [The sum of absolute deviations obtained by pairing a list with reference values at indices starting from zero equals the sum over all valid list indices, with any fallback value for out-of-range access](goal). -/
lemma list_grid_error_sum (l : List ℝ) (Q : ℕ → ℝ) (fallback : ℝ) :
    (List.zipWith (fun x y : ℝ => |x - y|) l ((List.range l.length).map Q)).sum =
      ∑ i : Fin l.length, |l.getD i fallback - Q i| := by
  induction l generalizing Q with
  | nil => simp
  | cons b l ih =>
    simpa [List.range_succ_eq_map, List.map_map, Function.comp_def,
      Fin.sum_univ_succ] using
      congrArg (fun t : ℝ => |b - Q 0| + t) (ih (fun i => Q (i + 1)))

-- @node: list_grid_error_sum_of_length
/-- If [the list has length N](hyp:hlen), [pairing it with the first N reference values and summing absolute deviations equals the sum over the N valid indices, regardless of the fallback value](goal). -/
lemma list_grid_error_sum_of_length (l : List ℝ) (Q : ℕ → ℝ) (fallback : ℝ)
    (N : ℕ) (hlen : l.length = N) :
    (List.zipWith (fun x y : ℝ => |x - y|) l ((List.range N).map Q)).sum =
      ∑ i : Fin N, |l.getD i fallback - Q i| := by
  subst N
  exact list_grid_error_sum l Q fallback

universe u v
variable {Ω : Type u} {X Z : Type v} {A : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: sorted_grid_quantile_error_le
/-- For [a positive grid size](hyp:hN) and [a reference quantile function nondecreasing between zero and one](hyp:hQ),
[sorting the clipped estimates weakly reduces their total absolute error against the reference quantiles at the interior grid levels](goal). -/
lemma sorted_grid_quantile_error_le (M : LatentIVModel Ω X Z)
    (raw : ℕ → A → ℕ → X → ℝ) (N : ℕ) (hN : 0 < N)
    (n : ℕ) (a : A) (x : X) (Q : ℝ → ℝ)
    (hQ : MonotoneOn Q (Ioo (0 : ℝ) 1)) :
    let q := (List.range (N - 1)).map (fun i => Q (gridLevel N hN (i + 1)))
    (List.zipWith (fun y z : ℝ => |y - z|) (sortedGrid M raw N n a x) q).sum ≤
      (List.zipWith (fun y z : ℝ => |y - z|)
        ((List.range (N - 1)).map (fun i => clippedGrid M raw n a (i + 1) x)) q).sum := by
  dsimp only
  apply merge_sort_quantile_error_le
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [List.length_map, List.length_range] at hi hj
    simp only [List.getElem_map, List.getElem_range]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hgrid (k : ℕ) (hk : k < N - 1) : gridLevel N hN (k + 1) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (by positivity) hNr
      · apply (div_lt_one hNr).mpr
        exact_mod_cast (show k + 1 < N by omega)
    apply hQ (hgrid i hi) (hgrid j hj)
    apply (div_le_div_iff_of_pos_right hNr).mpr
    exact_mod_cast (show i + 1 ≤ j + 1 by omega)
  · simp

-- @node: sorted_grid_quantile_error_sum_le
/-- For [a positive grid size](hyp:hN) and [a reference quantile function nondecreasing between zero and one](hyp:hQ),
[the sum of absolute errors of the sorted clipped estimates over the interior grid indices is bounded by the corresponding sum for the unsorted clipped estimates](goal). -/
lemma sorted_grid_quantile_error_sum_le (M : LatentIVModel Ω X Z)
    (raw : ℕ → A → ℕ → X → ℝ) (N : ℕ) (hN : 0 < N)
    (n : ℕ) (a : A) (x : X) (Q : ℝ → ℝ)
    (hQ : MonotoneOn Q (Ioo (0 : ℝ) 1)) :
    (∑ i : Fin (N - 1),
      |(sortedGrid M raw N n a x).getD i M.yMin - Q (gridLevel N hN (i + 1))|) ≤
      ∑ i : Fin (N - 1),
        |clippedGrid M raw n a (i + 1) x - Q (gridLevel N hN (i + 1))| := by
  have hs := sorted_grid_quantile_error_le M raw N hN n a x Q hQ
  have hsorted := list_grid_error_sum_of_length (sortedGrid M raw N n a x)
    (fun i => Q (gridLevel N hN (i + 1))) M.yMin (N - 1) (by simp [sortedGrid])
  have hraw := list_grid_error_sum_of_length
    ((List.range (N - 1)).map (fun i => clippedGrid M raw n a (i + 1) x))
    (fun i => Q (gridLevel N hN (i + 1))) M.yMin (N - 1) (by simp)
  dsimp only at hs
  rw [hsorted, hraw] at hs
  exact hs.trans_eq (by
    apply Finset.sum_congr rfl
    intro i hi
    simp [List.getD, i.isLt])

-- @node: sorted_selected_grid_error_le
/-- Given [a fallback outcome distribution supported on the model's outcome range at each covariate value](hyp:zeroLaw) and [a positive grid size](hyp:hN), [sorting the clipped estimates weakly reduces their sum of absolute errors against the selected quantiles, after weighting both sums by the lower propensity endpoint divided by the grid size](goal). -/
lemma sorted_selected_grid_error_le (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : MeasureTheory.ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    [MeasurableSpace A] (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ)
    (raw : ℕ → A → ℕ → X → ℝ) (N : ℕ) (hN : 0 < N)
    (n : ℕ) (a : A) (x : X) :
    pLow M.prop x * (N : ℝ)⁻¹ *
      (∑ i : Fin (N - 1), |(sortedGrid M raw N n a x).getD i M.yMin -
        selQuantile M zeroLaw pHat delta n a x (gridLevel N hN (i + 1))|) ≤
    pLow M.prop x * (N : ℝ)⁻¹ *
      ∑ i : Fin (N - 1), |clippedGrid M raw n a (i + 1) x -
        selQuantile M zeroLaw pHat delta n a x (gridLevel N hN (i + 1))| := by
  apply mul_le_mul_of_nonneg_left
    (sorted_grid_quantile_error_sum_le M raw N hN n a x
      (selQuantile M zeroLaw pHat delta n a x)
      (Causalean.Stat.monotoneOn_quantile _))
  exact mul_nonneg (population_support_endpoints M x).1.1 (inv_nonneg.mpr (Nat.cast_nonneg N))

end Papers.TbsPrteOptimalTransport
