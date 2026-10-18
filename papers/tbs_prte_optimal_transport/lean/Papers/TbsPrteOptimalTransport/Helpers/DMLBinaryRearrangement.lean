module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRemainderRates
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Fin
/-! Aggregate squared-error contraction for the binary DML rearrangement.
Clipping precedes sorting of the positive-level success regressions; the
structural boundary remains zero. -/
public section
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set
open scoped BigOperators
set_option linter.style.openClassical false
open scoped Classical

-- @node: sq_sorted_exchange
/-- If [the second fitted value is no larger than the first](hyp:hab) and
[the two target values are in increasing order](hyp:hcd), [exchanging the fitted
values weakly reduces their total squared error against the targets](goal). -/
lemma sq_sorted_exchange (a b c d : ℝ) (hab : b ≤ a) (hcd : c ≤ d) :
    (b - c)^2 + (a - d)^2 ≤ (a - c)^2 + (b - d)^2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hcd)]

-- @node: ordered_insert_squared_error_le
/-- If [the target list is nondecreasing](hyp:hq) and [has one more entry than
the original list](hyp:hlen), [ordered insertion of a new value gives no greater
total paired squared error than placing that value at the front](goal). -/
lemma ordered_insert_squared_error_le (a : ℝ) (l q : List ℝ)
    (hq : q.Pairwise (· ≤ ·)) (hlen : q.length = l.length + 1) :
    (List.zipWith (fun x y : ℝ => (x - y)^2) (l.orderedInsert (· ≤ ·) a) q).sum ≤
      (List.zipWith (fun x y : ℝ => (x - y)^2) (a :: l) q).sum := by
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
        have hex := sq_sorted_exchange a b c d (le_of_not_ge hab) hcd
        simp only [List.zipWith_cons_cons, List.sum_cons] at *
        linarith

-- @node: insertion_sort_squared_error_le
/-- If [the target list is nondecreasing](hyp:hq) and [has the same length as
the fitted list](hyp:hlen), [sorting the fitted list by insertion sort weakly
reduces its total squared error against the target list](goal). -/
lemma insertion_sort_squared_error_le (l q : List ℝ)
    (hq : q.Pairwise (· ≤ ·)) (hlen : q.length = l.length) :
    (List.zipWith (fun x y : ℝ => (x - y)^2) (l.insertionSort (· ≤ ·)) q).sum ≤
      (List.zipWith (fun x y : ℝ => (x - y)^2) l q).sum := by
  induction l generalizing q with
  | nil => simp
  | cons a l ih =>
    rw [List.insertionSort_cons]
    have hinsert := ordered_insert_squared_error_le a (l.insertionSort (· ≤ ·)) q hq
      (by simpa using hlen)
    apply hinsert.trans
    cases q with
    | nil => simp at hlen
    | cons c q =>
      simpa only [List.zipWith_cons_cons, List.sum_cons] using
        add_le_add_right (ih q hq.of_cons (by simpa using hlen)) ((a - c)^2)

-- @node: merge_sort_squared_error_le
/-- If [the target list is nondecreasing](hyp:hq) and [has the same length as
the fitted list](hyp:hlen), [sorting the fitted list by merge sort weakly reduces
its total squared error against the target list](goal). -/
lemma merge_sort_squared_error_le (l q : List ℝ)
    (hq : q.Pairwise (· ≤ ·)) (hlen : q.length = l.length) :
    (List.zipWith (fun x y : ℝ => (x - y)^2) (l.mergeSort (· ≤ ·)) q).sum ≤
      (List.zipWith (fun x y : ℝ => (x - y)^2) l q).sum := by
  rw [List.mergeSort_eq_insertionSort]
  exact insertion_sort_squared_error_le l q hq hlen

-- @node: list_squared_error_sum
/-- [The sum of paired squared errors between a list and a target sequence
evaluated at its successive positions equals the sum of the positionwise squared
errors over all valid list indices, regardless of the fallback value](goal). -/
lemma list_squared_error_sum (l : List ℝ) (Q : ℕ → ℝ) (fallback : ℝ) :
    (List.zipWith (fun x y : ℝ => (x - y)^2) l ((List.range l.length).map Q)).sum =
      ∑ i : Fin l.length, (l.getD i fallback - Q i)^2 := by
  induction l generalizing Q with
  | nil => simp
  | cons b l ih =>
    simpa [List.range_succ_eq_map, List.map_map, Function.comp_def,
      Fin.sum_univ_succ] using
      (ih (fun i => Q (i + 1)))

-- @node: list_squared_error_sum_of_length
/-- If [the list has the specified length](hyp:hlen), [pairing it with the
first that many values of a target sequence and summing squared errors equals
summing the positionwise squared errors over those indices](goal). -/
lemma list_squared_error_sum_of_length (l : List ℝ) (Q : ℕ → ℝ) (fallback : ℝ)
    (N : ℕ) (hlen : l.length = N) :
    (List.zipWith (fun x y : ℝ => (x - y)^2) l ((List.range N).map Q)).sum =
      ∑ i : Fin N, (l.getD i fallback - Q i)^2 := by
  subst N
  exact list_squared_error_sum l Q fallback

-- @node: clip_unit_squared_error_le
/-- If [the target lies between zero and one](hyp:hb), [clipping an arbitrary
estimate to that interval weakly reduces its squared error](goal). -/
lemma clip_unit_squared_error_le (a b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (min 1 (max 0 a) - b)^2 ≤ (a - b)^2 := by
  by_cases ha0 : a ≤ 0
  · rw [max_eq_left ha0, min_eq_right zero_le_one]
    nlinarith [hb.1]
  by_cases ha1 : 1 ≤ a
  · rw [max_eq_right (by linarith), min_eq_left ha1]
    nlinarith [hb.2]
  · rw [max_eq_right (by linarith), min_eq_right (by linarith)]

-- @node: clipped_list_squared_error_le
/-- If [every target entry lies between zero and one](hyp:hq), [clipping each
fitted entry to that interval weakly reduces the sum of squared errors over
the paired entries of the two lists](goal). -/
lemma clipped_list_squared_error_le (l q : List ℝ)
    (hq : ∀ b ∈ q, b ∈ Icc (0 : ℝ) 1) :
    (List.zipWith (fun a b : ℝ => (a - b)^2)
      (l.map (fun a => min 1 (max 0 a))) q).sum ≤
    (List.zipWith (fun a b : ℝ => (a - b)^2) l q).sum := by
  induction l generalizing q with
  | nil => simp
  | cons a l ih =>
    cases q with
    | nil => simp
    | cons b q =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons]
      exact add_le_add (clip_unit_squared_error_le a b (hq b (by simp)))
        (ih q (fun c hc => hq c (by simp [hc])))

-- @node: sorted_clipped_vector_squared_error_le
/-- If [the target sequence is nondecreasing over the first N positions](hyp:hg)
and [its values there lie between zero and one](hyp:hr), [clipping the first N
fitted values to that interval and sorting them weakly reduces their total
squared error against the target sequence](goal). -/
lemma sorted_clipped_vector_squared_error_le (N : ℕ) (f g : ℕ → ℝ)
    (hg : ∀ i j, i < N → j < N → i ≤ j → g i ≤ g j)
    (hr : ∀ i < N, g i ∈ Icc (0 : ℝ) 1) :
    let sorted := ((List.range N).map (fun i => min 1 (max 0 (f i)))).mergeSort (· ≤ ·)
    (∑ i : Fin N, (sorted.getD i 0 - g i)^2) ≤
      ∑ i : Fin N, (f i - g i)^2 := by
  let raw := (List.range N).map f
  let target := (List.range N).map g
  let clipped := raw.map (fun a => min 1 (max 0 a))
  have ht : target.Pairwise (· ≤ ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [target, List.length_map, List.length_range] at hi hj
    simp only [target, List.getElem_map, List.getElem_range]
    exact hg i j hi hj hij.le
  have hsort := merge_sort_squared_error_le clipped target ht (by simp [target, clipped, raw])
  have hclip := clipped_list_squared_error_le raw target (by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hr i (List.mem_range.mp hi))
  have hsorted := list_squared_error_sum_of_length
    (clipped.mergeSort (· ≤ ·)) g 0 N (by simp [clipped, raw])
  have hraw := list_squared_error_sum_of_length raw g 0 N (by simp [raw])
  have hrawsum : (∑ i : Fin N, (raw.getD i 0 - g i)^2) =
      ∑ i : Fin N, (f i - g i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp [raw, i.isLt]
  have htotal := hsort.trans hclip
  change _ ≤ (List.zipWith (fun x y : ℝ => (x - y)^2) raw ((List.range N).map g)).sum at htotal
  rw [hraw, hrawsum] at htotal
  change (List.zipWith (fun x y : ℝ => (x - y)^2) (clipped.mergeSort (· ≤ ·))
    ((List.range N).map g)).sum ≤ _ at htotal
  rw [hsorted] at htotal
  simpa only [clipped, raw, List.map_map, Function.comp_def] using htotal

universe v

-- @node: rearrangeP1_zero_boundary
/-- [The rearranged binary success regression retains a value of zero at
the structural zero boundary for every covariate value](goal). -/
lemma rearrangeP1_zero_boundary {Z X : Type v} (L : LevelData Z X)
    (e : NuisanceBin L) (x : X) :
    positiveValue (rearrangeP1 L e).P1 0 x = 0 := by
  simp [positiveValue]

-- @node: rearrangeP1_aggregate_squared_error_le
/-- If [the true success probabilities are nondecreasing across positive
levels at the given covariate value](hyp:hmono) and [all lie between zero and
one](hyp:hrange), [clipping and sorting the fitted probabilities weakly reduces
their aggregate squared error across positive levels at that covariate value](goal). -/
lemma rearrangeP1_aggregate_squared_error_le {Z X : Type v} (L : LevelData Z X)
    (e truth : NuisanceBin L) (x : X)
    (hmono : ∀ i j : PositiveIndex L.K, i.val ≤ j.val → truth.P1 i x ≤ truth.P1 j x)
    (hrange : ∀ i, truth.P1 i x ∈ Icc (0 : ℝ) 1) :
    (∑ i : Fin L.K,
      (positiveValue (rearrangeP1 L e).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2) ≤
    ∑ i : Fin L.K,
      (positiveValue e.P1 (i + 1) x - positiveValue truth.P1 (i + 1) x)^2 := by
  have h := sorted_clipped_vector_squared_error_le L.K
    (fun i => positiveValue e.P1 (i + 1) x)
    (fun i => positiveValue truth.P1 (i + 1) x)
    (by
      intro i j hi hj hij
      simp only [positiveValue, dif_pos (show 1 ≤ i + 1 ∧ i + 1 ≤ L.K by omega),
        dif_pos (show 1 ≤ j + 1 ∧ j + 1 ≤ L.K by omega)]
      exact hmono _ _ (by dsimp; omega))
    (by
      intro i hi
      simp only [positiveValue, dif_pos (show 1 ≤ i + 1 ∧ i + 1 ≤ L.K by omega)]
      exact hrange _)
  dsimp only at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [positiveValue, dif_pos (show 1 ≤ i.val + 1 ∧ i.val + 1 ≤ L.K by omega),
    rearrangeP1, Nat.add_sub_cancel]

-- @node: rearrangeP1_integrated_squared_error_le
/-- Suppose [the true success probabilities are nondecreasing across positive
levels at every covariate value](hyp:hmono), [lie between zero and one](hyp:hrange),
and [each rearranged squared error](hyp:hs) and [each original squared error](hyp:he)
is integrable under the covariate measure; then [clipping and sorting weakly
reduces the sum of integrated squared errors across positive levels](goal). -/
lemma rearrangeP1_integrated_squared_error_le {Z X : Type v} [MeasurableSpace X]
    (μ : Measure X) (L : LevelData Z X) (e truth : NuisanceBin L)
    (hmono : ∀ x, ∀ i j : PositiveIndex L.K,
      i.val ≤ j.val → truth.P1 i x ≤ truth.P1 j x)
    (hrange : ∀ x i, truth.P1 i x ∈ Icc (0 : ℝ) 1)
    (hs : ∀ i : Fin L.K, Integrable (fun x =>
      (positiveValue (rearrangeP1 L e).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2) μ)
    (he : ∀ i : Fin L.K, Integrable (fun x =>
      (positiveValue e.P1 (i + 1) x - positiveValue truth.P1 (i + 1) x)^2) μ) :
    (∑ i : Fin L.K, ∫ x,
      (positiveValue (rearrangeP1 L e).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2 ∂μ) ≤
    ∑ i : Fin L.K, ∫ x,
      (positiveValue e.P1 (i + 1) x - positiveValue truth.P1 (i + 1) x)^2 ∂μ := by
  rw [← integral_finsetSum _ (fun i _ => hs i),
    ← integral_finsetSum _ (fun i _ => he i)]
  apply integral_mono
    (integrable_finsetSum _ (fun i _ => hs i))
    (integrable_finsetSum _ (fun i _ => he i))
  intro x
  exact rearrangeP1_aggregate_squared_error_le L e truth x (hmono x) (hrange x)

-- Aggregate contraction gives a component bound by the sum of the original
-- L₂ errors, rather than a false componentwise contraction statement.
-- @node: rearrangeP1_component_l2_error_le_sum
/-- Suppose [the true success probabilities are nondecreasing across positive
levels at every covariate value](hyp:hmono), [lie between zero and one](hyp:hrange),
and [all rearranged squared errors](hyp:hs) and [all original squared errors](hyp:he)
are integrable; then [the L₂ error of any one rearranged positive-level regression
is bounded by the sum of the L₂ errors of all original positive-level regressions](goal). -/
lemma rearrangeP1_component_l2_error_le_sum {Z X : Type v} [MeasurableSpace X]
    (μ : Measure X) (L : LevelData Z X) (e truth : NuisanceBin L)
    (hmono : ∀ x, ∀ i j : PositiveIndex L.K,
      i.val ≤ j.val → truth.P1 i x ≤ truth.P1 j x)
    (hrange : ∀ x i, truth.P1 i x ∈ Icc (0 : ℝ) 1)
    (hs : ∀ i : Fin L.K, Integrable (fun x =>
      (positiveValue (rearrangeP1 L e).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2) μ)
    (he : ∀ i : Fin L.K, Integrable (fun x =>
      (positiveValue e.P1 (i + 1) x - positiveValue truth.P1 (i + 1) x)^2) μ)
    (i : Fin L.K) :
    Real.sqrt (∫ x,
      (positiveValue (rearrangeP1 L e).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2 ∂μ) ≤
    ∑ j : Fin L.K, Real.sqrt (∫ x,
      (positiveValue e.P1 (j + 1) x - positiveValue truth.P1 (j + 1) x)^2 ∂μ) := by
  let err := fun j : Fin L.K => ∫ x,
    (positiveValue e.P1 (j + 1) x - positiveValue truth.P1 (j + 1) x)^2 ∂μ
  have hnonneg : ∀ j, 0 ≤ err j := fun j => integral_nonneg (fun x => sq_nonneg _)
  have htotal := rearrangeP1_integrated_squared_error_le μ L e truth hmono hrange hs he
  have hcomponent : (∫ x,
      (positiveValue (rearrangeP1 L e).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2 ∂μ) ≤
      ∑ j : Fin L.K, ∫ x,
        (positiveValue (rearrangeP1 L e).P1 (j + 1) x -
          positiveValue truth.P1 (j + 1) x)^2 ∂μ := by
    apply Finset.single_le_sum _ (Finset.mem_univ i)
    intro j _
    exact integral_nonneg (fun x => sq_nonneg _)
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun j => Real.sqrt (err j))
    (fun j _ => Real.sqrt_nonneg _)
  simp only [Real.sq_sqrt (hnonneg _)] at hsq
  have hbound := hcomponent.trans (htotal.trans hsq)
  have hsum : 0 ≤ ∑ j : Fin L.K, Real.sqrt (err j) :=
    Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
  exact (Real.sqrt_le_sqrt hbound).trans_eq (Real.sqrt_sq hsum)

-- @node: rearrangeP1_component_rate
/-- Suppose [the comparison rate is positive at every sample size](hyp:hr),
[the true success probabilities are nondecreasing across positive levels](hyp:hmono)
and [lie between zero and one](hyp:hrange), [all rearranged squared errors](hyp:hs)
and [all original squared errors](hyp:he) are integrable for every fit, and
[each original positive-level L₂ error is negligible in probability relative
to the comparison rate](hyp:hRate); then [each rearranged positive-level L₂
error is also negligible in probability relative to that rate](goal). -/
lemma rearrangeP1_component_rate {Z X : Type v} {A : Type*}
    [MeasurableSpace X] [MeasurableSpace A]
    (μ : Measure X) (τ : Measure A) (L : LevelData Z X)
    (fit : ℕ → A → NuisanceBin L) (truth : NuisanceBin L)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hmono : ∀ x, ∀ i j : PositiveIndex L.K,
      i.val ≤ j.val → truth.P1 i x ≤ truth.P1 j x)
    (hrange : ∀ x i, truth.P1 i x ∈ Icc (0 : ℝ) 1)
    (hs : ∀ n a (i : Fin L.K), Integrable (fun x =>
      (positiveValue (rearrangeP1 L (fit n a)).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2) μ)
    (he : ∀ n a (i : Fin L.K), Integrable (fun x =>
      (positiveValue (fit n a).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2) μ)
    (hRate : ∀ i : Fin L.K, Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x,
        (positiveValue (fit n a).P1 (i + 1) x -
          positiveValue truth.P1 (i + 1) x)^2 ∂μ)) r τ)
    (i : Fin L.K) :
    Causalean.Stat.IsLittleOp (fun n a => Real.sqrt (∫ x,
      (positiveValue (rearrangeP1 L (fit n a)).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2 ∂μ)) r τ := by
  have hsum : ∀ (N : ℕ) (e : ℕ → A → Fin N → ℝ),
      (∀ j, Causalean.Stat.IsLittleOp (fun n a => e n a j) r τ) →
      Causalean.Stat.IsLittleOp (fun n a => ∑ j, e n a j) r τ := by
    intro N
    induction N with
    | zero =>
      intro e _
      have hz := maxErrors_isLittleOp τ ([] : List Unit) (fun _ _ _ => (0 : ℝ)) r hr
        (by simp)
      simpa only [List.map_nil, maxErrors, List.foldr_nil, Fin.sum_univ_zero] using hz
    | succ N ih =>
      intro e hh
      have ht := ih (fun n a j => e n a j.succ) (fun j => hh j.succ)
      simpa only [Fin.sum_univ_succ] using
        (hh 0).add_eventually_nonneg_rate (Filter.Eventually.of_forall (fun n => (hr n).le)) ht
  have htotal := hsum L.K (fun n a j => Real.sqrt (∫ x,
    (positiveValue (fit n a).P1 (j + 1) x -
      positiveValue truth.P1 (j + 1) x)^2 ∂μ)) hRate
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos htotal
  intro n a
  rw [one_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))]
  exact rearrangeP1_component_l2_error_le_sum μ L (fit n a) truth hmono hrange
    (hs n a) (he n a) i

end Papers.TbsPrteOptimalTransport
