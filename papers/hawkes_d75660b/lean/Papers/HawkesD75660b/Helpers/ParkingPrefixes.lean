module

public import Papers.HawkesD75660b.Basic

/-! Support, cumulative bijection, and parking-count fibers. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

/-- For [an alphabet length](hyp:n) and [a vector of positive integer preferences](hyp:π), [the combinatorial parking property](goal) requires [each sorted preference to be at most the alphabet length minus the vector length, with subtraction truncated at zero, plus its position counted from one](step:1) and [the vector length to equal the alphabet length](step:2). -/
def CombinatorialParkingFunction {m : ℕ} (n : ℕ) (π : PreferenceVector m) : Prop :=
  generalizedParkingOrder n π ∧ classicParkingSquare m n

/-- If [a preference vector has the combinatorial parking property](hyp:h), then [each sorted preference is at most the alphabet length minus the vector length, with subtraction truncated at zero, plus its position counted from one](goal). -/
lemma CombinatorialParkingFunction.order {m n : ℕ} {π : PreferenceVector m}
    (h : CombinatorialParkingFunction n π) : generalizedParkingOrder n π := by
  exact h.1

/-- If [the vector and alphabet lengths are positive and the vector length does not exceed the alphabet length](hyp:hparams), then [the combinatorial parking property is equivalent to the classic parking function property](goal). -/
lemma combinatorialParkingFunction_iff_classic {m n : ℕ} (π : PreferenceVector m)
    (hparams : generalizedParkingParameters m n) :
    CombinatorialParkingFunction n π ↔ ClassicParkingFunction n π := by
  exact ⟨fun h => ⟨hparams, h.1, h.2⟩, fun h => ⟨h.order, h.square⟩⟩

-- @node: preferenceCounts_coordinate_bound
/-- If [a count vector has total count equal to its length and every positive prefix contains at least as many preferences as its length](hyp:hκ), then [each coordinate count is at most the vector length](goal). -/
lemma preferenceCounts_coordinate_bound {n : ℕ} {κ : CountVector n}
    (hκ : PreferenceCounts κ) (a : Fin n) : κ a ≤ n := by
  calc
    κ a ≤ ∑ b : Fin n, κ b :=
      Finset.single_le_sum (fun b _ => Nat.zero_le (κ b)) (Finset.mem_univ a)
    _ = n := hκ.total

-- @node: classicParking_coordinate_bound
/-- If [a preference vector has the combinatorial parking property](hyp:hπ), then [every preference is at most the number of cars](goal). -/
lemma classicParking_coordinate_bound {n : ℕ} {π : PreferenceVector n}
    (hπ : CombinatorialParkingFunction n π) (a : Fin n) : (π a : ℕ) ≤ n := by
  have hmem : (π a : ℕ) ∈ sortedPreferences π := by
    simp [sortedPreferences]
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  have hlen : (sortedPreferences π).length = n := by simp [sortedPreferences]
  have hbound := hπ.order ⟨i, by omega⟩
  have hget : (sortedPreferences π)[i]?.getD 0 = (π a : ℕ) := by
    simp [List.getElem?_eq_getElem hi, heq]
  rw [hget] at hbound
  omega


-- @node: parking_countP_ofFn
/-- [The number of entries satisfying a Boolean test in the list formed from a finite indexed family equals the sum, over all indices, of one for a passing entry and zero otherwise](goal). -/
lemma parking_countP_ofFn {α : Type*} (p : α → Bool) {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).countP p = ∑ j : Fin n, if p (f j) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ, ih]
    omega

-- @node: prefixCount_parking_sorted
/-- If [a nonnegative threshold is at most the preference vector length](hyp:hi), then [the cumulative preference count through that threshold equals the number of sorted preferences no greater than the threshold](goal). -/
lemma prefixCount_parking_sorted {n : ℕ} (π : PreferenceVector n)
    (i : ℕ) (hi : i ≤ n) :
    prefixCount (preferenceCountsOfParking n π) i =
      (sortedPreferences π).countP (fun v => decide (v ≤ i)) := by
  classical
  rw [sortedPreferences, (List.mergeSort_perm _ _).countP_eq, parking_countP_ofFn]
  unfold prefixCount preferenceCountsOfParking
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hli : (π l : ℕ) ≤ i
  · let a : Fin n := ⟨(π l : ℕ) - 1, by have := (π l).pos; omega⟩
    have heq : ∀ b : Fin n, (π l : ℕ) = b.val + 1 ↔ b = a := by
      intro b
      have := (π l).pos
      dsimp [a]
      constructor
      · intro h; apply Fin.ext; dsimp; omega
      · intro h; subst b; dsimp; omega
    simp_rw [heq]
    have ha : a.val < i := by dsimp [a]; have := (π l).pos; omega
    have hterm : ∀ b : Fin n, (if b.val < i then if b = a then 1 else 0 else 0) =
        (if b = a then 1 else 0 : ℕ) := by
      intro b
      by_cases hba : b = a
      · subst b; simp [ha]
      · simp [hba]
    simp_rw [hterm]
    simp [hli]
  · have hz : ∀ b : Fin n, (if b.val < i then
          if (π l : ℕ) = b.val + 1 then 1 else 0 else 0) = (0 : ℕ) := by
      intro b
      split_ifs <;> omega
    simp [hli, hz]

-- @node: countsOfClassicParking_supported
/-- If [a preference vector has the combinatorial parking property](hyp:hπ), then [its preference counts sum to the vector length and each positive prefix count is at least the prefix length](goal). -/
lemma countsOfClassicParking_supported {n : ℕ} {π : PreferenceVector n}
    (hπ : CombinatorialParkingFunction n π) : PreferenceCounts (preferenceCountsOfParking n π) := by
  classical
  have hlen : (sortedPreferences π).length = n := by simp [sortedPreferences]
  constructor
  · change (∑ a, preferenceCountsOfParking n π a) = n
    have hall : prefixCount (preferenceCountsOfParking n π) n = n := by
      rw [prefixCount_parking_sorted π n le_rfl]
      rw [List.countP_eq_length.mpr]
      · exact hlen
      · intro v hv
        have hvπ : v ∈ List.ofFn (fun a => (π a : ℕ)) := by
          simpa [sortedPreferences] using hv
        obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hvπ
        exact decide_eq_true (classicParking_coordinate_bound hπ a)
    simpa [prefixCount] using hall
  · intro i hi hin
    rw [prefixCount_parking_sorted π i hin]
    have ht : ((sortedPreferences π).take i).countP (fun v => decide (v ≤ i)) = i := by
      apply Eq.trans (b := ((sortedPreferences π).take i).length) _ (by simp [hlen, hin])
      apply List.countP_eq_length.mpr
      intro v hv
      obtain ⟨j, hj, hv⟩ := List.mem_iff_getElem.mp hv
      have hji : j < i := lt_of_lt_of_le hj (List.length_take_le ..)
      have hjn : j < n := lt_of_lt_of_le hji hin
      have ho := hπ.order ⟨j, hjn⟩
      simp only [Nat.sub_self, Nat.zero_add] at ho
      have hjlen : j < (sortedPreferences π).length := by omega
      simp only [List.getElem?_eq_getElem hjlen, Option.getD_some] at ho
      have hv' : (sortedPreferences π)[j] = v := by simpa using hv
      exact decide_eq_true (hv' ▸ ho.trans (by omega))
    have hsub := (List.take_sublist i (sortedPreferences π)).countP_le
      (p := fun v => decide (v ≤ i))
    simpa [ht] using hsub

-- @node: classicParking_of_counts_supported
/-- If [the preference counts of a vector sum to its length and every positive prefix count is at least the prefix length](hyp:hκ), then [the vector has the combinatorial parking property with alphabet length equal to its length](goal). -/
lemma classicParking_of_counts_supported {n : ℕ} {π : PreferenceVector n}
    (hκ : PreferenceCounts (preferenceCountsOfParking n π)) :
    CombinatorialParkingFunction n π := by
  classical
  refine ⟨?_, rfl⟩
  intro a
  simp only [Nat.sub_self, Nat.zero_add]
  let l := sortedPreferences π
  have hlen : l.length = n := by simp [l, sortedPreferences]
  have ha : a.val < l.length := by omega
  change l[a.val]?.getD 0 ≤ a.val + 1
  rw [List.getElem?_eq_getElem ha, Option.getD_some]
  by_contra h
  have hlarge : a.val + 1 < l[a.val] := by omega
  have hs : l.Pairwise (· ≤ ·) := by
    exact List.pairwise_mergeSort' (· ≤ ·) _
  have hdrop : (l.drop a.val).countP (fun v => decide (v ≤ a.val + 1)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro v hv
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hv
    have hj' : a.val + j < l.length := by
      rw [List.length_drop] at hj
      omega
    have hmono := hs.rel_get_of_le
      (a := ⟨a.val, ha⟩) (b := ⟨a.val + j, hj'⟩) (by simp)
    have hv' : l[a.val + j] = v := by simpa using heq
    simp only [List.get_eq_getElem, hv'] at hmono
    simp only [decide_eq_true_eq]
    omega
  have hc := hκ.prefix (a.val + 1) (by omega) (by omega)
  rw [prefixCount_parking_sorted π (a.val + 1) (by omega)] at hc
  change a.val + 1 ≤ l.countP (fun v => decide (v ≤ a.val + 1)) at hc
  have hsplit := List.countP_append (l₁ := l.take a.val) (l₂ := l.drop a.val)
    (p := fun v => decide (v ≤ a.val + 1))
  rw [List.take_append_drop, hdrop, Nat.add_zero] at hsplit
  have hb := List.countP_le_length (l := l.take a.val)
    (p := fun v => decide (v ≤ a.val + 1))
  have ht := List.length_take_le a.val l
  omega

-- @node: cumulativePreferenceCounts_supported
/-- If [a count vector sums to its length and every positive prefix count is at least the prefix length](hyp:hκ), then [its cumulative counts are nondecreasing integers between one and the vector length, with each entry at least its position counted from one](goal). -/
lemma cumulativePreferenceCounts_supported {n : ℕ} {κ : CountVector n}
    (hκ : PreferenceCounts κ) :
    CumulativePreferenceCounts (cumulativePreferenceCounts κ) := by
  constructor
  · constructor
    · intro a
      have hlo := hκ.prefix (a.val + 1) (by omega) (by omega)
      have hhi : prefixCount κ (a.val + 1) ≤ n := by
        calc
          prefixCount κ (a.val + 1) ≤ ∑ b : Fin n, κ b := by
            unfold prefixCount
            exact Finset.sum_le_sum (fun b _ => by split_ifs <;> omega)
          _ = n := hκ.total
      change 1 ≤ (prefixCount κ (a.val + 1) : ℤ) ∧
        (prefixCount κ (a.val + 1) : ℤ) ≤ n
      exact ⟨by omega, by exact_mod_cast hhi⟩
    · intro a b hab
      change (prefixCount κ (a.val + 1) : ℤ) ≤ prefixCount κ (b.val + 1)
      apply Int.ofNat_le.mpr
      unfold prefixCount
      apply Finset.sum_le_sum
      intro c hc
      have hab' : a.val ≤ b.val := hab
      split_ifs <;> omega
  · intro a
    change (a.val + 1 : ℤ) ≤ (prefixCount κ (a.val + 1) : ℤ)
    exact_mod_cast hκ.prefix (a.val + 1) (by omega) (by omega)

-- @node: prefixCount_succ
/-- [Extending a count prefix by one coordinate increases its sum by exactly the count at that coordinate](goal). -/
lemma prefixCount_succ {n : ℕ} (κ : CountVector n) (a : Fin n) :
    prefixCount κ (a.val + 1) = prefixCount κ a.val + κ a := by
  classical
  unfold prefixCount
  calc
    (∑ b : Fin n, if b.val < a.val + 1 then κ b else 0) =
        ∑ b : Fin n, ((if b.val < a.val then κ b else 0) +
          if b = a then κ a else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hba : b = a
      · subst b
        simp
      · have hne : b.val ≠ a.val := fun h => hba (Fin.ext h)
        split_ifs <;> simp_all <;> omega
    _ = _ := by simp [Finset.sum_add_distrib]

/-- For [an integer valued vector](hyp:c), [the count difference vector records the difference between each entry and its predecessor, taking the predecessor of the first entry to be zero and replacing negative differences by zero](goal). -/
def countDifferences {n : ℕ} (c : Fin n → ℤ) : CountVector n :=
  fun a => Int.toNat (c a - if a.val = 0 then 0 else
    c ⟨a.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩)

-- @node: countDifferences_cumulative
/-- If [a count vector sums to its length and every positive prefix count is at least the prefix length](hyp:hκ), then [taking successive differences of its cumulative counts recovers the original count vector](goal). -/
lemma countDifferences_cumulative {n : ℕ} {κ : CountVector n}
    (hκ : PreferenceCounts κ) : countDifferences (cumulativePreferenceCounts κ) = κ := by
  funext a
  unfold countDifferences cumulativePreferenceCounts
  have hs := prefixCount_succ κ a
  by_cases ha : a.val = 0
  · simp only [ha, ↓reduceIte]
    have hz : prefixCount κ 0 = 0 := by simp [prefixCount]
    rw [ha, hz] at hs
    simp only [zero_add] at hs
    rw [hs]
    simp
  · simp only [ha, ↓reduceIte]
    have hpred : a.val - 1 + 1 = a.val := by omega
    simp only [hpred]
    rw [hs, Nat.cast_add]
    simp


-- @node: countDifferences_cast
/-- If [an integer vector is nondecreasing, has entries between one and its length, and has each entry at least its position counted from one](hyp:hc), then [each count difference, expressed as an integer, equals the entry minus its predecessor, using zero before the first entry](goal). -/
lemma countDifferences_cast {n : ℕ} {c : Fin n → ℤ}
    (hc : CumulativePreferenceCounts c) (a : Fin n) :
    (countDifferences c a : ℤ) =
      c a - if a.val = 0 then 0 else
        c ⟨a.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩ := by
  unfold countDifferences
  apply Int.toNat_of_nonneg
  split_ifs with ha
  · have := (hc.order.1 a).1
    omega
  · apply sub_nonneg.mpr
    exact hc.order.2 (show (⟨a.val - 1, _⟩ : Fin n) ≤ a from Nat.sub_le _ _)

-- @node: cumulative_countDifferences
/-- If [an integer vector is nondecreasing, has entries between one and its length, and has each entry at least its position counted from one](hyp:hc), then [the cumulative sums of its count differences recover the original vector](goal). -/
lemma cumulative_countDifferences {n : ℕ} {c : Fin n → ℤ}
    (hc : CumulativePreferenceCounts c) :
    cumulativePreferenceCounts (countDifferences c) = c := by
  have hprefix : ∀ i : ℕ, ∀ hi : i < n,
      (prefixCount (countDifferences c) (i + 1) : ℤ) = c ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [prefixCount_succ (countDifferences c) ⟨0, hi⟩, Nat.cast_add,
        countDifferences_cast hc]
      simp [prefixCount]
    | succ i ih =>
      intro hi
      rw [prefixCount_succ (countDifferences c) ⟨i + 1, hi⟩, Nat.cast_add,
        countDifferences_cast hc]
      have hp := ih (by omega)
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte, Nat.add_sub_cancel]
      rw [hp]
      omega
  funext a
  exact hprefix a.val a.isLt

-- @node: countDifferences_supported
/-- If [an integer vector is nondecreasing, has entries between one and its length, and has each entry at least its position counted from one](hyp:hc), then [its count differences sum to the vector length and every positive prefix sum is at least the prefix length](goal). -/
lemma countDifferences_supported {n : ℕ} {c : Fin n → ℤ}
    (hc : CumulativePreferenceCounts c) : PreferenceCounts (countDifferences c) := by
  have hinv := cumulative_countDifferences hc
  constructor
  · change (∑ a, countDifferences c a) = n
    by_cases hn : n = 0
    · subst n
      simp
    · let a : Fin n := ⟨n - 1, by omega⟩
      have ha : a.val + 1 = n := by dsimp [a]; omega
      have hcend := congrFun hinv a
      change (prefixCount (countDifferences c) (a.val + 1) : ℤ) = c a at hcend
      have hclo := hc.prefix a
      have hchi := (hc.order.1 a).2
      rw [ha] at hcend
      have hsum : prefixCount (countDifferences c) n = ∑ b, countDifferences c b := by
        simp [prefixCount]
      rw [hsum] at hcend
      have hlast : c a = n := by omega
      rw [hlast] at hcend
      exact_mod_cast hcend
  · intro i hi hin
    let a : Fin n := ⟨i - 1, by omega⟩
    have ha : a.val + 1 = i := by dsimp [a]; omega
    have hcval := congrFun hinv a
    change (prefixCount (countDifferences c) (a.val + 1) : ℤ) = c a at hcval
    have hlo := hc.prefix a
    rw [ha] at hcval
    omega





end Papers.HawkesD75660b
