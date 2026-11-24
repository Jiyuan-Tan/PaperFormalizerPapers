module

public import Papers.HawkesD75660b.Helpers.ParkingEnumeration
public import Mathlib.Data.Fintype.Powerset

/-! Splitting classic parking functions at a tight prefix. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

-- @node: parkingAppend_classic_iff
/-- If [every preference in the first block is at most m](hyp:hlow), [appending the second block after shifting its preferences by m gives a classic parking function exactly when both blocks are classic parking functions separately](goal). -/
lemma parkingAppend_classic_iff {m r : ℕ} (low : PreferenceVector m)
    (tail : PreferenceVector r) (hlow : ∀ i, (low i : ℕ) ≤ m) :
    CombinatorialParkingFunction (m + r) (parkingAppend m low tail) ↔
      CombinatorialParkingFunction m low ∧ CombinatorialParkingFunction r tail := by
  have hsplit : generalizedParkingOrder (m + r) (parkingAppend m low tail) →
      generalizedParkingOrder m low := by
    intro h
    apply (generalizedParkingOrder_iff_prefix le_rfl low).2
    intro t ht
    have hp := (generalizedParkingOrder_iff_prefix le_rfl _).1 h t (by omega)
    rw [parkingPrefix_append] at hp
    have hz : ∀ i : Fin r, ¬m + (tail i : ℕ) ≤ t := by
      intro i
      have := (tail i).pos
      omega
    simpa [hz] using hp
  constructor
  · intro h
    have hl := hsplit h.order
    have hp : ∀ t, t ≤ m → t ≤ parkingPrefix low t := by
      simpa using (generalizedParkingOrder_iff_prefix le_rfl low).1 hl
    have hr := (parkingAppend_order_iff le_rfl low tail hlow hp).1 h.order
    exact ⟨⟨hl, rfl⟩, ⟨by simpa using hr, rfl⟩⟩
  · rintro ⟨hl, hr⟩
    have hp : ∀ t, t ≤ m → t ≤ parkingPrefix low t := by
      simpa using (generalizedParkingOrder_iff_prefix le_rfl low).1 hl.order
    refine ⟨(parkingAppend_order_iff le_rfl low tail hlow hp).2 ?_, rfl⟩
    simpa using hr.order

-- @node: parkingBlockWord
/-- Given [a first preference word with m entries taking values from zero through m − 1](hyp:low) and [a second preference word with r entries taking values from zero through r − 1](hyp:tail), [the combined word concatenates the first word with the second word shifted upward by m](goal). -/
def parkingBlockWord {m r : ℕ} (low : Fin m → Fin m) (tail : Fin r → Fin r) :
    Fin (m + r) → Fin (m + r) :=
  Fin.append (fun i => (low i).castAdd r) (fun i => Fin.natAdd m (tail i))

-- @node: boundedParkingVector_block
/-- [Converting the combined bounded preference word to positive preferences gives the same vector as converting the two blocks separately and appending them with the second block shifted by the first block's length](goal). -/
lemma boundedParkingVector_block {m r : ℕ} (low : Fin m → Fin m)
    (tail : Fin r → Fin r) :
    boundedParkingVector (parkingBlockWord low tail) =
      parkingAppend m (boundedParkingVector low) (boundedParkingVector tail) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have h : parkingAppend m (boundedParkingVector low) (boundedParkingVector tail)
        (Fin.castAdd r j) = boundedParkingVector low j := Fin.append_left _ _ j
    rw [h]
    apply Subtype.ext
    simp [boundedParkingVector, parkingBlockWord]
  · have h : parkingAppend m (boundedParkingVector low) (boundedParkingVector tail)
        (Fin.natAdd m j) =
        (⟨m + (boundedParkingVector tail j : ℕ), by positivity⟩ : ℕ+) :=
      Fin.append_right _ _ j
    rw [h]
    apply Subtype.ext
    simp [boundedParkingVector, parkingBlockWord, Nat.add_assoc]

-- @node: parkingTightBlock_card
/-- [The number of classic parking words on m + r cars whose first m cars have preferences below m and whose remaining r cars have preferences at least m is (m + 1) to power m − 1 times (r + 1) to power r − 1, with negative exponents truncated to zero](goal). -/
lemma parkingTightBlock_card (m r : ℕ) :
    ((classicParkingSet (m + r)).filter (fun w =>
      (∀ i : Fin m, (w (Fin.castAdd r i)).val < m) ∧
      (∀ j : Fin r, m ≤ (w (Fin.natAdd m j)).val))).card =
      (m + 1) ^ (m - 1) * (r + 1) ^ (r - 1) := by
  classical
  rw [← classicParking_enumeration m, ← classicParking_enumeration r,
    ← Finset.card_product]
  symm
  apply Finset.card_bij (fun pair _ => parkingBlockWord pair.1 pair.2)
  · intro pair hp
    obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [boundedParkingVector_block]
      apply (parkingAppend_classic_iff _ _ (fun i => by
        change (pair.1 i).val + 1 ≤ m
        have := (pair.1 i).isLt
        omega)).2
      exact ⟨(Finset.mem_filter.mp hl).2, (Finset.mem_filter.mp hr).2⟩
    · constructor <;> intro i
      · simpa [parkingBlockWord] using (pair.1 i).isLt
      · simp [parkingBlockWord]
  · intro a ha b hb he
    apply Prod.ext
    · funext i
      apply Fin.ext
      have h := congrArg (fun w => (w (Fin.castAdd r i)).val) he
      simpa [parkingBlockWord] using h
    · funext i
      apply Fin.ext
      have h := congrArg (fun w => (w (Fin.natAdd m i)).val) he
      simpa [parkingBlockWord] using h
  · intro w hw
    obtain ⟨hw, hl, hr⟩ := Finset.mem_filter.mp hw
    let low : Fin m → Fin m := fun i => ⟨(w (Fin.castAdd r i)).val, hl i⟩
    let tail : Fin r → Fin r := fun j =>
      ⟨(w (Fin.natAdd m j)).val - m, by
        have := (w (Fin.natAdd m j)).isLt
        have := hr j
        omega⟩
    have he : parkingBlockWord low tail = w := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · apply Fin.ext
        simp [parkingBlockWord, low]
      · apply Fin.ext
        simp only [parkingBlockWord, Fin.append_right, Fin.val_natAdd]
        exact Nat.add_sub_of_le (hr j)
    have hc := (Finset.mem_filter.mp hw).2
    rw [← he, boundedParkingVector_block] at hc
    have hparts := (parkingAppend_classic_iff _ _ (fun i => by
      change (low i).val + 1 ≤ m
      have := (low i).isLt
      omega)).1 hc
    refine ⟨(low, tail), Finset.mem_product.mpr ⟨?_, ?_⟩, he⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparts.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparts.2⟩

-- @node: parkingLowCars
/-- For [a bounded preference word w](hyp:w) and [a cutoff m](hyp:m), [the low-car set consists of the car labels whose preferences are strictly below m](goal). -/
def parkingLowCars {n : ℕ} (w : Fin n → Fin n) (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (w i).val < m)

-- @node: parkingLowCars_card
/-- If [the cutoff m is at most the number of cars n](hyp:hm), [the number of cars whose preferences in w are below m equals the cumulative count through m in the count vector associated with w's positive preference vector](goal). -/
lemma parkingLowCars_card {n : ℕ} (w : Fin n → Fin n) {m : ℕ} (hm : m ≤ n) :
    (parkingLowCars w m).card =
      prefixCount (preferenceCountsOfParking n (boundedParkingVector w)) m := by
  classical
  rw [prefixCount_parking_sorted _ _ hm]
  change _ = parkingPrefix (boundedParkingVector w) m
  rw [parkingPrefix_eq_sum]
  unfold parkingLowCars
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [boundedParkingVector, Nat.lt_iff_add_one_le]
  rfl

-- @node: classicParking_reindex
/-- [Relabeling the cars of a bounded preference word by any permutation preserves, in both directions, whether its positive preference vector is a classic parking function](goal). -/
lemma classicParking_reindex {n : ℕ} (w : Fin n → Fin n) (e : Equiv.Perm (Fin n)) :
    CombinatorialParkingFunction n (boundedParkingVector (w ∘ e)) ↔
      CombinatorialParkingFunction n (boundedParkingVector w) := by
  have hp (t : ℕ) : parkingPrefix (boundedParkingVector (w ∘ e)) t =
      parkingPrefix (boundedParkingVector w) t := by
    simp only [parkingPrefix_eq_sum, boundedParkingVector, Function.comp_apply]
    exact Equiv.sum_comp e (fun i => if (w i).val + 1 ≤ t then (1 : ℕ) else 0)
  constructor <;> intro h <;> refine ⟨?_, rfl⟩
  · apply (generalizedParkingOrder_iff_prefix le_rfl _).2
    intro t ht
    have hh := (generalizedParkingOrder_iff_prefix le_rfl _).1 h.order t ht
    rwa [hp] at hh
  · apply (generalizedParkingOrder_iff_prefix le_rfl _).2
    intro t ht
    rw [hp]
    exact (generalizedParkingOrder_iff_prefix le_rfl _).1 h.order t ht

-- @node: parkingTightSubset_card
/-- If [A contains exactly m of the m + r car labels](hyp:hA), [the number of classic parking words whose cars with preferences below m are exactly A is (m + 1) to power m − 1 times (r + 1) to power r − 1, with negative exponents truncated to zero](goal). -/
lemma parkingTightSubset_card (m r : ℕ) (A : Finset (Fin (m + r))) (hA : A.card = m) :
    ((classicParkingSet (m + r)).filter (fun w => parkingLowCars w m = A)).card =
      (m + 1) ^ (m - 1) * (r + 1) ^ (r - 1) := by
  classical
  let el : Fin m ≃ {i : Fin (m + r) // i ∈ A} :=
    Fintype.equivOfCardEq (by simpa using hA.symm)
  let er : Fin r ≃ {i : Fin (m + r) // i ∉ A} :=
    Fintype.equivOfCardEq (by simp [Fintype.card_subtype_compl, hA])
  let e : Equiv.Perm (Fin (m + r)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr el er).trans (Equiv.sumCompl (· ∈ A)))
  have hel (i : Fin m) : e (Fin.castAdd r i) ∈ A := by
    change (Equiv.sumCompl (· ∈ A))
      ((Equiv.sumCongr el er) (finSumFinEquiv.symm (Fin.castAdd r i))) ∈ A
    simpa using (el i).property
  have her (j : Fin r) : e (Fin.natAdd m j) ∉ A := by
    change (Equiv.sumCompl (· ∈ A))
      ((Equiv.sumCongr el er) (finSumFinEquiv.symm (Fin.natAdd m j))) ∉ A
    simpa using (er j).property
  rw [← parkingTightBlock_card m r]
  apply Finset.card_bij (fun w _ => w ∘ e)
  · intro w hw
    obtain ⟨hw, heq⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (classicParking_reindex w e).2 (Finset.mem_filter.mp hw).2⟩
    · have hh (i : Fin (m + r)) : (w i).val < m ↔ i ∈ A := by
        rw [← heq]
        simp [parkingLowCars]
      exact ⟨fun i => (hh _).2 (hel i), fun j => Nat.le_of_not_gt
        (fun h => her j ((hh _).1 h))⟩
  · intro w hw v hv heq
    funext i
    have h := congrFun heq (e.symm i)
    simpa using h
  · intro w hw
    obtain ⟨hw, hl, hr⟩ := Finset.mem_filter.mp hw
    have hclassic := (classicParking_reindex w e.symm).2 (Finset.mem_filter.mp hw).2
    have heq : parkingLowCars (w ∘ e.symm) m = A := by
      apply Finset.ext
      intro i
      obtain ⟨j, rfl⟩ := e.surjective i
      simp only [parkingLowCars, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.comp_apply, Equiv.symm_apply_apply]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · exact iff_of_true (hl j) (hel j)
      · exact iff_of_false (by have := hr j; omega) (her j)
    refine ⟨w ∘ e.symm, Finset.mem_filter.mpr ⟨?_, heq⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclassic⟩
    · funext i
      simp

-- @node: parkingTightPrefix_card
/-- [The number of classic parking words on m + r cars with cumulative preference count exactly m through the first m positions equals the binomial coefficient choosing m from m + r times (m + 1) to power m − 1 times (r + 1) to power r − 1, with negative exponents truncated to zero](goal). -/
lemma parkingTightPrefix_card (m r : ℕ) :
    ((classicParkingSet (m + r)).filter (fun w =>
      prefixCount (preferenceCountsOfParking (m + r) (boundedParkingVector w)) m = m)).card =
      (m + r).choose m * ((m + 1) ^ (m - 1) * (r + 1) ^ (r - 1)) := by
  classical
  let S := (classicParkingSet (m + r)).filter (fun w =>
    prefixCount (preferenceCountsOfParking (m + r) (boundedParkingVector w)) m = m)
  have hf (A : Finset (Fin (m + r))) (hA : A ∈ Finset.univ.powersetCard m) :
      (S.filter (fun w => parkingLowCars w m = A)).card =
        (m + 1) ^ (m - 1) * (r + 1) ^ (r - 1) := by
    have hc : A.card = m := (Finset.mem_powersetCard.mp hA).2
    have heq : S.filter (fun w => parkingLowCars w m = A) =
        (classicParkingSet (m + r)).filter (fun w => parkingLowCars w m = A) := by
      ext w
      simp only [S, Finset.mem_filter, and_assoc]
      constructor
      · rintro ⟨hw, hp, he⟩
        exact ⟨hw, he⟩
      · rintro ⟨hw, he⟩
        refine ⟨hw, ?_, he⟩
        rw [← parkingLowCars_card w (by omega), he, hc]
    rw [heq, parkingTightSubset_card m r A hc]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := Finset.univ.powersetCard m) (f := fun w => parkingLowCars w m)
    (by
      intro w hw
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [parkingLowCars_card w (by omega)]
      exact (Finset.mem_filter.mp hw).2)
  change S.card = _
  rw [hsum]
  calc
    _ = ∑ _A ∈ Finset.univ.powersetCard m,
        (m + 1) ^ (m - 1) * (r + 1) ^ (r - 1) :=
      Finset.sum_congr rfl hf
    _ = _ := by simp [Finset.card_powersetCard]

open Classical in
-- @node: canonicalCount_event_card
/-- [The preference count probability of any property p equals the number of classic labeled parking words whose associated count vectors satisfy p, divided by (n + 1) to power n − 1, with that exponent taken as zero when n is zero](goal). -/
lemma canonicalCount_event_card (n : ℕ) (p : CountVector n → Prop) :
    (preferenceCountMeasure n).real {k | p k} =
      (((classicParkingSet n).filter (fun w =>
        p (preferenceCountsOfParking n (boundedParkingVector w)))).card : ℝ) /
          (n + 1 : ℝ) ^ (n - 1) := by
  classical
  rw [← (uniformParking_counts_law n).measureReal_eq (p := p)
    (Set.to_countable _).measurableSet]
  have hs : ({w : Fin n → Fin n | p (preferenceCountsOfParking n (boundedParkingVector w))} :
      Set (Fin n → Fin n)) =
      (Finset.univ.filter (fun w : Fin n → Fin n =>
        p (preferenceCountsOfParking n (boundedParkingVector w))) : Set (Fin n → Fin n)) := by
    ext w
    simp
  rw [measureReal_def, hs, uniformOn_apply_finset]
  have hi : classicParkingSet n ∩ Finset.univ.filter (fun w =>
      p (preferenceCountsOfParking n (boundedParkingVector w))) =
      (classicParkingSet n).filter (fun w =>
        p (preferenceCountsOfParking n (boundedParkingVector w))) := by
    ext w
    simp
  rw [hi, classicParking_enumeration]
  simp [ENNReal.toReal_add]

-- @node: canonicalTightPrefix_mass
/-- If [m is at most the count vector length n](hyp:hm), [the probability that the cumulative preference count through m equals m is the binomial coefficient choosing m from n times (m + 1) to power m − 1 times (n − m + 1) to power n − m − 1, divided by (n + 1) to power n − 1, with negative exponents truncated to zero](goal). -/
lemma canonicalTightPrefix_mass {n m : ℕ} (hm : m ≤ n) :
    (preferenceCountMeasure n).real {k | prefixCount k m = m} =
      (n.choose m : ℝ) * ((m + 1 : ℝ) ^ (m - 1) *
        (n - m + 1 : ℝ) ^ (n - m - 1)) / (n + 1 : ℝ) ^ (n - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [canonicalCount_event_card]
  have hc := parkingTightPrefix_card m r
  have hcard : ((classicParkingSet (m + r)).filter (fun w =>
      prefixCount (preferenceCountsOfParking (m + r) (boundedParkingVector w)) m = m)).card =
      (m + r).choose m * ((m + 1) ^ (m - 1) * (r + 1) ^ (r - 1)) := hc
  convert congrArg (fun t : ℕ => (t : ℝ) / (m + r + 1 : ℝ) ^ (m + r - 1)) hcard using 1 <;>
    push_cast
  · congr 3
    ext w
    simp
  · simp

-- @node: canonicalTightPrefix_mass_zpow
/-- If [m is smaller than the count vector length n](hyp:hm), [the probability that the cumulative preference count through m equals m is the binomial coefficient choosing m from n times (m + 1) to integer power m − 1 times (n − m + 1) to integer power n − m − 1, divided by (n + 1) to integer power n − 1](goal). -/
lemma canonicalTightPrefix_mass_zpow {n m : ℕ} (hm : m < n) :
    (preferenceCountMeasure n).real {k | prefixCount k m = m} =
      (n.choose m : ℝ) *
        ((m + 1 : ℝ) ^ ((m : ℤ) - 1) / (n + 1 : ℝ) ^ ((n : ℤ) - 1)) *
        ((n : ℝ) - m + 1) ^ ((n : ℤ) - m - 1) := by
  have hn : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
  have hr : (n : ℤ) - m - 1 = ((n - m - 1 : ℕ) : ℤ) := by omega
  have hp : (m + 1 : ℝ) ^ ((m : ℤ) - 1) = (m + 1 : ℝ) ^ (m - 1) := by
    by_cases hz : m = 0
    · subst m
      norm_num
    · rw [show (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [canonicalTightPrefix_mass (Nat.le_of_lt hm), hn, hr, hp, zpow_natCast,
    zpow_natCast]
  ring

end Papers.HawkesD75660b
