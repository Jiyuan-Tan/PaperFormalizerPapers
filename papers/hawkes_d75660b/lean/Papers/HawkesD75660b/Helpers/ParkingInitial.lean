module

public import Papers.HawkesD75660b.Helpers.TightPrefixes

/-! Enumeration of the initial preference count by its set of labeled cars. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

/-- If [the initial block has positive size](hyp:hs), [the number of classic parking
vectors in which precisely the initial block prefers spot one is one when no cars
remain, and otherwise equals the initial block's size times the total car count raised
to the remaining car count minus one](goal). -/
-- @node: parkingInitialBlock_card
lemma parkingInitialBlock_card (s r : ℕ) (hs : 0 < s) :
    ((classicParkingSet (s + r)).filter (fun w =>
      (∀ i : Fin s, (w (Fin.castAdd r i)).val = 0) ∧
      (∀ j : Fin r, 0 < (w (Fin.natAdd s j)).val))).card =
      if r = 0 then 1 else s * (s + r) ^ (r - 1) := by
  classical
  let low : PreferenceVector s := fun _ => 1
  have hlow : ∀ i, (low i : ℕ) ≤ 1 := by simp [low]
  have hp : ∀ t, t ≤ 1 → t ≤ parkingPrefix low t := by
    intro t ht
    by_cases hz : t = 0
    · omega
    · have he : t = 1 := by omega
      subst t
      simpa [parkingPrefix_eq_sum, low] using (show 1 ≤ s by omega)
  have hc := parkingCompletionSet_card (r := r) (by omega : 1 ≤ s) low hlow hp
  have he : (parkingCompletionSet (r := r) 1 low).card =
      ((classicParkingSet (s + r)).filter (fun w =>
        (∀ i : Fin s, (w (Fin.castAdd r i)).val = 0) ∧
        (∀ j : Fin r, 0 < (w (Fin.natAdd s j)).val))).card := by
    let f := fun π (hπ : π ∈ parkingCompletionSet (r := r) 1 low) =>
      fun i : Fin (s + r) => (⟨(π i : ℕ) - 1, by
        have hb := classicParking_coordinate_bound
          (⟨((mem_parkingCompletionSet low π).1 hπ).1, rfl⟩ :
            CombinatorialParkingFunction (s + r) π) i
        have := (π i).pos
        omega⟩ : Fin (s + r))
    have hf (π) (hπ : π ∈ parkingCompletionSet (r := r) 1 low) :
        boundedParkingVector (f π hπ) = π := by
      funext i
      apply Subtype.ext
      change (π i : ℕ) - 1 + 1 = (π i : ℕ)
      have := (π i).pos
      omega
    apply Finset.card_bij f
    · intro π hπ
      obtain ⟨ho, hl, hr⟩ := (mem_parkingCompletionSet low π).1 hπ
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_, ?_⟩
      · rw [hf π hπ]
        exact ⟨ho, rfl⟩
      · intro i
        change (π (Fin.castAdd r i) : ℕ) - 1 = 0
        simp [hl, low]
      · intro j
        change 0 < (π (Fin.natAdd s j) : ℕ) - 1
        have := (hr j).1
        omega
    · intro π hπ σ hσ heq
      rw [← hf π hπ, ← hf σ hσ, heq]
    · intro w hw
      obtain ⟨hw, hl, hr⟩ := Finset.mem_filter.mp hw
      have hmem : boundedParkingVector w ∈ parkingCompletionSet (r := r) 1 low := by
        apply (mem_parkingCompletionSet low _).2
        refine ⟨(Finset.mem_filter.mp hw).2.order, ?_, ?_⟩
        · intro i
          apply Subtype.ext
          change (w (Fin.castAdd r i)).val + 1 = 1
          rw [hl i]
        · intro j
          change 1 < (w (Fin.natAdd s j)).val + 1 ∧
            (w (Fin.natAdd s j)).val + 1 ≤ s + r
          have := (w (Fin.natAdd s j)).isLt
          exact ⟨by have := hr j; omega, by omega⟩
      refine ⟨boundedParkingVector w, hmem, ?_⟩
      funext i
      apply Fin.ext
      simp [f, boundedParkingVector]
  rw [he] at hc
  simpa only [Nat.sub_add_cancel (show 1 ≤ s by omega),
    Nat.sub_add_cancel (show 1 ≤ s + r by omega)] using hc

/-- If [the prescribed number of cars preferring spot one is positive](hyp:hs) and
[a fixed subset of the cars has that size](hyp:hA), [the number of classic parking
vectors in which precisely that subset prefers spot one is one when no other cars
remain, and otherwise equals the subset's size times the total car count raised to
the number of remaining cars minus one](goal). -/
-- @node: parkingInitialSubset_card
lemma parkingInitialSubset_card (s r : ℕ) (hs : 0 < s)
    (A : Finset (Fin (s + r))) (hA : A.card = s) :
    ((classicParkingSet (s + r)).filter (fun w => parkingLowCars w 1 = A)).card =
      if r = 0 then 1 else s * (s + r) ^ (r - 1) := by
  classical
  let el : Fin s ≃ {i : Fin (s + r) // i ∈ A} :=
    Fintype.equivOfCardEq (by simpa using hA.symm)
  let er : Fin r ≃ {i : Fin (s + r) // i ∉ A} :=
    Fintype.equivOfCardEq (by simp [Fintype.card_subtype_compl, hA])
  let e : Equiv.Perm (Fin (s + r)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr el er).trans (Equiv.sumCompl (· ∈ A)))
  have hel (i : Fin s) : e (Fin.castAdd r i) ∈ A := by
    change (Equiv.sumCompl (· ∈ A))
      ((Equiv.sumCongr el er) (finSumFinEquiv.symm (Fin.castAdd r i))) ∈ A
    simpa using (el i).property
  have her (j : Fin r) : e (Fin.natAdd s j) ∉ A := by
    change (Equiv.sumCompl (· ∈ A))
      ((Equiv.sumCongr el er) (finSumFinEquiv.symm (Fin.natAdd s j))) ∉ A
    simpa using (er j).property
  rw [← parkingInitialBlock_card s r hs]
  apply Finset.card_bij (fun w _ => w ∘ e)
  · intro w hw
    obtain ⟨hw, heq⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (classicParking_reindex w e).2 (Finset.mem_filter.mp hw).2⟩
    · intro i
      have hh : (w (e (Fin.castAdd r i))).val < 1 := by
        have := hel i
        rw [← heq] at this
        simpa [parkingLowCars] using this
      change (w (e (Fin.castAdd r i))).val = 0
      omega
    · intro j
      have hh : ¬(w (e (Fin.natAdd s j))).val < 1 := by
        intro h
        apply her j
        rw [← heq]
        simpa [parkingLowCars] using h
      change 0 < (w (e (Fin.natAdd s j))).val
      omega
  · intro w hw v hv heq
    funext i
    have h := congrFun heq (e.symm i)
    simpa using h
  · intro w hw
    obtain ⟨hw, hl, hr⟩ := Finset.mem_filter.mp hw
    have hclassic := (classicParking_reindex w e.symm).2 (Finset.mem_filter.mp hw).2
    have heq : parkingLowCars (w ∘ e.symm) 1 = A := by
      apply Finset.ext
      intro i
      obtain ⟨j, rfl⟩ := e.surjective i
      simp only [parkingLowCars, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.comp_apply, Equiv.symm_apply_apply]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · exact iff_of_true (by have := hl j; omega) (hel j)
      · exact iff_of_false (by have := hr j; omega) (her j)
    refine ⟨w ∘ e.symm, Finset.mem_filter.mpr ⟨?_, heq⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclassic⟩
    · funext i
      simp

/-- If [the prescribed number of cars preferring spot one is positive](hyp:hs),
[the number of classic parking vectors with exactly that many cars preferring spot one
equals the number of ways to choose those cars times one if no cars remain, or times
the prescribed number multiplied by the total car count raised to the remaining car count minus one otherwise](goal). -/
-- @node: parkingInitialCount_card
lemma parkingInitialCount_card (s r : ℕ) (hs : 0 < s) :
    ((classicParkingSet (s + r)).filter (fun w =>
      (parkingLowCars w 1).card = s)).card =
      (s + r).choose s * (if r = 0 then 1 else s * (s + r) ^ (r - 1)) := by
  classical
  let S := (classicParkingSet (s + r)).filter (fun w => (parkingLowCars w 1).card = s)
  have hf (A : Finset (Fin (s + r))) (hA : A ∈ Finset.univ.powersetCard s) :
      (S.filter (fun w => parkingLowCars w 1 = A)).card =
        if r = 0 then 1 else s * (s + r) ^ (r - 1) := by
    have hc : A.card = s := (Finset.mem_powersetCard.mp hA).2
    have heq : S.filter (fun w => parkingLowCars w 1 = A) =
        (classicParkingSet (s + r)).filter (fun w => parkingLowCars w 1 = A) := by
      ext w
      simp only [S, Finset.mem_filter, and_assoc]
      constructor
      · rintro ⟨hw, hp, he⟩
        exact ⟨hw, he⟩
      · rintro ⟨hw, he⟩
        exact ⟨hw, by rw [he, hc], he⟩
    rw [heq, parkingInitialSubset_card s r hs A hc]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := Finset.univ.powersetCard s) (f := fun w => parkingLowCars w 1)
    (by
      intro w hw
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, (Finset.mem_filter.mp hw).2⟩)
  change S.card = _
  rw [hsum]
  calc
    _ = ∑ _A ∈ Finset.univ.powersetCard s,
        (if r = 0 then 1 else s * (s + r) ^ (r - 1)) := Finset.sum_congr rfl hf
    _ = _ := by simp [Finset.card_powersetCard]

-- @node: parkingInitialCount_eq
/-- For [a positive car count](hyp:hn), [the first coordinate of the preference count
vector equals the number of cars whose bounded label is zero, or equivalently whose
positive preference is spot one](goal). -/
lemma parkingInitialCount_eq {n : ℕ} (hn : 0 < n) (w : Fin n → Fin n) :
    preferenceCountsOfParking n (boundedParkingVector w) ⟨0, hn⟩ =
      (parkingLowCars w 1).card := by
  classical
  unfold preferenceCountsOfParking parkingLowCars
  congr 1
  ext i
  simp [boundedParkingVector]

/-- If [the prescribed initial count is positive](hyp:hs), [the preference count measure
assigns to the event that the first coordinate equals this count the following mass:
the total car count choose the prescribed count, multiplied by one when no other cars
remain or by the prescribed count times the total car count raised to the remaining
car count minus one otherwise, and divided by the total car count plus one raised to
the total car count minus one](goal). -/
-- @node: canonicalInitialCount_mass
lemma canonicalInitialCount_mass (s r : ℕ) (hs : 0 < s) :
    ∀ a : Fin (s + r), a.val = 0 →
    (preferenceCountMeasure (s + r)).real {q | q a = s} =
      ((s + r).choose s : ℝ) *
        (if r = 0 then 1 else (s : ℝ) * (s + r : ℝ) ^ (r - 1)) /
          (s + r + 1 : ℝ) ^ (s + r - 1) := by
  intro a ha
  have ha' : a = ⟨0, by omega⟩ := Fin.ext ha
  rw [ha']
  rw [canonicalCount_event_card]
  simp_rw [parkingInitialCount_eq (by omega : 0 < s + r)]
  rw [parkingInitialCount_card s r hs]
  push_cast
  split_ifs <;> simp_all

/-- If [the nonnegative integer v is at most t](hyp:hv), [under the preference count
measure for t plus one cars, the probability that the first count is v plus one equals
t choose v times t plus one raised to t minus v, divided by t plus two raised to t](goal). -/
-- @node: canonicalInitialShift_mass
lemma canonicalInitialShift_mass (t v : ℕ) (hv : v ≤ t) :
    (preferenceCountMeasure (t + 1)).real {q | q ⟨0, by omega⟩ = v + 1} =
      (t.choose v : ℝ) * (t + 1 : ℝ) ^ (t - v) / (t + 2 : ℝ) ^ t := by
  have hsum : v + 1 + (t - v) = t + 1 := by omega
  have hh := canonicalInitialCount_mass (v + 1) (t - v) (by omega)
  rw [hsum] at hh
  specialize hh ⟨0, by omega⟩ rfl
  simp only [Nat.add_sub_cancel] at hh
  have hreal : (v + 1 : ℝ) + ((t - v : ℕ) : ℝ) = t + 1 := by exact_mod_cast hsum
  push_cast at hh
  rw [hreal] at hh
  rw [hh, show (t : ℝ) + 1 + 1 = t + 2 by ring]
  by_cases he : t - v = 0
  · have hvt : v = t := by omega
    subst v
    simp
  · rw [if_neg he]
    have hc : ((t + 1).choose (v + 1) : ℝ) * (v + 1 : ℝ) =
        (t + 1 : ℝ) * (t.choose v : ℝ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq t v).symm
    have hp : (t + 1 : ℝ) ^ (t - v) =
        (t + 1 : ℝ) * (t + 1 : ℝ) ^ (t - v - 1) := by
      conv_lhs => rw [show t - v = (t - v - 1) + 1 by omega]
      rw [pow_succ, mul_comm]
    rw [← mul_assoc, hc, hp]
    congr 1; ring

end Papers.HawkesD75660b
