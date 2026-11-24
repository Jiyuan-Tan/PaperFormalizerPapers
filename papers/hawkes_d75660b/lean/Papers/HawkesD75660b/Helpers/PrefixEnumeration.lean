module

public import Papers.HawkesD75660b.Helpers.TightPrefixes

/-! Fixed low-preference allocation fibers for interior prefix enumeration. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

/-- Suppose [the cut m is at most the first block size s](hyp:hms), [all prescribed preferences of that block are at most m](hyp:hlow), and [at least t of those preferences are at most t for every t up to m](hyp:hp). Then [the number of classic parking words agreeing with that block and having all r remaining preferences above m is one when r is zero, and otherwise is (s − m + 1) times (s + r − m + 1) raised to r − 1](goal). -/
-- @node: parkingPrefixBlock_card
lemma parkingPrefixBlock_card {s r m : ℕ} (hms : m ≤ s)
    (low : PreferenceVector s) (hlow : ∀ i, (low i : ℕ) ≤ m)
    (hp : ∀ t, t ≤ m → t ≤ parkingPrefix low t) :
    ((classicParkingSet (s + r)).filter (fun w =>
      (∀ i : Fin s, boundedParkingVector w (Fin.castAdd r i) = low i) ∧
      (∀ j : Fin r, m ≤ (w (Fin.natAdd s j)).val))).card =
      if r = 0 then 1 else (s - m + 1) * (s + r - m + 1) ^ (r - 1) := by
  classical
  have hc := parkingCompletionSet_card (r := r) hms low hlow hp
  have he : (parkingCompletionSet (r := r) m low).card =
      ((classicParkingSet (s + r)).filter (fun w =>
        (∀ i : Fin s, boundedParkingVector w (Fin.castAdd r i) = low i) ∧
        (∀ j : Fin r, m ≤ (w (Fin.natAdd s j)).val))).card := by
    let f := fun π (hπ : π ∈ parkingCompletionSet (r := r) m low) =>
      fun i : Fin (s + r) => (⟨(π i : ℕ) - 1, by
        have hb := classicParking_coordinate_bound
          (⟨((mem_parkingCompletionSet low π).1 hπ).1, rfl⟩ :
            CombinatorialParkingFunction (s + r) π) i
        have := (π i).pos
        omega⟩ : Fin (s + r))
    have hf (π) (hπ : π ∈ parkingCompletionSet (r := r) m low) :
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
        rw [hf π hπ]
        exact hl i
      · intro j
        change m ≤ (π (Fin.natAdd s j) : ℕ) - 1
        have := (hr j).1
        omega
    · intro π hπ σ hσ heq
      rw [← hf π hπ, ← hf σ hσ, heq]
    · intro w hw
      obtain ⟨hw, hl, hr⟩ := Finset.mem_filter.mp hw
      have hmem : boundedParkingVector w ∈ parkingCompletionSet (r := r) m low := by
        apply (mem_parkingCompletionSet low _).2
        refine ⟨(Finset.mem_filter.mp hw).2.order, ?_, ?_⟩
        · exact hl
        · intro j
          change m < (w (Fin.natAdd s j)).val + 1 ∧
            (w (Fin.natAdd s j)).val + 1 ≤ s + r
          have := (w (Fin.natAdd s j)).isLt
          exact ⟨by have := hr j; omega, by omega⟩
      refine ⟨boundedParkingVector w, hmem, ?_⟩
      funext i
      apply Fin.ext
      simp [f, boundedParkingVector]
  rw [he] at hc
  exact hc

/-- Suppose [the cut m is at most s](hyp:hms), [an allocation of s + r car labels to buckets numbered zero through m places exactly s labels below bucket m](hyp:hcount), and [for every t up to m, at least t labels occupy buckets whose number plus one is at most t](hyp:hprefix). Then [the number of classic parking words whose preferences, numbered from zero and clipped at m, equal this allocation is one when r is zero, and otherwise is (s − m + 1) times (s + r − m + 1) raised to r − 1](goal). -/
-- @node: parkingPrefixAllocation_fiber_card
lemma parkingPrefixAllocation_fiber_card {s r m : ℕ} (hms : m ≤ s)
    (f : Fin (s + r) → Fin (m + 1))
    (hcount : (Finset.univ.filter (fun i => (f i).val < m)).card = s)
    (hprefix : ∀ t, t ≤ m →
      t ≤ ∑ i : Fin (s + r), if (f i).val + 1 ≤ t then 1 else 0) :
    ((classicParkingSet (s + r)).filter (fun w =>
      ∀ i, min (w i).val m = (f i).val)).card =
      if r = 0 then 1 else (s - m + 1) * (s + r - m + 1) ^ (r - 1) := by
  classical
  let A := Finset.univ.filter (fun i => (f i).val < m)
  have hA : A.card = s := hcount
  let el : Fin s ≃ {i : Fin (s + r) // i ∈ A} :=
    Fintype.equivOfCardEq (by simpa using hA.symm)
  let er : Fin r ≃ {i : Fin (s + r) // i ∉ A} :=
    Fintype.equivOfCardEq (by simp [Fintype.card_subtype_compl, hA])
  let e : Equiv.Perm (Fin (s + r)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr el er).trans (Equiv.sumCompl (· ∈ A)))
  have hel (i : Fin s) : (f (e (Fin.castAdd r i))).val < m := by
    have he : e (Fin.castAdd r i) ∈ A := by
      change (Equiv.sumCompl (· ∈ A))
        ((Equiv.sumCongr el er) (finSumFinEquiv.symm (Fin.castAdd r i))) ∈ A
      simpa using (el i).property
    simpa [A] using he
  have her (j : Fin r) : (f (e (Fin.natAdd s j))).val = m := by
    have he : e (Fin.natAdd s j) ∉ A := by
      change (Equiv.sumCompl (· ∈ A))
        ((Equiv.sumCongr el er) (finSumFinEquiv.symm (Fin.natAdd s j))) ∉ A
      simpa using (er j).property
    have hb := (f (e (Fin.natAdd s j))).isLt
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at he
    omega
  let low : PreferenceVector s := fun i =>
    ⟨(f (e (Fin.castAdd r i))).val + 1, Nat.succ_pos _⟩
  have hlow : ∀ i, (low i : ℕ) ≤ m := by
    intro i
    have := hel i
    change (f (e (Fin.castAdd r i))).val + 1 ≤ m
    omega
  have hp : ∀ t, t ≤ m → t ≤ parkingPrefix low t := by
    intro t ht
    have hh := hprefix t ht
    have heq := Equiv.sum_comp e
      (fun i => if (f i).val + 1 ≤ t then (1 : ℕ) else 0)
    rw [← heq, Fin.sum_univ_add] at hh
    have hz : ∀ j : Fin r,
        (if (f (e (Fin.natAdd s j))).val + 1 ≤ t then 1 else 0 : ℕ) = 0 := by
      intro j
      rw [her j]
      simp [show ¬m + 1 ≤ t by omega]
    rw [parkingPrefix_eq_sum]
    simp only [hz, Finset.sum_const_zero, Nat.add_zero] at hh
    change t ≤ ∑ i : Fin s, if (f (e (Fin.castAdd r i))).val + 1 ≤ t then (1 : ℕ) else 0
    exact hh
  rw [← parkingPrefixBlock_card hms low hlow hp]
  apply Finset.card_bij (fun w _ => w ∘ e)
  · intro w hw
    obtain ⟨hw, hf⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (classicParking_reindex w e).2 (Finset.mem_filter.mp hw).2⟩
    · intro i
      apply Subtype.ext
      have hh := hf (e (Fin.castAdd r i))
      have hb := hel i
      change (w (e (Fin.castAdd r i))).val + 1 =
        (f (e (Fin.castAdd r i))).val + 1
      omega
    · intro j
      have hh := hf (e (Fin.natAdd s j))
      rw [her j] at hh
      change m ≤ (w (e (Fin.natAdd s j))).val
      omega
  · intro w hw v hv heq
    funext i
    have h := congrFun heq (e.symm i)
    simpa using h
  · intro w hw
    obtain ⟨hw, hl, hr⟩ := Finset.mem_filter.mp hw
    have hc := (classicParking_reindex w e.symm).2 (Finset.mem_filter.mp hw).2
    have hf : ∀ i, min ((w ∘ e.symm) i).val m = (f i).val := by
      intro i
      obtain ⟨j, rfl⟩ := e.surjective i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · have hh := congrArg (fun x : ℕ+ => (x : ℕ)) (hl j)
        have hb := hel j
        change (w (Fin.castAdd r j)).val + 1 =
          (f (e (Fin.castAdd r j))).val + 1 at hh
        omega
      · rw [her j]
        exact min_eq_right (hr j)
    refine ⟨w ∘ e.symm, Finset.mem_filter.mpr ⟨?_, hf⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    · funext i
      simp

/-- For [a nonnegative cut m](hyp:m) and [a word of preferences numbered from zero](hyp:w), [the parking allocation replaces each preference by its minimum with m, retaining the lower buckets and combining all others in bucket m](goal). -/
-- @node: parkingAllocation
def parkingAllocation {n : ℕ} (m : ℕ) (w : Fin n → Fin n) :
    Fin n → Fin (m + 1) :=
  fun i => ⟨min (w i).val m, by omega⟩

/-- [A word's parking allocation equals a given allocation if and only if, for every car, the minimum of its preference numbered from zero and the cut equals its allocated bucket number](goal). -/
-- @node: parkingAllocation_eq_iff
lemma parkingAllocation_eq_iff {n m : ℕ} (w : Fin n → Fin n)
    (f : Fin n → Fin (m + 1)) :
    parkingAllocation m w = f ↔ ∀ i, min (w i).val m = (f i).val := by
  constructor
  · intro h i
    exact congrArg Fin.val (congrFun h i)
  · intro h
    funext i
    exact Fin.ext (h i)

/-- If [the cut does not exceed the number of cars](hyp:hm), then [the number of cars in any allocation bucket below the cut equals the count of their positive integer preferences at that bucket number plus one](goal). -/
-- @node: parkingAllocation_low_count
lemma parkingAllocation_low_count {n m : ℕ} (hm : m ≤ n)
    (w : Fin n → Fin n) (a : Fin m) :
    Fintype.card {i // parkingAllocation m w i = a.castSucc} =
      preferenceCountsOfParking n (boundedParkingVector w) ⟨a.val, by omega⟩ := by
  classical
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun i => parkingAllocation m w i = a.castSucc)).card =
    (Finset.univ.filter (fun i => (boundedParkingVector w i : ℕ) = a.val + 1)).card
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [Fin.ext_iff]
  change min (w i).val m = a.val ↔ (w i).val + 1 = a.val + 1
  have := a.isLt
  omega

/-- Suppose [the cut m is at most s](hyp:hms), [every allocation in a finite collection places exactly s of the s + r car labels in buckets below m](hyp:hcount), and [every allocation places at least t labels in buckets numbered below t for every t up to m](hyp:hprefix). Then [the number of classic parking words with an allocation in that collection equals the collection size times one when r is zero, or times (s − m + 1) times (s + r − m + 1) raised to r − 1 otherwise](goal). -/
-- @node: parkingPrefixAllocations_card
lemma parkingPrefixAllocations_card {s r m : ℕ} (hms : m ≤ s)
    (F : Finset (Fin (s + r) → Fin (m + 1)))
    (hcount : ∀ f ∈ F, (Finset.univ.filter (fun i => (f i).val < m)).card = s)
    (hprefix : ∀ f ∈ F, ∀ t, t ≤ m →
      t ≤ ∑ i : Fin (s + r), if (f i).val + 1 ≤ t then 1 else 0) :
    ((classicParkingSet (s + r)).filter (fun w => parkingAllocation m w ∈ F)).card =
      F.card * (if r = 0 then 1 else (s - m + 1) * (s + r - m + 1) ^ (r - 1)) := by
  classical
  let S := (classicParkingSet (s + r)).filter (fun w => parkingAllocation m w ∈ F)
  have hf (f) (hf : f ∈ F) :
      (S.filter (fun w => parkingAllocation m w = f)).card =
        if r = 0 then 1 else (s - m + 1) * (s + r - m + 1) ^ (r - 1) := by
    have heq : S.filter (fun w => parkingAllocation m w = f) =
        (classicParkingSet (s + r)).filter (fun w =>
          ∀ i, min (w i).val m = (f i).val) := by
      ext w
      simp only [S, Finset.mem_filter]
      rw [← parkingAllocation_eq_iff]
      constructor
      · rintro ⟨⟨hw, _⟩, he⟩
        exact ⟨hw, he⟩
      · rintro ⟨hw, he⟩
        exact ⟨⟨hw, he.symm ▸ hf⟩, he⟩
    rw [heq]
    exact parkingPrefixAllocation_fiber_card hms f (hcount f hf) (hprefix f hf)
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := F) (f := parkingAllocation m)
    (by intro w hw; exact (Finset.mem_filter.mp hw).2)
  change S.card = _
  rw [hsum]
  calc
    _ = ∑ _f ∈ F,
        (if r = 0 then 1 else (s - m + 1) * (s + r - m + 1) ^ (r - 1)) :=
      Finset.sum_congr rfl hf
    _ = _ := by simp

/-- If [each bucket of an allocation contains its prescribed number of car labels](hyp:hc), then [the sum of any nonnegative integer bucket statistic over cars equals the sum over buckets of the prescribed bucket size times the statistic](goal). -/
-- @node: prefixAllocation_sum
lemma prefixAllocation_sum {n m : ℕ} (f : Fin n → Fin (m + 1))
    (c : Fin (m + 1) → ℕ)
    (hc : ∀ a, Fintype.card {i // f i = a} = c a)
    (g : Fin (m + 1) → ℕ) :
    (∑ i, g (f i)) = ∑ a, c a * g a := by
  classical
  rw [← Fintype.sum_fiberwise' f g]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hc]

/-- Suppose [an allocation has prescribed low bucket sizes k and a final bucket of size r](hyp:hc), and [the prescribed low counts sum to at least t over the first t buckets for every t up to the cut](hyp:hp). Then [the number of labels below the final bucket equals the sum of the low counts, and at least t labels occupy the first t buckets for every t up to the cut](goal). -/
-- @node: prefixAllocation_feasible
lemma prefixAllocation_feasible {m : ℕ} (k : Fin m → ℕ) (r : ℕ)
    (f : Fin ((∑ a, k a) + r) → Fin (m + 1))
    (hc : ∀ a, Fintype.card {i // f i = a} = Fin.snoc (α := fun _ => ℕ) k r a)
    (hp : ∀ t, t ≤ m → t ≤ ∑ a : Fin m, if a.val + 1 ≤ t then k a else 0) :
    (Finset.univ.filter (fun i => (f i).val < m)).card = ∑ a, k a ∧
    (∀ t, t ≤ m → t ≤ ∑ i, if (f i).val + 1 ≤ t then 1 else 0) := by
  classical
  constructor
  · rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [prefixAllocation_sum f _ hc (fun a => if a.val < m then 1 else 0),
      Fin.sum_univ_castSucc]
    simp
  · intro t ht
    rw [prefixAllocation_sum f _ hc (fun a => if a.val + 1 ≤ t then 1 else 0),
      Fin.sum_univ_castSucc]
    simpa [show ¬m + 1 ≤ t by omega, mul_ite] using hp t ht

/-- Suppose [the cut m does not exceed the sum S of the prescribed low counts k](hyp:hms), and [the first t low counts sum to at least t for every t up to m](hyp:hp). Then [the number of classic parking words with allocation bucket sizes k followed by r equals the number of labeled allocations with those sizes times one when r is zero, or times (S − m + 1) times (S + r − m + 1) raised to r − 1 otherwise](goal). -/
-- @node: parkingPrescribedPrefix_card
lemma parkingPrescribedPrefix_card {m : ℕ} (k : Fin m → ℕ) (r : ℕ)
    (hms : m ≤ ∑ a, k a)
    (hp : ∀ t, t ≤ m → t ≤ ∑ a : Fin m, if a.val + 1 ≤ t then k a else 0) :
    ((classicParkingSet ((∑ a, k a) + r)).filter (fun w =>
      ∀ a, Fintype.card {i // parkingAllocation m w i = a} =
        Fin.snoc (α := fun _ => ℕ) k r a)).card =
      Fintype.card {f : Fin ((∑ a, k a) + r) → Fin (m + 1) //
        ∀ a, Fintype.card {i // f i = a} = Fin.snoc (α := fun _ => ℕ) k r a} *
      (if r = 0 then 1 else ((∑ a, k a) - m + 1) *
        ((∑ a, k a) + r - m + 1) ^ (r - 1)) := by
  classical
  let F := Finset.univ.filter (fun f : Fin ((∑ a, k a) + r) → Fin (m + 1) =>
    ∀ a, Fintype.card {i // f i = a} = Fin.snoc (α := fun _ => ℕ) k r a)
  have hf (f) (hf : f ∈ F) :=
    prefixAllocation_feasible k r f (Finset.mem_filter.mp hf).2 hp
  have hh := parkingPrefixAllocations_card hms F
    (fun f h => (hf f h).1) (fun f h => (hf f h).2)
  simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and,
    Fintype.card_subtype] using hh

/-- If [the cut m is at most the sum of the prescribed low counts k plus the remainder r](hyp:hm), then [a word has allocation bucket sizes k followed by r if and only if its positive preference counts in categories one through m equal k](goal). -/
-- @node: parkingAllocation_prescribed_iff
lemma parkingAllocation_prescribed_iff {m : ℕ} (k : Fin m → ℕ) (r : ℕ)
    (hm : m ≤ (∑ a, k a) + r) (w : Fin ((∑ a, k a) + r) → Fin ((∑ a, k a) + r)) :
    (∀ a, Fintype.card {i // parkingAllocation m w i = a} =
      Fin.snoc (α := fun _ => ℕ) k r a) ↔
    (∀ a : Fin m, preferenceCountsOfParking ((∑ a, k a) + r)
      (boundedParkingVector w) ⟨a.val, by omega⟩ = k a) := by
  constructor
  · intro hc a
    rw [← parkingAllocation_low_count hm w a]
    simpa using hc a.castSucc
  · intro hc
    have hl (a : Fin m) :
        Fintype.card {i // parkingAllocation m w i = a.castSucc} = k a := by
      rw [parkingAllocation_low_count hm w a]
      exact hc a
    have ht := Fintype.sum_fiberwise' (parkingAllocation m w) (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at ht
    rw [Fin.sum_univ_castSucc] at ht
    simp only [hl, Fintype.card_fin] at ht
    intro a
    refine Fin.lastCases ?_ (fun b => ?_) a
    · simp only [Fin.snoc_last]
      omega
    · simpa using hl b

open Classical in
/-- [The number of allocations of S + r labeled cars to low buckets with prescribed sizes k summing to S and a final bucket of size r, multiplied by r factorial and the product of the factorials of the low bucket sizes, equals (S + r) factorial](goal). -/
-- @node: prefixAllocation_card
lemma prefixAllocation_card {m : ℕ} (k : Fin m → ℕ) (r : ℕ) :
    Fintype.card {f : Fin ((∑ a, k a) + r) → Fin (m + 1) //
      ∀ a, Fintype.card {i // f i = a} = Fin.snoc (α := fun _ => ℕ) k r a} *
        (r.factorial * ∏ a, (k a).factorial) = ((∑ a, k a) + r).factorial := by
  classical
  have h := countFibers_prescribed_card (α := Fin ((∑ a, k a) + r)) (Fin.snoc (α := fun _ => ℕ) k r)
    (by simp [Fin.sum_univ_castSucc])
  simp only [Fintype.card_fin] at h
  convert h using 1
  congr 1
  · congr!
  · simp [Fin.prod_univ_castSucc, mul_comm]

/-- Suppose [the cut m does not exceed the sum S of the prescribed low counts k](hyp:hms), and [the first t low counts sum to at least t for every t up to m](hyp:hp). Then [the number of classic parking words with low preference counts k, multiplied by r factorial and the product of the factorials of k, equals (S + r) factorial times a completion factor that is one when r is zero and otherwise (S − m + 1) times (S + r − m + 1) raised to r − 1](goal). -/
-- @node: parkingPrefixCount_card_factorial
lemma parkingPrefixCount_card_factorial {m : ℕ} (k : Fin m → ℕ) (r : ℕ)
    (hms : m ≤ ∑ a, k a)
    (hp : ∀ t, t ≤ m → t ≤ ∑ a : Fin m, if a.val + 1 ≤ t then k a else 0) :
    ((classicParkingSet ((∑ a, k a) + r)).filter (fun w =>
      ∀ a : Fin m, preferenceCountsOfParking ((∑ a, k a) + r)
        (boundedParkingVector w) ⟨a.val, by omega⟩ = k a)).card *
        (r.factorial * ∏ a, (k a).factorial) =
      ((∑ a, k a) + r).factorial *
        (if r = 0 then 1 else ((∑ a, k a) - m + 1) *
          ((∑ a, k a) + r - m + 1) ^ (r - 1)) := by
  classical
  have hh := parkingPrescribedPrefix_card k r hms hp
  simp_rw [parkingAllocation_prescribed_iff k r (by omega)] at hh
  rw [hh]
  calc
    _ = (Fintype.card {f : Fin ((∑ a, k a) + r) → Fin (m + 1) //
        ∀ a, Fintype.card {i // f i = a} = Fin.snoc (α := fun _ => ℕ) k r a} *
          (r.factorial * ∏ a, (k a).factorial)) *
        (if r = 0 then 1 else ((∑ a, k a) - m + 1) *
          ((∑ a, k a) + r - m + 1) ^ (r - 1)) := by ring
    _ = _ := by rw [prefixAllocation_card]

/-- Suppose [the cut m does not exceed the sum S of the prescribed low counts k](hyp:hms), and [the first t low counts sum to at least t for every t up to m](hyp:hp). Then [under the canonical preference count measure for S + r cars, the probability of low counts k equals (S + r) factorial times the completion factor, divided by the product of (S + r + 1) raised to S + r − 1, r factorial, and all low count factorials; the completion factor is one when r is zero and otherwise (S − m + 1) times (S + r − m + 1) raised to r − 1](goal). -/
-- @node: canonicalPrescribedPrefix_mass
lemma canonicalPrescribedPrefix_mass {m : ℕ} (k : Fin m → ℕ) (r : ℕ)
    (hms : m ≤ ∑ a, k a)
    (hp : ∀ t, t ≤ m → t ≤ ∑ a : Fin m, if a.val + 1 ≤ t then k a else 0) :
    (preferenceCountMeasure ((∑ a, k a) + r)).real
        {q | ∀ a : Fin m, q ⟨a.val, by omega⟩ = k a} =
      ((((∑ a, k a) + r).factorial : ℝ) *
        (if r = 0 then 1 else (((∑ a, k a) - m + 1 : ℕ) : ℝ) *
          (((∑ a, k a) + r - m + 1 : ℕ) : ℝ) ^ (r - 1))) /
        (((((∑ a, k a) + r : ℕ) : ℝ) + 1) ^ ((∑ a, k a) + r - 1) *
          (r.factorial : ℝ) * ∏ a, ((k a).factorial : ℝ)) := by
  classical
  rw [canonicalCount_event_card]
  have hh := parkingPrefixCount_card_factorial k r hms hp
  have hreal := congrArg (fun t : ℕ => (t : ℝ)) hh
  simp only [Nat.cast_mul, Nat.cast_prod] at hreal
  have hc : ((if r = 0 then 1 else ((∑ a, k a) - m + 1) *
      ((∑ a, k a) + r - m + 1) ^ (r - 1) : ℕ) : ℝ) =
      (if r = 0 then 1 else (((∑ a, k a) - m + 1 : ℕ) : ℝ) *
        (((∑ a, k a) + r - m + 1 : ℕ) : ℝ) ^ (r - 1)) := by
    split_ifs <;> push_cast <;> rfl
  rw [hc] at hreal
  have hnorm : (((((∑ a, k a) + r : ℕ) : ℝ) + 1) ^
      ((∑ a, k a) + r - 1)) ≠ 0 := by positivity
  apply (div_eq_div_iff hnorm (mul_ne_zero (mul_ne_zero hnorm (by positivity))
    (by positivity))).2
  calc
    _ = (↑((classicParkingSet ((∑ a, k a) + r)).filter (fun w =>
        ∀ a : Fin m, preferenceCountsOfParking ((∑ a, k a) + r)
          (boundedParkingVector w) ⟨a.val, by omega⟩ = k a)).card *
        ((r.factorial : ℝ) * ∏ a, ((k a).factorial : ℝ))) *
          (((((∑ a, k a) + r : ℕ) : ℝ) + 1) ^ ((∑ a, k a) + r - 1)) := by
      simp only [mul_assoc]
      congr 1
      · congr 2
        ext w
        simp only [Finset.mem_filter]
      · ring
    _ = _ := by rw [hreal]

/-- If [the restricted block length m is at most the full count vector length n](hyp:hm) and [the prefix length t is at most m](hyp:ht), then [summing the first t counts within the restricted block equals the full vector's prefix count through t](goal). -/
-- @node: prefixCount_restrict_sum
lemma prefixCount_restrict_sum {n m : ℕ} (hm : m ≤ n) (k : CountVector n)
    (t : ℕ) (ht : t ≤ m) :
    (∑ a : Fin m, if a.val < t then k ⟨a.val, lt_of_lt_of_le a.isLt hm⟩ else 0) =
      prefixCount k t := by
  classical
  unfold prefixCount
  apply Finset.sum_bij_ne_zero (fun a _ _ => (⟨a.val, lt_of_lt_of_le a.isLt hm⟩ : Fin n))
  · intros; exact Finset.mem_univ _
  · intro a ha hza b hb hzb he
    exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
  · intro b hb hzb
    have hbt : b.val < t := by
      by_contra h
      simp [h] at hzb
    let a : Fin m := ⟨b.val, by omega⟩
    refine ⟨a, Finset.mem_univ _, ?_, ?_⟩
    · simpa [a, hbt] using hzb
    · exact Fin.ext rfl
  · intros; rfl

/-- Suppose [the cut m is at most the total number n of cars](hyp:hm), [the prescribed low counts k plus the remainder r sum to n](hyp:hn), [the cut does not exceed the sum S of the low counts](hyp:hms), and [the first t low counts sum to at least t for every t up to m](hyp:hp). Then [under the canonical preference count measure for n cars, the probability of low counts k equals n factorial times a completion factor, divided by the product of (n + 1) raised to n − 1, r factorial, and all low count factorials; the completion factor is one when r is zero and otherwise (S − m + 1) times (n − m + 1) raised to r − 1](goal). -/
-- @node: canonicalPrescribedPrefix_mass_of_total
lemma canonicalPrescribedPrefix_mass_of_total {n m : ℕ} (hm : m ≤ n)
    (k : Fin m → ℕ) (r : ℕ) (hn : (∑ a, k a) + r = n)
    (hms : m ≤ ∑ a, k a)
    (hp : ∀ t, t ≤ m → t ≤ ∑ a : Fin m, if a.val + 1 ≤ t then k a else 0) :
    (preferenceCountMeasure n).real
        {q | ∀ a : Fin m, q ⟨a.val, lt_of_lt_of_le a.isLt hm⟩ = k a} =
      ((n.factorial : ℝ) *
        (if r = 0 then 1 else (((∑ a, k a) - m + 1 : ℕ) : ℝ) *
          ((n - m + 1 : ℕ) : ℝ) ^ (r - 1))) /
        (((n : ℝ) + 1) ^ (n - 1) *
          (r.factorial : ℝ) * ∏ a, ((k a).factorial : ℝ)) := by
  subst n
  exact canonicalPrescribedPrefix_mass k r hms hp

end Papers.HawkesD75660b
