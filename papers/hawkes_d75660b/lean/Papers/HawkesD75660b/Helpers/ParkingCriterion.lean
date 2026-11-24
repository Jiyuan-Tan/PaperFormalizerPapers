module

public import Papers.HawkesD75660b.Helpers.ParkingPrefixes

/-! A prefix formulation of the manuscript's generalized sorted criterion.
The order predicate, unlike `GeneralizedParkingFunction`, also covers zero cars. -/

@[expose] public section
noncomputable section
namespace Papers.HawkesD75660b

/-- For [a vector of positive preferences](hyp:π) and [a threshold](hyp:t),
[the preference prefix count is the number of entries at most that threshold, counting repetitions](goal). -/
def parkingPrefix {r : ℕ} (π : PreferenceVector r) (t : ℕ) : ℕ :=
  (sortedPreferences π).countP (fun v => decide (v ≤ t))

/-- [The number of preferences at most a threshold equals the sum, over all cars,
of one if the car's preference is at most that threshold and zero otherwise](goal). -/
lemma parkingPrefix_eq_sum {r : ℕ} (π : PreferenceVector r) (t : ℕ) :
    parkingPrefix π t = ∑ i : Fin r, if (π i : ℕ) ≤ t then 1 else 0 := by
  classical
  rw [parkingPrefix, sortedPreferences, (List.mergeSort_perm _ _).countP_eq,
    parking_countP_ofFn]
  simp

/-- If [the number of cars is at most the number of spots](hyp:hrq),
[the sorted preference criterion holds exactly when every threshold up to the number of spots
is at most the number of unused spots plus the number of preferences at most that threshold](goal). -/
lemma generalizedParkingOrder_iff_prefix {r q : ℕ} (hrq : r ≤ q)
    (π : PreferenceVector r) :
    generalizedParkingOrder q π ↔ ∀ t, t ≤ q → t ≤ q - r + parkingPrefix π t := by
  classical
  let l := sortedPreferences π
  have hlen : l.length = r := by simp [l, sortedPreferences]
  constructor
  · intro h t ht
    by_cases hsmall : t ≤ q - r
    · omega
    let k := t - (q - r)
    have hk : k ≤ r := by dsimp [k]; omega
    have htake : (l.take k).countP (fun v => decide (v ≤ t)) = k := by
      apply Eq.trans (b := (l.take k).length) _ (by simp [hlen, hk])
      apply List.countP_eq_length.mpr
      intro v hv
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hv
      have hjk : j < k := lt_of_lt_of_le hj (List.length_take_le ..)
      have hjr : j < r := by omega
      have ho := h ⟨j, hjr⟩
      have hjl : j < l.length := by omega
      change l[j]?.getD 0 ≤ q - r + (j + 1) at ho
      rw [List.getElem?_eq_getElem hjl, Option.getD_some] at ho
      have hv' : l[j] = v := by simpa using heq
      rw [hv'] at ho
      simp only [decide_eq_true_eq]
      dsimp [k] at hjk
      omega
    have hsub := (List.take_sublist k l).countP_le (p := fun v => decide (v ≤ t))
    change t ≤ q - r + l.countP (fun v => decide (v ≤ t))
    rw [htake] at hsub
    dsimp [k] at hsub
    omega
  · intro h a
    have ha : a.val < l.length := by have := a.isLt; omega
    change l[a.val]?.getD 0 ≤ q - r + (a.val + 1)
    rw [List.getElem?_eq_getElem ha, Option.getD_some]
    by_contra hn
    let t := q - r + (a.val + 1)
    have ht : t ≤ q := by dsimp [t]; have := a.isLt; omega
    have hs : l.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) _
    have hdrop : (l.drop a.val).countP (fun v => decide (v ≤ t)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro v hv
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hv
      have hj' : a.val + j < l.length := by rw [List.length_drop] at hj; omega
      have hmono := hs.rel_get_of_le
        (a := ⟨a.val, ha⟩) (b := ⟨a.val + j, hj'⟩) (by simp)
      have hv' : l[a.val + j] = v := by simpa using heq
      simp only [List.get_eq_getElem, hv'] at hmono
      simp only [decide_eq_true_eq]
      dsimp [t]
      omega
    have hc := h t ht
    change t ≤ q - r + l.countP (fun v => decide (v ≤ t)) at hc
    have hsplit := List.countP_append (l₁ := l.take a.val) (l₂ := l.drop a.val)
      (p := fun v => decide (v ≤ t))
    rw [List.take_append_drop, hdrop, Nat.add_zero] at hsplit
    have hb := List.countP_le_length (l := l.take a.val)
      (p := fun v => decide (v ≤ t))
    have htaken := List.length_take_le a.val l
    dsimp [t] at hc hsplit hb
    omega

/-- Given [a nonnegative shift](hyp:m), [an initial block of preferences](hyp:low),
and [a remaining block of preferences](hyp:tail), [the appended preference vector consists
of the initial block followed by the remaining block with the shift added to every entry](goal). -/
def parkingAppend {s r : ℕ} (m : ℕ) (low : PreferenceVector s)
    (tail : PreferenceVector r) : PreferenceVector (s + r) :=
  Fin.append low (fun i => (⟨m + (tail i : ℕ), by have := (tail i).pos; omega⟩ : ℕ+))

/-- [The prefix count of an appended preference vector at a threshold equals the initial
block's prefix count plus the number of remaining preferences whose shifted values are at most that threshold](goal). -/
lemma parkingPrefix_append {s r : ℕ} (m t : ℕ) (low : PreferenceVector s)
    (tail : PreferenceVector r) :
    parkingPrefix (parkingAppend m low tail) t =
      parkingPrefix low t + ∑ i : Fin r, if m + (tail i : ℕ) ≤ t then 1 else 0 := by
  classical
  have hl (i : Fin s) : parkingAppend m low tail (Fin.castAdd r i) = low i :=
    Fin.append_left _ _ i
  have hr (i : Fin r) : (parkingAppend m low tail (Fin.natAdd s i) : ℕ) =
      m + (tail i : ℕ) := congrArg (fun x : ℕ+ => (x : ℕ)) (Fin.append_right _ _ i)
  simp only [parkingPrefix_eq_sum]
  rw [Fin.sum_univ_add]
  simp only [hl, hr]

/-- If [every initial preference is at most the shift](hyp:hlow), [the appended vector's
prefix count at the shift plus a threshold equals the initial block's size plus the
remaining block's prefix count at that threshold](goal). -/
lemma parkingPrefix_append_shift {s r : ℕ} (m u : ℕ) (low : PreferenceVector s)
    (tail : PreferenceVector r) (hlow : ∀ i, (low i : ℕ) ≤ m) :
    parkingPrefix (parkingAppend m low tail) (m + u) = s + parkingPrefix tail u := by
  classical
  rw [parkingPrefix_append, parkingPrefix_eq_sum, parkingPrefix_eq_sum]
  have hl : ∀ i, (low i : ℕ) ≤ m + u := fun i => (hlow i).trans (by omega)
  simp [hl]

/-- Suppose [the shift is at most the initial block's size](hyp:hms),
[all initial preferences are at most the shift](hyp:hlow), and [at every threshold up to
the shift there are at least that many initial preferences at most the threshold](hyp:hprefix).
Then [the appended vector satisfies the sorted criterion with as many spots as total cars
if and only if the remaining block satisfies it with that many spots minus the shift](goal). -/
lemma parkingAppend_order_iff {s r m : ℕ} (hms : m ≤ s)
    (low : PreferenceVector s) (tail : PreferenceVector r)
    (hlow : ∀ i, (low i : ℕ) ≤ m)
    (hprefix : ∀ t, t ≤ m → t ≤ parkingPrefix low t) :
    generalizedParkingOrder (s + r) (parkingAppend m low tail) ↔
      generalizedParkingOrder (s + r - m) tail := by
  rw [generalizedParkingOrder_iff_prefix (Nat.le_refl _),
    generalizedParkingOrder_iff_prefix (by omega : r ≤ s + r - m)]
  simp only [Nat.sub_self, Nat.zero_add]
  constructor
  · intro h u hu
    have h' := h (m + u) (by omega)
    rw [parkingPrefix_append_shift m u low tail hlow] at h'
    omega
  · intro h t ht
    by_cases htm : t ≤ m
    · rw [parkingPrefix_append]
      exact (hprefix t htm).trans (Nat.le_add_right _ _)
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (by omega : m ≤ t)
      rw [parkingPrefix_append_shift m u low tail hlow]
      have h' := h u (by omega)
      omega

end Papers.HawkesD75660b

