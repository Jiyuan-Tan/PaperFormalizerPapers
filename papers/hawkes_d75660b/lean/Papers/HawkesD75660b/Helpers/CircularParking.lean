module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Tactic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Fintype.BigOperators

/-! Circular parking by removing the first available spot in cyclic order.
Spots are `Fin (q+1)`; subtraction measures the forward cyclic distance. -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace Papers.HawkesD75660b
open Classical

/-- For [a set of available spots](hyp:E), [a preferred spot](hyp:p), and
[the guarantee that at least one spot is available](hyp:h), the
[chosen spot](goal) is the first available spot encountered clockwise from the preference. -/
def circularChoice {q : ℕ} (E : Finset (Fin (q + 1))) (p : Fin (q + 1))
    (h : E.Nonempty) : Fin (q + 1) :=
  p + (E.image (fun e => e - p)).min' (h.image _)

/-- If [at least one spot is available](hyp:h), then [the spot chosen clockwise
from any preference belongs to the available set](goal). -/
lemma circularChoice_mem {q : ℕ} (E : Finset (Fin (q + 1))) (p : Fin (q + 1))
    (h : E.Nonempty) : circularChoice E p h ∈ E := by
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp
    (Finset.min'_mem (E.image (fun e => e - p)) (h.image _))
  unfold circularChoice
  rw [← heq, add_comm p, sub_add_cancel]
  exact he

/-- For [a set of available spots](hyp:E) and [one car's preferred spot](hyp:p),
the [remaining available set](goal) is obtained by removing the first available
spot clockwise from the preference, if one exists; an empty set remains empty. -/
def circularStep {q : ℕ} (E : Finset (Fin (q + 1))) (p : Fin (q + 1)) :
    Finset (Fin (q + 1)) :=
  if h : E.Nonempty then E.erase (circularChoice E p h) else E

/-- [One arrival reduces the number of available spots by one, with subtraction
truncated at zero](goal). -/
lemma circularStep_card {q : ℕ} (E : Finset (Fin (q + 1))) (p : Fin (q + 1)) :
    (circularStep E p).card = E.card - 1 := by
  unfold circularStep
  split_ifs with h
  · exact Finset.card_erase_of_mem (circularChoice_mem E p h)
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

/-- [Every spot available after one arrival was available before that arrival](goal). -/
lemma circularStep_subset {q : ℕ} (E : Finset (Fin (q + 1))) (p : Fin (q + 1)) :
    circularStep E p ⊆ E := by
  unfold circularStep
  split_ifs
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

/-- Starting from [an available set](hyp:E), the [parking procedure for an ordered
list of preferences](goal) [leaves the set unchanged when no cars arrive](step:1)
and [otherwise parks the first car and processes the remaining cars in order](step:2). -/
def circularRun {q : ℕ} (E : Finset (Fin (q + 1))) :
    List (Fin (q + 1)) → Finset (Fin (q + 1))
  | [] => E
  | p :: ps => circularRun (circularStep E p) ps

/-- [The number of spots left available after processing a list of cars equals
the initial number minus the list length, with subtraction truncated at zero](goal). -/
lemma circularRun_card {q : ℕ} (ps : List (Fin (q + 1)))
    (E : Finset (Fin (q + 1))) :
    (circularRun E ps).card = E.card - ps.length := by
  induction ps generalizing E with
  | nil => simp [circularRun]
  | cons p ps ih =>
    simp only [circularRun, ih, circularStep_card, List.length_cons]
    omega

/-- [Every spot available after processing a list of cars belongs to the initial
available set](goal). -/
lemma circularRun_subset {q : ℕ} (ps : List (Fin (q + 1)))
    (E : Finset (Fin (q + 1))) : circularRun E ps ⊆ E := by
  induction ps generalizing E with
  | nil => exact Finset.Subset.refl _
  | cons p ps ih => exact (ih _).trans (circularStep_subset E p)

/-- For [preferences indexed by car arrival order](hyp:w), the [empty spots after
parking](goal) are those left by processing all cars on an initially empty circle. -/
def circularEmpty {r q : ℕ} (w : Fin r → Fin (q + 1)) : Finset (Fin (q + 1)) :=
  circularRun Finset.univ (List.ofFn w)

/-- [Parking r cars on an initially empty circle of q + 1 spots leaves q + 1 minus r
empty spots, with subtraction truncated at zero](goal). -/
lemma circularEmpty_card {r q : ℕ} (w : Fin r → Fin (q + 1)) :
    (circularEmpty w).card = q + 1 - r := by
  simp [circularEmpty, circularRun_card]

/-- For [a number of cars](hyp:r) and [one less than the number of circular spots](hyp:q),
a [pointed parking configuration](goal) consists of a preference word together
with a distinguished spot that remains empty after parking. -/
abbrev CircularPointed (r q : ℕ) :=
  Σ w : Fin r → Fin (q + 1), {e // e ∈ circularEmpty w}

/-- [The number of preference words for r cars on q + 1 circular spots, each paired
with a distinguished surviving empty spot, is (q + 1) to the power r times
q + 1 minus r, with subtraction truncated at zero](goal). -/
lemma circularPointed_card (r q : ℕ) :
    Fintype.card (CircularPointed r q) = (q + 1) ^ r * (q + 1 - r) := by
  simp [CircularPointed, Fintype.card_sigma, Fintype.card_subtype, circularEmpty_card]

/-- For [a circular displacement](hyp:a) and [a set of spots](hyp:E), the
[rotated set](goal) is obtained by adding the displacement to every spot modulo
the number of spots. -/
def rotateSpots {q : ℕ} (a : Fin (q + 1)) (E : Finset (Fin (q + 1))) :=
  E.image (fun e => e + a)

/-- If [the available set is nonempty](hyp:h), then [rotating both the available
set and the preference rotates the chosen spot by the same displacement](goal). -/
lemma circularChoice_rotate {q : ℕ} (a p : Fin (q + 1))
    (E : Finset (Fin (q + 1))) (h : E.Nonempty) :
    circularChoice (rotateSpots a E) (p + a) (h.image _) =
      circularChoice E p h + a := by
  have he : (rotateSpots a E).image (fun e => e - (p + a)) =
      E.image (fun e => e - p) := by
    simp only [rotateSpots, Finset.image_image, Function.comp_def, add_sub_add_right_eq_sub]
  unfold circularChoice
  simp only [he]
  abel

/-- [Rotating the available set and a car's preference before parking gives the
rotation of the available set left after parking that car](goal). -/
lemma circularStep_rotate {q : ℕ} (a p : Fin (q + 1))
    (E : Finset (Fin (q + 1))) :
    circularStep (rotateSpots a E) (p + a) = rotateSpots a (circularStep E p) := by
  by_cases h : E.Nonempty
  · have hr : (rotateSpots a E).Nonempty := h.image _
    rw [circularStep, dif_pos hr, circularChoice_rotate a p E h,
      circularStep, dif_pos h]
    exact (Finset.image_erase (fun x y hxy => add_right_cancel hxy) E _).symm
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst E
    simp [circularStep, rotateSpots]

/-- [Rotating the initial available set and every preference in an arrival list
rotates the available set left after all arrivals by the same displacement](goal). -/
lemma circularRun_rotate {q : ℕ} (a : Fin (q + 1))
    (ps : List (Fin (q + 1))) (E : Finset (Fin (q + 1))) :
    circularRun (rotateSpots a E) (ps.map (fun p => p + a)) =
      rotateSpots a (circularRun E ps) := by
  induction ps generalizing E with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, circularRun, circularStep_rotate, ih]

/-- [Rotating the set of all circular spots leaves that set unchanged](goal). -/
lemma rotateSpots_univ {q : ℕ} (a : Fin (q + 1)) :
    rotateSpots a Finset.univ = Finset.univ := by
  ext e
  simp only [rotateSpots, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact ⟨e - a, sub_add_cancel e a⟩

/-- [Adding a common circular displacement to every car's preference rotates
the set of spots left empty by that same displacement](goal). -/
lemma circularEmpty_rotate {r q : ℕ} (a : Fin (q + 1))
    (w : Fin r → Fin (q + 1)) :
    circularEmpty (fun i => w i + a) = rotateSpots a (circularEmpty w) := by
  unfold circularEmpty
  have he : List.ofFn (fun i => w i + a) = (List.ofFn w).map (fun p => p + a) :=
    by simpa only [Function.comp_def] using
      (List.map_ofFn (f := w) (g := fun p : Fin (q + 1) => p + a)).symm
  rw [he]
  conv_lhs => rw [← rotateSpots_univ a]
  exact circularRun_rotate a _ _

/-- For [a number of cars](hyp:r) and [one less than the number of circular spots](hyp:q),
the [last-spot slice](goal) consists of preference words whose parking outcome
leaves spot q empty. -/
abbrev CircularLastSlice (r q : ℕ) :=
  {w : Fin r → Fin (q + 1) // Fin.last q ∈ circularEmpty w}

/-- [A spot shifted by a circular displacement remains empty under the shifted
preferences exactly when the original spot remains empty under the original preferences](goal). -/
lemma mem_circularEmpty_rotate {r q : ℕ} (w : Fin r → Fin (q + 1))
    (e a : Fin (q + 1)) :
    e + a ∈ circularEmpty (fun i => w i + a) ↔ e ∈ circularEmpty w := by
  rw [circularEmpty_rotate]
  change e + a ∈ (circularEmpty w).image (fun x => x + a) ↔ _
  simp only [Finset.mem_image, add_left_inj, exists_eq_right]

/-- For [a number of cars](hyp:r) and [one less than the number of circular spots](hyp:q),
the [bijection between pointed configurations and pairs of a last-spot word and
a circular spot](goal) rotates the distinguished empty spot to spot q and
records its original location; the inverse rotates back to the recorded location. -/
def circularPointedEquiv (r q : ℕ) :
    CircularPointed r q ≃ CircularLastSlice r q × Fin (q + 1) where
  toFun x := (⟨fun i => x.1 i + (Fin.last q - x.2.val), by
    have h := (mem_circularEmpty_rotate x.1 x.2.val (Fin.last q - x.2.val)).mpr
      x.2.property
    simpa only [← add_sub_assoc, add_sub_cancel_left] using h⟩, x.2.val)
  invFun x := ⟨fun i => x.1.val i + (x.2 - Fin.last q), ⟨x.2, by
    have h := (mem_circularEmpty_rotate x.1.val (Fin.last q) (x.2 - Fin.last q)).mpr
      x.1.property
    simpa only [← add_sub_assoc, add_sub_cancel_left] using h⟩⟩
  left_inv x := by
    obtain ⟨w, e, he⟩ := x
    dsimp
    have hf : (fun i => (w i + (Fin.last q - e)) + (e - Fin.last q)) = w := by
      funext i
      abel
    apply Sigma.ext hf
    apply (Subtype.heq_iff_coe_eq (fun x => by dsimp only; rw [hf])).mpr
    rfl
  right_inv x := by
    obtain ⟨⟨w, hw⟩, e⟩ := x
    dsimp
    congr 1
    apply Subtype.ext
    funext i
    abel

/-- [The number of preference words leaving spot q empty, multiplied by q + 1,
equals (q + 1) to the power r times q + 1 minus r, with subtraction truncated at zero](goal). -/
lemma circularLastSlice_mul (r q : ℕ) :
    Fintype.card (CircularLastSlice r q) * (q + 1) =
      (q + 1) ^ r * (q + 1 - r) := by
  have h := Fintype.card_congr (circularPointedEquiv r q)
  rw [circularPointed_card, Fintype.card_prod, Fintype.card_fin] at h
  exact h.symm

/-- If [the number r of cars is positive](hyp:hr), then [the number of preference
words leaving spot q empty equals (q + 1 minus r) times (q + 1) to the power
(r minus 1), with subtraction truncated at zero](goal). -/
lemma circularLastSlice_card {r q : ℕ} (hr : 0 < r) :
    Fintype.card (CircularLastSlice r q) = (q + 1 - r) * (q + 1) ^ (r - 1) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos q)
  calc
    Fintype.card (CircularLastSlice r q) * (q + 1) =
        (q + 1) ^ r * (q + 1 - r) := circularLastSlice_mul r q
    _ = ((q + 1 - r) * (q + 1) ^ (r - 1)) * (q + 1) := by
      have hp : (q + 1) ^ r = (q + 1) ^ (r - 1) * (q + 1) := by
        nth_rw 1 [show r = (r - 1) + 1 from by omega]
        exact pow_succ _ _
      rw [hp]
      ac_rfl

/-- If [a car's preferred spot is available](hyp:hp), then [the car chooses that
preferred spot](goal). -/
lemma circularChoice_of_mem {q : ℕ} (E : Finset (Fin (q + 1)))
    (p : Fin (q + 1)) (hp : p ∈ E) : circularChoice E p ⟨p, hp⟩ = p := by
  have hzero : (E.image (fun e => e - p)).min' ((show E.Nonempty from ⟨p, hp⟩).image _) = 0 := by
    apply (Finset.min'_eq_iff _ _ _).mpr
    constructor
    · exact Finset.mem_image.mpr ⟨p, hp, sub_self p⟩
    · intro b hb
      exact Fin.zero_le b
  simp only [circularChoice, hzero, add_zero]

/-- [A car's preferred spot is unavailable after that car's arrival](goal). -/
lemma preference_not_mem_circularStep {q : ℕ} (E : Finset (Fin (q + 1)))
    (p : Fin (q + 1)) : p ∉ circularStep E p := by
  by_cases hp : p ∈ E
  · rw [circularStep, dif_pos ⟨p, hp⟩, circularChoice_of_mem E p hp]
    exact Finset.notMem_erase _ _
  · exact fun h => hp (circularStep_subset E p h)

/-- If [a spot occurs as a preference in the arrival list](hyp:hp), then [that
spot is unavailable after processing the entire list](goal). -/
lemma preference_not_mem_circularRun {q : ℕ} (ps : List (Fin (q + 1)))
    (E : Finset (Fin (q + 1))) (p : Fin (q + 1)) (hp : p ∈ ps) :
    p ∉ circularRun E ps := by
  induction ps generalizing E with
  | nil => simp at hp
  | cons a ps ih =>
    rcases List.mem_cons.mp hp with h | h
    · subst p
      exact fun he => preference_not_mem_circularStep E a (circularRun_subset ps _ he)
    · exact ih _ h

/-- [Every car's preference in a word leaving spot q empty has numerical label
strictly less than q](goal). -/
lemma circularLastSlice_preference_lt {r q : ℕ} (w : CircularLastSlice r q)
    (i : Fin r) : (w.val i).val < q := by
  have hne : w.val i ≠ Fin.last q := by
    intro he
    have hn := preference_not_mem_circularRun (List.ofFn w.val) Finset.univ
      (w.val i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact hn (he.symm ▸ w.property)
  have hv := (w.val i).isLt
  have hnval : (w.val i).val ≠ q := fun h => hne (Fin.ext h)
  omega

/-- For [a number of cars](hyp:r) and [a preference alphabet of q spots](hyp:q),
the [last-avoiding words](goal) are preference words using labels zero through
q minus one that leave spot q empty when parked on the circle of q + 1 spots. -/
abbrev LastAvoidingWords (r q : ℕ) :=
  {w : Fin r → Fin q // Fin.last q ∈ circularEmpty (fun i => (w i).castSucc)}

/-- For [a number of cars](hyp:r) and [a smaller alphabet size](hyp:q), the
[bijection between the last-spot slice and last-avoiding words](goal) restricts
preferences to labels below q; its inverse views those labels on the circle of q + 1 spots. -/
def circularLastSliceEquiv (r q : ℕ) : CircularLastSlice r q ≃ LastAvoidingWords r q where
  toFun w := ⟨fun i => ⟨(w.val i).val, circularLastSlice_preference_lt w i⟩, by
    have he : (fun i => (⟨(w.val i).val, circularLastSlice_preference_lt w i⟩ : Fin q).castSucc)
        = w.val := by funext i; exact Fin.ext rfl
    rw [he]
    exact w.property⟩
  invFun w := ⟨fun i => (w.val i).castSucc, w.property⟩
  left_inv w := by apply Subtype.ext; funext i; exact Fin.ext rfl
  right_inv w := by apply Subtype.ext; funext i; exact Fin.ext rfl

/-- If [the number r of cars is positive](hyp:hr), then [the number of preference
words using labels below q and leaving spot q empty equals (q + 1 minus r)
times (q + 1) to the power (r minus 1), with subtraction truncated at zero](goal). -/
lemma lastAvoidingWords_card {r q : ℕ} (hr : 0 < r) :
    Fintype.card (LastAvoidingWords r q) = (q + 1 - r) * (q + 1) ^ (r - 1) := by
  rw [← Fintype.card_congr (circularLastSliceEquiv r q)]
  exact circularLastSlice_card hr

/-- If [a comparison spot is available](hyp:he), then [the forward cyclic distance
from the preference to the chosen spot is no greater than the distance to that
comparison spot](goal). -/
lemma circularChoice_distance_le {q : ℕ} (E : Finset (Fin (q + 1)))
    (p e : Fin (q + 1)) (he : e ∈ E) :
    circularChoice E p ⟨e, he⟩ - p ≤ e - p := by
  have h := Finset.min'_le (E.image (fun x => x - p)) (e - p)
    (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  simpa only [circularChoice, add_sub_cancel_left] using h

/-- If [spot q is available](hyp:he), then [the chosen spot has label at least
as large as the preference, so parking does not wrap around the circle](goal). -/
lemma circularChoice_no_wrap {q : ℕ} (E : Finset (Fin (q + 1)))
    (p : Fin (q + 1)) (he : Fin.last q ∈ E) :
    p ≤ circularChoice E p ⟨Fin.last q, he⟩ := by
  have h := circularChoice_distance_le E p (Fin.last q) he
  have hl : (Fin.last q).val = q := rfl
  fin_omega

/-- If [a comparison spot is available](hyp:he) and [the preference is no larger
than that spot](hyp:hp), then [the chosen spot is no larger than the comparison spot](goal). -/
lemma circularChoice_le_of_le {q : ℕ} (E : Finset (Fin (q + 1)))
    (p e : Fin (q + 1)) (he : e ∈ E) (hp : p ≤ e) :
    circularChoice E p ⟨e, he⟩ ≤ e := by
  have h := circularChoice_distance_le E p e he
  fin_omega

/-- If [at least one spot is available](hyp:h), then [the number of available
spots satisfying a given property before an arrival equals the number afterward
plus one if the chosen spot satisfies the property, and plus zero otherwise](goal). -/
lemma circularStep_filter_card {q : ℕ} (E : Finset (Fin (q + 1)))
    (p : Fin (q + 1)) (h : E.Nonempty) (P : Fin (q + 1) → Prop) [DecidablePred P] :
    ((circularStep E p).filter P).card +
        (if P (circularChoice E p h) then 1 else 0) = (E.filter P).card := by
  rw [circularStep, dif_pos h]
  have hf : (E.erase (circularChoice E p h)).filter P =
      (E.filter P).erase (circularChoice E p h) := by ext x; simp; tauto
  rw [hf]
  by_cases hp : P (circularChoice E p h)
  · rw [if_pos hp]
    exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨circularChoice_mem E p h, hp⟩)
  · simp [hp]

/-- If [a spot remains available after all arrivals](hyp:he), then [the initial
number of available spots with larger labels is at most the final number of
such spots plus the number of cars whose preferences have larger labels](goal). -/
lemma circularRun_suffix_occupied {q : ℕ} (ps : List (Fin (q + 1)))
    (E : Finset (Fin (q + 1))) (e : Fin (q + 1))
    (he : e ∈ circularRun E ps) :
    (E.filter (fun x => e < x)).card ≤
      ((circularRun E ps).filter (fun x => e < x)).card +
        ps.countP (fun p => decide (e < p)) := by
  induction ps generalizing E with
  | nil => simp [circularRun]
  | cons p ps ih =>
    have heE := circularRun_subset (p :: ps) E he
    have hi := ih (circularStep E p) he
    have hc := circularStep_filter_card E p ⟨e, heE⟩ (fun x => e < x)
    have hb : e < circularChoice E p ⟨e, heE⟩ → e < p := by
      intro h
      by_contra hn
      have := circularChoice_le_of_le E p e heE (le_of_not_gt hn)
      exact (not_lt_of_ge this) h
    simp only [circularRun, List.countP_cons, decide_eq_true_eq] at *
    split_ifs at hc ⊢ <;> omega

/-- If [spot q remains available after all arrivals](hyp:he), then [the number
of cars preferring labels above any threshold plus the final number of available
spots above that threshold is at most the initial number of available spots above it](goal). -/
lemma circularRun_suffix_preferences {q : ℕ} (ps : List (Fin (q + 1)))
    (E : Finset (Fin (q + 1))) (t : Fin (q + 1))
    (he : Fin.last q ∈ circularRun E ps) :
    ps.countP (fun p => decide (t < p)) +
      ((circularRun E ps).filter (fun x => t < x)).card ≤
        (E.filter (fun x => t < x)).card := by
  induction ps generalizing E with
  | nil => simp [circularRun]
  | cons p ps ih =>
    have heE := circularRun_subset (p :: ps) E he
    have hi := ih (circularStep E p) he
    have hc := circularStep_filter_card E p ⟨Fin.last q, heE⟩ (fun x => t < x)
    have hb := circularChoice_no_wrap E p heE
    simp only [circularRun, List.countP_cons, decide_eq_true_eq]
    split_ifs at hc ⊢ <;> omega

/-- [The number of circular spots whose labels exceed a threshold t is q minus t](goal). -/
lemma circular_suffix_card {q : ℕ} (t : Fin (q + 1)) :
    (Finset.univ.filter (fun x : Fin (q + 1) => t < x)).card = q - t.val := by
  have he : Finset.univ.filter (fun x : Fin (q + 1) => t < x) = Finset.Ioi t := by
    ext x
    simp
  rw [he, Fin.card_Ioi]
  simp

/-- If [the number of cars is at most q](hyp:hrq), then [spot q remains empty
exactly when, for every threshold t below q, the number of cars preferring a
label greater than t is at most q minus 1 minus t](goal).

The bound on the number of cars ensures there is a surviving hole to use as
barrier in the reverse implication. -/
lemma circularEmpty_last_iff_suffix {r q : ℕ} (hrq : r ≤ q)
    (w : Fin r → Fin (q + 1)) :
    Fin.last q ∈ circularEmpty w ↔ ∀ t : Fin q,
      (List.ofFn w).countP (fun p => decide (t.castSucc < p)) ≤ q - 1 - t.val := by
  constructor
  · intro h t
    have hi := circularRun_suffix_preferences (List.ofFn w) Finset.univ t.castSucc h
    rw [circular_suffix_card] at hi
    have hm : Fin.last q ∈ (circularEmpty w).filter (fun x => t.castSucc < x) := by
      exact Finset.mem_filter.mpr ⟨h, t.isLt⟩
    have hp := Finset.card_pos.mpr ⟨Fin.last q, hm⟩
    change 0 < ((circularRun Finset.univ (List.ofFn w)).filter
      (fun x => t.castSucc < x)).card at hp
    have ht := t.isLt
    simp only [Fin.val_castSucc] at hi
    omega
  · intro h
    have hn : (circularEmpty w).Nonempty := by
      apply Finset.card_pos.mp
      rw [circularEmpty_card]
      omega
    let e := (circularEmpty w).max' hn
    have he : e ∈ circularEmpty w := Finset.max'_mem _ _
    by_contra hlast
    have hel : e.val < q := by
      have hv := e.isLt
      have hne : e ≠ Fin.last q := fun heq => hlast (heq ▸ he)
      have hnval : e.val ≠ q := fun hv => hne (Fin.ext hv)
      omega
    have hz : (circularEmpty w).filter (fun x => e < x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx, hgt⟩ := Finset.mem_filter.mp hx
      exact (not_lt_of_ge (Finset.le_max' _ _ hx)) hgt
    have hi := circularRun_suffix_occupied (List.ofFn w) Finset.univ e he
    change (Finset.univ.filter (fun x => e < x)).card ≤
      ((circularEmpty w).filter (fun x => e < x)).card + _ at hi
    rw [circular_suffix_card, hz, Finset.card_empty, Nat.zero_add] at hi
    have hb := h ⟨e.val, hel⟩
    have heq : (⟨e.val, hel⟩ : Fin q).castSucc = e := Fin.ext rfl
    rw [heq] at hb
    change (List.ofFn w).countP (fun p => decide (e < p)) ≤ q - 1 - e.val at hb
    omega

end Papers.HawkesD75660b






