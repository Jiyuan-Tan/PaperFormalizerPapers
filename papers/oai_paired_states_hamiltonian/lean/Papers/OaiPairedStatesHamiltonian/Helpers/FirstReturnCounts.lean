module

public import Papers.OaiPairedStatesHamiltonian.Helpers.FirstReturn
public import Mathlib.Data.Fintype.Card

/-! Exact orbit counts for first-return restrictions. An original orbit is lost
precisely when it contains no retained point, including singleton orbits. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

variable {D : Type} [Fintype D] (p : Equiv.Perm D) (U : Set D)

-- @node: firstReturn_step_sameCycle
/-- [A retained point and its first return belong to the same cycle of the
original permutation](goal). -/
lemma firstReturn_step_sameCycle (d : U) :
    p.SameCycle d.val (firstReturnPerm p U d).val := by
  obtain ⟨n, hn, he, hfirst⟩ := Classical.choose_spec (exists_firstReturnPerm p U) d
  change (firstReturnPerm p U d).val = (p ^ n) d.val at he
  exact ⟨(n : ℤ), by simpa only [zpow_natCast] using he.symm⟩

-- @node: sameCycle_firstReturnPerm_iff
/-- [Two retained points lie in the same cycle of the first-return permutation
if and only if they lie in the same cycle of the original permutation](goal). -/
lemma sameCycle_firstReturnPerm_iff (a b : U) :
    (firstReturnPerm p U).SameCycle a b ↔ p.SameCycle a.val b.val := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Equiv.Perm.SameCycle.refl p a.val
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans (firstReturn_step_sameCycle p U _)
  · exact sameCycle_firstReturnPerm p U a b

-- @node: orbitHits
/-- For [a permutation of a finite set](hyp:p), [a retained subset](hyp:U), and
[one of the permutation's orbits](hyp:o), [the orbit meets the retained
subset](goal) means that some retained point belongs to that orbit. -/
noncomputable def orbitHits (o : orbitType p) : Prop :=
  ∃ d : U, orbitOf p d.val = o

-- @node: firstReturnOrbitMap
/-- For [a permutation of a finite set](hyp:p) and [a retained subset](hyp:U),
[the map from first-return orbits to original orbits](goal) assigns to each
first-return orbit the original orbit containing its points. -/
noncomputable def firstReturnOrbitMap : orbitType (firstReturnPerm p U) → orbitType p :=
  Quotient.map Subtype.val (fun {a b} h => (sameCycle_firstReturnPerm_iff p U a b).mp h)

-- @node: firstReturnOrbitMap_injective
/-- [Distinct orbits of the first-return permutation map to distinct orbits of
the original permutation](goal). -/
lemma firstReturnOrbitMap_injective : Function.Injective (firstReturnOrbitMap p U) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      intro h
      exact Quotient.sound ((sameCycle_firstReturnPerm_iff p U a b).mpr (Quotient.exact h))

-- @node: firstReturnOrbitEquiv
/-- For [a permutation of a finite set](hyp:p) and [a retained subset](hyp:U),
[the correspondence between first-return orbits and original orbits meeting the
retained subset](goal) is the bijection sending each first-return orbit to the
original orbit containing it. -/
noncomputable def firstReturnOrbitEquiv :
    orbitType (firstReturnPerm p U) ≃ {o : orbitType p // orbitHits p U o} :=
  Equiv.ofBijective
    (fun o => ⟨firstReturnOrbitMap p U o, by
      induction o using Quotient.inductionOn with
      | h d => exact ⟨d, rfl⟩⟩)
    ⟨fun a b h => firstReturnOrbitMap_injective p U (congrArg Subtype.val h), by
      rintro ⟨o, d, hd⟩
      exact ⟨orbitOf (firstReturnPerm p U) d, Subtype.ext hd⟩⟩

-- @node: card_firstReturn_orbits
/-- [The number of first-return orbits equals the number of original orbits
that meet the retained subset](goal). -/
lemma card_firstReturn_orbits :
    Nat.card (orbitType (firstReturnPerm p U)) = Nat.card {o : orbitType p // orbitHits p U o} :=
  Nat.card_congr (firstReturnOrbitEquiv p U)

-- @node: card_firstReturn_orbits_add_missing
/-- [The number of first-return orbits plus the number of original orbits that
miss the retained subset equals the total number of original orbits](goal). -/
lemma card_firstReturn_orbits_add_missing :
    Nat.card (orbitType (firstReturnPerm p U)) +
      Nat.card {o : orbitType p // ¬ orbitHits p U o} = Nat.card (orbitType p) := by
  letI : Fintype (orbitType p) := Fintype.ofFinite _
  letI : Fintype {o : orbitType p // orbitHits p U o} := Fintype.ofFinite _
  letI : Fintype {o : orbitType p // ¬ orbitHits p U o} := Fintype.ofFinite _
  rw [card_firstReturn_orbits]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl]
  have hle : Fintype.card {o : orbitType p // orbitHits p U o} ≤ Fintype.card (orbitType p) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  omega

-- @node: firstReturnPerm_apply_of_spec
/-- If [the number of steps is positive](hyp:hn), [iteration for that many steps
from a retained point ends in the retained subset](hyp:hmem), and [no earlier
positive iterate is retained](hyp:hfirst), then [that iterate is the point's
first return](goal). -/
lemma firstReturnPerm_apply_of_spec (d : U) (n : ℕ) (hn : 0 < n)
    (hmem : (p ^ n) d.val ∈ U)
    (hfirst : ∀ m, 0 < m → m < n → (p ^ m) d.val ∉ U) :
    (firstReturnPerm p U d).val = (p ^ n) d.val := by
  obtain ⟨k, hk, he, hmin⟩ := Classical.choose_spec (exists_firstReturnPerm p U) d
  have hnk : n = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hmin n hn h hmem
    · exact hfirst k hk h (he ▸ (firstReturnPerm p U d).property)
  rwa [hnk]

-- @node: firstReturnPerm_unique
/-- If [a permutation of the retained subset sends every point to a positive
iterate of the original permutation with no earlier positive retained
iterate](hyp:hq), then [it equals the first-return permutation](goal). -/
lemma firstReturnPerm_unique (q : Equiv.Perm U)
    (hq : ∀ d : U, ∃ n : ℕ, 0 < n ∧ (q d).val = (p ^ n) d.val ∧
      ∀ m, 0 < m → m < n → (p ^ m) d.val ∉ U) : q = firstReturnPerm p U := by
  ext d
  obtain ⟨n, hn, he, hm⟩ := hq d
  exact he.trans (firstReturnPerm_apply_of_spec p U d n hn (he ▸ (q d).property) hm).symm

-- @node: orbit_notHits_iff
/-- [An original orbit misses the retained subset if and only if every point
in that orbit lies outside the retained subset](goal). -/
lemma orbit_notHits_iff (o : orbitType p) :
    ¬ orbitHits p U o ↔ ∀ d : D, orbitOf p d = o → d ∉ U := by
  constructor
  · intro h d hd hu
    exact h ⟨⟨d, hu⟩, hd⟩
  · rintro h ⟨d, hd⟩
    exact h d.val hd d.property

-- @node: orbit_notHits_delete_one
/-- [An orbit misses all points other than a designated point if and only if
that point is fixed by the permutation and the orbit is its singleton
orbit](goal). -/
lemma orbit_notHits_delete_one (a : D) (o : orbitType p) :
    ¬ orbitHits p {d | d ≠ a} o ↔ p a = a ∧ o = orbitOf p a := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Quotient.exists_rep o
    have hda : d = a := by
      by_contra hne
      exact h ⟨⟨d, hne⟩, hd⟩
    subst d
    refine ⟨?_, hd.symm⟩
    by_contra hne
    have hpa : orbitOf p (p a) = orbitOf p a :=
      Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl p a))
    exact h ⟨⟨p a, hne⟩, hpa.trans hd⟩
  · rintro ⟨hfix, rfl⟩ ⟨d, hd⟩
    exact d.property ((Quotient.exact hd : p.SameCycle d.val a).eq_of_right hfix)

-- @node: card_firstReturn_delete_one
/-- [Deleting one point and taking first returns preserves the number of
orbits, except that one orbit is lost when the deleted point is fixed](goal). -/
lemma card_firstReturn_delete_one (a : D) :
    Nat.card (orbitType (firstReturnPerm p {d | d ≠ a})) +
      (if p a = a then 1 else 0) = Nat.card (orbitType p) := by
  have h := card_firstReturn_orbits_add_missing p {d | d ≠ a}
  have hm : Nat.card {o : orbitType p // ¬ orbitHits p {d | d ≠ a} o} =
      if p a = a then 1 else 0 := by
    letI : Fintype (orbitType p) := Fintype.ofFinite _
    letI : Fintype {o : orbitType p // ¬ orbitHits p {d | d ≠ a} o} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp_rw [orbit_notHits_delete_one]
    by_cases hfix : p a = a <;> simp [hfix, Finset.filter_eq']
  rwa [hm] at h

-- @node: orbit_notHits_delete_pair
/-- For [two distinct deleted points](hyp:hab), [an orbit misses all remaining
points if and only if it is the singleton orbit of either deleted point fixed
by the permutation, or the two-point orbit in which the permutation exchanges
the deleted points](goal). -/
lemma orbit_notHits_delete_pair (a b : D) (hab : a ≠ b) (o : orbitType p) :
    ¬ orbitHits p {d | d ≠ a ∧ d ≠ b} o ↔
      (p a = a ∧ o = orbitOf p a) ∨ (p b = b ∧ o = orbitOf p b) ∨
        (p a = b ∧ p b = a ∧ o = orbitOf p a) := by
  have step (x : D) : orbitOf p (p x) = orbitOf p x :=
    Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl p x))
  constructor
  · intro h
    have only (d : D) (hd : orbitOf p d = o) : d = a ∨ d = b := by
      by_cases ha : d = a
      · exact Or.inl ha
      · right
        by_contra hb
        exact h ⟨⟨d, ha, hb⟩, hd⟩
    obtain ⟨d, hd⟩ := Quotient.exists_rep o
    rcases only d hd with hda | hdb
    · subst d
      rcases only (p a) ((step a).trans hd) with ha | ha
      · exact Or.inl ⟨ha, hd.symm⟩
      · right; right
        refine ⟨ha, ?_, hd.symm⟩
        rcases only (p b) ((step b).trans ((congrArg (orbitOf p) ha).symm.trans
          ((step a).trans hd))) with hb | hb
        · exact hb
        · exact (hab (p.injective (ha.trans hb.symm))).elim
    · subst d
      rcases only (p b) ((step b).trans hd) with hb | hb
      · right; right
        have hao : orbitOf p a = o := (congrArg (orbitOf p) hb).symm.trans ((step b).trans hd)
        refine ⟨?_, hb, hao.symm⟩
        rcases only (p a) ((step a).trans hao) with ha | ha
        · exact (hab (p.injective (ha.trans hb.symm))).elim
        · exact ha
      · exact Or.inr (Or.inl ⟨hb, hd.symm⟩)
  · rintro (⟨ha, rfl⟩ | ⟨hb, rfl⟩ | ⟨ha, hb, rfl⟩)
    · rintro ⟨d, hd⟩
      exact d.property.1 ((Quotient.exact hd : p.SameCycle d.val a).eq_of_right ha)
    · rintro ⟨d, hd⟩
      exact d.property.2 ((Quotient.exact hd : p.SameCycle d.val b).eq_of_right hb)
    · rintro ⟨d, hd⟩
      obtain ⟨n, hn⟩ := (Quotient.exact hd : p.SameCycle d.val a).symm.exists_nat_pow_eq
      have hp (n : ℕ) : (p ^ n) a = a ∨ (p ^ n) a = b := by
        induction n with
        | zero => exact Or.inl rfl
        | succ n ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          rcases ih with h | h
          · exact Or.inr (by rw [h, ha])
          · exact Or.inl (by rw [h, hb])
      rcases hp n with h | h
      · exact d.property.1 (hn.symm.trans h)
      · exact d.property.2 (hn.symm.trans h)

-- @node: card_firstReturn_delete_pair
/-- When [the two deleted points are distinct](hyp:hab), [the number of
first-return orbits plus one for each deleted fixed point and one if the two
deleted points form a two-point cycle equals the original number of
orbits](goal). -/
lemma card_firstReturn_delete_pair (a b : D) (hab : a ≠ b) :
    Nat.card (orbitType (firstReturnPerm p {d | d ≠ a ∧ d ≠ b})) +
      (if p a = a then 1 else 0) + (if p b = b then 1 else 0) +
      (if p a = b ∧ p b = a then 1 else 0) = Nat.card (orbitType p) := by
  have h := card_firstReturn_orbits_add_missing p {d | d ≠ a ∧ d ≠ b}
  have hm : Nat.card {o : orbitType p // ¬ orbitHits p {d | d ≠ a ∧ d ≠ b} o} =
      (if p a = a then 1 else 0) + (if p b = b then 1 else 0) +
        (if p a = b ∧ p b = a then 1 else 0) := by
    letI : Fintype (orbitType p) := Fintype.ofFinite _
    letI : Fintype {o : orbitType p // ¬ orbitHits p {d | d ≠ a ∧ d ≠ b} o} :=
      Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp_rw [orbit_notHits_delete_pair p a b hab, ← and_assoc]
    by_cases ha : p a = a
    · have hc : ¬ (p a = b ∧ p b = a) := fun hc => hab (ha.symm.trans hc.1)
      by_cases hb : p b = b
      · have ho : orbitOf p a ≠ orbitOf p b := fun he =>
          hab ((Quotient.exact he : p.SameCycle a b).eq_of_left ha)
        simp [ha, hb, hc, hab, hab.symm, Finset.filter_or, Finset.filter_eq', ho]
      · simp [ha, hb, hc, hab, hab.symm, Finset.filter_eq']
    · by_cases hb : p b = b
      · have hc : ¬ (p a = b ∧ p b = a) := fun hc => hab (hc.2.symm.trans hb)
        simp [ha, hb, hc, hab, hab.symm, Finset.filter_eq']
      · by_cases hc : p a = b ∧ p b = a <;> simp [ha, hb, hc, hab, hab.symm, Finset.filter_eq']
  rw [hm] at h
  omega

-- @node: firstReturn_mul_fixed_complement
/-- Suppose [a second permutation fixes every point outside the retained
subset](hyp:hfix) and [agrees on retained points with a permutation of that
subset](hyp:htU). Then [first return for the composition, applying the second
permutation before the original one, equals the retained permutation followed
by first return for the original permutation](goal). -/
lemma firstReturn_mul_fixed_complement (t : Equiv.Perm D) (tU : Equiv.Perm U)
    (hfix : ∀ x, x ∉ U → t x = x) (htU : ∀ d : U, t d.val = (tU d).val) :
    firstReturnPerm (p * t) U = firstReturnPerm p U * tU := by
  ext d
  obtain ⟨n, hn, he, hmin⟩ := Classical.choose_spec (exists_firstReturnPerm p U) (tU d)
  change (firstReturnPerm p U (tU d)).val = (p ^ n) (tU d).val at he
  have orbit (m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
      ((p * t) ^ m) d.val = (p ^ m) (tU d).val := by
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hz : m = 0
      · subst m
        simpa only [Nat.zero_add, pow_one, Equiv.Perm.mul_apply] using congrArg p (htU d)
      · have hp : 0 < m := by omega
        calc
          ((p * t) ^ (m + 1)) d.val = p (t (((p * t) ^ m) d.val)) := by
            rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
          _ = p (t ((p ^ m) (tU d).val)) := by rw [ih hp (by omega)]
          _ = p ((p ^ m) (tU d).val) := by rw [hfix _ (hmin m hp (by omega))]
          _ = (p ^ (m + 1)) (tU d).val := by rw [pow_succ', Equiv.Perm.mul_apply]
  have hmem : ((p * t) ^ n) d.val ∈ U := by
    rw [orbit n hn le_rfl, ← he]
    exact (firstReturnPerm p U (tU d)).property
  have hm (m : ℕ) (hm : 0 < m) (hmn : m < n) : ((p * t) ^ m) d.val ∉ U := by
    rw [orbit m hm (by omega)]
    exact hmin m hm hmn
  exact (firstReturnPerm_apply_of_spec (p * t) U d n hn hmem hm).trans
    ((orbit n hn le_rfl).trans he.symm)

namespace RotationSystem
variable (R : RotationSystem)

-- @node: RotationSystem.deleteEdgeDarts
/-- In [a rotation system](hyp:R), for [a dart specifying an edge to
delete](hyp:a), [the retained dart set](goal) consists of darts that are
[different from the specified dart](step:1) and [different from its reverse
dart](step:2). -/
noncomputable def deleteEdgeDarts (a : R.Dart) : Set R.Dart :=
  {d | d ≠ a ∧ d ≠ R.edgeInv a}

-- @node: RotationSystem.deleteEdgeDarts_inv
/-- [A dart's reverse survives deletion of a specified edge if and only if the
dart itself survives](goal). -/
lemma deleteEdgeDarts_inv (a d : R.Dart) :
    R.edgeInv d ∈ R.deleteEdgeDarts a ↔ d ∈ R.deleteEdgeDarts a := by
  change (R.edgeInv d ≠ a ∧ R.edgeInv d ≠ R.edgeInv a) ↔
    (d ≠ a ∧ d ≠ R.edgeInv a)
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun h => hb (congrArg R.edgeInv h),
      fun h => ha ((congrArg R.edgeInv h).trans (R.edgeInv_involutive a))⟩
  · rintro ⟨ha, hb⟩
    refine ⟨?_, fun h => ha (R.edgeInv.injective h)⟩
    intro h
    exact hb ((R.edgeInv_involutive d).symm.trans (congrArg R.edgeInv h))

-- @node: RotationSystem.deleteEdgeInv
/-- In [a rotation system](hyp:R), after deleting [the edge specified by a
dart](hyp:a), [the edge-reversal permutation on surviving darts](goal) is the
restriction of the original edge reversal. -/
noncomputable def deleteEdgeInv (a : R.Dart) : Equiv.Perm (R.deleteEdgeDarts a) :=
  R.edgeInv.subtypePerm (R.deleteEdgeDarts_inv a)

-- @node: RotationSystem.deleteEdgeFacePerm
/-- In [a rotation system](hyp:R), after deleting [the edge specified by a
dart](hyp:a), [the face permutation on surviving darts](goal) applies surviving
edge reversal and then first return under the original vertex rotation. -/
noncomputable def deleteEdgeFacePerm (a : R.Dart) : Equiv.Perm (R.deleteEdgeDarts a) :=
  firstReturnPerm R.rot (R.deleteEdgeDarts a) * R.deleteEdgeInv a

-- @node: RotationSystem.deleteEdgeFacePerm_eq_firstReturn_swap
/-- [The face permutation after deleting an edge equals first return to the
surviving darts under the permutation that first exchanges the deleted edge's
two darts and then applies the original face permutation](goal). -/
lemma deleteEdgeFacePerm_eq_firstReturn_swap (a : R.Dart) :
    R.deleteEdgeFacePerm a =
      firstReturnPerm (R.facePerm * Equiv.swap a (R.edgeInv a)) (R.deleteEdgeDarts a) := by
  have hfix (x : R.Dart) (hx : x ∉ R.deleteEdgeDarts a) :
      (R.edgeInv * Equiv.swap a (R.edgeInv a)) x = x := by
    by_cases ha : x = a
    · subst x
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, R.edgeInv_involutive a]
    · have hb : x = R.edgeInv a := by
        by_contra hb
        exact hx ⟨ha, hb⟩
      subst x
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have ht (d : R.deleteEdgeDarts a) :
      (R.edgeInv * Equiv.swap a (R.edgeInv a)) d.val = (R.deleteEdgeInv a d).val := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne d.property.1 d.property.2]
    rfl
  have he := firstReturn_mul_fixed_complement R.rot (R.deleteEdgeDarts a)
    (R.edgeInv * Equiv.swap a (R.edgeInv a)) (R.deleteEdgeInv a) hfix ht
  change firstReturnPerm R.rot (R.deleteEdgeDarts a) * R.deleteEdgeInv a = _
  rw [show R.facePerm * Equiv.swap a (R.edgeInv a) =
    R.rot * (R.edgeInv * Equiv.swap a (R.edgeInv a)) from mul_assoc _ _ _]
  exact he.symm

-- @node: RotationSystem.deleteEdgeFacePerm_orbit_count
/-- [The number of face orbits after deleting an edge, plus one for each of
its darts fixed by vertex rotation and one if vertex rotation exchanges its
two darts, equals the number of orbits of the permutation that first exchanges
those darts and then applies the original face permutation](goal). -/
lemma deleteEdgeFacePerm_orbit_count (a : R.Dart) :
    Nat.card (orbitType (R.deleteEdgeFacePerm a)) +
      (if R.rot a = a then 1 else 0) +
      (if R.rot (R.edgeInv a) = R.edgeInv a then 1 else 0) +
      (if R.rot a = R.edgeInv a ∧ R.rot (R.edgeInv a) = a then 1 else 0) =
      Nat.card (orbitType (R.facePerm * Equiv.swap a (R.edgeInv a))) := by
  rw [R.deleteEdgeFacePerm_eq_firstReturn_swap]
  have h := card_firstReturn_delete_pair
    (R.facePerm * Equiv.swap a (R.edgeInv a)) a (R.edgeInv a)
    (R.edgeInv_fixedPointFree a).symm
  have ha : (R.facePerm * Equiv.swap a (R.edgeInv a)) a = R.rot a := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, facePerm,
      R.edgeInv_involutive a]
  have hb : (R.facePerm * Equiv.swap a (R.edgeInv a)) (R.edgeInv a) =
      R.rot (R.edgeInv a) := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, facePerm]
  simpa only [deleteEdgeDarts, ha, hb] using h

end RotationSystem

end OaiPairedStatesHamiltonian
