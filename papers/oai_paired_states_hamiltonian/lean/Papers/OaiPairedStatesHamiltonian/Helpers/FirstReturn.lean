module

public import Papers.OaiPairedStatesHamiltonian.Helpers.DualMap

/-! First-return permutations on a retained subset of a finite permutation. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

open Classical
attribute [local instance] propDecidable

-- @node: exists_firstReturnPerm
/-- [For any permutation of a finite set and any retained subset, there is a
permutation of that subset that sends each retained point to its first return:
the image is reached after a positive number of iterations of the original
permutation, and no earlier positive iterate belongs to the retained subset](goal). -/
lemma exists_firstReturnPerm {D : Type} [Fintype D] (p : Equiv.Perm D) (U : Set D) :
    ∃ q : Equiv.Perm U, ∀ d : U, ∃ n : ℕ, 0 < n ∧
      (q d).val = (p ^ n) d.val ∧ ∀ m, 0 < m → m < n → (p ^ m) d.val ∉ U := by
  classical
  have returns (d : U) : ∃ n : ℕ, 0 < n ∧ (p ^ n) d.val ∈ U := by
    obtain ⟨n, hn, hp⟩ := (isOfFinOrder_of_finite p).exists_pow_eq_one
    exact ⟨n, hn, by simpa only [hp, Equiv.Perm.one_apply] using d.property⟩
  let n (d : U) : ℕ := Nat.find (returns d)
  have hn (d : U) : 0 < n d ∧ (p ^ n d) d.val ∈ U := Nat.find_spec (returns d)
  have hfirst (d : U) (m : ℕ) (hm : 0 < m) (hlt : m < n d) :
      (p ^ m) d.val ∉ U := by
    intro hmem
    exact (Nat.find_min (returns d) hlt) ⟨hm, hmem⟩
  let q : U → U := fun d => ⟨(p ^ n d) d.val, (hn d).2⟩
  have ordered (a b : U) (hab : q a = q b) (hle : n a ≤ n b) : a = b := by
    have heq : (p ^ n a) a.val = (p ^ n b) b.val := congrArg Subtype.val hab
    have hrel : (p ^ (n b - n a)) b.val = a.val := by
      apply (p ^ n a).injective
      calc
        (p ^ n a) ((p ^ (n b - n a)) b.val) = (p ^ n b) b.val := by
          rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hle]
        _ = (p ^ n a) a.val := heq.symm
    have hsame : n a = n b := by
      by_contra hne
      have hpos : 0 < n b - n a := by omega
      have hlt : n b - n a < n b := by have := (hn a).1; omega
      exact hfirst b (n b - n a) hpos hlt (hrel.symm ▸ a.property)
    apply Subtype.ext
    apply (p ^ n a).injective
    simpa only [hsame] using heq
  have hinj : Function.Injective q := by
    intro a b hab
    rcases le_total (n a) (n b) with h | h
    · exact ordered a b hab h
    · exact (ordered b a hab.symm h).symm
  refine ⟨Equiv.ofBijective q ⟨hinj, Finite.surjective_of_injective hinj⟩, ?_⟩
  intro d
  exact ⟨n d, (hn d).1, rfl, hfirst d⟩

/-- Given [a permutation of a finite set](hyp:p) and [a subset of points to
retain](hyp:U), the [first-return permutation on the retained subset](goal) sends
each retained point to the next retained point reached by a positive number of
iterations of the original permutation. -/
noncomputable def firstReturnPerm {D : Type} [Fintype D] (p : Equiv.Perm D) (U : Set D) :
    Equiv.Perm U := Classical.choose (exists_firstReturnPerm p U)

/-- If [two retained points lie in the same orbit of the original permutation](hyp:h),
then [they lie in the same orbit of its first-return permutation on the retained
subset](goal). -/
-- @node: sameCycle_firstReturnPerm
lemma sameCycle_firstReturnPerm {D : Type} [Fintype D] (p : Equiv.Perm D)
    (U : Set D) (a b : U) (h : p.SameCycle a.val b.val) :
    (firstReturnPerm p U).SameCycle a b := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  suffices ∀ k : ℕ, ∀ a b : U, (p ^ k) a.val = b.val →
      (firstReturnPerm p U).SameCycle a b from this k a b hk
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a b hk
    by_cases hz : k = 0
    · subst k
      have hab : a = b := Subtype.ext (by simpa using hk)
      subst b
      exact Equiv.Perm.SameCycle.refl _ a
    · obtain ⟨n, hn, heq, hmin⟩ :=
        Classical.choose_spec (exists_firstReturnPerm p U) a
      have hle : n ≤ k := by
        by_contra hgt
        exact hmin k (Nat.pos_of_ne_zero hz) (by omega) (hk ▸ b.property)
      change (firstReturnPerm p U a).val = (p ^ n) a.val at heq
      have hnext : (p ^ (k - n)) (firstReturnPerm p U a).val = b.val := by
        rw [heq, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle]
        exact hk
      have htail := ih (k - n) (by omega) (firstReturnPerm p U a) b hnext
      exact Equiv.Perm.sameCycle_apply_left.mp htail

end OaiPairedStatesHamiltonian
