module

public import Papers.OaiPairedStatesHamiltonian.Helpers.FirstReturnCounts

/-! Successive first returns agree with a single first return to the smaller
retained set. This identifies the rotations in successive edge deletions. -/

public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

variable {D : Type} [Fintype D] (p : Equiv.Perm D) (U V : Set D)

-- @node: firstReturnPerm_nested_segment
/-- Suppose [the smaller retained set is contained in the larger one](hyp:hVU),
[the number of permutation steps is positive](hyp:hn), [those steps end in the
smaller set](hyp:hend), and [no earlier positive step visits the smaller
set](hyp:hfirst). Then [a positive number of first returns to the larger set
reaches that same endpoint, with no earlier positive return in the smaller
set](goal). -/
lemma firstReturnPerm_nested_segment (hVU : V ⊆ U) (d : U) (n : ℕ)
    (hn : 0 < n) (hend : (p ^ n) d.val ∈ V)
    (hfirst : ∀ m, 0 < m → m < n → (p ^ m) d.val ∉ V) :
    ∃ k : ℕ, 0 < k ∧ ((firstReturnPerm p U ^ k) d).val = (p ^ n) d.val ∧
      ∀ m, 0 < m → m < k → ((firstReturnPerm p U ^ m) d).val ∉ V := by
  induction n using Nat.strong_induction_on generalizing d with
  | h n ih =>
    let q := firstReturnPerm p U
    obtain ⟨t, ht, he, hmin⟩ := Classical.choose_spec (exists_firstReturnPerm p U) d
    change (q d).val = (p ^ t) d.val at he
    have hle : t ≤ n := by
      by_contra h
      exact hmin n hn (by omega) (hVU hend)
    by_cases htn : t = n
    · refine ⟨1, by omega, ?_, ?_⟩
      · simpa only [pow_one, htn] using he
      · intro m hm hmk
        omega
    · have hp : 0 < n - t := by omega
      have hstep (m : ℕ) : (p ^ m) (q d).val = (p ^ (t + m)) d.val := by
        rw [he, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm]
      have hend' : (p ^ (n - t)) (q d).val ∈ V := by
        rw [hstep, Nat.add_sub_of_le hle]
        exact hend
      have hfirst' : ∀ m, 0 < m → m < n - t → (p ^ m) (q d).val ∉ V := by
        intro m hm hmn
        rw [hstep]
        exact hfirst (t + m) (by omega) (by omega)
      obtain ⟨k, hk, hke, hkm⟩ := ih (n - t) (by omega) (q d) hp hend' hfirst'
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · change ((q ^ (k + 1)) d).val = _
        rw [pow_succ, Equiv.Perm.mul_apply, hke, hstep, Nat.add_sub_of_le hle]
      · intro m hm hmk
        change ((q ^ m) d).val ∉ V
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
        rw [pow_succ, Equiv.Perm.mul_apply]
        by_cases hj : j = 0
        · subst j
          simp only [pow_zero, Equiv.Perm.one_apply]
          rw [he]
          exact hfirst t ht (by omega)
        · exact hkm j (Nat.pos_of_ne_zero hj) (by omega)

-- @node: firstReturnPerm_nested_apply
/-- If [the smaller retained set is contained in the larger one](hyp:hVU), then,
starting from [a dart in both retained sets](hyp:d), [first returning to the larger
set and then to the smaller set gives the same dart as first returning directly
to the smaller set](goal). -/
lemma firstReturnPerm_nested_apply (hVU : V ⊆ U)
    (d : {x : U // x.val ∈ V}) :
    (firstReturnPerm (firstReturnPerm p U) {x : U | x.val ∈ V} d).val.val =
      (firstReturnPerm p V ⟨d.val.val, d.property⟩).val := by
  obtain ⟨n, hn, he, hmin⟩ := Classical.choose_spec (exists_firstReturnPerm p V)
    (⟨d.val.val, d.property⟩ : V)
  change (firstReturnPerm p V ⟨d.val.val, d.property⟩).val = (p ^ n) d.val.val at he
  have hend : (p ^ n) d.val.val ∈ V := he ▸ (firstReturnPerm p V _).property
  obtain ⟨k, hk, hke, hkm⟩ := firstReturnPerm_nested_segment p U V hVU d.val n hn hend hmin
  have hmem : (firstReturnPerm p U ^ k) d.val ∈ {x : U | x.val ∈ V} := by
    change ((firstReturnPerm p U ^ k) d.val).val ∈ V
    rwa [hke]
  have h := firstReturnPerm_apply_of_spec (firstReturnPerm p U)
    {x : U | x.val ∈ V} d k hk hmem hkm
  exact (congrArg Subtype.val h).trans (hke.trans he.symm)

-- @node: perm_pow_intertwine
/-- If [a map carries each step of one permutation to a step of another](hyp:hi),
then [it also carries any specified number of steps from any starting point to
the same number of steps of the second permutation](goal). -/
lemma perm_pow_intertwine {A B : Type} (p : Equiv.Perm A) (q : Equiv.Perm B)
    (i : A → B) (hi : ∀ a, i (p a) = q (i a)) (n : ℕ) (a : A) :
    i ((p ^ n) a) = (q ^ n) (i a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, hi, ih]

-- @node: firstReturnPerm_equiv_apply
/-- If [a bijective relabelling carries steps of the first permutation to steps
of the second](hyp:he) and [membership in the first retained set is equivalent
to membership of the relabelled point in the second](hyp:hST), then [relabelling
the first return gives the first return of the relabelled starting point](goal). -/
lemma firstReturnPerm_equiv_apply {A B : Type} [Fintype A] [Fintype B]
    (p : Equiv.Perm A) (q : Equiv.Perm B) (e : A ≃ B)
    (he : ∀ a, e (p a) = q (e a)) (S : Set A) (T : Set B)
    (hST : ∀ a, a ∈ S ↔ e a ∈ T) (a : S) :
    e (firstReturnPerm p S a).val =
      (firstReturnPerm q T ⟨e a.val, (hST a.val).mp a.property⟩).val := by
  obtain ⟨n, hn, hnext, hmin⟩ := Classical.choose_spec (exists_firstReturnPerm p S) a
  change (firstReturnPerm p S a).val = (p ^ n) a.val at hnext
  have hpow := perm_pow_intertwine p q e he
  have hmem : (q ^ n) (e a.val) ∈ T := by
    rw [← hpow n a.val, ← hnext]
    exact (hST _).mp (firstReturnPerm p S a).property
  have hfirst : ∀ m, 0 < m → m < n → (q ^ m) (e a.val) ∉ T := by
    intro m hm hmn h
    rw [← hpow m a.val] at h
    exact hmin m hm hmn ((hST _).mpr h)
  rw [hnext, hpow n a.val]
  exact (firstReturnPerm_apply_of_spec q T ⟨e a.val, (hST a.val).mp a.property⟩ n hn hmem hfirst).symm

end OaiPairedStatesHamiltonian
