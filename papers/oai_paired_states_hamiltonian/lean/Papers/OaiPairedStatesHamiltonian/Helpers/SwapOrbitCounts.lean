module

public import Papers.OaiPairedStatesHamiltonian.Helpers.FirstReturnCounts

/-! Multiplication by a transposition splits or merges exactly two permutation
orbits. Orbits avoiding the transposition endpoints are preserved explicitly. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

variable {D : Type} [Fintype D]

-- @node: orbitAvoids
/-- For a [permutation](hyp:p), a [set of excluded points](hyp:U), and a [starting point](hyp:x),
[orbit avoidance](goal) means that every point in the starting point's cycle lies outside the excluded set. -/
noncomputable def orbitAvoids (p : Equiv.Perm D) (U : Set D) (x : D) : Prop :=
  ∀ y, p.SameCycle x y → y ∉ U

-- @node: orbitAvoids_transfer
/-- If [two permutations agree outside an excluded set](hyp:heq) and [the first permutation's cycle
through the starting point avoids that set](hyp:hx), then [all nonnegative iterates of the starting
point agree for the two permutations, and its cycle under the second permutation also avoids the set](goal). -/
lemma orbitAvoids_transfer (p q : Equiv.Perm D) (U : Set D)
    (heq : ∀ x, x ∉ U → p x = q x) (x : D) (hx : orbitAvoids p U x) :
    (∀ n : ℕ, (p ^ n) x = (q ^ n) x) ∧ orbitAvoids q U x := by
  have hp (n : ℕ) : (p ^ n) x = (q ^ n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← ih]
      exact heq _ (hx _ ((Equiv.Perm.SameCycle.refl p x).pow_right))
  refine ⟨hp, ?_⟩
  intro y hy
  obtain ⟨n, rfl⟩ := hy.exists_nat_pow_eq
  rw [← hp]
  exact hx _ ((Equiv.Perm.SameCycle.refl p x).pow_right)

-- @node: sameCycle_transfer_of_avoids
/-- If [two permutations agree outside an excluded set](hyp:heq) and [the first permutation's cycle
through a point avoids that set](hyp:hx), then [another point belongs to that cycle under the first
permutation exactly when it belongs to the corresponding cycle under the second](goal). -/
lemma sameCycle_transfer_of_avoids (p q : Equiv.Perm D) (U : Set D)
    (heq : ∀ x, x ∉ U → p x = q x) (x y : D) (hx : orbitAvoids p U x) :
    p.SameCycle x y ↔ q.SameCycle x y := by
  have h := orbitAvoids_transfer p q U heq x hx
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk⟩ := (show p.SameCycle x y from ⟨n, hn⟩).exists_nat_pow_eq
    exact ⟨(k : ℤ), by simpa only [zpow_natCast, ← h.1 k] using hk⟩
  · intro hy
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    exact ⟨(n : ℤ), by simpa only [zpow_natCast, ← h.1 n] using hn⟩

-- @node: orbitAvoids_out
/-- If [an orbit does not meet the excluded set](hyp:ho), then [the cycle through its chosen
representative avoids the excluded set](goal). -/
lemma orbitAvoids_out (p : Equiv.Perm D) (U : Set D)
    (o : orbitType p) (ho : ¬ orbitHits p U o) : orbitAvoids p U o.out := by
  intro y hy hyU
  exact ho ⟨⟨y, hyU⟩, (Quotient.sound hy).symm.trans (Quotient.out_eq o)⟩

-- @node: missingOrbitMap
/-- For [two permutations](hyp:p,q) and an [excluded set](hyp:U), assuming [the permutations agree
outside that set](hyp:heq), the [map between orbits avoiding the set](goal) sends each orbit of the
first permutation to the orbit of the second through a chosen representative. -/
noncomputable def missingOrbitMap (p q : Equiv.Perm D) (U : Set D)
    (heq : ∀ x, x ∉ U → p x = q x) :
    {o : orbitType p // ¬ orbitHits p U o} →
      {o : orbitType q // ¬ orbitHits q U o} := fun o =>
  ⟨orbitOf q o.val.out, by
    rintro ⟨y, hy⟩
    exact (orbitAvoids_transfer p q U heq _ (orbitAvoids_out p U o.val o.property)).2
      y.val (Quotient.exact hy).symm y.property⟩

-- @node: missingOrbitMap_rep
/-- Suppose [two permutations agree outside an excluded set](hyp:heq). If [a point represents an
orbit of the first permutation that avoids the set](hyp:hx), then [the orbit map sends that orbit
to the second permutation's orbit through the same point](goal). -/
lemma missingOrbitMap_rep (p q : Equiv.Perm D) (U : Set D)
    (heq : ∀ x, x ∉ U → p x = q x)
    (o : {o : orbitType p // ¬ orbitHits p U o}) (x : D)
    (hx : orbitOf p x = o.val) :
    (missingOrbitMap p q U heq o).val = orbitOf q x := by
  apply Quotient.sound
  exact (sameCycle_transfer_of_avoids p q U heq _ x
    (orbitAvoids_out p U o.val o.property)).mp
      (Quotient.exact ((Quotient.out_eq o.val).trans hx.symm))

-- @node: missingOrbitEquiv
/-- For [two permutations](hyp:p,q) and an [excluded set](hyp:U), [agreement outside the excluded
set](hyp:heq) gives a [bijection between their orbits avoiding that set](goal), matching orbits
through the same representative. -/
noncomputable def missingOrbitEquiv (p q : Equiv.Perm D) (U : Set D)
    (heq : ∀ x, x ∉ U → p x = q x) :
    {o : orbitType p // ¬ orbitHits p U o} ≃
      {o : orbitType q // ¬ orbitHits q U o} where
  toFun := missingOrbitMap p q U heq
  invFun := missingOrbitMap q p U (fun x hx => (heq x hx).symm)
  left_inv o := by
    apply Subtype.ext
    exact (missingOrbitMap_rep q p U (fun x hx => (heq x hx).symm) _ o.val.out rfl).trans
      (Quotient.out_eq o.val)
  right_inv o := by
    apply Subtype.ext
    exact (missingOrbitMap_rep p q U heq _ o.val.out rfl).trans (Quotient.out_eq o.val)

-- @node: card_missing_orbits_congr
/-- If [two permutations agree outside an excluded set](hyp:heq), then [they have the same number
of orbits that do not meet that set](goal). -/
lemma card_missing_orbits_congr (p q : Equiv.Perm D) (U : Set D)
    (heq : ∀ x, x ∉ U → p x = q x) :
    Nat.card {o : orbitType p // ¬ orbitHits p U o} =
      Nat.card {o : orbitType q // ¬ orbitHits q U o} :=
  Nat.card_congr (missingOrbitEquiv p q U heq)

-- @node: orbitHits_pair_iff
/-- [An orbit meets a set consisting of two specified points exactly when it is the orbit of
one of those points](goal). -/
lemma orbitHits_pair_iff (p : Equiv.Perm D) (a b : D) (o : orbitType p) :
    orbitHits p {x | x = a ∨ x = b} o ↔ o = orbitOf p a ∨ o = orbitOf p b := by
  constructor
  · rintro ⟨⟨x, hx⟩, he⟩
    rcases hx with rfl | rfl
    · exact Or.inl he.symm
    · exact Or.inr he.symm
  · rintro (rfl | rfl)
    · exact ⟨⟨a, Or.inl rfl⟩, rfl⟩
    · exact ⟨⟨b, Or.inr rfl⟩, rfl⟩

-- @node: card_orbits_hit_pair
/-- [The number of orbits meeting two specified points is one if the points lie in the same
cycle, and two otherwise](goal). -/
lemma card_orbits_hit_pair (p : Equiv.Perm D) (a b : D) :
    Nat.card {o : orbitType p // orbitHits p {x | x = a ∨ x = b} o} =
      if p.SameCycle a b then 1 else 2 := by
  letI : Fintype (orbitType p) := Fintype.ofFinite _
  letI : Fintype {o : orbitType p // orbitHits p {x | x = a ∨ x = b} o} :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [orbitHits_pair_iff]
  by_cases h : p.SameCycle a b
  · have he : orbitOf p a = orbitOf p b := Quotient.sound h
    simp [h, he, Finset.filter_eq']
  · have he : orbitOf p a ≠ orbitOf p b := fun he => h (Quotient.exact he)
    simp [h, Finset.filter_or, Finset.filter_eq', he]

-- @node: pairPerm_sameCycle_iff
/-- For [two distinct points](hyp:hab) and [a permutation of just those points](hyp:q), [the points lie
in the same cycle exactly when the permutation sends the first point to the second](goal). -/
lemma pairPerm_sameCycle_iff (a b : D) (hab : a ≠ b)
    (q : Equiv.Perm {x : D | x = a ∨ x = b}) :
    q.SameCycle ⟨a, Or.inl rfl⟩ ⟨b, Or.inr rfl⟩ ↔
      q ⟨a, Or.inl rfl⟩ = ⟨b, Or.inr rfl⟩ := by
  constructor
  · intro h
    apply Subtype.ext
    rcases (q ⟨a, Or.inl rfl⟩).property with ha | hb
    · have hf : q ⟨a, Or.inl rfl⟩ = ⟨a, Or.inl rfl⟩ := Subtype.ext ha
      exact (hab (congrArg Subtype.val (h.eq_of_left hf))).elim
    · exact hb
  · intro h
    rw [← h]
    exact (Equiv.Perm.SameCycle.refl q _).apply_right

variable [DecidableEq D]

-- @node: sameCycle_mul_swap_pair
/-- For [two distinct points](hyp:hab), [applying their transposition before a permutation puts
them in the same cycle exactly when they were in different cycles of the original permutation](goal). -/
lemma sameCycle_mul_swap_pair (p : Equiv.Perm D) (a b : D) (hab : a ≠ b) :
    (p * Equiv.swap a b).SameCycle a b ↔ ¬ p.SameCycle a b := by
  let U : Set D := {x | x = a ∨ x = b}
  let aa : U := ⟨a, Or.inl rfl⟩
  let bb : U := ⟨b, Or.inr rfl⟩
  let q := firstReturnPerm p U
  have hne : aa ≠ bb := fun he => hab (congrArg Subtype.val he)
  have ht : firstReturnPerm (p * Equiv.swap a b) U = q * Equiv.swap aa bb := by
    apply firstReturn_mul_fixed_complement
    · intro x hx
      exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (Or.inl h))
        (fun h => hx (Or.inr h))
    · intro d
      rcases d.property with ha | hb
      · have hd : d = aa := Subtype.ext ha
        rw [hd]
        simp only [Equiv.swap_apply_left]
        exact Equiv.swap_apply_left a b
      · have hd : d = bb := Subtype.ext hb
        rw [hd]
        simp only [Equiv.swap_apply_right]
        exact Equiv.swap_apply_right a b
  have hp := sameCycle_firstReturnPerm_iff p U aa bb
  have hs := sameCycle_firstReturnPerm_iff (p * Equiv.swap a b) U aa bb
  rw [← hs, ht, pairPerm_sameCycle_iff a b hab,
    ← hp, pairPerm_sameCycle_iff a b hab]
  change q (Equiv.swap aa bb aa) = bb ↔ ¬ q aa = bb
  rw [Equiv.swap_apply_left]
  constructor
  · intro hb ha
    exact hne (q.injective (ha.trans hb.symm))
  · intro ha
    apply Subtype.ext
    rcases (q bb).property with hqa | hqb
    · have hfix : q aa = aa := by
        apply Subtype.ext
        rcases (q aa).property with h | h
        · exact h
        · exact (ha (Subtype.ext h)).elim
      exact (hne (q.injective (hfix.trans (Subtype.ext hqa).symm))).elim
    · exact hqb

-- @node: card_orbits_mul_swap
/-- For [two distinct points](hyp:hab), [composing a permutation with their transposition increases
the orbit count by one when they originally share a cycle, and decreases it by one otherwise](goal). -/
lemma card_orbits_mul_swap (p : Equiv.Perm D) (a b : D) (hab : a ≠ b) :
    Nat.card (orbitType (p * Equiv.swap a b)) + (if p.SameCycle a b then 0 else 1) =
      Nat.card (orbitType p) + (if p.SameCycle a b then 1 else 0) := by
  let U : Set D := {x | x = a ∨ x = b}
  have hm := card_missing_orbits_congr p (p * Equiv.swap a b) U (by
    intro x hx
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
      (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))])
  have hp := card_firstReturn_orbits_add_missing p U
  have hq := card_firstReturn_orbits_add_missing (p * Equiv.swap a b) U
  rw [card_firstReturn_orbits, card_orbits_hit_pair] at hp hq
  simp only [sameCycle_mul_swap_pair p a b hab] at hq
  by_cases h : p.SameCycle a b <;> simp only [h, if_true, if_false, not_true_eq_false,
    not_false_eq_true] at hp hq ⊢ <;> omega

variable {V : Type} [Fintype V] (H : SimpleGraph V) (a b : V)

-- @node: componentMergeMap
/-- For a [simple graph](hyp:H) and [two vertices](hyp:a,b), the [component map for adding their
edge](goal) sends each original connected component to the connected component containing it
after the edge is added. -/
noncomputable def componentMergeMap :
    H.ConnectedComponent → (H ⊔ SimpleGraph.edge a b).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE le_sup_left)

-- @node: componentMergeMap_swap
/-- [Swapping the original components of the two endpoints before mapping to components of the
graph with their edge added leaves the image of every component unchanged](goal). -/
lemma componentMergeMap_swap (c : H.ConnectedComponent) :
    componentMergeMap H a b
        (Equiv.swap (H.connectedComponentMk a) (H.connectedComponentMk b) c) =
      componentMergeMap H a b c := by
  have hab : componentMergeMap H a b (H.connectedComponentMk a) =
      componentMergeMap H a b (H.connectedComponentMk b) := by
    change (H ⊔ SimpleGraph.edge a b).connectedComponentMk a =
      (H ⊔ SimpleGraph.edge a b).connectedComponentMk b
    by_cases he : a = b
    · exact congrArg _ he
    · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (Or.inr ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, he⟩))
  by_cases ha : c = H.connectedComponentMk a
  · rw [ha, Equiv.swap_apply_left]
    exact hab.symm
  by_cases hb : c = H.connectedComponentMk b
  · rw [hb, Equiv.swap_apply_right]
    exact hab
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

-- @node: componentMergeOrbitLift
/-- For a [simple graph](hyp:H) and [two vertices](hyp:a,b), the [map from component-swap orbits
to enlarged-graph components](goal) sends an orbit under the swap of the endpoints' original
components to their common image after adding the edge. -/
noncomputable def componentMergeOrbitLift :
    orbitType (Equiv.swap (H.connectedComponentMk a) (H.connectedComponentMk b)) →
      (H ⊔ SimpleGraph.edge a b).ConnectedComponent :=
  Quotient.lift (componentMergeMap H a b) (by
    intro c d h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, componentMergeMap_swap]
      exact ih)

-- @node: componentMergeOrbitProjection
/-- For a [simple graph](hyp:H) and [two vertices](hyp:a,b), the [projection from components after
adding their edge to component-swap orbits](goal) sends a component to the orbit of any of its
vertices' original components under the swap of the endpoints' original components. -/
noncomputable def componentMergeOrbitProjection :
    (H ⊔ SimpleGraph.edge a b).ConnectedComponent →
      orbitType (Equiv.swap (H.connectedComponentMk a) (H.connectedComponentMk b)) := by
  let t := Equiv.swap (H.connectedComponentMk a) (H.connectedComponentMk b)
  have hab : orbitOf t (H.connectedComponentMk a) = orbitOf t (H.connectedComponentMk b) := by
    apply Quotient.sound
    exact ⟨(1 : ℤ), by simp [t]⟩
  refine Quot.lift (fun v => orbitOf t (H.connectedComponentMk v)) ?_
  intro v w h
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons v u w h p ih =>
    apply Eq.trans _ ih
    rcases h with hh | he
    · exact congrArg (orbitOf t)
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hh)
    · obtain ⟨he, hne⟩ := (SimpleGraph.edge_adj a b v u).mp he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm

-- @node: componentMergeOrbitEquiv
/-- For a [simple graph](hyp:H) and [two vertices](hyp:a,b), the [component-merger bijection](goal)
identifies connected components after adding their edge with orbits of the swap of their
original connected components. -/
noncomputable def componentMergeOrbitEquiv :
    (H ⊔ SimpleGraph.edge a b).ConnectedComponent ≃
      orbitType (Equiv.swap (H.connectedComponentMk a) (H.connectedComponentMk b)) where
  toFun := componentMergeOrbitProjection H a b
  invFun := componentMergeOrbitLift H a b
  left_inv c := by
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => rfl
  right_inv o := by
    induction o using Quotient.inductionOn with
    | h c =>
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h v => rfl

-- @node: card_orbits_one
/-- [The identity permutation has as many orbits as there are elements of its underlying type](goal). -/
lemma card_orbits_one (X : Type) : Nat.card (orbitType (1 : Equiv.Perm X)) = Nat.card X := by
  apply Eq.symm
  apply Nat.card_congr
  apply Equiv.ofBijective (orbitOf (1 : Equiv.Perm X))
  constructor
  · intro x y he
    exact Equiv.Perm.sameCycle_one.mp (Quotient.exact he)
  · exact Quotient.mk_surjective

-- @node: card_components_sup_edge
/-- [Adding an edge leaves the number of connected components unchanged when its endpoints were
already connected, and reduces that number by one otherwise](goal). -/
lemma card_components_sup_edge :
    Nat.card (H ⊔ SimpleGraph.edge a b).ConnectedComponent +
        (if H.Reachable a b then 0 else 1) = Nat.card H.ConnectedComponent := by
  rw [Nat.card_congr (componentMergeOrbitEquiv H a b)]
  by_cases h : H.Reachable a b
  · have he := SimpleGraph.ConnectedComponent.sound h
    simp only [he, Equiv.swap_self, if_pos h, Nat.add_zero]
    exact card_orbits_one _
  · have he : H.connectedComponentMk a ≠ H.connectedComponentMk b :=
      fun he => h (SimpleGraph.ConnectedComponent.exact he)
    letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
    have ht := card_orbits_mul_swap (1 : Equiv.Perm H.ConnectedComponent)
      (H.connectedComponentMk a) (H.connectedComponentMk b) he
    simpa only [one_mul, Equiv.Perm.sameCycle_one, if_neg he, if_neg h,
      card_orbits_one, Nat.add_zero] using ht

end OaiPairedStatesHamiltonian
