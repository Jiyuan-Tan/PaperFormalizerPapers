module

public import Papers.OaiPairedStatesHamiltonian.Helpers.StatesCore

/-! Endpoint rigidity and independent switches on the permutation orbits of a pair. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

-- @node: pairedDart_same_black_face
/-- If [the map is a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol)
and [the paired darts selected by two pairs at two black nonouter faces have the same
undirected edge](hyp:he), then [those faces are equal](goal). -/
lemma pairedDart_same_black_face (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p q : Pair T col t0)
    (t u : blackNonOuter T col t0)
    (he : T.edgeOf (pairedDart T col t0 hT p.val.1 p.val.2 p.property t) =
      T.edgeOf (pairedDart T col t0 hT q.val.1 q.val.2 q.property u)) : t = u := by
  apply Subtype.ext
  have ht := (pairedDart_spec T col t0 hT p.val.1 p.val.2 p.property t).2.2
  have hu := (pairedDart_spec T col t0 hT q.val.1 q.val.2 q.property u).2.2
  have hbt := (Finset.mem_filter.mp t.property).2.1
  have hbu := (Finset.mem_filter.mp u.property).2.1
  have hc := normalizedColoring_partition T col hcol t0
  rcases (T.edgeOf_eq_iff _ _).mp he with he | he
  · rw [he] at hu
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact ht.symm.trans hu
    · exact (hc _ ((ht ▸ hbt).trans (hu ▸ hbu).symm)).elim
    · exact (hc _ ((hu ▸ hbu).trans (ht ▸ hbt).symm)).elim
    · exact ht.symm.trans hu
  · rw [he, T.edgeInv_involutive] at hu
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact (hc _ ((ht ▸ hbt).trans (hu ▸ hbu).symm)).elim
    · exact ht.symm.trans hu
    · exact ht.symm.trans hu
    · exact (hc _ ((hu ▸ hbu).trans (ht ▸ hbt).symm)).elim

-- @node: groupKey_eq_pairedDart_edges
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), if
[two pairs have the same set of undirected paired edges](hyp:hkey), then [their
paired darts at any black nonouter face have the same undirected edge](goal). -/
lemma groupKey_eq_pairedDart_edges (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p q : Pair T col t0)
    (hkey : groupKey T col t0 hT q = groupKey T col t0 hT p)
    (t : blackNonOuter T col t0) :
    T.edgeOf (pairedDart T col t0 hT q.val.1 q.val.2 q.property t) =
      T.edgeOf (pairedDart T col t0 hT p.val.1 p.val.2 p.property t) := by
  have hm : T.edgeOf (pairedDart T col t0 hT q.val.1 q.val.2 q.property t) ∈
      groupKey T col t0 hT q := Finset.mem_image.mpr ⟨_,
    (pairedEdges_mem_iff T col t0 hT _ _ q.property _).mpr ⟨t, rfl⟩, rfl⟩
  rw [hkey] at hm
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hm
  obtain ⟨u, rfl⟩ := (pairedEdges_mem_iff T col t0 hT _ _ p.property d).mp hd
  have hut := pairedDart_same_black_face T col t0 hT hcol p q u t he
  subst u
  exact he.symm

-- @node: groupKey_eq_endpoints
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), if
[two pairs have the same set of undirected paired edges](hyp:hkey), then [at each
black nonouter face their two assigned vertices agree either in order or in reverse order](goal). -/
lemma groupKey_eq_endpoints (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p q : Pair T col t0)
    (hkey : groupKey T col t0 hT q = groupKey T col t0 hT p)
    (t : blackNonOuter T col t0) :
    (q.val.1.val t = p.val.1.val t ∧ q.val.2.val t = p.val.2.val t) ∨
      (q.val.1.val t = p.val.2.val t ∧ q.val.2.val t = p.val.1.val t) := by
  have hp := pairedDart_spec T col t0 hT p.val.1 p.val.2 p.property t
  have hq := pairedDart_spec T col t0 hT q.val.1 q.val.2 q.property t
  have he := groupKey_eq_pairedDart_edges T col t0 hT hcol p q hkey t
  rcases (T.edgeOf_eq_iff _ _).mp he with he | he
  · exact Or.inl ⟨Subtype.ext (hq.1.symm.trans ((congrArg T.vert he).symm.trans hp.1)),
      Subtype.ext (hq.2.1.symm.trans ((congrArg T.head he).symm.trans hp.2.1))⟩
  · have hi : T.head (T.edgeInv (pairedDart T col t0 hT q.val.1 q.val.2 q.property t)) =
        T.vert (pairedDart T col t0 hT q.val.1 q.val.2 q.property t) :=
      congrArg T.vert (T.edgeInv_involutive _)
    exact Or.inr ⟨Subtype.ext (hq.1.symm.trans (hi.symm.trans
        ((congrArg T.head he).symm.trans hp.2.1))),
      Subtype.ext (hq.2.1.symm.trans ((congrArg T.vert he).symm.trans hp.1))⟩

-- @node: pairTriangleFlag
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a reference pair](hyp:p), [a comparison pair](hyp:q), and [a black nonouter face](hyp:t),
the [triangle agreement flag](goal) is true exactly when the two pairs' first states
assign the same vertex to that face. -/
noncomputable def pairTriangleFlag (p q : Pair T col t0) (t : blackNonOuter T col t0) : Bool :=
  decide (q.val.1.val t = p.val.1.val t)

-- @node: pairTriangleFlag_step
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), suppose
[two pairs have the same undirected paired edges](hyp:hkey) and [the first state of
the reference pair at the second face equals its second state at the first face](hyp:hu).
Then [the triangle agreement flags at these two faces are equal](goal). -/
lemma pairTriangleFlag_step (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p q : Pair T col t0) (hkey : groupKey T col t0 hT q = groupKey T col t0 hT p)
    (t u : blackNonOuter T col t0) (hu : p.val.1.val u = p.val.2.val t) :
    pairTriangleFlag T col t0 p q t = pairTriangleFlag T col t0 p q u := by
  have hne : t ≠ u := fun h => p.property.distinct t (h ▸ hu)
  rcases groupKey_eq_endpoints T col t0 hT hcol p q hkey t with ht | ht <;>
    rcases groupKey_eq_endpoints T col t0 hT hcol p q hkey u with hv | hv
  · simp [pairTriangleFlag, ht.1, hv.1]
  · exact (hne (q.val.2.property.bijective.1 (ht.2.trans (hu.symm.trans hv.2.symm)))).elim
  · exact (hne (q.val.1.property.bijective.1 (ht.1.trans (hu.symm.trans hv.1.symm)))).elim
  · simp [pairTriangleFlag, ht.1, hv.1, (p.property.distinct t).symm,
      (p.property.distinct u).symm]

-- @node: pairVertexFlag_step
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), if
[two pairs have the same undirected paired edges](hyp:hkey), then [the triangle
agreement flag, read at the face assigned to each vertex by the reference pair's
first state, is unchanged by one step of its pair permutation](goal). -/
lemma pairVertexFlag_step (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p q : Pair T col t0) (hkey : groupKey T col t0 hT q = groupKey T col t0 hT p)
    (v : nonRoot T t0) :
    pairTriangleFlag T col t0 p q ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm
      (pairPermutation T col t0 p.val.1 p.val.2 v)) =
    pairTriangleFlag T col t0 p q ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm v) := by
  obtain ⟨t, rfl⟩ := p.val.1.property.bijective.2 v
  rw [pairPermutation_apply_state]
  change pairTriangleFlag T col t0 p q _ = pairTriangleFlag T col t0 p q
    ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm
      ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective) t))
  rw [Equiv.symm_apply_apply]
  exact (pairTriangleFlag_step T col t0 hT hcol p q hkey t _
    ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective).apply_symm_apply _)).symm

-- @node: bool_constant_on_perm_orbit
/-- If [a Boolean function is unchanged by one application of a permutation](hyp:hb)
and [two elements lie in the same permutation cycle](hyp:h), then [the function
takes the same value at those elements](goal). -/
lemma bool_constant_on_perm_orbit {α : Type} [Finite α] (f : Equiv.Perm α)
    (b : α → Bool) (hb : ∀ v, b (f v) = b v) {v w : α}
    (h : f.SameCycle v w) : b v = b w := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  symm
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hb, ih]

-- @node: pairOrbitFlags
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), [a partition coloring assumption](hyp:hcol),
[a reference pair](hyp:p), and [a comparison pair](hyp:q) with [the same undirected
paired edges](hyp:hkey), the [orbit agreement flags](goal) assign to each reference
permutation orbit the common triangle agreement flag of its vertices. -/
noncomputable def pairOrbitFlags (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p q : Pair T col t0) (hkey : groupKey T col t0 hT q = groupKey T col t0 hT p) :
    orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool :=
  Quotient.lift (fun v => pairTriangleFlag T col t0 p q
    ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm v))
    (fun _ _ h => bool_constant_on_perm_orbit
      (pairPermutation T col t0 p.val.1 p.val.2)
      (fun v => pairTriangleFlag T col t0 p q
        ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm v))
      (pairVertexFlag_step T col t0 hT hcol p q hkey) h)

-- @node: pairOrbitFlags_at_state
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), for
[two pairs with the same undirected paired edges](hyp:hkey), [the agreement flag of
the orbit containing the reference pair's first assigned vertex equals the triangle
agreement flag at that face](goal). -/
lemma pairOrbitFlags_at_state (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p q : Pair T col t0) (hkey : groupKey T col t0 hT q = groupKey T col t0 hT p)
    (t : blackNonOuter T col t0) :
    pairOrbitFlags T col t0 hT hcol p q hkey
      (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t)) =
        pairTriangleFlag T col t0 p q t := by
  change pairTriangleFlag T col t0 p q
    ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm
      ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective) t)) = _
  rw [Equiv.symm_apply_apply]

-- @node: pair_state_orbit_eq
/-- For any pair and any black nonouter face, [the vertices assigned by its first
and second states belong to the same orbit of its pair permutation](goal). -/
lemma pair_state_orbit_eq (p : Pair T col t0) (t : blackNonOuter T col t0) :
    orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t) =
      orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.2.val t) := by
  apply Quotient.sound
  rw [← pairPermutation_apply_state T col t0 p.val.1 p.val.2 t]
  exact (Equiv.Perm.SameCycle.refl _ _).apply_right

-- @node: pair_switch_bijective
/-- For any pair and any Boolean choice on its permutation orbits, [assigning each
black nonouter face its first-state vertex when its orbit's choice is true and its
second-state vertex otherwise gives a bijection onto the nonroot vertices](goal). -/
lemma pair_switch_bijective (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) :
    Function.Bijective (fun t => if b (orbitOf (pairPermutation T col t0 p.val.1 p.val.2)
      (p.val.1.val t)) then p.val.1.val t else p.val.2.val t) := by
  let f := pairPermutation T col t0 p.val.1 p.val.2
  have ho := pair_state_orbit_eq T col t0 p
  constructor
  · intro t u he
    dsimp only at he
    by_cases ht : b (orbitOf f (p.val.1.val t)) = true <;>
      by_cases hu : b (orbitOf f (p.val.1.val u)) = true
    · dsimp only [f] at ht hu
      simp only [ht, hu, ↓reduceIte] at he
      exact p.val.1.property.bijective.1 he
    · dsimp only [f] at ht hu
      simp only [ht, hu, ↓reduceIte] at he
      exact (hu ((congrArg b ((ho u).trans (congrArg (orbitOf f) he).symm)) ▸ ht)).elim
    · dsimp only [f] at ht hu
      simp only [ht, hu, ↓reduceIte] at he
      exact (ht ((congrArg b ((ho t).trans (congrArg (orbitOf f) he))) ▸ hu)).elim
    · dsimp only [f] at ht hu
      simp only [ht, hu, ↓reduceIte] at he
      exact p.val.2.property.bijective.1 he
  · intro v
    by_cases hv : b (orbitOf f v) = true <;> dsimp only [f] at hv
    · obtain ⟨t, ht⟩ := p.val.1.property.bijective.2 v
      refine ⟨t, ?_⟩
      dsimp only
      simp only [ht, hv, ↓reduceIte]
    · obtain ⟨t, ht⟩ := p.val.2.property.bijective.2 v
      refine ⟨t, ?_⟩
      dsimp only
      rw [ho t, ht]
      simp [hv]

-- @node: switchPairState
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a pair of states](hyp:p), and [a Boolean choice for each pair-permutation orbit](hyp:b),
the [switched state](goal) assigns each face its first-state vertex when its orbit's
choice is true and its second-state vertex otherwise. -/
noncomputable def switchPairState (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) : State T col t0 :=
  ⟨fun t => if b (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t))
    then p.val.1.val t else p.val.2.val t,
    ⟨pair_switch_bijective T col t0 p b, by
      intro t
      dsimp only
      by_cases hb : b (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t)) = true
      · simpa [hb] using p.val.1.property.incident t
      · simpa [hb] using p.val.2.property.incident t⟩⟩

-- @node: switchPair
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a pair of states](hyp:p), and [a Boolean choice for each pair-permutation orbit](hyp:b),
the [switched pair](goal) keeps the two state assignments in their original order
on true orbits and exchanges them on false orbits. -/
noncomputable def switchPair (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) : Pair T col t0 :=
  ⟨(switchPairState T col t0 p b, switchPairState T col t0 p (fun k => !b k)),
    ⟨by
      intro t
      change (if b _ then _ else _) ≠ (if !b _ then _ else _)
      cases b (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t))
      · simpa using (p.property.distinct t).symm
      · simpa using p.property.distinct t⟩⟩

-- @node: switchPair_endpoints
/-- For any pair, orbit choices, and black nonouter face, [the switched pair's first
and second assigned vertices are the original first and second vertices when the
orbit choice is true, and the original second and first vertices otherwise](goal). -/
lemma switchPair_endpoints (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool)
    (t : blackNonOuter T col t0) :
    ((switchPair T col t0 p b).val.1.val t =
      if b (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t))
      then p.val.1.val t else p.val.2.val t) ∧
    ((switchPair T col t0 p b).val.2.val t =
      if b (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t))
      then p.val.2.val t else p.val.1.val t) := by
  constructor
  · rfl
  · change (if !b _ then _ else _) = _
    cases b (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t)) <;> rfl

-- @node: switchPair_dart
/-- In [a sphere triangulation](hyp:hT), [the paired dart at a face after switching
is the original dart when that face's orbit choice is true and its reversed dart
otherwise](goal). -/
lemma switchPair_dart (hT : IsSphereTriangulation T) (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool)
    (t : blackNonOuter T col t0) :
    pairedDart T col t0 hT (switchPair T col t0 p b).val.1
      (switchPair T col t0 p b).val.2 (switchPair T col t0 p b).property t =
    if b (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t))
      then pairedDart T col t0 hT p.val.1 p.val.2 p.property t
      else T.edgeInv (pairedDart T col t0 hT p.val.1 p.val.2 p.property t) := by
  have hp := pairedDart_spec T col t0 hT p.val.1 p.val.2 p.property t
  have hq := pairedDart_spec T col t0 hT (switchPair T col t0 p b).val.1
    (switchPair T col t0 p b).val.2 (switchPair T col t0 p b).property t
  have he := switchPair_endpoints T col t0 p b t
  split <;> rename_i hb
  · simp [hb] at he
    apply T.dart_eq_of_endpoints hT.props.2.1
    · exact hq.1.trans ((congrArg Subtype.val he.1).trans hp.1.symm)
    · exact hq.2.1.trans ((congrArg Subtype.val he.2).trans hp.2.1.symm)
  · simp [hb] at he
    apply T.dart_eq_of_endpoints hT.props.2.1
    · exact hq.1.trans ((congrArg Subtype.val he.1).trans hp.2.1.symm)
    · exact hq.2.1.trans ((congrArg Subtype.val he.2).trans
        (hp.1.symm.trans (congrArg T.vert (T.edgeInv_involutive _)).symm))

-- @node: switchPair_groupKey
/-- In [a sphere triangulation](hyp:hT), [switching a pair independently on its
permutation orbits preserves its set of undirected paired edges](goal). -/
lemma switchPair_groupKey (hT : IsSphereTriangulation T) (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) :
    groupKey T col t0 hT (switchPair T col t0 p b) = groupKey T col t0 hT p := by
  have he (t : blackNonOuter T col t0) :
      T.edgeOf (pairedDart T col t0 hT (switchPair T col t0 p b).val.1
        (switchPair T col t0 p b).val.2 (switchPair T col t0 p b).property t) =
      T.edgeOf (pairedDart T col t0 hT p.val.1 p.val.2 p.property t) := by
    rw [switchPair_dart]
    split
    · rfl
    · exact ((T.edgeOf_eq_iff _ _).mpr (Or.inr rfl)).symm
  ext e
  simp only [groupKey, undirectedPairedEdges, Finset.mem_image, pairedEdges_mem_iff]
  constructor <;> rintro ⟨d, ⟨t, rfl⟩, hd⟩
  · exact ⟨_, ⟨t, rfl⟩, (he t).symm.trans hd⟩
  · exact ⟨_, ⟨t, rfl⟩, (he t).trans hd⟩

-- @node: switchPair_flags
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol),
[the orbit agreement flags comparing a pair with its switched pair are exactly
the Boolean choices used for the switch](goal). -/
lemma switchPair_flags (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) :
    pairOrbitFlags T col t0 hT hcol p (switchPair T col t0 p b)
      (switchPair_groupKey T col t0 hT p b) = b := by
  funext k
  induction k using Quotient.inductionOn with | h v =>
    obtain ⟨t, rfl⟩ := p.val.1.property.bijective.2 v
    change pairOrbitFlags T col t0 hT hcol p (switchPair T col t0 p b) _
      (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t)) = _
    rw [pairOrbitFlags_at_state]
    unfold pairTriangleFlag
    rw [(switchPair_endpoints T col t0 p b t).1]
    cases hb : b (orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t)) <;>
      simp_all only [orbitOf, Bool.false_eq_true, ↓reduceIte, decide_true, decide_false,
        (p.property.distinct t).symm]

-- @node: switchPair_of_flags
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), if
[two pairs have the same undirected paired edges](hyp:hkey), then [switching the
reference pair according to their orbit agreement flags recovers the comparison pair](goal). -/
lemma switchPair_of_flags (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p q : Pair T col t0) (hkey : groupKey T col t0 hT q = groupKey T col t0 hT p) :
    switchPair T col t0 p (pairOrbitFlags T col t0 hT hcol p q hkey) = q := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> funext t
  all_goals
    have he := switchPair_endpoints T col t0 p (pairOrbitFlags T col t0 hT hcol p q hkey) t
    rw [pairOrbitFlags_at_state] at he
    rcases groupKey_eq_endpoints T col t0 hT hcol p q hkey t with h | h
  · simpa [pairTriangleFlag, h.1] using he.1
  · simpa [pairTriangleFlag, h.1, (p.property.distinct t).symm] using he.1
  · simpa [pairTriangleFlag, h.1, h.2] using he.2
  · simpa [pairTriangleFlag, h.1, h.2, (p.property.distinct t).symm] using he.2

-- @node: pairGroupOrbitEquiv
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), [a partition coloring assumption](hyp:hcol),
and [a reference pair](hyp:p), the [bijection between pairs with the same undirected
paired edges and Boolean choices on reference permutation orbits](goal) sends each
pair to its orbit agreement flags and reconstructs it by switching the reference pair. -/
noncomputable def pairGroupOrbitEquiv (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) :
    {q : Pair T col t0 // groupKey T col t0 hT q = groupKey T col t0 hT p} ≃
      (orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) where
  toFun q := pairOrbitFlags T col t0 hT hcol p q.val q.property
  invFun b := ⟨switchPair T col t0 p b, switchPair_groupKey T col t0 hT p b⟩
  left_inv q := Subtype.ext (switchPair_of_flags T col t0 hT hcol p q.val q.property)
  right_inv b := switchPair_flags T col t0 hT hcol p b

-- @node: pairOrbitRep_toList_mem
/-- For any pair, permutation orbit, and nonroot vertex, [the vertex appears in the
permutation's cycle list starting from the chosen orbit representative if and only
if it belongs to that orbit](goal). -/
lemma pairOrbitRep_toList_mem (p : Pair T col t0)
    (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) (v : nonRoot T t0) :
    v ∈ (pairPermutation T col t0 p.val.1 p.val.2).toList (pairOrbitRep T col t0 p k) ↔
      orbitOf (pairPermutation T col t0 p.val.1 p.val.2) v = k := by
  let f := pairPermutation T col t0 p.val.1 p.val.2
  have hrep : orbitOf f (pairOrbitRep T col t0 p k) = k :=
    Classical.choose_spec (Quotient.exists_rep k)
  rw [Equiv.Perm.mem_toList_iff, and_iff_left
    (Equiv.Perm.mem_support.mpr (pairPermutation_fixedPointFree T col t0 _ _ p.property (pairOrbitRep T col t0 p k)))]
  exact ⟨fun h => (Quotient.sound h).symm.trans hrep,
    fun h => Quotient.exact (hrep.trans h.symm)⟩

-- @node: pairCycleAt_mem_iff
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol), [a dart
belongs to the paired cycle of an orbit if and only if it is the paired dart of
some black nonouter face whose first-state vertex lies in that orbit](goal). -/
lemma pairCycleAt_mem_iff (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (k : orbitType (pairPermutation T col t0 p.val.1 p.val.2))
    (d : T.Dart) : d ∈ (pairCycleAt T col t0 hT hcol p k).val ↔
      ∃ t : blackNonOuter T col t0,
        orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t) = k ∧
        pairedDart T col t0 hT p.val.1 p.val.2 p.property t = d := by
  change d ∈ ((pairPermutation T col t0 p.val.1 p.val.2).toList
    (pairOrbitRep T col t0 p k)).map (pairedVertexDart T col t0 hT _ _ p.property) ↔ _
  constructor
  · intro hd
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hd
    let t := (Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm v
    refine ⟨t, ?_, rfl⟩
    have ht : p.val.1.val t = v :=
      (Equiv.ofBijective p.val.1.val p.val.1.property.bijective).apply_symm_apply v
    rw [ht]
    exact (pairOrbitRep_toList_mem T col t0 p k v).mp hv
  · rintro ⟨t, ht, rfl⟩
    apply List.mem_map.mpr
    refine ⟨p.val.1.val t, (pairOrbitRep_toList_mem T col t0 p k _).mpr ht, ?_⟩
    change pairedDart T col t0 hT _ _ p.property
      ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm
        ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective) t)) = _
    rw [Equiv.symm_apply_apply]

-- @node: pairCycleAt_injective
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol),
[distinct permutation orbits of a pair give distinct paired cycles](goal). -/
lemma pairCycleAt_injective (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) : Function.Injective (pairCycleAt T col t0 hT hcol p) := by
  intro k j he
  obtain ⟨t, ht⟩ := p.val.1.property.bijective.2 (pairOrbitRep T col t0 p k)
  have hk : orbitOf (pairPermutation T col t0 p.val.1 p.val.2) (p.val.1.val t) = k := by
    rw [ht]
    exact Classical.choose_spec (Quotient.exists_rep k)
  have hm := (pairCycleAt_mem_iff T col t0 hT hcol p k _).mpr ⟨t, hk, rfl⟩
  rw [he] at hm
  obtain ⟨u, hu, hut⟩ := (pairCycleAt_mem_iff T col t0 hT hcol p j _).mp hm
  have hut' := pairedDart_injective T col t0 hT _ _ p.property hut
  subst u
  exact hk.symm.trans hu

-- @node: pairCycleEquiv
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation assumption](hyp:hT), [a partition coloring assumption](hyp:hcol),
and [a pair](hyp:p), the [bijection from pair-permutation orbits to paired cycles](goal)
assigns to each orbit its directed paired cycle. -/
noncomputable def pairCycleEquiv (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) :
    orbitType (pairPermutation T col t0 p.val.1 p.val.2) ≃ pairedCycles T col t0 hT hcol p :=
  by
  letI : Fintype (orbitType (pairPermutation T col t0 p.val.1 p.val.2)) := Fintype.ofFinite _
  exact Equiv.ofBijective (fun k => ⟨pairCycleAt T col t0 hT hcol p k,
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩) ⟨by
      intro k j he
      exact pairCycleAt_injective T col t0 hT hcol p (congrArg Subtype.val he), by
      rintro ⟨C, hC⟩
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hC
      exact ⟨k, Subtype.ext hk⟩⟩

-- @node: switchPair_cycle_union
/-- In [a sphere triangulation](hyp:hT) with [a partition coloring](hyp:hcol),
[the switched pair's directed paired edges are the union of the original paired
cycles, keeping each cycle's direction on true orbits and reversing it on false orbits](goal). -/
lemma switchPair_cycle_union (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0)
    (b : orbitType (pairPermutation T col t0 p.val.1 p.val.2) → Bool) :
    pairedEdges T col t0 hT (switchPair T col t0 p b).val.1
      (switchPair T col t0 p b).val.2 (switchPair T col t0 p b).property =
    (pairedCycles T col t0 hT hcol p).attach.biUnion (fun C =>
      if b ((pairCycleEquiv T col t0 hT hcol p).symm C) then C.val.val.toFinset
      else (reverseDarts T C.val.val).toFinset) := by
  let e := pairCycleEquiv T col t0 hT hcol p
  let f := pairPermutation T col t0 p.val.1 p.val.2
  ext d
  constructor
  · intro hd
    obtain ⟨t, rfl⟩ := (pairedEdges_mem_iff T col t0 hT _ _
      (switchPair T col t0 p b).property d).mp hd
    let k := orbitOf f (p.val.1.val t)
    have hm : pairedDart T col t0 hT p.val.1 p.val.2 p.property t ∈ (e k).val.val :=
      (pairCycleAt_mem_iff T col t0 hT hcol p k _).mpr ⟨t, rfl, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨e k, Finset.mem_attach _ _, ?_⟩
    change _ ∈ if b (e.symm (e k)) then _ else _
    rw [e.symm_apply_apply, switchPair_dart]
    change (if b k then pairedDart T col t0 hT p.val.1 p.val.2 p.property t
      else T.edgeInv (pairedDart T col t0 hT p.val.1 p.val.2 p.property t)) ∈
        if b k then (e k).val.val.toFinset else (reverseDarts T (e k).val.val).toFinset
    by_cases hb : b k = true
    · rw [if_pos hb, if_pos hb]
      exact List.mem_toFinset.mpr hm
    · rw [if_neg hb, if_neg hb]
      exact List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨_, List.mem_reverse.mpr hm, rfl⟩)
  · intro hd
    obtain ⟨C, _, hd⟩ := Finset.mem_biUnion.mp hd
    let k := e.symm C
    have hC : pairCycleAt T col t0 hT hcol p k = C.val :=
      congrArg Subtype.val (e.apply_symm_apply C)
    change d ∈ (if b k then C.val.val.toFinset else (reverseDarts T C.val.val).toFinset) at hd
    by_cases hb : b k = true
    · rw [if_pos hb] at hd
      have hm : d ∈ (pairCycleAt T col t0 hT hcol p k).val := by
        rw [hC]
        exact List.mem_toFinset.mp hd
      obtain ⟨t, ht, htd⟩ := (pairCycleAt_mem_iff T col t0 hT hcol p k d).mp hm
      apply (pairedEdges_mem_iff T col t0 hT _ _ (switchPair T col t0 p b).property d).mpr
      refine ⟨t, ?_⟩
      rw [switchPair_dart, ht, if_pos hb, htd]
    · rw [if_neg hb] at hd
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
      have hm : a ∈ (pairCycleAt T col t0 hT hcol p k).val := by
        rw [hC]
        exact List.mem_reverse.mp ha
      obtain ⟨t, ht, hta⟩ := (pairCycleAt_mem_iff T col t0 hT hcol p k a).mp hm
      apply (pairedEdges_mem_iff T col t0 hT _ _ (switchPair T col t0 p b).property _).mpr
      refine ⟨t, ?_⟩
      rw [switchPair_dart, ht, if_neg hb, hta]

end OaiPairedStatesHamiltonian
