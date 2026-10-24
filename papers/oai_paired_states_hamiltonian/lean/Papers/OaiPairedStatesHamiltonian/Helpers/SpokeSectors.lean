module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SpokeProjection
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleExterior

/-! Paths between glued complementary regions lift to paths through individual
sectors, with equivalence steps for gluing and explicit crossings of retained
spokes. This layer uses only the rotation and the face quotient. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

section QuotientPaths
variable {α : Type*} (r s : α → α → Prop)

-- @node: gluedStep
/-- Given [a gluing relation](hyp:r) and [a crossing relation](hyp:s), a
[combined step](goal) between [two objects](hyp:a,b) either identifies them
through a chain of gluings or crosses directly from the first to the second. -/
noncomputable def gluedStep (a b : α) : Prop := Relation.EqvGen r a b ∨ s a b

-- @node: quotientCrossing
/-- For [a gluing relation](hyp:r), [a crossing relation](hyp:s), and [two
gluing classes](hyp:a,b), a [crossing between the classes](goal) means that
there are representatives with [a crossing between them](step:1), [the first
in the first class](step:2), and [the second in the second class](step:3). -/
noncomputable def quotientCrossing
    (a b : Quotient (Relation.EqvGen.setoid r)) : Prop :=
  ∃ x y, s x y ∧ Quotient.mk _ x = a ∧ Quotient.mk _ y = b

-- @node: quotient_path_iff_glued_path
/-- Given a gluing relation, a crossing relation, and [two
objects](hyp:a,b), [a finite crossing path between their gluing classes exists
if and only if a finite path between the objects exists whose steps are
gluings or crossings](goal); paths of length zero are allowed. -/
lemma quotient_path_iff_glued_path (a b : α) :
    Relation.ReflTransGen (quotientCrossing r s) (Quotient.mk _ a) (Quotient.mk _ b) ↔
      Relation.ReflTransGen (gluedStep r s) a b := by
  constructor
  · intro h
    have lift {x y : Quotient (Relation.EqvGen.setoid r)}
        (p : Relation.ReflTransGen (quotientCrossing r s) x y) :
        ∀ a b, Quotient.mk _ a = x → Quotient.mk _ b = y →
          Relation.ReflTransGen (gluedStep r s) a b := by
      induction p with
      | refl =>
        intro a b ha hb
        exact Relation.ReflTransGen.single (Or.inl (Quotient.exact (ha.trans hb.symm)))
      | @tail y z p h ih =>
        intro a b ha hb
        obtain ⟨u, v, huv, hu, hv⟩ := h
        have h1 : Relation.ReflTransGen (gluedStep r s) u v :=
          .single (Or.inr huv)
        have h2 : Relation.ReflTransGen (gluedStep r s) v b :=
          .single (Or.inl (Quotient.exact (hv.trans hb.symm)))
        exact (ih a u ha hu).trans (h1.trans h2)
    exact lift h a b rfl rfl
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c p h ih =>
      rcases h with h | h
      · have hq : Quotient.mk (Relation.EqvGen.setoid r) b = Quotient.mk _ c :=
          Quotient.sound h
        exact hq ▸ ih
      · exact ih.tail ⟨b, c, h, rfl, rfl⟩

end QuotientPaths

variable (T : SphereMap)

-- @node: spokeSectorAt
/-- For [a spherical map](hyp:T), [selected faces](hyp:faces), and [a directed
spoke](hyp:d), the [sector on its left](goal) is the preceding corner's sector
when it points toward a face center, and its supplying corner's sector otherwise. -/
noncomputable def spokeSectorAt (faces : Finset T.Face) (d : SpokeDart T faces) :
    SpokePiece T faces := Sum.inr (if d.2 then prevCorner T faces d.1 else d.1)

-- @node: spokeSectorAt_class
/-- In a spherical map with [selected faces](hyp:faces), for [a
directed spoke](hyp:d), [the gluing class of its left sector is its assigned
complementary region](goal). -/
lemma spokeSectorAt_class (faces : Finset T.Face) (d : SpokeDart T faces) :
    spokeFaceClass T faces (spokeSectorAt T faces d) = spokeDartFace T faces d := rfl

-- @node: spokeSectorCrossing
/-- For [a spherical map](hyp:T) [that is a triangulation](hyp:hT), [selected
faces](hyp:faces) with [no edge selected on both sides](hyp:hfaces), [a set of
excluded spoke edges](hyp:S), and [two pieces](hyp:a,b), a [sector crossing](goal)
exists when some directed spoke has [its edge outside the excluded set](step:1),
[the first piece as its left sector](step:2), and [the second piece as the
left sector of its reverse](step:3). -/
noncomputable def spokeSectorCrossing (hT : IsSphereTriangulation T)
    (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (S : Set (spokeRotation T hT faces hfaces).Edge) (a b : SpokePiece T faces) : Prop :=
  ∃ d : SpokeDart T faces, (spokeRotation T hT faces hfaces).edgeOf d ∉ S ∧
    spokeSectorAt T faces d = a ∧
      spokeSectorAt T faces ((spokeRotation T hT faces hfaces).edgeInv d) = b

-- @node: spokeFaceCrossing
/-- For [a spherical map](hyp:T) [that is a triangulation](hyp:hT), [selected
faces](hyp:faces) with [no edge selected on both sides](hyp:hfaces), [excluded
spoke edges](hyp:S), and [two glued regions](hyp:a,b), a [region crossing](goal)
exists when some directed spoke has [its edge outside the excluded set](step:1),
[the first region on its left](step:2), and [the second region on the left of
its reverse](step:3). -/
noncomputable def spokeFaceCrossing (hT : IsSphereTriangulation T)
    (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (S : Set (spokeRotation T hT faces hfaces).Edge) (a b : SpokeFace T faces) : Prop :=
  ∃ d : SpokeDart T faces, (spokeRotation T hT faces hfaces).edgeOf d ∉ S ∧
    spokeDartFace T faces d = a ∧
      spokeDartFace T faces ((spokeRotation T hT faces hfaces).edgeInv d) = b

-- @node: spoke_quotient_crossing_eq
/-- For a spherical map [that is a triangulation](hyp:hT) with
[selected faces](hyp:faces) such that [no edge is selected on both sides](hyp:hfaces),
and [excluded spoke edges](hyp:S), [the crossing relation induced on gluing
classes by sector crossings equals the direct region crossing relation](goal). -/
lemma spoke_quotient_crossing_eq (hT : IsSphereTriangulation T)
    (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (S : Set (spokeRotation T hT faces hfaces).Edge) :
    quotientCrossing (spokePieceRelation T faces) (spokeSectorCrossing T hT faces hfaces S) =
      spokeFaceCrossing T hT faces hfaces S := by
  funext a b
  apply propext
  constructor
  · rintro ⟨x, y, ⟨d, hd, hx, hy⟩, hxa, hyb⟩
    exact ⟨d, hd, (congrArg (spokeFaceClass T faces) hx).trans hxa,
      (congrArg (spokeFaceClass T faces) hy).trans hyb⟩
  · rintro ⟨d, hd, ha, hb⟩
    exact ⟨_, _, ⟨d, hd, rfl, rfl⟩, ha, hb⟩

-- @node: spoke_face_path_iff_sector_path
/-- For a spherical map [that is a triangulation](hyp:hT), [selected
faces](hyp:faces) with [no edge selected on both sides](hyp:hfaces), [excluded
spoke edges](hyp:S), and [two pieces](hyp:a,b), [their regions are connected by
a finite path crossing only nonexcluded spokes if and only if the pieces are
connected by a finite path of gluings and crossings of nonexcluded spokes](goal). -/
lemma spoke_face_path_iff_sector_path (hT : IsSphereTriangulation T)
    (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (S : Set (spokeRotation T hT faces hfaces).Edge) (a b : SpokePiece T faces) :
    Relation.ReflTransGen (spokeFaceCrossing T hT faces hfaces S)
      (spokeFaceClass T faces a) (spokeFaceClass T faces b) ↔
    Relation.ReflTransGen
      (gluedStep (spokePieceRelation T faces) (spokeSectorCrossing T hT faces hfaces S)) a b := by
  rw [← spoke_quotient_crossing_eq T hT faces hfaces S]
  exact quotient_path_iff_glued_path _ _ a b

section SectorValues
variable {β : Type*} (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (value : T.Face → β)

-- @node: spokePieceValue
/-- For [a spherical map](hyp:T), [selected faces](hyp:faces), and [values
assigned to the original faces](hyp:value), the [value of a piece](goal) is
[its original face's value for an unselected face](step:1), and [the value of
the face across its supplying side for a selected-face sector](step:2). -/
noncomputable def spokePieceValue : SpokePiece T faces → β
  | Sum.inl f => value f.val
  | Sum.inr d => value (T.faceOf (T.edgeInv d.val))

include hfaces in
-- @node: spokePieceValue_across
/-- In a spherical map with selected faces satisfying
no edge is selected on both sides, let face values
[agree across every edge whose two faces are unselected](hyp:hvalue).
Then [the pieces on opposite sides of any oriented edge have equal values](goal),
for [each oriented edge](hyp:d). -/
lemma spokePieceValue_across
    (hvalue : ∀ d, T.faceOf d ∉ faces → T.faceOf (T.edgeInv d) ∉ faces →
      value (T.faceOf d) = value (T.faceOf (T.edgeInv d))) (d : T.Dart) :
    spokePieceValue T faces value (spokePieceAt T faces d) =
      spokePieceValue T faces value (spokePieceAt T faces (T.edgeInv d)) := by
  by_cases hd : T.faceOf d ∈ faces
  · have hi : T.faceOf (T.edgeInv d) ∉ faces := fun h => hfaces d ⟨hd, h⟩
    simp only [spokePieceAt, dif_pos hd, dif_neg hi, spokePieceValue]
  · by_cases hi : T.faceOf (T.edgeInv d) ∈ faces
    · simp only [spokePieceAt, dif_neg hd, dif_pos hi, spokePieceValue,
        T.edgeInv_involutive d]
    · simp only [spokePieceAt, dif_neg hd, dif_neg hi, spokePieceValue]
      exact hvalue d hd hi

include hfaces in
-- @node: spokePieceValue_eq_of_glued
/-- In a spherical map with selected faces such that
no edge is selected on both sides, if face values
[agree across edges between unselected faces](hyp:hvalue) and [two pieces](hyp:a,b)
[are equivalent under gluing](hyp:h), then [those pieces have equal values](goal). -/
lemma spokePieceValue_eq_of_glued
    (hvalue : ∀ d, T.faceOf d ∉ faces → T.faceOf (T.edgeInv d) ∉ faces →
      value (T.faceOf d) = value (T.faceOf (T.edgeInv d)))
    {a b : SpokePiece T faces} (h : Relation.EqvGen (spokePieceRelation T faces) a b) :
    spokePieceValue T faces value a = spokePieceValue T faces value b := by
  induction h with
  | rel a b h =>
    obtain ⟨d, rfl, rfl⟩ := h
    exact spokePieceValue_across T faces hfaces value hvalue d
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hab hbc => exact hab.trans hbc

-- @node: spokeFaceValue
/-- For [a spherical map](hyp:T), [selected faces](hyp:faces) with [no edge
selected on both sides](hyp:hfaces), and [face values](hyp:value) that
[agree across edges between unselected faces](hyp:hvalue), the [value of a
glued region](goal) is the value of any of its pieces. -/
noncomputable def spokeFaceValue
    (hvalue : ∀ d, T.faceOf d ∉ faces → T.faceOf (T.edgeInv d) ∉ faces →
      value (T.faceOf d) = value (T.faceOf (T.edgeInv d))) : SpokeFace T faces → β :=
  Quotient.lift (spokePieceValue T faces value)
    (fun _ _ h => spokePieceValue_eq_of_glued T faces hfaces value hvalue h)

-- @node: spokeFaceValue_unselected
/-- In a spherical map with selected faces such that
no edge is selected on both sides, suppose face values
[agree across edges between unselected faces](hyp:hvalue). For [a face](hyp:f)
[that is unselected](hyp:hf), [the value of its glued region equals its original
face value](goal). -/
lemma spokeFaceValue_unselected
    (hvalue : ∀ d, T.faceOf d ∉ faces → T.faceOf (T.edgeInv d) ∉ faces →
      value (T.faceOf d) = value (T.faceOf (T.edgeInv d))) (f : T.Face) (hf : f ∉ faces) :
    spokeFaceValue T faces hfaces value hvalue
      (spokeFaceClass T faces (Sum.inl ⟨f, hf⟩)) = value f := rfl

-- @node: spokeFaceValue_sector
/-- In a spherical map with selected faces such that
no edge is selected on both sides, suppose face values
[agree across edges between unselected faces](hyp:hvalue). For [a corner of a
selected face](hyp:d), [the value of its sector's glued region equals the
value of the face across its supplying side](goal). -/
lemma spokeFaceValue_sector
    (hvalue : ∀ d, T.faceOf d ∉ faces → T.faceOf (T.edgeInv d) ∉ faces →
      value (T.faceOf d) = value (T.faceOf (T.edgeInv d))) (d : SpokeCorner T faces) :
    spokeFaceValue T faces hfaces value hvalue (spokeFaceClass T faces (Sum.inr d)) =
      value (T.faceOf (T.edgeInv d.val)) := rfl

end SectorValues

-- @node: cycle_side_value_glues
/-- In a spherical map [that is connected](hyp:hc), let [selected
faces](hyp:faces) and [a cycle](hyp:D) satisfy [every cycle edge has a selected
face on at least one side](hyp:hD). For [an oriented edge](hyp:d) with [its own
face unselected](hyp:hd) and [its reverse face unselected](hyp:hi), [the two
faces have the same truth value for lying in the cycle's left region](goal). -/
lemma cycle_side_value_glues (hc : T.IsConnectedMap) (faces : Finset T.Face)
    (D : T.Cycle)
    (hD : ∀ e ∈ D.val, T.faceOf e ∈ faces ∨ T.faceOf (T.edgeInv e) ∈ faces)
    (d : T.Dart) (hd : T.faceOf d ∉ faces) (hi : T.faceOf (T.edgeInv d) ∉ faces) :
    (T.faceOf d ∈ T.leftRegion D) = (T.faceOf (T.edgeInv d) ∈ T.leftRegion D) := by
  apply propext
  apply T.leftRegion_across_noncycle hc D d
  intro he
  obtain ⟨e, he, hed⟩ := List.mem_map.mp he
  have hs := hD e he
  rcases (T.edgeOf_eq_iff e d).mp hed with h | h
  · subst d
    exact hs.elim hd hi
  · subst d
    rw [T.edgeInv_involutive] at hi
    exact hs.elim hi hd

-- @node: projectSpokeDarts_selected_side
/-- In a spherical map with [a Boolean face coloring](hyp:col) and
[a distinguished outer face](hyp:t0), assume [the map is a triangulation](hyp:hT)
and [opposite sides of every edge have different colors](hyp:hcol). Given
[a cycle of the bounded spoke graph](hyp:C) and [an original oriented edge](hyp:e)
[appearing in its projected edge list](hyp:he), [at least one face incident
to that edge is black and is not the outer face](goal). -/
lemma projectSpokeDarts_selected_side (col : T.Face → Bool) (t0 : T.Face)
    (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle) (e : T.Dart)
    (he : e ∈ projectSpokeDarts T (blackNonOuter T col t0) C.val) :
    T.faceOf e ∈ blackNonOuter T col t0 ∨
      T.faceOf (T.edgeInv e) ∈ blackNonOuter T col t0 := by
  unfold projectSpokeDarts at he
  obtain ⟨⟨a, b⟩, hab, he⟩ := List.mem_filterMap.mp he
  by_cases ha : a.2 = true
  swap
  · simp [ha] at he
  have hex := spoke_shortcut_exists T col t0 hT hcol C a b hab ha
  simp only [ha, ↓reduceIte, dif_pos hex, Option.some.injEq] at he
  have hside := (Classical.choose_spec hex).2.2
  rw [he] at hside
  exact hside.elim (fun h => Or.inl (h.symm ▸ a.1.property))
    (fun h => Or.inr (h.symm ▸ a.1.property))

-- @node: projected_side_glues
/-- For a spherical map, [a Boolean face coloring](hyp:col), and
[a distinguished outer face](hyp:t0), assume [a triangulation](hyp:hT) and
[different colors across every edge](hyp:hcol). Given [a bounded spoke
cycle](hyp:C) and [an original oriented edge](hyp:d) with [its own face outside
the black nonouter faces](hyp:hd) and [its reverse face outside that set](hyp:hi),
[both faces have the same truth value for belonging to the projected cycle's
left region](goal). -/
lemma projected_side_glues (col : T.Face → Bool) (t0 : T.Face)
    (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle) (d : T.Dart)
    (hd : T.faceOf d ∉ blackNonOuter T col t0)
    (hi : T.faceOf (T.edgeInv d) ∉ blackNonOuter T col t0) :
    (T.faceOf d ∈ T.leftRegion
      ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
        project_spoke_cycle T col t0 hT hcol C⟩) =
    (T.faceOf (T.edgeInv d) ∈ T.leftRegion
      ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
        project_spoke_cycle T col t0 hT hcol C⟩) :=
  cycle_side_value_glues T hT.props.1 _ _
    (projectSpokeDarts_selected_side T col t0 hT hcol C) d hd hi

-- @node: spokeProjectedSide
/-- For [a spherical map](hyp:T), [a Boolean face coloring](hyp:col), and
[a distinguished outer face](hyp:t0), with [a triangulation](hyp:hT) and
[different colors across every edge](hyp:hcol), the [projected left-side
predicate on glued spoke regions](goal) associated with [a bounded spoke
cycle](hyp:C) descends from membership in the projected cycle's left region. -/
noncomputable def spokeProjectedSide (col : T.Face → Bool) (t0 : T.Face)
    (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    SpokeFace T (blackNonOuter T col t0) → Prop :=
  spokeFaceValue T (blackNonOuter T col t0) (bounded_faces_disjoint T col t0 hcol)
    (fun f => f ∈ T.leftRegion
      ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
        project_spoke_cycle T col t0 hT hcol C⟩)
    (projected_side_glues T col t0 hT hcol C)

-- @node: spokeProjectedSide_outer
/-- For a spherical map, [a Boolean face coloring](hyp:col), and
[a distinguished outer face](hyp:t0), assume [a triangulation](hyp:hT) and
[different colors across every edge](hyp:hcol). For [a bounded spoke cycle](hyp:C),
[the outer spoke region satisfies the projected left-side predicate if and
only if the original outer face lies in the projected cycle's left region](goal). -/
lemma spokeProjectedSide_outer (col : T.Face → Bool) (t0 : T.Face)
    (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    spokeProjectedSide T col t0 hT hcol C (spokeOuter T col t0 hT hcol) ↔
      t0 ∈ T.leftRegion
        ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
          project_spoke_cycle T col t0 hT hcol C⟩ := Iff.rfl

end OaiPairedStatesHamiltonian
