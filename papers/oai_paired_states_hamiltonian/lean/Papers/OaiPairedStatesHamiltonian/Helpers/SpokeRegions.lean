module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SpokeGenus

/-! Inherited spoke embeddings, their cycle projections, and signed incidence weights. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


variable (T : SphereMap)

/-- For [a spherical map](hyp:T) and [a set of selected faces](hyp:faces), the
[pieces left after inserting spokes](goal) are [the unselected faces](step:1)
and [one sector for each side of a selected face](step:2). -/
abbrev SpokePiece (faces : Finset T.Face) := {f : T.Face // f ∉ faces} ⊕ SpokeCorner T faces
/-- For [a spherical map](hyp:T), [selected faces](hyp:faces), and [an oriented
edge](hyp:d), the [piece incident to that edge](goal) is its side's sector when
its face is selected, and otherwise its entire face. -/
noncomputable def spokePieceAt (faces : Finset T.Face) (d : T.Dart) : SpokePiece T faces :=
  if h : T.faceOf d ∈ faces then Sum.inr ⟨d, h⟩ else Sum.inl ⟨T.faceOf d, h⟩
/-- In [a spherical map](hyp:T) with [selected faces](hyp:faces), [two pieces](hyp:a,b)
are [directly glued](goal) when some oriented edge has [the first piece on its
own side](step:1) and [the second piece on its reverse side](step:2). -/
noncomputable def spokePieceRelation (faces : Finset T.Face) (a b : SpokePiece T faces) : Prop :=
  ∃ d : T.Dart, spokePieceAt T faces d = a ∧ spokePieceAt T faces (T.edgeInv d) = b
/-- For [a spherical map](hyp:T) and [selected faces](hyp:faces), the [glued
complementary regions](goal) are pieces identified whenever they can be joined
by a sequence of direct gluings. -/
abbrev SpokeFace (faces : Finset T.Face) := Quotient (Relation.EqvGen.setoid (spokePieceRelation T faces))
/-- For [a spherical map](hyp:T) and [selected faces](hyp:faces), the [region
containing a piece](goal) is the gluing class of [that piece](hyp:a). -/
noncomputable def spokeFaceClass (faces : Finset T.Face) (a : SpokePiece T faces) : SpokeFace T faces :=
  Quotient.mk _ a
/-- For [a spherical map](hyp:T) and [selected faces](hyp:faces), the [glued
complementary regions have a finite enumeration](goal). -/
noncomputable instance (faces : Finset T.Face) : Fintype (SpokeFace T faces) := Fintype.ofFinite _
/-- For [a spherical map](hyp:T) and [selected faces](hyp:faces), [equality of
glued complementary regions can be decided](goal). -/
noncomputable instance (faces : Finset T.Face) : DecidableEq (SpokeFace T faces) := Classical.decEq _

-- @node: prevCorner_mem
/-- In a spherical map, given [selected faces](hyp:faces) and [a corner
of a selected face](hyp:d), [the preceding corner along its face also belongs
to a selected face](goal). -/
lemma prevCorner_mem (faces : Finset T.Face) (d : SpokeCorner T faces) :
    T.faceOf (T.facePerm.symm d.val) ∈ faces := by
  rw [← T.dual_rot_vertex (T.facePerm.symm d.val), T.facePerm.apply_symm_apply]
  exact d.property
/-- For [a spherical map](hyp:T), [selected faces](hyp:faces), and [a selected
face corner](hyp:d), the [previous corner](goal) is its predecessor along the
boundary of the same face. -/
noncomputable def prevCorner (faces : Finset T.Face) (d : SpokeCorner T faces) : SpokeCorner T faces :=
  ⟨T.facePerm.symm d.val, prevCorner_mem T faces d⟩
/-- In [a spherical map](hyp:T) with [selected faces](hyp:faces), the [region
on the left of a directed spoke](goal) is the class of the preceding corner's
sector if [the spoke](hyp:d) points toward a face center, and of its supplying
corner's sector otherwise. -/
noncomputable def spokeDartFace (faces : Finset T.Face) (d : SpokeDart T faces) : SpokeFace T faces :=
  spokeFaceClass T faces (Sum.inr (if d.2 then prevCorner T faces d.1 else d.1))

-- @node: triangulation_vertex_has_dart
/-- If a spherical map [is a triangulation](hyp:hT), then at
[any vertex](hyp:v) [there is an oriented edge based at that vertex](goal). -/
lemma triangulation_vertex_has_dart (hT : IsSphereTriangulation T) (v : T.Vertex) :
    ∃ d, T.vert d = v := by
  exact triangulation_has_dart_at_vertex T hT v
/-- For [a spherical map](hyp:T) [that is a triangulation](hyp:hT) with
[selected faces](hyp:faces), the [region assigned to an original vertex](goal)
is obtained from an arbitrarily chosen oriented edge based at [that vertex](hyp:v). -/
noncomputable def spokeVertexFace (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (v : T.Vertex) : SpokeFace T faces :=
  spokeFaceClass T faces (spokePieceAt T faces (Classical.choose (triangulation_vertex_has_dart T hT v)))

-- @node: spokeFaceClass_across
/-- In a spherical map with [selected faces](hyp:faces), [the pieces
on opposite sides of an oriented edge belong to the same glued region](goal),
for [every oriented edge](hyp:d). -/
lemma spokeFaceClass_across (faces : Finset T.Face) (d : T.Dart) :
    spokeFaceClass T faces (spokePieceAt T faces d) =
      spokeFaceClass T faces (spokePieceAt T faces (T.edgeInv d)) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨d, rfl, rfl⟩)

-- @node: SphereMap.facePerm_symm_rot
/-- In a spherical map, for [an oriented edge](hyp:d), [rotating once
around its initial vertex and then moving backward along the face boundary
gives the reversed edge](goal). -/
lemma SphereMap.facePerm_symm_rot (d : T.Dart) :
    T.facePerm.symm (T.rot d) = T.edgeInv d := by
  apply T.facePerm.injective
  rw [T.facePerm.apply_symm_apply]
  change T.rot d = T.rot (T.edgeInv (T.edgeInv d))
  rw [T.edgeInv_involutive]

-- @node: spokeFaceClass_skip
/-- In a spherical map with [selected faces](hyp:faces), start at
[an oriented edge](hyp:d) and take [a number of vertex rotations](hyp:n).
If [this number is positive](hyp:hn) and [every strictly intermediate rotation
has an unselected face](hyp:hdel), then [the piece preceding the final edge
along its face and the starting piece belong to the same glued region](goal). -/
lemma spokeFaceClass_skip (faces : Finset T.Face) (d : T.Dart) (n : ℕ) (hn : 0 < n)
    (hdel : ∀ m, 0 < m → m < n → T.faceOf ((T.rot ^ m) d) ∉ faces) :
    spokeFaceClass T faces (spokePieceAt T faces (T.facePerm.symm ((T.rot ^ n) d))) =
      spokeFaceClass T faces (spokePieceAt T faces d) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, T.facePerm_symm_rot]
    apply (spokeFaceClass_across T faces ((T.rot ^ n) d)).symm.trans
    by_cases hz : n = 0
    · subst n
      rfl
    · have hp : 0 < n := Nat.pos_of_ne_zero hz
      have hd := hdel n hp (Nat.lt_succ_self n)
      have hf : T.faceOf (T.facePerm.symm ((T.rot ^ n) d)) =
          T.faceOf ((T.rot ^ n) d) := by
        rw [← T.dual_rot_vertex (T.facePerm.symm ((T.rot ^ n) d)),
          T.facePerm.apply_symm_apply]
      have hprev : T.faceOf (T.facePerm.symm ((T.rot ^ n) d)) ∉ faces := by
        rw [hf]
        exact hd
      have he : spokePieceAt T faces ((T.rot ^ n) d) =
          spokePieceAt T faces (T.facePerm.symm ((T.rot ^ n) d)) := by
        simp only [spokePieceAt, dif_neg hd, dif_neg hprev]
        exact congrArg Sum.inl (Subtype.ext hf.symm)
      exact (congrArg (spokeFaceClass T faces) he).trans
        (ih hp (fun m hm hmn => hdel m hm (by omega)))

set_option backward.isDefEq.respectTransparency false in
-- @node: spokeDartFace_facePerm
/-- For a spherical map [that is a triangulation](hyp:hT) with
[selected faces](hyp:faces) such that [no edge has selected faces on both
sides](hyp:hfaces), [moving a directed spoke one step along its face boundary
preserves its assigned region](goal), for [every directed spoke](hyp:d). -/
lemma spokeDartFace_facePerm (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (d : SpokeDart T faces) :
    spokeDartFace T faces ((spokeRotation T hT faces hfaces).facePerm d) =
      spokeDartFace T faces d := by
  let N := spokeRotation T hT faces hfaces
  have spec := (Classical.choose_spec (exists_spokePerms T hT faces hfaces)).2.1
  rcases d with ⟨d, b⟩
  cases b
  · have hs := spec (d, true)
    change (N.rot (d, true)).2 = true ∧
      (N.rot (d, true)).1 = firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d at hs
    have he : N.facePerm (d, false) =
        (firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d, true) := by
      change N.rot (N.edgeInv (d, false)) = _
      rw [spokeRotation_edgeInv]
      exact Prod.ext hs.2 hs.1
    change spokeDartFace T faces (N.facePerm (d, false)) = _
    rw [he]
    obtain ⟨n, hn, hval, hdel⟩ := Classical.choose_spec
      (exists_firstReturnPerm T.rot {d | T.faceOf d ∈ faces}) d
    change (firstReturnPerm T.rot _ d).val = (T.rot ^ n) d.val at hval
    have h := spokeFaceClass_skip T faces d.val n hn hdel
    rw [← hval] at h
    let e := firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d
    have ha : spokePieceAt T faces (T.facePerm.symm e.val) =
        Sum.inr (prevCorner T faces e) := by
      rw [spokePieceAt, dif_pos (prevCorner_mem T faces e)]
      rfl
    have hb : spokePieceAt T faces d.val = Sum.inr d := by
      rw [spokePieceAt, dif_pos d.property]
    exact (congrArg (spokeFaceClass T faces) ha).symm.trans
      (h.trans (congrArg (spokeFaceClass T faces) hb))
  · have hs := spec (d, false)
    change (N.rot (d, false)).2 = false ∧
      (N.rot (d, false)).1.val = T.facePerm.symm d.val at hs
    have he : N.facePerm (d, true) = (prevCorner T faces d, false) := by
      change N.rot (N.edgeInv (d, true)) = _
      rw [spokeRotation_edgeInv]
      exact Prod.ext (Subtype.ext hs.2) hs.1
    change spokeDartFace T faces (N.facePerm (d, true)) = _
    rw [he]
    rfl

-- @node: exists_spokeBoundaryFace
/-- For a spherical map [that is a triangulation](hyp:hT) with
[selected faces](hyp:faces) such that [no edge has selected faces on both
sides](hyp:hfaces), [there is an assignment of local boundaries to glued
regions that agrees with the region of every directed spoke, and every
isolated vertex is an original vertex assigned its vertex region](goal). -/
lemma exists_spokeBoundaryFace (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    ∃ place : (spokeRotation T hT faces hfaces).LocalBoundary → SpokeFace T faces,
      (∀ d, place (Sum.inl (orbitOf (spokeRotation T hT faces hfaces).facePerm d)) =
        spokeDartFace T faces d) ∧
      (∀ v : (spokeRotation T hT faces hfaces).Puncture,
        ∃ w : T.Vertex, v.val = Sum.inl w ∧ place (Sum.inr v) = spokeVertexFace T hT faces w) := by
  let N := spokeRotation T hT faces hfaces
  have invariant (d e : N.Dart) (h : N.facePerm.SameCycle d e) :
      spokeDartFace T faces d = spokeDartFace T faces e := by
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans (spokeDartFace_facePerm T hT faces hfaces _).symm
  have no_center (v : N.Puncture) (f : faces) : v.val ≠ Sum.inr f := by
    intro hv
    have hc : 0 < (T.faceDarts f.val).card := by
      rw [← T.faceLength_eq_card_faceDarts, (hT.props.2.2.2 f.val).1]
      omega
    obtain ⟨d, hd⟩ := Finset.card_pos.mp hc
    have hf : T.faceOf d = f.val := (Finset.mem_filter.mp hd).2
    let e : SpokeCorner T faces := ⟨d, hf.symm ▸ f.property⟩
    apply v.property (e, false)
    exact (congrArg Sum.inr (Subtype.ext hf)).trans hv.symm
  have original (v : N.Puncture) : ∃ w : T.Vertex, v.val = Sum.inl w := by
    cases hv : v.val with
    | inl w => exact ⟨w, rfl⟩
    | inr f => exact (no_center v f hv).elim
  let place : N.LocalBoundary → SpokeFace T faces := Sum.elim
    (Quotient.lift (spokeDartFace T faces) invariant)
    (fun v => spokeVertexFace T hT faces (Classical.choose (original v)))
  refine ⟨place, fun _ => rfl, ?_⟩
  intro v
  exact ⟨Classical.choose (original v), Classical.choose_spec (original v), rfl⟩
/-- For [a spherical map](hyp:T) [that is a triangulation](hyp:hT) with
[selected faces](hyp:faces) satisfying [the condition that no edge has selected
faces on both sides](hyp:hfaces), the [local boundary placement](goal) chooses
an assignment agreeing with directed spoke regions and original vertex regions. -/
noncomputable def spokeBoundaryFace (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    (spokeRotation T hT faces hfaces).LocalBoundary → SpokeFace T faces :=
  Classical.choose (exists_spokeBoundaryFace T hT faces hfaces)
-- @node: spoke_placement_connected
/-- For a spherical map [that is a triangulation](hyp:hT) with
[selected faces](hyp:faces) such that [no edge has selected faces on both
sides](hyp:hfaces), [the incidence graph joining spoke components to their
assigned complementary regions is connected](goal). -/
lemma spoke_placement_connected (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    ((spokeRotation T hT faces hfaces).placementGraph (SpokeFace T faces)
      (spokeBoundaryFace T hT faces hfaces)).Connected := by
  classical
  let N := spokeRotation T hT faces hfaces
  let place := spokeBoundaryFace T hT faces hfaces
  let G := N.placementGraph (SpokeFace T faces) place
  let rep : T.Face → N.Component ⊕ SpokeFace T faces := fun f =>
    if hf : f ∈ faces then
      Sum.inl (N.toSimpleGraph.connectedComponentMk (Sum.inr ⟨f, hf⟩))
    else Sum.inr (spokeFaceClass T faces (Sum.inl ⟨f, hf⟩))
  have dart_place (d : N.Dart) :
      place (Sum.inl (orbitOf N.facePerm d)) = spokeDartFace T faces d :=
    (Classical.choose_spec (exists_spokeBoundaryFace T hT faces hfaces)).1 d
  have face_link (d : T.Dart) : G.Reachable (rep (T.faceOf d))
      (Sum.inr (spokeFaceClass T faces (spokePieceAt T faces d))) := by
    by_cases hf : T.faceOf d ∈ faces
    · let e : N.Dart := (⟨d, hf⟩, false)
      apply SimpleGraph.Adj.reachable
      dsimp only [rep]
      rw [dif_pos hf]
      change ∃ b, N.compOf b = N.toSimpleGraph.connectedComponentMk
          (Sum.inr ⟨T.faceOf d, hf⟩) ∧
        place b = spokeFaceClass T faces (spokePieceAt T faces d)
      refine ⟨Sum.inl (orbitOf N.facePerm e), rfl, ?_⟩
      exact (dart_place e).trans (by simp only [spokeDartFace, e, spokePieceAt, dif_pos hf]; rfl)
    · have he : rep (T.faceOf d) =
          Sum.inr (spokeFaceClass T faces (spokePieceAt T faces d)) := by
        simp only [rep, dif_neg hf, spokePieceAt]
      exact he ▸ SimpleGraph.Reachable.refl _
  have face_paths (f g : T.Face) : G.Reachable (rep f) (rep g) := by
    have hc : (T.dualRotation hT.props.1).toSimpleGraph.connectedComponentMk f =
        (T.dualRotation hT.props.1).toSimpleGraph.connectedComponentMk g :=
      (T.dual_component_subsingleton hT.props.1).elim _ _
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hc
    clear hc
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons f g h hadj p ih =>
      obtain ⟨hne, d, hd, hg⟩ := hadj
      have hd' : T.faceOf d = f := hd
      have hg' : T.faceOf (T.edgeInv d) = g := hg
      have hedge : G.Reachable (rep f) (rep g) := by
        rw [← hd', ← hg']
        exact (face_link d).trans ((spokeFaceClass_across T faces d) ▸
          (face_link (T.edgeInv d)).symm)
      exact hedge.trans ih
  let : Nonempty T.Vertex := hT.props.1.nonempty
  obtain ⟨d0, _⟩ := triangulation_has_dart_at_vertex T hT (Classical.arbitrary T.Vertex)
  let base := rep (T.faceOf d0)
  have face_to_base (f : SpokeFace T faces) : G.Reachable (Sum.inr f) base := by
    induction f using Quotient.inductionOn with
    | h a =>
      cases a with
      | inl f =>
        have he : rep f.val = Sum.inr (spokeFaceClass T faces (Sum.inl f)) := by
          simp only [rep, dif_neg f.property]
        exact he ▸ face_paths f.val (T.faceOf d0)
      | inr d =>
        have he : spokePieceAt T faces d.val = Sum.inr d := by
          simp only [spokePieceAt, dif_pos d.property]
        exact (he ▸ face_link d.val).symm.trans (face_paths _ _)
  have all_to_base (a : N.Component ⊕ SpokeFace T faces) : G.Reachable a base := by
    cases a with
    | inr f => exact face_to_base f
    | inl K =>
      obtain ⟨v, hv⟩ := K.exists_rep
      have hv' : N.toSimpleGraph.connectedComponentMk v = K := hv
      have boundary : ∃ b : N.LocalBoundary, N.compOf b = K := by
        by_cases hd : ∃ d : N.Dart, N.vert d = v
        · obtain ⟨d, hd⟩ := hd
          exact ⟨Sum.inl (orbitOf N.facePerm d), (congrArg
            N.toSimpleGraph.connectedComponentMk hd).trans hv'⟩
        · exact ⟨Sum.inr ⟨v, fun d he => hd ⟨d, he⟩⟩, hv'⟩
      obtain ⟨b, hb⟩ := boundary
      have ha : G.Adj (Sum.inl K) (Sum.inr (place b)) := ⟨b, hb, rfl⟩
      exact ha.reachable.trans (face_to_base (place b))
  let : Nonempty (N.Component ⊕ SpokeFace T faces) := ⟨base⟩
  refine ⟨?_⟩
  intro a b
  exact (all_to_base a).trans (all_to_base b).symm

end OaiPairedStatesHamiltonian
