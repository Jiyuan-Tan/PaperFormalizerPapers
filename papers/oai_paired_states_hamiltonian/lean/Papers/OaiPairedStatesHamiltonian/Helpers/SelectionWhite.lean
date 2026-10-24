module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SelectionCycles

/-! The two white endpoints of a deleted spoke and the farther-endpoint selection. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
open Classical
attribute [local instance] propDecidable
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

variable (T : SphereMap) (hT : IsSphereTriangulation T)
  (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)

-- @node: triangulation_face_tail_injective
/-- In [a sphere triangulation](hyp:hT), if [the first directed edge lies on a given face](hyp:hd),
[the second lies on that same face](hyp:he), and [their starting vertices agree](hyp:hv),
then [the two directed edges are equal](goal). -/
lemma triangulation_face_tail_injective (hT : IsSphereTriangulation T) (f : T.Face) (d e : T.Dart)
    (hd : T.faceOf d = f) (he : T.faceOf e = f) (hv : T.vert d = T.vert e) : d = e := by
  have hc : ((T.faceDarts f).image T.vert).card = (T.faceDarts f).card := by
    rw [← triangulation_faceVertices_eq_image T hT,
      ← T.faceLength_eq_card_faceDarts]
    exact (hT.props.2.2.2 f).2.trans (hT.props.2.2.2 f).1.symm
  exact (Finset.injOn_of_card_image_eq hc)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩) hv

-- @node: selectionCandidate_eq_corner_or_prev
/-- In a sphere triangulation, [each candidate side at a state's chosen vertex
of a nonouter black face is either the outgoing facial side or the reverse of its predecessor](goal). -/
lemma selectionCandidate_eq_corner_or_prev (s : State T col t0)
    (t : blackNonOuter T col t0) (d : SelectionCandidate T col t0 s t) :
    d.val = (stateCorner T hT col t0 s t).val ∨
      d.val = T.edgeInv (T.facePerm.symm (stateCorner T hT col t0 s t).val) := by
  have hc := stateCorner_spec T hT col t0 s t
  rcases d.property.2 with hd | hd
  · exact Or.inl (triangulation_face_tail_injective T hT t.val _ _ hd hc.1
      (d.property.1.trans hc.2.symm))
  · have hf : T.faceOf (T.facePerm (T.edgeInv d.val)) = t.val :=
      (T.dual_rot_vertex _).trans hd
    have hv : T.vert (T.facePerm (T.edgeInv d.val)) =
        T.vert (stateCorner T hT col t0 s t).val := by
      change T.vert (T.rot (T.edgeInv (T.edgeInv d.val))) = _
      rw [T.edgeInv_involutive, T.rot_vertex]
      exact d.property.1.trans hc.2.symm
    have he := triangulation_face_tail_injective T hT t.val _ _ hf hc.1 hv
    right
    have hi := congrArg T.facePerm.symm he
    rw [T.facePerm.symm_apply_apply] at hi
    exact (T.edgeInv_involutive d.val).symm.trans (congrArg T.edgeInv hi)

-- @node: whiteFaceEquiv_false
/-- For a sphere triangulation with a partition coloring,
[the white face corresponding to the forward side of a spoke corner is the original face
across that corner's directed edge](goal). -/
lemma whiteFaceEquiv_false (d : SpokeCorner T (blackFaces T col t0)) :
    (whiteFaceEquiv T hT col hcol t0
      ((spokeGraphAll T col t0 hT hcol).faceOf (d, false))).val =
        T.faceOf (T.edgeInv d.val) := by
  exact Classical.choose_spec (exists_whiteFaceEquiv T hT col hcol t0) d

-- @node: whiteFaceEquiv_true
/-- For a sphere triangulation with a partition coloring,
[the white face corresponding to the reverse side of a spoke corner is the original face
across the preceding directed edge on its black face](goal). -/
lemma whiteFaceEquiv_true (d : SpokeCorner T (blackFaces T col t0)) :
    (whiteFaceEquiv T hT col hcol t0
      ((spokeGraphAll T col t0 hT hcol).faceOf (d, true))).val =
        T.faceOf (T.edgeInv (T.facePerm.symm d.val)) := by
  let N := spokeGraphAll T col t0 hT hcol
  have hs := (Classical.choose_spec (exists_spokePerms T hT
    (blackFaces T col t0) (black_faces_disjoint T col t0 hcol))).2.1 (d, false)
  have hp : N.facePerm (d, true) = (prevCorner T (blackFaces T col t0) d, false) := by
    change (spokeRotation T hT (blackFaces T col t0)
      (black_faces_disjoint T col t0 hcol)).rot
        ((spokeRotation T hT (blackFaces T col t0)
          (black_faces_disjoint T col t0 hcol)).edgeInv (d, true)) = _
    rw [spokeRotation_edgeInv]
    exact Prod.ext (Subtype.ext hs.2) hs.1
  have hf := N.dual_rot_vertex (d, true)
  rw [hp] at hf
  rw [← hf]
  exact whiteFaceEquiv_false T hT col hcol t0 (prevCorner T (blackFaces T col t0) d)

-- @node: exists_candidates_of_stateCorner
/-- In a sphere triangulation, [there are two candidates at each state's chosen
corner of a nonouter black face: one is the corner's outgoing directed edge, and the other
is the reverse of its facial predecessor](goal). -/
lemma exists_candidates_of_stateCorner (s : State T col t0) (t : blackNonOuter T col t0) :
    ∃ a b : SelectionCandidate T col t0 s t,
      a.val = (stateCorner T hT col t0 s t).val ∧
      b.val = T.edgeInv (T.facePerm.symm (stateCorner T hT col t0 s t).val) := by
  let c := stateCorner T hT col t0 s t
  have hc := stateCorner_spec T hT col t0 s t
  have hf : T.faceOf (T.facePerm.symm c.val) = t.val := by
    rw [← T.dual_rot_vertex (T.facePerm.symm c.val), T.facePerm.apply_symm_apply]
    exact hc.1
  have hv : T.vert (T.edgeInv (T.facePerm.symm c.val)) = (s.val t).val := by
    have h := T.rot_vertex (T.edgeInv (T.facePerm.symm c.val))
    change T.vert (T.facePerm (T.facePerm.symm c.val)) = _ at h
    rw [T.facePerm.apply_symm_apply] at h
    exact h.symm.trans hc.2
  exact ⟨⟨c.val, hc.2, Or.inl hc.1⟩,
    ⟨T.edgeInv (T.facePerm.symm c.val), hv, Or.inr (by
      rw [T.edgeInv_involutive]; exact hf)⟩, rfl, rfl⟩

-- @node: candidateWhite_corner
/-- In a sphere triangulation with a partition coloring, if
[a candidate is the outgoing directed edge at the state's corner](hyp:hd), then
[its associated white face is the face on the forward side of that corner's spoke](goal). -/
lemma candidateWhite_corner (s : State T col t0) (t : blackNonOuter T col t0)
    (d : SelectionCandidate T col t0 s t)
    (hd : d.val = (stateCorner T hT col t0 s t).val) :
    candidateWhite T hT col hcol t0 s t d =
      (spokeGraphAll T col t0 hT hcol).faceOf (stateCorner T hT col t0 s t, false) := by
  apply (whiteFaceEquiv T hT col hcol t0).injective
  apply Subtype.ext
  change (whiteFaceEquiv T hT col hcol t0
    ((whiteFaceEquiv T hT col hcol t0).symm _)).val = _
  rw [Equiv.apply_symm_apply, whiteFaceEquiv_false]
  dsimp only
  rw [hd, if_pos (stateCorner_spec T hT col t0 s t).1]

-- @node: candidateWhite_prev
/-- In a sphere triangulation with a partition coloring, if
[a candidate is the reverse of the directed edge preceding the state's corner](hyp:hd),
then [its associated white face is the face on the reverse side of that corner's spoke](goal). -/
lemma candidateWhite_prev (s : State T col t0) (t : blackNonOuter T col t0)
    (d : SelectionCandidate T col t0 s t)
    (hd : d.val = T.edgeInv (T.facePerm.symm (stateCorner T hT col t0 s t).val)) :
    candidateWhite T hT col hcol t0 s t d =
      (spokeGraphAll T col t0 hT hcol).faceOf (stateCorner T hT col t0 s t, true) := by
  have hf : T.faceOf (T.edgeInv d.val) = t.val := by
    rw [hd, T.edgeInv_involutive,
      ← T.dual_rot_vertex (T.facePerm.symm (stateCorner T hT col t0 s t).val),
      T.facePerm.apply_symm_apply]
    exact (stateCorner_spec T hT col t0 s t).1
  have hn : T.faceOf d.val ≠ t.val := by
    intro he
    exact normalizedColoring_partition T col hcol t0 d.val (by rw [he, hf])
  apply (whiteFaceEquiv T hT col hcol t0).injective
  apply Subtype.ext
  change (whiteFaceEquiv T hT col hcol t0
    ((whiteFaceEquiv T hT col hcol t0).symm _)).val = _
  rw [Equiv.apply_symm_apply, whiteFaceEquiv_true]
  dsimp only
  rw [if_neg hn, hd]

-- @node: candidateWhite_eq_endpoint
/-- In a sphere triangulation with a partition coloring,
[the white face associated with any candidate is one of the two faces incident to
the spoke at the state's corner](goal). -/
lemma candidateWhite_eq_endpoint (s : State T col t0) (t : blackNonOuter T col t0)
    (d : SelectionCandidate T col t0 s t) :
    candidateWhite T hT col hcol t0 s t d =
        (spokeGraphAll T col t0 hT hcol).faceOf (stateCorner T hT col t0 s t, false) ∨
      candidateWhite T hT col hcol t0 s t d =
        (spokeGraphAll T col t0 hT hcol).faceOf (stateCorner T hT col t0 s t, true) := by
  rcases selectionCandidate_eq_corner_or_prev T hT col t0 s t d with h | h
  · exact Or.inl (candidateWhite_corner T hT col hcol t0 s t d h)
  · exact Or.inr (candidateWhite_prev T hT col hcol t0 s t d h)

-- @node: stateCorner_white_adj
/-- In a sphere triangulation with a partition coloring, suppose
[the states choose different vertices on every nonouter black face](hyp:hpair),
[the graph of edges opposite the second state's chosen vertices is a forest](hyp:hforest),
and [there are no separating triangles](hyp:hsep). Then [the two white faces incident
to the second state's corner spoke are adjacent in its white-face graph](goal). -/
lemma stateCorner_white_adj (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T)
    (t : blackNonOuter T col t0) :
    (whiteFaceGraph T hT col hcol t0 s).Adj
      ((spokeGraphAll T col t0 hT hcol).faceOf (stateCorner T hT col t0 s t, false))
      ((spokeGraphAll T col t0 hT hcol).faceOf (stateCorner T hT col t0 s t, true)) := by
  let N := spokeGraphAll T col t0 hT hcol
  let d : N.Dart := (stateCorner T hT col t0 s t, false)
  have hd : N.edgeOf d ∈ deletedSpokes T hT col hcol t0 s := ⟨t, rfl⟩
  have ht := deletedSpokes_dual_isTree T hT col hcol t0 r s hpair hforest hsep
  have hn := (N.dual (spokeAll_connected T hT col hcol t0)).forest_no_loop _ ht.1 d hd
  have hi : N.edgeInv d = (stateCorner T hT col t0 s t, true) :=
    spokeRotation_edgeInv T hT _ _ d
  change N.faceOf d ≠ N.faceOf (N.edgeInv d) at hn
  refine ⟨?_, d, hd, rfl, ?_⟩
  · simpa only [hi] using hn
  · change N.faceOf (N.edgeInv d) = _
    rw [hi]

-- @node: selectedWhiteFace
/-- Given [a sphere map](hyp:T), [its sphere triangulation property](hyp:hT),
[a face coloring](hyp:col) that [partitions the faces into the two colors](hyp:hcol),
[an outer face](hyp:t0), [a state](hyp:s), [a distinguished edge](hyp:e0)
[incident to the outer face](hyp:he0), and [a nonouter black face](hyp:t),
the [selected white face](goal) is the white face associated with a candidate side
of that black face maximizing distance from the white root. -/
noncomputable def selectedWhiteFace (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) :
    (spokeGraphAll T col t0 hT hcol).Face :=
  candidateWhite T hT col hcol t0 s t
    (Classical.choose (exists_farthestCandidate T hT col hcol t0 s e0 he0 t))

-- @node: selectedWhiteFace_farther
/-- In a sphere triangulation with a partition coloring, suppose
[the states choose different vertices on every nonouter black face](hyp:hpair),
[the graph of edges opposite the second state's chosen vertices is a forest](hyp:hforest),
[there are no separating triangles](hyp:hsep), and [the distinguished edge lies on the outer face](hyp:he0).
Then [the selected white face is one of the two endpoints of the corner spoke, and its
distance from the white root is exactly one greater than the other endpoint's distance](goal). -/
lemma selectedWhiteFace_farther (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T)
    (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) :
    let G := whiteFaceGraph T hT col hcol t0 s
    let root := whiteRoot T hT col hcol t0 e0 he0
    let a := (spokeGraphAll T col t0 hT hcol).faceOf (stateCorner T hT col t0 s t, false)
    let b := (spokeGraphAll T col t0 hT hcol).faceOf (stateCorner T hT col t0 s t, true)
    (selectedWhiteFace T hT col hcol t0 s e0 he0 t = a ∧ G.dist root b + 1 = G.dist root a) ∨
      (selectedWhiteFace T hT col hcol t0 s e0 he0 t = b ∧ G.dist root a + 1 = G.dist root b) := by
  dsimp only
  let c := Classical.choose (exists_farthestCandidate T hT col hcol t0 s e0 he0 t)
  have hmax := Classical.choose_spec (exists_farthestCandidate T hT col hcol t0 s e0 he0 t)
  obtain ⟨a, b, ha, hb⟩ := exists_candidates_of_stateCorner T hT col t0 s t
  have hma := hmax a
  have hmb := hmax b
  rw [candidateWhite_corner T hT col hcol t0 s t a ha] at hma
  rw [candidateWhite_prev T hT col hcol t0 s t b hb] at hmb
  have hd := (whiteFaceGraph_isTree T hT col hcol t0 r s hpair hforest hsep).dist_eq_dist_add_one_of_adj (whiteRoot T hT col hcol t0 e0 he0)
      (stateCorner_white_adj T hT col hcol t0 r s hpair hforest hsep t)
  rcases candidateWhite_eq_endpoint T hT col hcol t0 s t c with hc | hc
  · left
    refine ⟨hc, ?_⟩
    change _ ≤ (whiteFaceGraph T hT col hcol t0 s).dist
      (whiteRoot T hT col hcol t0 e0 he0) (candidateWhite T hT col hcol t0 s t c) at hmb
    rw [hc] at hmb
    omega
  · right
    refine ⟨hc, ?_⟩
    change _ ≤ (whiteFaceGraph T hT col hcol t0 s).dist
      (whiteRoot T hT col hcol t0 e0 he0) (candidateWhite T hT col hcol t0 s t c) at hma
    rw [hc] at hma
    omega

-- @node: tree_closer_neighbor_unique
/-- If [a graph is a tree](hyp:hG), [one vertex is a neighbor of a given vertex](hyp:hu),
[another vertex is also its neighbor](hyp:hw), and [both neighbors are strictly closer
to a fixed root than the given vertex](hyp:hdu,hdw),
then [the two neighbors coincide](goal). -/
lemma tree_closer_neighbor_unique {V : Type} (G : SimpleGraph V) (hG : G.IsTree)
    (root v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (hdu : G.dist root u < G.dist root v) (hdw : G.dist root w < G.dist root v) : u = w := by
  classical
  obtain ⟨p, hp, hlen⟩ := hG.connected.exists_path_of_dist root v
  have parent (a : V) (ha : G.Adj v a) (hda : G.dist root a < G.dist root v) :
      a = p.penultimate := by
    obtain ⟨q, hq, hqlen⟩ := hG.connected.exists_path_of_dist root a
    have hmem : a ∈ p.support := by
      by_contra hn
      have hv := hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp ha.symm hn
      have he := hG.isAcyclic.path_concat hp hq ha hv
      have hl := congrArg SimpleGraph.Walk.length he
      rw [SimpleGraph.Walk.length_concat, hlen, hqlen] at hl
      omega
    exact hG.isAcyclic.eq_penultimate_of_adj_end hp ha hmem
  exact (parent u hu hdu).trans (parent w hw hdw).symm

-- @node: stateCorner_edge_injective
/-- In a sphere triangulation with a partition coloring,
[distinct nonouter black faces have distinct spoke edges at their state-chosen corners](goal). -/
lemma stateCorner_edge_injective (s : State T col t0) :
    Function.Injective (fun t : blackNonOuter T col t0 =>
      (spokeGraphAll T col t0 hT hcol).edgeOf (stateCorner T hT col t0 s t, false)) := by
  intro t u he
  rcases ((spokeGraphAll T col t0 hT hcol).edgeOf_eq_iff _ _).mp he with he | he
  · have hc := congrArg (fun d => T.faceOf d.1.val) he
    rw [(stateCorner_spec T hT col t0 s u).1,
      (stateCorner_spec T hT col t0 s t).1] at hc
    exact Subtype.ext hc.symm
  · have hi : (spokeGraphAll T col t0 hT hcol).edgeInv
        (stateCorner T hT col t0 s t, false) = (stateCorner T hT col t0 s t, true) :=
      spokeRotation_edgeInv T hT _ _ _
    rw [hi] at he
    exact Bool.noConfusion (congrArg Prod.snd he)

-- @node: selectedWhiteFace_ne_root
/-- In a sphere triangulation with a partition coloring, suppose
[the states choose different vertices on every nonouter black face](hyp:hpair),
[the graph of edges opposite the second state's chosen vertices is a forest](hyp:hforest),
[there are no separating triangles](hyp:hsep), and [the distinguished edge lies on the outer face](hyp:he0).
Then [the white face selected for any nonouter black face differs from the white root](goal). -/
lemma selectedWhiteFace_ne_root (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T)
    (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) :
    selectedWhiteFace T hT col hcol t0 s e0 he0 t ≠ whiteRoot T hT col hcol t0 e0 he0 := by
  intro he
  rcases selectedWhiteFace_farther T hT col hcol t0 r s hpair hforest hsep e0 he0 t with
    ⟨hf, hd⟩ | ⟨hf, hd⟩
  · rw [← hf, he, SimpleGraph.dist_self] at hd
    omega
  · rw [← hf, he, SimpleGraph.dist_self] at hd
    omega

-- @node: selectedWhiteFace_injective
/-- In a sphere triangulation with a partition coloring, suppose
[the states choose different vertices on every nonouter black face](hyp:hpair),
[the graph of edges opposite the second state's chosen vertices is a forest](hyp:hforest),
[there are no separating triangles](hyp:hsep), and [the distinguished edge lies on the outer face](hyp:he0).
Then [distinct nonouter black faces select distinct white faces](goal). -/
lemma selectedWhiteFace_injective (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T)
    (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) :
    Function.Injective (selectedWhiteFace T hT col hcol t0 s e0 he0) := by
  let N := spokeGraphAll T col t0 hT hcol
  let G := whiteFaceGraph T hT col hcol t0 s
  let root := whiteRoot T hT col hcol t0 e0 he0
  have ht := whiteFaceGraph_isTree T hT col hcol t0 r s hpair hforest hsep
  have spec (t : blackNonOuter T col t0) : ∃ d : N.Dart,
      N.edgeOf d = N.edgeOf (stateCorner T hT col t0 s t, false) ∧
      N.faceOf d = selectedWhiteFace T hT col hcol t0 s e0 he0 t ∧
      G.Adj (N.faceOf d) (N.faceOf (N.edgeInv d)) ∧
      G.dist root (N.faceOf (N.edgeInv d)) < G.dist root (N.faceOf d) := by
    have ha := stateCorner_white_adj T hT col hcol t0 r s hpair hforest hsep t
    have hi (b : Bool) : N.edgeInv (stateCorner T hT col t0 s t, b) =
        (stateCorner T hT col t0 s t, !b) := spokeRotation_edgeInv T hT _ _ _
    rcases selectedWhiteFace_farther T hT col hcol t0 r s hpair hforest hsep e0 he0 t with
      ⟨hf, hd⟩ | ⟨hf, hd⟩
    · refine ⟨(stateCorner T hT col t0 s t, false), rfl, hf.symm, ?_, ?_⟩
      · simpa only [hi, Bool.not_false] using ha
      · simpa only [hi, Bool.not_false] using Nat.lt_of_succ_le (Nat.le_of_eq hd)
    · refine ⟨(stateCorner T hT col t0 s t, true), ?_, hf.symm, ?_, ?_⟩
      · exact ((N.edgeOf_eq_iff _ _).mpr (Or.inr (hi false).symm)).symm
      · simpa only [hi, Bool.not_true] using ha.symm
      · simpa only [hi, Bool.not_true] using Nat.lt_of_succ_le (Nat.le_of_eq hd)
  intro t u he
  obtain ⟨d, hd, hdf, hadj, hdist⟩ := spec t
  obtain ⟨e, hee, hef, hadj', hdist'⟩ := spec u
  have hv : N.faceOf d = N.faceOf e := hdf.trans (he.trans hef.symm)
  have hh : N.faceOf (N.edgeInv d) = N.faceOf (N.edgeInv e) := by
    apply tree_closer_neighbor_unique G ht root (N.faceOf d)
      (N.faceOf (N.edgeInv d)) (N.faceOf (N.edgeInv e)) hadj
    · simpa only [hv] using hadj'
    · exact hdist
    · simpa only [hv] using hdist'
  have hdel (a : blackNonOuter T col t0) :
      N.edgeOf (stateCorner T hT col t0 s a, false) ∈ deletedSpokes T hT col hcol t0 s := ⟨a, rfl⟩
  have hedge : N.edgeOf d = N.edgeOf e :=
    (N.dual (spokeAll_connected T hT col hcol t0)).forest_no_parallel _
      (deletedSpokes_dual_isTree T hT col hcol t0 r s hpair hforest hsep).1
      d e (hd.symm ▸ hdel t) (hee.symm ▸ hdel u) (by
        change s(N.faceOf d, N.faceOf (N.edgeInv d)) = s(N.faceOf e, N.faceOf (N.edgeInv e))
        rw [hv, hh])
  exact stateCorner_edge_injective T hT col hcol t0 s (hd.symm.trans (hedge.trans hee))

-- @node: white_face_card_eq_blackNonOuter_add_one
/-- In a sphere triangulation with a partition coloring,
[the number of faces of the full spoke map is one more than the number of nonouter black faces](goal). -/
lemma white_face_card_eq_blackNonOuter_add_one :
    Fintype.card (spokeGraphAll T col t0 hT hcol).Face = (blackNonOuter T col t0).card + 1 := by
  have he : blackNonOuter T col t0 = (blackFaces T col t0).erase t0 := by
    ext f
    simp only [blackNonOuter, blackFaces, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    exact and_comm
  have hb : t0 ∈ blackFaces T col t0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, normalizedColoring_self T col t0⟩
  rw [he, Finset.card_erase_add_one hb]
  have hc := (standingCounts_of_triangulation T hT (normalizedColoring T col t0)
    (normalizedColoring_partition T col hcol t0)).1
  rw [Fintype.card_congr (whiteFaceEquiv T hT col hcol t0), Fintype.card_subtype]
  exact hc

-- @node: selectedWhiteFace_existsUnique
/-- In a sphere triangulation with a partition coloring, suppose
[the states choose different vertices on every nonouter black face](hyp:hpair),
[the graph of edges opposite the second state's chosen vertices is a forest](hyp:hforest),
[there are no separating triangles](hyp:hsep), and [the distinguished edge lies on the outer face](hyp:he0).
For [any white face other than the white root](hyp:hf), [there is exactly one nonouter
black face that selects it](goal). -/
lemma selectedWhiteFace_existsUnique (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T)
    (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0)
    (f : (spokeGraphAll T col t0 hT hcol).Face)
    (hf : f ≠ whiteRoot T hT col hcol t0 e0 he0) :
    ∃! t : blackNonOuter T col t0, selectedWhiteFace T hT col hcol t0 s e0 he0 t = f := by
  let image := Finset.univ.image (selectedWhiteFace T hT col hcol t0 s e0 he0)
  have hi := selectedWhiteFace_injective T hT col hcol t0 r s hpair hforest hsep e0 he0
  have hs : image ⊆ Finset.univ.erase (whiteRoot T hT col hcol t0 e0 he0) := by
    intro a ha
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_erase.mpr ⟨selectedWhiteFace_ne_root T hT col hcol t0
      r s hpair hforest hsep e0 he0 t, Finset.mem_univ _⟩
  have hc : image.card = (blackNonOuter T col t0).card := by
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_coe]
  have he : image = Finset.univ.erase (whiteRoot T hT col hcol t0 e0 he0) := by
    apply Finset.eq_of_subset_of_card_le hs
    have hcard := white_face_card_eq_blackNonOuter_add_one T hT col hcol t0
    have herase := Finset.card_erase_add_one
      (s := (Finset.univ : Finset (spokeGraphAll T col t0 hT hcol).Face))
      (Finset.mem_univ (whiteRoot T hT col hcol t0 e0 he0))
    rw [Finset.card_univ] at herase
    omega
  have hmem : f ∈ image := he.symm ▸ Finset.mem_erase.mpr ⟨hf, Finset.mem_univ _⟩
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
  exact ⟨t, ht, fun u hu => hi (hu.trans ht.symm)⟩

-- @node: candidateWhite_edgeOnFace_iff
/-- In a sphere triangulation with a partition coloring, for
[a face colored white after normalization at the outer face](hyp:hf),
[a candidate's underlying edge is incident to that face if and only if the candidate's
associated white face corresponds to it under the white-face equivalence](goal). -/
lemma candidateWhite_edgeOnFace_iff (s : State T col t0) (t : blackNonOuter T col t0)
    (d : SelectionCandidate T col t0 s t) (f : T.Face)
    (hf : normalizedColoring T col t0 f = false) :
    T.edgeOnFace (T.edgeOf d.val) f ↔
      (whiteFaceEquiv T hT col hcol t0 (candidateWhite T hT col hcol t0 s t d)).val = f := by
  change _ ↔ (whiteFaceEquiv T hT col hcol t0
    ((whiteFaceEquiv T hT col hcol t0).symm _)).val = f
  rw [Equiv.apply_symm_apply]
  dsimp only
  have hft : f ≠ t.val := by
    intro he
    have hb := nonOuter_black T col t0 t
    rw [← he, hf] at hb
    cases hb
  by_cases hd : T.faceOf d.val = t.val
  · rw [if_pos hd]
    constructor
    · rintro ⟨e, he, hef⟩
      rcases (T.edgeOf_eq_iff e d.val).mp he with h | h
      · exact (hft (hef.symm.trans (h.symm ▸ hd))).elim
      · have hi : e = T.edgeInv d.val :=
          (T.edgeInv_involutive e).symm.trans (congrArg T.edgeInv h.symm)
        exact hi ▸ hef
    · intro he
      exact ⟨T.edgeInv d.val,
        ((T.edgeOf_eq_iff _ _).mpr (Or.inr rfl)).symm, he⟩
  · rw [if_neg hd]
    have hi := d.property.2.resolve_left hd
    constructor
    · rintro ⟨e, he, hef⟩
      rcases (T.edgeOf_eq_iff e d.val).mp he with h | h
      · exact h.symm ▸ hef
      · have hie : T.edgeInv d.val = e :=
          (congrArg T.edgeInv h).trans (T.edgeInv_involutive e)
        exact (hft (hef.symm.trans (hie ▸ hi))).elim
    · intro he
      exact ⟨d.val, rfl, he⟩

-- @node: selectedWhiteFace_edgeOnFace_iff
/-- In a sphere triangulation with a partition coloring, let
[the distinguished edge be incident to the outer face](hyp:he0) and
[the given face be white in the normalized coloring](hyp:hf). Then
[the edge selected for a nonouter black face is incident to the given face if and only
if the selected white face corresponds to it under the white-face equivalence](goal). -/
lemma selectedWhiteFace_edgeOnFace_iff (s : State T col t0) (e0 : T.Edge)
    (he0 : T.edgeOnFace e0 t0) (t : blackNonOuter T col t0) (f : T.Face)
    (hf : normalizedColoring T col t0 f = false) :
    T.edgeOnFace (T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t)) f ↔
      (whiteFaceEquiv T hT col hcol t0 (selectedWhiteFace T hT col hcol t0 s e0 he0 t)).val = f := by
  exact candidateWhite_edgeOnFace_iff T hT col hcol t0 s t _ f hf

-- @node: whiteRoot_value
/-- In a sphere triangulation with a partition coloring, if
[the distinguished edge lies on the outer face](hyp:he0), then [the white root corresponds
to the original face across the distinguished edge from the outer face](goal). -/
lemma whiteRoot_value (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) :
    (whiteFaceEquiv T hT col hcol t0 (whiteRoot T hT col hcol t0 e0 he0)).val =
      T.faceOf (T.edgeInv (outerEdgeDart T t0 e0 he0)) := by
  change (whiteFaceEquiv T hT col hcol t0
    ((whiteFaceEquiv T hT col hcol t0).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  exact if_pos (outerEdgeDart_face T t0 e0 he0)

-- @node: outer_edge_white_incidence_iff
/-- In a sphere triangulation with a partition coloring, if
[the distinguished edge lies on the outer face](hyp:he0), then [it is incident to the
original white face corresponding to a spoke-map face if and only if that spoke-map
face is the white root](goal). -/
lemma outer_edge_white_incidence_iff (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0)
    (f : (spokeGraphAll T col t0 hT hcol).Face) :
    T.edgeOnFace e0 (whiteFaceEquiv T hT col hcol t0 f).val ↔
      f = whiteRoot T hT col hcol t0 e0 he0 := by
  let d := outerEdgeDart T t0 e0 he0
  have hd : T.edgeOf d = e0 := (Classical.choose_spec (exists_outerEdgeDart T t0 e0 he0)).1
  have hdf : T.faceOf d = t0 := outerEdgeDart_face T t0 e0 he0
  have hwhite := (whiteFaceEquiv T hT col hcol t0 f).property
  constructor
  · rintro ⟨e, he, hef⟩
    have hside : T.faceOf (T.edgeInv d) = (whiteFaceEquiv T hT col hcol t0 f).val := by
      rcases (T.edgeOf_eq_iff d e).mp (hd.trans he.symm) with h | h
      · have hb : normalizedColoring T col t0 (T.faceOf e) = true := by
          rw [h, hdf]
          exact normalizedColoring_self T col t0
        rw [hef, hwhite] at hb
        cases hb
      · exact h ▸ hef
    apply (whiteFaceEquiv T hT col hcol t0).injective
    apply Subtype.ext
    exact hside.symm.trans (whiteRoot_value T hT col hcol t0 e0 he0).symm
  · rintro rfl
    refine ⟨T.edgeInv d, ?_, ?_⟩
    · exact (((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm).trans hd
    · exact (whiteRoot_value T hT col hcol t0 e0 he0).symm

-- @node: selectedSet_white_face_existsUnique
/-- In a sphere triangulation with a partition coloring, suppose
[the states choose different vertices on every nonouter black face](hyp:hpair),
[the graph of edges opposite the second state's chosen vertices is a forest](hyp:hforest),
[there are no separating triangles](hyp:hsep), and [the distinguished edge lies on the outer face](hyp:he0).
For [any face white in the normalized coloring](hyp:hf), [exactly one edge in the selected
set is incident to that face](goal). -/
lemma selectedSet_white_face_existsUnique (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T)
    (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) (f : T.Face)
    (hf : normalizedColoring T col t0 f = false) :
    ∃! e : T.Edge, e ∈ selectedSet T hT col hcol t0 s e0 he0 ∧ T.edgeOnFace e f := by
  let q := whiteFaceEquiv T hT col hcol t0
  have each (g : (spokeGraphAll T col t0 hT hcol).Face) :
      ∃! e : T.Edge, e ∈ selectedSet T hT col hcol t0 s e0 he0 ∧ T.edgeOnFace e (q g).val := by
    have incident (t : blackNonOuter T col t0) :
        T.edgeOnFace (T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t)) (q g).val ↔
          selectedWhiteFace T hT col hcol t0 s e0 he0 t = g := by
      rw [selectedWhiteFace_edgeOnFace_iff T hT col hcol t0 s e0 he0 t _ (q g).property]
      exact ⟨fun he => q.injective (Subtype.ext he), fun he => congrArg (fun a => (q a).val) he⟩
    by_cases hg : g = whiteRoot T hT col hcol t0 e0 he0
    · refine ⟨e0, ⟨Finset.mem_insert_self _ _,
        (outer_edge_white_incidence_iff T hT col hcol t0 e0 he0 g).mpr hg⟩, ?_⟩
      intro e he
      rcases Finset.mem_insert.mp he.1 with heq | heq
      · exact heq
      · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp heq
        exact (selectedWhiteFace_ne_root T hT col hcol t0 r s hpair hforest hsep e0 he0 t
          (((incident t).mp he.2).trans hg)).elim
    · obtain ⟨t, ht, hu⟩ := selectedWhiteFace_existsUnique T hT col hcol t0
        r s hpair hforest hsep e0 he0 g hg
      refine ⟨T.edgeOf (selectedDart T hT col hcol t0 s e0 he0 t),
        ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩),
          (incident t).mpr ht⟩, ?_⟩
      intro e he
      rcases Finset.mem_insert.mp he.1 with heq | heq
      · exact (hg ((outer_edge_white_incidence_iff T hT col hcol t0 e0 he0 g).mp
          (heq ▸ he.2))).elim
      · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp heq
        rw [hu u ((incident u).mp he.2)]
  have h := each (q.symm ⟨f, hf⟩)
  simpa only [Equiv.apply_symm_apply] using h

end OaiPairedStatesHamiltonian
