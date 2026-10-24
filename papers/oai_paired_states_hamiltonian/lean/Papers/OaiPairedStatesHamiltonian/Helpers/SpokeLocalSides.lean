module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SpokeSectors
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleSeparation

/-! Local shortcut uniqueness and side labels at selected triangle centers. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

-- @node: projectSpokeDarts_mem_witness
/-- Suppose [the map is a sphere triangulation](hyp:hT) and [the coloring separates
faces across every edge](hyp:hcol). If [a directed edge belongs to the projected
spoke cycle](hyp:he), then [it joins the original vertices of some consecutive
pair of cycle spokes whose first spoke points toward a selected center, and its
underlying edge borders that center's triangle](goal). -/
lemma projectSpokeDarts_mem_witness (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (e : T.Dart) (he : e ∈ projectSpokeDarts T (blackNonOuter T col t0) C.val) :
    ∃ a b, (a, b) ∈ C.val.zip (C.val.rotate 1) ∧ a.2 = true ∧
      FaceDart T (T.faceOf a.1.val) (T.vert a.1.val) (T.vert b.1.val) e := by
  unfold projectSpokeDarts at he
  obtain ⟨⟨a, b⟩, hab, he⟩ := List.mem_filterMap.mp he
  by_cases ha : a.2 = true
  · have hex := spoke_shortcut_exists T col t0 hT hcol C a b hab ha
    simp only [ha, ↓reduceIte, dif_pos hex, Option.some.injEq] at he
    exact ⟨a, b, hab, ha, he ▸ Classical.choose_spec hex⟩
  · simp [ha] at he

-- @node: spoke_shortcut_same_face
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the coloring separates
faces across every edge](hyp:hcol), [two spokes are consecutive on the cycle](hyp:hab),
and [the first points toward a selected center](hyp:ha). Then [the second points
away from a center and both spokes belong to the same original triangle](goal). -/
lemma spoke_shortcut_same_face (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true) :
    b.2 = false ∧ T.faceOf a.1.val = T.faceOf b.1.val := by
  have hb : b.2 = false := by
    rw [spoke_cycle_alternates T col t0 hT hcol C a b hab, ha]
    rfl
  refine ⟨hb, ?_⟩
  have hs := cyclic_zip_map_step C.val _ _ (spoke_cycle_head_map T col t0 hT hcol C) a b hab
  change spokeVert T _ ((spokeRotation T hT _ _).edgeInv a) = spokeVert T _ b at hs
  rw [spokeRotation_edgeInv] at hs
  simpa only [spokeVert, ha, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Sum.inr.injEq, Subtype.ext_iff] using hs

-- @node: spoke_shortcut_pair_unique
/-- Suppose [the map is a sphere triangulation](hyp:hT) and [the coloring separates
faces across every edge](hyp:hcol). If [one pair of spokes is consecutive on the
cycle](hyp:hab), [a second pair is also consecutive](hyp:hcd), [the first spoke of
the first pair points toward a center](hyp:ha), [the first spoke of the second
pair also points toward a center](hyp:hc), and [these centers belong to the same
triangle](hyp:hf), then [the two pairs agree spoke by spoke](goal).

The third triangle vertex is allowed to occur elsewhere on the cycle. -/
lemma spoke_shortcut_pair_unique (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b c d : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1))
    (hcd : (c, d) ∈ C.val.zip (C.val.rotate 1))
    (ha : a.2 = true) (hc : c.2 = true)
    (hf : T.faceOf a.1.val = T.faceOf c.1.val) : a = c ∧ b = d := by
  let N := spokeGraphBounded T col t0 hT hcol
  have hb := spoke_shortcut_same_face T col t0 hT hcol C a b hab ha
  have hd := spoke_shortcut_same_face T col t0 hT hcol C c d hcd hc
  have hv : N.vert b = N.vert d := by
    change spokeVert T _ b = spokeVert T _ d
    simp only [spokeVert, hb.1, hd.1, Bool.false_eq_true, ↓reduceIte,
      Sum.inr.injEq, Subtype.ext_iff]
    exact hb.2.symm.trans (hf.trans hd.2)
  have hbd : b = d := List.inj_on_of_nodup_map C.property.2
    (List.mem_rotate.mp (List.of_mem_zip hab).2)
    (List.mem_rotate.mp (List.of_mem_zip hcd).2) hv
  have hnh : (C.val.map N.head).Nodup := by
    rw [spoke_cycle_head_map T col t0 hT hcol C, List.map_rotate]
    exact List.nodup_rotate.mpr C.property.2
  have hs := cyclic_zip_map_step C.val _ _ (spoke_cycle_head_map T col t0 hT hcol C) a b hab
  have ht := cyclic_zip_map_step C.val _ _ (spoke_cycle_head_map T col t0 hT hcol C) c d hcd
  exact ⟨List.inj_on_of_nodup_map hnh (List.of_mem_zip hab).1
    (List.of_mem_zip hcd).1 (hs.trans ((congrArg N.vert hbd).trans ht.symm)), hbd⟩

-- @node: spoke_unvisited_edge_not_projected
/-- Suppose [the map is a sphere triangulation](hyp:hT) and [the coloring separates
faces across every edge](hyp:hcol). If [the cycle never visits a selected triangle's
center](hyp:hmiss) and [a directed edge has that triangle on either side](hyp:hd),
then [its underlying edge is absent from the projected cycle](goal). -/
lemma spoke_unvisited_edge_not_projected (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (f : blackNonOuter T col t0)
    (hmiss : ∀ a ∈ C.val,
      (spokeGraphBounded T col t0 hT hcol).vert a ≠ Sum.inr f)
    (d : T.Dart) (hd : T.faceOf d = f.val ∨ T.faceOf (T.edgeInv d) = f.val) :
    T.edgeOf d ∉ (projectSpokeDarts T (blackNonOuter T col t0) C.val).map T.edgeOf := by
  intro he
  obtain ⟨e, he, hed⟩ := List.mem_map.mp he
  obtain ⟨a, b, hab, ha, hface⟩ := projectSpokeDarts_mem_witness T col t0 hT hcol C e he
  have hf : T.faceOf a.1.val = f.val :=
    selected_edge_face_unique T _ (bounded_faces_disjoint T col t0 hcol)
      _ _ a.1.property f.property e d hface.2.2 hd hed
  have hb := spoke_shortcut_same_face T col t0 hT hcol C a b hab ha
  apply hmiss b (List.mem_rotate.mp (List.of_mem_zip hab).2)
  change spokeVert T _ b = Sum.inr f
  simp only [spokeVert, hb.1, Bool.false_eq_true, ↓reduceIte, Sum.inr.injEq,
    Subtype.ext_iff]
  exact hb.2.symm.trans hf

-- @node: spoke_unvisited_sector_side
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the coloring separates
faces across every edge](hyp:hcol), [the cycle avoids a selected triangle's
center](hyp:hmiss), and [a selected corner belongs to that triangle](hyp:hd).
Then [the corner's sector has the projected left-side label exactly when the
original triangle lies to the left of the projected cycle](goal). -/
lemma spoke_unvisited_sector_side (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (f : blackNonOuter T col t0)
    (hmiss : ∀ a ∈ C.val,
      (spokeGraphBounded T col t0 hT hcol).vert a ≠ Sum.inr f)
    (d : SpokeCorner T (blackNonOuter T col t0)) (hd : T.faceOf d.val = f.val) :
    spokeProjectedSide T col t0 hT hcol C (spokeFaceClass T _ (Sum.inr d)) ↔
      f.val ∈ T.leftRegion
        ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
          project_spoke_cycle T col t0 hT hcol C⟩ := by
  change T.faceOf (T.edgeInv d.val) ∈ T.leftRegion _ ↔ _
  rw [← hd]
  exact (T.leftRegion_across_noncycle hT.props.1 _ d.val
    (spoke_unvisited_edge_not_projected T col t0 hT hcol C f hmiss d.val (Or.inl hd))).symm

-- @node: spoke_shortcut_dart_unique
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the coloring separates
faces across every edge](hyp:hcol), [two spokes are consecutive on the cycle](hyp:hab),
and [the first points toward a selected center](hyp:ha). If [one directed edge
joins their original vertices along the supplying triangle](hyp:he), [another
belongs to the projected cycle](hyp:hd), and [that other edge borders the same
triangle on either side](hyp:hf), then [the two directed edges are equal](goal). -/
lemma spoke_shortcut_dart_unique (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true)
    (e : T.Dart) (he : FaceDart T (T.faceOf a.1.val) (T.vert a.1.val) (T.vert b.1.val) e)
    (d : T.Dart) (hd : d ∈ projectSpokeDarts T (blackNonOuter T col t0) C.val)
    (hf : T.faceOf d = T.faceOf a.1.val ∨
      T.faceOf (T.edgeInv d) = T.faceOf a.1.val) : d = e := by
  obtain ⟨c, q, hcq, hc, hde⟩ := projectSpokeDarts_mem_witness T col t0 hT hcol C d hd
  have hface : T.faceOf c.1.val = T.faceOf a.1.val :=
    selected_edge_face_unique T _ (bounded_faces_disjoint T col t0 hcol)
      _ _ c.1.property a.1.property d d hde.2.2 hf rfl
  obtain ⟨rfl, rfl⟩ := spoke_shortcut_pair_unique T col t0 hT hcol C c q a b hcq hab hc ha hface
  exact T.dart_eq_of_endpoints hT.props.2.1 d e (hde.1.trans he.1.symm)
    (hde.2.1.trans he.2.1.symm)

-- @node: spoke_other_edge_not_projected
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the coloring separates
faces across every edge](hyp:hcol), [two spokes are consecutive on the cycle](hyp:hab),
and [the first points toward a selected center](hyp:ha). Given [a directed shortcut
joining their original vertices along the supplying triangle](hyp:he), if [another
directed edge has that triangle as its face](hyp:hf) and [its underlying edge
differs from the shortcut's](hyp:hne), then [its underlying edge is absent from
the projected cycle](goal). -/
lemma spoke_other_edge_not_projected (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true)
    (e : T.Dart) (he : FaceDart T (T.faceOf a.1.val) (T.vert a.1.val) (T.vert b.1.val) e)
    (d : T.Dart) (hf : T.faceOf d = T.faceOf a.1.val)
    (hne : T.edgeOf d ≠ T.edgeOf e) :
    T.edgeOf d ∉ (projectSpokeDarts T (blackNonOuter T col t0) C.val).map T.edgeOf := by
  intro hd
  obtain ⟨q, hq, hqd⟩ := List.mem_map.mp hd
  have hs : T.faceOf q = T.faceOf a.1.val ∨
      T.faceOf (T.edgeInv q) = T.faceOf a.1.val := by
    rcases (T.edgeOf_eq_iff q d).mp hqd with h | h
    · exact Or.inl (h ▸ hf)
    · exact Or.inr (h ▸ hf)
  have hqe := spoke_shortcut_dart_unique T col t0 hT hcol C a b hab ha e he q hq hs
  exact hne (hqd.symm.trans (congrArg T.edgeOf hqe))

-- @node: spoke_other_side_value
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the coloring separates
faces across every edge](hyp:hcol), [two spokes are consecutive on the cycle](hyp:hab),
and [the first points toward a selected center](hyp:ha). Given [a directed shortcut
joining their original vertices along the supplying triangle](hyp:he), if [a
selected corner belongs to that triangle](hyp:hf) and [its edge differs from the
shortcut's](hyp:hne), then [its sector has the projected left-side label exactly
when the supplying triangle lies to the left of the projected cycle](goal). -/
lemma spoke_other_side_value (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true)
    (e : T.Dart) (he : FaceDart T (T.faceOf a.1.val) (T.vert a.1.val) (T.vert b.1.val) e)
    (d : SpokeCorner T (blackNonOuter T col t0)) (hf : T.faceOf d.val = T.faceOf a.1.val)
    (hne : T.edgeOf d.val ≠ T.edgeOf e) :
    spokeProjectedSide T col t0 hT hcol C (spokeFaceClass T _ (Sum.inr d)) ↔
      T.faceOf a.1.val ∈ T.leftRegion
        ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
          project_spoke_cycle T col t0 hT hcol C⟩ := by
  change T.faceOf (T.edgeInv d.val) ∈ T.leftRegion _ ↔ _
  rw [← hf]
  exact (T.leftRegion_across_noncycle hT.props.1 _ d.val
    (spoke_other_edge_not_projected T col t0 hT hcol C a b hab ha e he d.val hf hne)).symm

-- @node: triangle_face_corner_cases
/-- If [the map is a sphere triangulation](hyp:hT) and [two directed edges have
the same face](hyp:hf), then [the second is the first, its successor around the
face, or its predecessor around the face](goal). -/
lemma triangle_face_corner_cases (hT : IsSphereTriangulation T) (d e : T.Dart)
    (hf : T.faceOf e = T.faceOf d) :
    e = d ∨ e = T.facePerm d ∨ e = T.facePerm.symm d := by
  have hd : d ∈ T.faceDarts (T.faceOf d) := by simp [SphereMap.faceDarts]
  have he : e ∈ T.faceDarts (T.faceOf d) := by simp [SphereMap.faceDarts, hf]
  have hcyc : T.facePerm.IsCycleOn (↑(T.faceDarts (T.faceOf d)) : Set T.Dart) := by
    simpa [SphereMap.faceDarts] using T.dual_rot_fibre hT.props.1 (T.faceOf d)
  have hcard : (T.faceDarts (T.faceOf d)).card = 3 :=
    (T.faceLength_eq_card_faceDarts _).symm.trans (hT.props.2.2.2 _).1
  obtain ⟨n, hn, hde⟩ := hcyc.exists_pow_eq hd he
  rw [hcard] at hn
  have hthree := hcyc.pow_card_apply hd
  rw [hcard] at hthree
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn_cases with rfl | rfl | rfl
  · exact Or.inl (by simpa using hde.symm)
  · exact Or.inr (Or.inl (by simpa using hde.symm))
  · refine Or.inr (Or.inr ?_)
    apply T.facePerm.injective
    rw [T.facePerm.apply_symm_apply, ← hde]
    exact hthree

-- @node: spoke_shortcut_mem_projected
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the coloring separates
faces across every edge](hyp:hcol), [two spokes are consecutive on the cycle](hyp:hab),
and [the first points toward a selected center](hyp:ha). If [a directed edge joins
their original vertices along the supplying triangle](hyp:he), then [that directed
edge belongs to the projected cycle](goal). -/
lemma spoke_shortcut_mem_projected (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true)
    (e : T.Dart) (he : FaceDart T (T.faceOf a.1.val) (T.vert a.1.val) (T.vert b.1.val) e) :
    e ∈ projectSpokeDarts T (blackNonOuter T col t0) C.val := by
  have hex := spoke_shortcut_exists T col t0 hT hcol C a b hab ha
  have hs := Classical.choose_spec hex
  have heq : Classical.choose hex = e := T.dart_eq_of_endpoints hT.props.2.1 _ e
    (hs.1.trans he.1.symm) (hs.2.1.trans he.2.1.symm)
  apply List.mem_filterMap.mpr
  exact ⟨(a, b), hab, by simp only [ha, ↓reduceIte, dif_pos hex, heq]⟩

-- @node: spoke_triangle_shortcut_cases
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the coloring separates
faces across every edge](hyp:hcol), [two spokes are consecutive on the cycle](hyp:hab),
and [the first points toward a selected center](hyp:ha). Given [a directed shortcut
joining their original vertices along the supplying triangle](hyp:he), [either
the second corner succeeds the first around the face and the shortcut is the
first corner's directed edge, or it precedes the first and the shortcut is the
reverse of the second corner's directed edge](goal). -/
lemma spoke_triangle_shortcut_cases (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true)
    (e : T.Dart) (he : FaceDart T (T.faceOf a.1.val) (T.vert a.1.val) (T.vert b.1.val) e) :
    (b.1.val = T.facePerm a.1.val ∧ e = a.1.val) ∨
      (b.1.val = T.facePerm.symm a.1.val ∧ e = T.edgeInv b.1.val) := by
  have hb := spoke_shortcut_same_face T col t0 hT hcol C a b hab ha
  rcases triangle_face_corner_cases T hT a.1.val b.1.val hb.2.symm with h | h | h
  · exact (hT.props.2.1.1 e (he.1.trans ((congrArg T.vert h).symm.trans he.2.1.symm))).elim
  · refine Or.inl ⟨h, ?_⟩
    apply T.dart_eq_of_endpoints hT.props.2.1
    · exact he.1
    · rw [he.2.1, h]
      exact T.rot_vertex _
  · refine Or.inr ⟨h, ?_⟩
    apply T.dart_eq_of_endpoints hT.props.2.1
    · rw [he.1]
      change T.vert a.1.val = T.head b.1.val
      rw [h]
      exact (congrArg T.vert (T.facePerm.apply_symm_apply a.1.val)).symm.trans
        (T.rot_vertex _)
    · exact he.2.1.trans (congrArg T.vert (T.edgeInv_involutive b.1.val)).symm

-- @node: triangle_corner_neighbors_ne
/-- If [the map is a sphere triangulation](hyp:hT), then [both the successor and
the predecessor of any directed edge around its face differ from that edge](goal). -/
lemma triangle_corner_neighbors_ne (hT : IsSphereTriangulation T) (d : T.Dart) :
    T.facePerm d ≠ d ∧ T.facePerm.symm d ≠ d := by
  have hn : T.facePerm d ≠ d := by
    intro h
    apply hT.props.2.1.1 d
    exact (congrArg T.vert h).symm.trans (T.rot_vertex _)
  refine ⟨hn, ?_⟩
  intro h
  apply hn
  exact (congrArg T.facePerm h).symm.trans (T.facePerm.apply_symm_apply d)

-- @node: triangle_corner_next_ne_prev
/-- If [the map is a sphere triangulation](hyp:hT), then [the successor and
predecessor of any directed edge around its face are distinct](goal). -/
lemma triangle_corner_next_ne_prev (hT : IsSphereTriangulation T) (d : T.Dart) :
    T.facePerm d ≠ T.facePerm.symm d := by
  have hcyc : T.facePerm.IsCycleOn (↑(T.faceDarts (T.faceOf d)) : Set T.Dart) := by
    simpa [SphereMap.faceDarts] using T.dual_rot_fibre hT.props.1 (T.faceOf d)
  have hcard : (T.faceDarts (T.faceOf d)).card = 3 :=
    (T.faceLength_eq_card_faceDarts _).symm.trans (hT.props.2.2.2 _).1
  have hthree := hcyc.pow_card_apply (show d ∈ T.faceDarts (T.faceOf d) by
    simp [SphereMap.faceDarts])
  rw [hcard] at hthree
  intro h
  have htwo : T.facePerm (T.facePerm d) = d := by rw [h, T.facePerm.apply_symm_apply]
  have hone : T.facePerm d = d := by
    change T.facePerm (T.facePerm (T.facePerm d)) = d at hthree
    rwa [htwo] at hthree
  exact (triangle_corner_neighbors_ne T hT d).1 hone

-- @node: selected_corner_edge_injective
/-- If [no edge has selected faces on both sides](hyp:hfaces) and [two corners
of selected faces have the same underlying edge](hyp:h), then [the corners are
equal](goal). -/
lemma selected_corner_edge_injective (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (d e : SpokeCorner T faces) (h : T.edgeOf d.val = T.edgeOf e.val) : d = e := by
  rcases (T.edgeOf_eq_iff d.val e.val).mp h with h | h
  · exact Subtype.ext h.symm
  · exact (hfaces d.val ⟨d.property, h ▸ e.property⟩).elim

-- @node: spoke_shortcut_sector_split
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the coloring separates
faces across every edge](hyp:hcol), [two spokes are consecutive on the cycle](hyp:hab),
and [the first points toward a selected center](hyp:ha). Given [a directed shortcut
joining their original vertices along the supplying triangle](hyp:he) and [a
corner of that triangle](hyp:hf) whose [edge equals the shortcut's edge](hyp:hq),
[that corner's sector has the projected left-side label exactly when the triangle
is not to the left of the projected cycle, while every other corner of the
triangle has that label exactly when the triangle is to the left](goal).

The labels are assigned to the actual face classes of the spoke map. -/
lemma spoke_shortcut_sector_split (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true)
    (e : T.Dart) (he : FaceDart T (T.faceOf a.1.val) (T.vert a.1.val) (T.vert b.1.val) e)
    (q : SpokeCorner T (blackNonOuter T col t0)) (hf : T.faceOf q.val = T.faceOf a.1.val)
    (hq : T.edgeOf q.val = T.edgeOf e) :
    (spokeProjectedSide T col t0 hT hcol C (spokeFaceClass T _ (Sum.inr q)) ↔
      T.faceOf a.1.val ∉ T.leftRegion
        ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
          project_spoke_cycle T col t0 hT hcol C⟩) ∧
    ∀ d : SpokeCorner T (blackNonOuter T col t0),
      T.faceOf d.val = T.faceOf a.1.val → d ≠ q →
      (spokeProjectedSide T col t0 hT hcol C (spokeFaceClass T _ (Sum.inr d)) ↔
        T.faceOf a.1.val ∈ T.leftRegion
          ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
            project_spoke_cycle T col t0 hT hcol C⟩) := by
  let D : T.Cycle := ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
    project_spoke_cycle T col t0 hT hcol C⟩
  have hem : e ∈ D.val := spoke_shortcut_mem_projected T col t0 hT hcol C a b hab ha e he
  have hl := T.cycle_face_mem_leftRegion D e hem
  obtain ⟨outer, hout⟩ := T.exists_face_outside_cycle_leftRegion hT.props.1 D
  have hr := T.cycle_boundary_opposite_outside hT.props.1 D outer hout e hem
  constructor
  · change T.faceOf (T.edgeInv q.val) ∈ T.leftRegion D ↔ T.faceOf a.1.val ∉ T.leftRegion D
    rw [← hf]
    rcases (T.edgeOf_eq_iff q.val e).mp hq with h | h
    · rw [h] at hl hr
      exact ⟨fun hp => (hr hp).elim, fun hn => (hn hl).elim⟩
    · rw [h] at hl
      rw [h, T.edgeInv_involutive] at hr
      exact ⟨fun _ => hr, fun _ => hl⟩
  · intro d hd hne
    apply spoke_other_side_value T col t0 hT hcol C a b hab ha e he d hd
    intro hedge
    exact hne (selected_corner_edge_injective T _ (bounded_faces_disjoint T col t0 hcol)
      d q (hedge.trans hq.symm))

-- @node: spoke_shortcut_oriented_sectors
/-- Suppose [the map is a sphere triangulation](hyp:hT), [the coloring separates
faces across every edge](hyp:hcol), [two spokes are consecutive on the cycle](hyp:hab),
and [the first points toward a selected center](hyp:ha). Then [the sectors at the
predecessor of the first corner and at the second corner have the projected
left-side label, while the sectors at the first corner and at the predecessor
of the second corner do not](goal). -/
lemma spoke_shortcut_oriented_sectors (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true) :
    spokeProjectedSide T col t0 hT hcol C
        (spokeFaceClass T _ (Sum.inr (prevCorner T _ a.1))) ∧
    spokeProjectedSide T col t0 hT hcol C (spokeFaceClass T _ (Sum.inr b.1)) ∧
    ¬ spokeProjectedSide T col t0 hT hcol C (spokeFaceClass T _ (Sum.inr a.1)) ∧
    ¬ spokeProjectedSide T col t0 hT hcol C
        (spokeFaceClass T _ (Sum.inr (prevCorner T _ b.1))) := by
  obtain ⟨e, he⟩ := spoke_shortcut_exists T col t0 hT hcol C a b hab ha
  let D : T.Cycle := ⟨projectSpokeDarts T (blackNonOuter T col t0) C.val,
    project_spoke_cycle T col t0 hT hcol C⟩
  have hem : e ∈ D.val := spoke_shortcut_mem_projected T col t0 hT hcol C a b hab ha e he
  have hl := T.cycle_face_mem_leftRegion D e hem
  obtain ⟨outer, hout⟩ := T.exists_face_outside_cycle_leftRegion hT.props.1 D
  have hr := T.cycle_boundary_opposite_outside hT.props.1 D outer hout e hem
  have hb := spoke_shortcut_same_face T col t0 hT hcol C a b hab ha
  have hprev (d : SpokeCorner T (blackNonOuter T col t0)) :
      T.faceOf (prevCorner T _ d).val = T.faceOf d.val := by
    change T.faceOf (T.facePerm.symm d.val) = T.faceOf d.val
    rw [← T.dual_rot_vertex (T.facePerm.symm d.val), T.facePerm.apply_symm_apply]
  have hprevne (d : SpokeCorner T (blackNonOuter T col t0)) :
      prevCorner T _ d ≠ d := by
    intro hd
    exact (triangle_corner_neighbors_ne T hT d.val).2 (congrArg Subtype.val hd)
  rcases spoke_triangle_shortcut_cases T col t0 hT hcol C a b hab ha e he with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · have hs := spoke_shortcut_sector_split T col t0 hT hcol C a b hab ha _ he a.1 rfl rfl
    have hn : ¬ spokeProjectedSide T col t0 hT hcol C
        (spokeFaceClass T _ (Sum.inr a.1)) := fun hp => hs.1.mp hp hl
    have hba : b.1 ≠ a.1 := by
      intro hba
      exact (triangle_corner_neighbors_ne T hT a.1.val).1
        (h.symm.trans (congrArg Subtype.val hba))
    have hpba : prevCorner T _ b.1 = a.1 := by
      apply Subtype.ext
      change T.facePerm.symm b.1.val = a.1.val
      rw [h, T.facePerm.symm_apply_apply]
    exact ⟨(hs.2 _ (hprev a.1) (hprevne a.1)).mpr hl,
      (hs.2 _ hb.2.symm hba).mpr hl, hn, hpba ▸ hn⟩
  · have hl' : T.faceOf (T.edgeInv b.1.val) ∈ T.leftRegion D := hl
    have hr' : T.faceOf b.1.val ∉ T.leftRegion D := by
      rw [T.edgeInv_involutive] at hr
      exact hr
    have hfa : T.faceOf a.1.val ∉ T.leftRegion D := hb.2 ▸ hr'
    have hqe : T.edgeOf b.1.val = T.edgeOf (T.edgeInv b.1.val) :=
      (T.edgeOf_eq_iff b.1.val (T.edgeInv b.1.val)).mpr (Or.inr rfl)
    have hs := spoke_shortcut_sector_split T col t0 hT hcol C a b hab ha _ he b.1 hb.2.symm hqe
    have hn (d : SpokeCorner T (blackNonOuter T col t0))
        (hd : T.faceOf d.val = T.faceOf a.1.val) (hne : d ≠ b.1) :
        ¬ spokeProjectedSide T col t0 hT hcol C (spokeFaceClass T _ (Sum.inr d)) :=
      fun hp => hfa ((hs.2 d hd hne).mp hp)
    have habne : a.1 ≠ b.1 := by
      intro habne
      exact (triangle_corner_neighbors_ne T hT a.1.val).2
        (h.symm.trans (congrArg Subtype.val habne).symm)
    have hpab : prevCorner T _ a.1 = b.1 := Subtype.ext h.symm
    have hp : spokeProjectedSide T col t0 hT hcol C (spokeFaceClass T _ (Sum.inr b.1)) :=
      hs.1.mpr hfa
    exact ⟨hpab ▸ hp, hp, hn a.1 rfl habne,
      hn _ ((hprev b.1).trans hb.2.symm) (hprevne b.1)⟩

-- @node: spokeGraphBounded_faceOf
/-- If [the map is a sphere triangulation](hyp:hT) and [the coloring separates
faces across every edge](hyp:hcol), then [the face assigned to any directed spoke
in the bounded spoke map equals its prescribed sector face class](goal). -/
lemma spokeGraphBounded_faceOf (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (d : SpokeDart T (blackNonOuter T col t0)) :
    (spokeGraphBounded T col t0 hT hcol).faceOf d =
      spokeDartFace T (blackNonOuter T col t0) d :=
  (Classical.choose_spec (exists_spokeBoundaryFace T hT _
    (bounded_faces_disjoint T col t0 hcol))).1 d

-- @node: spokeProjectedSide_cycle_dart
/-- Suppose [the map is a sphere triangulation](hyp:hT) and [the coloring separates
faces across every edge](hyp:hcol). If [a directed spoke belongs to the cycle](hyp:hd),
then [its face has the projected left-side label and the face of its reverse
does not](goal). -/
lemma spokeProjectedSide_cycle_dart (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (d : SpokeDart T (blackNonOuter T col t0)) (hd : d ∈ C.val) :
    spokeProjectedSide T col t0 hT hcol C
        ((spokeGraphBounded T col t0 hT hcol).faceOf d) ∧
    ¬ spokeProjectedSide T col t0 hT hcol C
        ((spokeGraphBounded T col t0 hT hcol).faceOf
          ((spokeGraphBounded T col t0 hT hcol).edgeInv d)) := by
  have pair (a b : SpokeDart T (blackNonOuter T col t0))
      (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true) :
      (spokeProjectedSide T col t0 hT hcol C (spokeDartFace T _ a) ∧
        ¬ spokeProjectedSide T col t0 hT hcol C (spokeDartFace T _ (a.1, !a.2))) ∧
      (spokeProjectedSide T col t0 hT hcol C (spokeDartFace T _ b) ∧
        ¬ spokeProjectedSide T col t0 hT hcol C (spokeDartFace T _ (b.1, !b.2))) := by
    have hs := spoke_shortcut_oriented_sectors T col t0 hT hcol C a b hab ha
    have hb := (spoke_shortcut_same_face T col t0 hT hcol C a b hab ha).1
    simpa only [spokeDartFace, ha, hb, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte] using And.intro (And.intro hs.1 hs.2.2.1) (And.intro hs.2.1 hs.2.2.2)
  rw [spokeGraphBounded_faceOf, spokeGraphBounded_faceOf]
  change spokeProjectedSide T col t0 hT hcol C (spokeDartFace T _ d) ∧
    ¬ spokeProjectedSide T col t0 hT hcol C
      (spokeDartFace T _ ((spokeRotation T hT _ _).edgeInv d))
  rw [spokeRotation_edgeInv]
  cases hb : d.2 with
  | true =>
    have hm : d ∈ (C.val.zip (C.val.rotate 1)).map Prod.fst := by
      rw [List.map_fst_zip (by simp)]
      exact hd
    obtain ⟨⟨a, b⟩, hab, he⟩ := List.mem_map.mp hm
    change a = d at he
    subst a
    simpa only [hb] using (pair d b hab hb).1
  | false =>
    have hm : d ∈ (C.val.zip (C.val.rotate 1)).map Prod.snd := by
      rw [List.map_snd_zip (by simp)]
      exact List.mem_rotate.mpr hd
    obtain ⟨⟨a, b⟩, hab, he⟩ := List.mem_map.mp hm
    change b = d at he
    subst b
    have ha : a.2 = true := by
      have halt := spoke_cycle_alternates T col t0 hT hcol C a d hab
      cases h : a.2 <;> simp_all
    simpa only [hb] using (pair a d hab ha).2

-- @node: spokeProjectedSide_across_noncycle
/-- Suppose [the map is a sphere triangulation](hyp:hT) and [the coloring separates
faces across every edge](hyp:hcol). If [a spoke's underlying edge is absent from
the cycle](hyp:hd), then [the faces on its two sides have the same projected
left-side label](goal). -/
lemma spokeProjectedSide_across_noncycle (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (d : SpokeDart T (blackNonOuter T col t0))
    (hd : (spokeGraphBounded T col t0 hT hcol).edgeOf d ∉
      C.val.map (spokeGraphBounded T col t0 hT hcol).edgeOf) :
    spokeProjectedSide T col t0 hT hcol C ((spokeGraphBounded T col t0 hT hcol).faceOf d) ↔
      spokeProjectedSide T col t0 hT hcol C
        ((spokeGraphBounded T col t0 hT hcol).faceOf
          ((spokeGraphBounded T col t0 hT hcol).edgeInv d)) := by
  let N := spokeGraphBounded T col t0 hT hcol
  let Q := fun r : SpokeCorner T (blackNonOuter T col t0) =>
    spokeProjectedSide T col t0 hT hcol C (spokeFaceClass T _ (Sum.inr r))
  have hprev (r : SpokeCorner T (blackNonOuter T col t0)) :
      T.faceOf (prevCorner T _ r).val = T.faceOf r.val := by
    change T.faceOf (T.facePerm.symm r.val) = T.faceOf r.val
    rw [← T.dual_rot_vertex (T.facePerm.symm r.val), T.facePerm.apply_symm_apply]
  have hcorner (a : N.Dart) (ha : a ∈ C.val) : d.1 ≠ a.1 := by
    intro h
    apply hd
    apply List.mem_map.mpr
    refine ⟨a, ha, (N.edgeOf_eq_iff a d).mpr ?_⟩
    by_cases hb : d.2 = a.2
    · exact Or.inl (Prod.ext h hb)
    · right
      change d = (spokeRotation T hT _ _).edgeInv a
      rw [spokeRotation_edgeInv]
      refine Prod.ext ?_ ?_
      · exact h
      · cases ha : a.2 <;> cases hd : d.2 <;> simp_all
  have hlabels : Q d.1 ↔ Q (prevCorner T _ d.1) := by
    by_cases hv : ∃ x ∈ C.val, x.2 = false ∧ T.faceOf x.1.val = T.faceOf d.1.val
    · obtain ⟨b, hbmem, hb, hbf⟩ := hv
      have hm : b ∈ (C.val.zip (C.val.rotate 1)).map Prod.snd := by
        rw [List.map_snd_zip (by simp)]
        exact List.mem_rotate.mpr hbmem
      obtain ⟨⟨a, b'⟩, hab, heq⟩ := List.mem_map.mp hm
      change b' = b at heq
      subst b'
      have ha : a.2 = true := by
        have halt := spoke_cycle_alternates T col t0 hT hcol C a b hab
        cases h : a.2 <;> simp_all
      have hface := (spoke_shortcut_same_face T col t0 hT hcol C a b hab ha).2
      have hda : T.faceOf d.1.val = T.faceOf a.1.val := (hface.trans hbf).symm
      have hna := hcorner a (List.of_mem_zip hab).1
      have hnb := hcorner b hbmem
      obtain ⟨e, he⟩ := spoke_shortcut_exists T col t0 hT hcol C a b hab ha
      rcases spoke_triangle_shortcut_cases T col t0 hT hcol C a b hab ha e he with
        ⟨h, rfl⟩ | ⟨h, rfl⟩
      · have hs := spoke_shortcut_sector_split T col t0 hT hcol C a b hab ha _ he a.1 rfl rfl
        have hnpa : prevCorner T _ d.1 ≠ a.1 := by
          intro hp
          apply hnb
          apply Subtype.ext
          have hp' := congrArg (fun r => T.facePerm r.val) hp
          change T.facePerm (T.facePerm.symm d.1.val) = T.facePerm a.1.val at hp'
          rw [T.facePerm.apply_symm_apply, ← h] at hp'
          exact hp'
        exact (hs.2 _ hda hna).trans ((hs.2 _ ((hprev _).trans hda) hnpa).symm)
      · have hqe : T.edgeOf b.1.val = T.edgeOf (T.edgeInv b.1.val) :=
          (T.edgeOf_eq_iff b.1.val (T.edgeInv b.1.val)).mpr (Or.inr rfl)
        have hs := spoke_shortcut_sector_split T col t0 hT hcol C a b hab ha _ he b.1 hface.symm hqe
        have hnpb : prevCorner T _ d.1 ≠ b.1 := by
          intro hp
          apply hna
          apply Subtype.ext
          have hp' := congrArg (fun r => T.facePerm r.val) hp
          change T.facePerm (T.facePerm.symm d.1.val) = T.facePerm b.1.val at hp'
          rw [T.facePerm.apply_symm_apply, h, T.facePerm.apply_symm_apply] at hp'
          exact hp'
        exact (hs.2 _ hda hnb).trans ((hs.2 _ ((hprev _).trans hda) hnpb).symm)
    · let f : blackNonOuter T col t0 := ⟨T.faceOf d.1.val, d.1.property⟩
      have hmiss : ∀ a ∈ C.val, N.vert a ≠ Sum.inr f := by
        intro a ha heq
        change spokeVert T _ a = Sum.inr f at heq
        cases hb : a.2 with
        | true => simp [spokeVert, hb] at heq
        | false =>
          have hf : T.faceOf a.1.val = T.faceOf d.1.val := by
            simpa only [spokeVert, hb, Bool.false_eq_true, ↓reduceIte,
              Sum.inr.injEq, Subtype.ext_iff, f] using heq
          exact hv ⟨a, ha, hb, hf⟩
      exact (spoke_unvisited_sector_side T col t0 hT hcol C f hmiss d.1 rfl).trans
        ((spoke_unvisited_sector_side T col t0 hT hcol C f hmiss _ (hprev _)).symm)
  rw [spokeGraphBounded_faceOf, spokeGraphBounded_faceOf]
  change _ ↔ spokeProjectedSide T col t0 hT hcol C
    (spokeDartFace T _ ((spokeRotation T hT _ _).edgeInv d))
  rw [spokeRotation_edgeInv]
  cases hb : d.2 with
  | false => simpa only [spokeDartFace, hb, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte, Q] using hlabels
  | true => simpa only [spokeDartFace, hb, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Q] using hlabels.symm

-- @node: spokeProjectedSide_avoiding_path
/-- Suppose [the map is a sphere triangulation](hyp:hT) and [the coloring separates
faces across every edge](hyp:hcol). If [two local boundaries are joined by a path
crossing only edges outside the cycle](hyp:hp), then [their containing faces have
the same projected left-side label](goal). -/
lemma spokeProjectedSide_avoiding_path (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (b c : (spokeGraphBounded T col t0 hT hcol).LocalBoundary)
    (hp : (spokeGraphBounded T col t0 hT hcol).localBoundariesJoinedAvoiding C.val b c) :
    spokeProjectedSide T col t0 hT hcol C ((spokeGraphBounded T col t0 hT hcol).boundaryFace b) ↔
      spokeProjectedSide T col t0 hT hcol C
        ((spokeGraphBounded T col t0 hT hcol).boundaryFace c) := by
  induction hp with
  | refl => exact Iff.rfl
  | tail hp hs ih =>
    obtain ⟨d, hd, rfl, rfl⟩ := hs
    exact ih.trans (spokeProjectedSide_across_noncycle T col t0 hT hcol C d hd)

-- @node: spokeProjectedSide_leftLocalRegion
/-- Suppose [the map is a sphere triangulation](hyp:hT) and [the coloring separates
faces across every edge](hyp:hcol). If [a local boundary lies in the spoke cycle's
local left region](hyp:hb), then [its containing face has the projected left-side
label](goal). -/
lemma spokeProjectedSide_leftLocalRegion (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (b : (spokeGraphBounded T col t0 hT hcol).LocalBoundary)
    (hb : b ∈ (spokeGraphBounded T col t0 hT hcol).leftLocalRegion C) :
    spokeProjectedSide T col t0 hT hcol C
      ((spokeGraphBounded T col t0 hT hcol).boundaryFace b) := by
  obtain ⟨d, hd, hp⟩ := hb
  exact (spokeProjectedSide_avoiding_path T col t0 hT hcol C _ b hp).mp
    (spokeProjectedSide_cycle_dart T col t0 hT hcol C d hd).1

end OaiPairedStatesHamiltonian
