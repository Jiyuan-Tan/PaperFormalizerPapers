module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SpokeMaps

/-! Shortcutting spoke cycles and their signed incidence weights. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

/-- For [a sphere map](hyp:T), [selected faces](hyp:faces), and
[an ordered list of directed spokes in those faces](hyp:ds), the
[projected list of original darts](goal) examines cyclically consecutive spokes
and keeps a dart from the first corner's vertex to the second corner's vertex
inside the first corner's face whenever the first spoke points toward the center
and such a dart exists. -/
noncomputable def projectSpokeDarts (faces : Finset T.Face) (ds : List (SpokeDart T faces)) : List T.Dart :=
  (ds.zip (ds.rotate 1)).filterMap (fun p =>
    if p.1.2 then
      if h : ∃ e, FaceDart T (T.faceOf p.1.1.val) (T.vert p.1.1.val) (T.vert p.2.1.val) e
      then some (Classical.choose h) else none
    else none)

-- @node: cyclic_zip_map_step
/-- For [a function assigning heads to entries](hyp:head) and
[a function assigning tails to entries](hyp:tail), if
[the list of heads equals the list of tails shifted cyclically by one
position](hyp:h) and [two entries occur consecutively in that cyclic list](hyp:hab),
then [the head of the first entry equals the tail of the second](goal). -/
lemma cyclic_zip_map_step {α β : Type*} (ds : List α) (head tail : α → β)
    (h : ds.map head = (ds.rotate 1).map tail)
    (a b : α) (hab : (a, b) ∈ ds.zip (ds.rotate 1)) : head a = tail b := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hab
  have hi' : i < ds.length := by simpa using hi
  have hi'' : i < (ds.rotate 1).length := by simpa using hi'
  have he' : (ds[i], (ds.rotate 1)[i]) = (a, b) := by
    simpa only [List.getElem_zip] using he
  have hm := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi',
    List.getElem?_eq_getElem hi'', Option.map_some, Option.some.injEq] at hm
  rcases Prod.mk.inj he' with ⟨ha, hb⟩
  rw [ha, hb] at hm
  exact hm

-- @node: spoke_cycle_head_map
/-- If [the sphere map is a triangulation](hyp:hT) and
[the face coloring assigns different colors across every edge](hyp:hcol), then
for [a cycle in the bounded black spoke map](hyp:C),
[the ordered heads equal the ordered starting vertices shifted cyclically by
one position](goal). -/
lemma spoke_cycle_head_map (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    C.val.map (spokeGraphBounded T col t0 hT hcol).head =
      (C.val.rotate 1).map (spokeGraphBounded T col t0 hT hcol).vert := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa only [List.getElem_map, List.getElem_rotate, List.get_eq_getElem] using
      C.property.1.2.2 ⟨i, by simpa using hi⟩

-- @node: spoke_cycle_alternates
/-- If [the sphere map is a triangulation](hyp:hT),
[the face coloring assigns different colors across every edge](hyp:hcol), and
[a bounded black spoke cycle](hyp:C) has [two cyclically consecutive darts](hyp:hab),
then [their direction flags are opposite: one points toward a face center and
the other away from it](goal). -/
lemma spoke_cycle_alternates (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) : b.2 = !a.2 := by
  have hs := cyclic_zip_map_step C.val _ _ (spoke_cycle_head_map T col t0 hT hcol C) a b hab
  change spokeVert T _ ((spokeRotation T hT _ _).edgeInv a) = spokeVert T _ b at hs
  rw [spokeRotation_edgeInv] at hs
  cases ha : a.2 <;> cases hb : b.2 <;> simp_all [spokeVert]

-- @node: spoke_shortcut_exists
/-- If [the sphere map is a triangulation](hyp:hT),
[the face coloring assigns different colors across every edge](hyp:hcol), and
[a bounded black spoke cycle](hyp:C) has [two cyclically consecutive darts](hyp:hab)
with [the first pointing toward a face center](hyp:ha), then
[an original dart joins their original vertices in that same triangle](goal). -/
lemma spoke_shortcut_exists (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle)
    (a b : SpokeDart T (blackNonOuter T col t0))
    (hab : (a, b) ∈ C.val.zip (C.val.rotate 1)) (ha : a.2 = true) :
    ∃ e, FaceDart T (T.faceOf a.1.val) (T.vert a.1.val) (T.vert b.1.val) e := by
  have hb : b.2 = false := by rw [spoke_cycle_alternates T col t0 hT hcol C a b hab, ha]; rfl
  have hs := cyclic_zip_map_step C.val _ _ (spoke_cycle_head_map T col t0 hT hcol C) a b hab
  change spokeVert T _ ((spokeRotation T hT _ _).edgeInv a) = spokeVert T _ b at hs
  rw [spokeRotation_edgeInv] at hs
  have hf : T.faceOf a.1.val = T.faceOf b.1.val := by
    simpa only [spokeVert, ha, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Sum.inr.injEq, Subtype.ext_iff] using hs
  have incident (d : SpokeCorner T (blackNonOuter T col t0)) :
      T.vert d.val ∈ T.faceVertices (T.faceOf d.val) := by
    rw [triangulation_faceVertices_eq_image T hT]
    exact Finset.mem_image.mpr ⟨d.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  apply exists_faceDart T hT _ _ _ (incident a.1) (hf ▸ incident b.1)
  intro hv
  have hinj : Set.InjOn T.vert (↑(T.faceDarts (T.faceOf a.1.val)) : Set T.Dart) := by
    apply Finset.card_image_iff.mp
    rw [← triangulation_faceVertices_eq_image T hT]
    exact (hT.props.2.2.2 _).2.trans
      ((T.faceLength_eq_card_faceDarts _).symm.trans (hT.props.2.2.2 _).1).symm
  have hc : a.1 = b.1 := Subtype.ext (hinj
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf.symm⟩) hv)
  let N := spokeGraphBounded T col t0 hT hcol
  have he : N.edgeOf a = N.edgeOf b := by
    apply (N.edgeOf_eq_iff a b).mpr
    right
    change b = (spokeRotation T hT _ _).edgeInv a
    rw [spokeRotation_edgeInv]
    exact Prod.ext hc.symm (by rw [ha, hb]; rfl)
  have heq := List.inj_on_of_nodup_map C.property.1.2.1 (List.of_mem_zip hab).1
    (List.mem_rotate.mp (List.of_mem_zip hab).2) he
  have := congrArg Prod.snd heq
  simp only [ha, hb, Bool.true_eq_false] at this

-- @node: projectSpokeDarts_vertex_maps
/-- If [the sphere map is a triangulation](hyp:hT) and
[the face coloring assigns different colors across every edge](hyp:hcol), then
for [a bounded black spoke cycle](hyp:C),
[the projected starting vertices are exactly the original vertices of the
centerward spokes in order, and the projected heads are exactly the original
vertices of the outward spokes in the cyclically shifted list](goal). -/
lemma projectSpokeDarts_vertex_maps (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    (projectSpokeDarts T (blackNonOuter T col t0) C.val).map T.vert =
      C.val.filterMap (fun d => if d.2 then some (T.vert d.1.val) else none) ∧
    (projectSpokeDarts T (blackNonOuter T col t0) C.val).map T.head =
      (C.val.rotate 1).filterMap (fun d => if !d.2 then some (T.vert d.1.val) else none) := by
  constructor
  · unfold projectSpokeDarts
    rw [List.map_filterMap]
    calc
      _ = (C.val.zip (C.val.rotate 1)).filterMap
          (fun p => if p.1.2 then some (T.vert p.1.1.val) else none) := by
        apply List.filterMap_congr
        rintro ⟨a, b⟩ hab
        by_cases ha : a.2 = true
        · have hex := spoke_shortcut_exists T col t0 hT hcol C a b hab ha
          simp only [ha, ↓reduceIte, dif_pos hex, Option.map_some]
          exact congrArg some (Classical.choose_spec hex).1
        · simp [ha]
      _ = _ := by
        change (C.val.zip (C.val.rotate 1)).filterMap
          ((fun d : SpokeDart T (blackNonOuter T col t0) =>
            if d.2 then some (T.vert d.1.val) else none) ∘ Prod.fst) = _
        rw [← List.filterMap_map, List.map_fst_zip (by simp)]
        rfl
  · unfold projectSpokeDarts
    rw [List.map_filterMap]
    calc
      _ = (C.val.zip (C.val.rotate 1)).filterMap
          (fun p => if !p.2.2 then some (T.vert p.2.1.val) else none) := by
        apply List.filterMap_congr
        rintro ⟨a, b⟩ hab
        have hb := spoke_cycle_alternates T col t0 hT hcol C a b hab
        by_cases ha : a.2 = true
        · have hex := spoke_shortcut_exists T col t0 hT hcol C a b hab ha
          simp only [ha, Bool.not_true] at hb
          simp only [ha, hb, Bool.not_false, ↓reduceIte, dif_pos hex, Option.map_some]
          exact congrArg some (Classical.choose_spec hex).2.1
        · have ha' : a.2 = false := Bool.eq_false_iff.mpr ha
          simp [ha', hb]
      _ = _ := by
        change (C.val.zip (C.val.rotate 1)).filterMap
          ((fun d : SpokeDart T (blackNonOuter T col t0) =>
            if !d.2 then some (T.vert d.1.val) else none) ∘ Prod.snd) = _
        rw [← List.filterMap_map, List.map_snd_zip (by simp)]
        rfl

-- @node: spoke_shift_corner_map
/-- If [the sphere map is a triangulation](hyp:hT),
[no edge has selected faces on both sides](hyp:hfaces), and
[the heads of a spoke list equal its starting vertices shifted cyclically by
one position](hyp:hmap), then [the ordered original vertices of its outward
spokes equal those of the centerward spokes in the shifted list](goal). -/
lemma spoke_shift_corner_map (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (ds : List (SpokeDart T faces))
    (hmap : ds.map (spokeRotation T hT faces hfaces).head =
      (ds.rotate 1).map (spokeRotation T hT faces hfaces).vert) :
    ds.filterMap (fun d => if !d.2 then some (T.vert d.1.val) else none) =
      (ds.rotate 1).filterMap (fun d => if d.2 then some (T.vert d.1.val) else none) := by
  conv_lhs => rw [← List.map_fst_zip (l₁ := ds) (l₂ := ds.rotate 1) (by simp),
    List.filterMap_map]
  conv_rhs => rw [← List.map_snd_zip (l₁ := ds) (l₂ := ds.rotate 1) (by simp),
    List.filterMap_map]
  apply List.filterMap_congr
  rintro ⟨a, b⟩ hab
  have hs := cyclic_zip_map_step ds _ _ hmap a b hab
  change spokeVert T faces ((spokeRotation T hT faces hfaces).edgeInv a) =
    spokeVert T faces b at hs
  rw [spokeRotation_edgeInv] at hs
  cases ha : a.2 <;> cases hb : b.2 <;> simp_all [spokeVert]

-- @node: filterMap_alternating_rotate_two
/-- For [a list](hyp:ds), [a Boolean selection rule](hyp:b), and
[a map assigning a value to each entry](hyp:g), if
[the selection flags alternate between every cyclically consecutive pair](hyp:halt),
then [shifting the list cyclically by two positions before selecting and mapping
entries gives the selected values shifted cyclically by one position](goal). -/
lemma filterMap_alternating_rotate_two {α β : Type*} (ds : List α) (b : α → Bool) (g : α → β)
    (halt : ∀ a c, (a, c) ∈ ds.zip (ds.rotate 1) → b c = !b a) :
    (ds.rotate 2).filterMap (fun a => if b a then some (g a) else none) =
      (ds.filterMap (fun a => if b a then some (g a) else none)).rotate 1 := by
  cases ds with
  | nil => simp
  | cons a ds =>
    cases ds with
    | nil =>
      have h := halt a a (by simp)
      cases hb : b a <;> simp [hb] at h
    | cons c ds =>
      have h := halt a c (by simp [List.rotate_cons_succ])
      cases ha : b a <;> simp only [ha, Bool.not_false, Bool.not_true] at h <;>
        simp [List.rotate_cons_succ, List.filterMap_append, ha, h, List.append_assoc]

-- @node: projectSpokeDarts_vertices_nodup
/-- If [the sphere map is a triangulation](hyp:hT) and
[the face coloring assigns different colors across every edge](hyp:hcol), then
for [a bounded black spoke cycle](hyp:C),
[the projected darts have no repeated starting vertex](goal). -/
lemma projectSpokeDarts_vertices_nodup (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    ((projectSpokeDarts T (blackNonOuter T col t0) C.val).map T.vert).Nodup := by
  rw [(projectSpokeDarts_vertex_maps T col t0 hT hcol C).1]
  have hn := C.property.2
  change (C.val.map (spokeVert T (blackNonOuter T col t0))).Nodup at hn
  have h := hn.filterMap (f := Sum.elim some (fun _ => none)) (by
    intro a b v ha hb
    cases a <;> cases b <;> simp_all)
  rw [List.filterMap_map] at h
  convert h using 1
  apply List.filterMap_congr
  intro d hd
  cases hb : d.2 <;> simp [spokeVert, hb, Function.comp_def]

-- @node: projectSpokeDarts_nonempty
/-- If [the sphere map is a triangulation](hyp:hT) and
[the face coloring assigns different colors across every edge](hyp:hcol), then
[a bounded black spoke cycle](hyp:C) [projects to a nonempty list of original
darts](goal). -/
lemma projectSpokeDarts_nonempty (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    projectSpokeDarts T (blackNonOuter T col t0) C.val ≠ [] := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  have hz : a ∈ (C.val.zip (C.val.rotate 1)).map Prod.fst := by
    rw [List.map_fst_zip (by simp)]
    exact ha
  obtain ⟨⟨a', b⟩, hab, he⟩ := List.mem_map.mp hz
  dsimp only at he
  subst a'
  have hex : ∃ d ∈ C.val, d.2 = true := by
    cases hb : a.2 with
    | true => exact ⟨a, ha, hb⟩
    | false =>
      refine ⟨b, List.mem_rotate.mp (List.of_mem_zip hab).2, ?_⟩
      rw [spoke_cycle_alternates T col t0 hT hcol C a b hab, hb]
      rfl
  obtain ⟨d, hd, hb⟩ := hex
  have hm : T.vert d.1.val ∈ (projectSpokeDarts T (blackNonOuter T col t0) C.val).map T.vert := by
    rw [(projectSpokeDarts_vertex_maps T col t0 hT hcol C).1]
    exact List.mem_filterMap.mpr ⟨d, hd, by simp [hb]⟩
  intro he
  simpa [he] using hm

-- @node: projectSpokeDarts_head_map
/-- If [the sphere map is a triangulation](hyp:hT) and
[the face coloring assigns different colors across every edge](hyp:hcol), then
for [a bounded black spoke cycle](hyp:C),
[the projected heads equal the projected starting vertices shifted cyclically by
one position](goal). -/
lemma projectSpokeDarts_head_map (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    (projectSpokeDarts T (blackNonOuter T col t0) C.val).map T.head =
      ((projectSpokeDarts T (blackNonOuter T col t0) C.val).rotate 1).map T.vert := by
  let ds : List (SpokeDart T (blackNonOuter T col t0)) := C.val
  have hm : ds.map (spokeRotation T hT _ (bounded_faces_disjoint T col t0 hcol)).head =
      (ds.rotate 1).map (spokeRotation T hT _ (bounded_faces_disjoint T col t0 hcol)).vert :=
    spoke_cycle_head_map T col t0 hT hcol C
  have hrot : (ds.rotate 1).map (spokeRotation T hT _ (bounded_faces_disjoint T col t0 hcol)).head =
      ((ds.rotate 1).rotate 1).map (spokeRotation T hT _ (bounded_faces_disjoint T col t0 hcol)).vert := by
    simpa only [← List.map_rotate] using congrArg (fun ds => ds.rotate 1) hm
  rw [(projectSpokeDarts_vertex_maps T col t0 hT hcol C).2]
  change (ds.rotate 1).filterMap (fun d => if !d.2 then some (T.vert d.1.val) else none) = _
  rw [spoke_shift_corner_map T hT _ (bounded_faces_disjoint T col t0 hcol) (ds.rotate 1) hrot,
    List.rotate_rotate]
  rw [filterMap_alternating_rotate_two ds (fun d => d.2) (fun d => T.vert d.1.val)
    (spoke_cycle_alternates T col t0 hT hcol C)]
  rw [List.map_rotate]
  exact congrArg (fun vs => vs.rotate 1) (projectSpokeDarts_vertex_maps T col t0 hT hcol C).1.symm

-- @node: selected_edge_face_unique
/-- If [no edge has selected faces on both sides](hyp:hfaces),
[one face is selected](hyp:hf), [another face is selected](hyp:hg),
[a dart's edge borders the first face on at least one side](hyp:hd),
[another dart's edge borders the second face on at least one side](hyp:he), and
[the two darts represent the same undirected edge](hyp:hedge), then
[the two faces are equal](goal). -/
lemma selected_edge_face_unique (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (f g : T.Face) (hf : f ∈ faces) (hg : g ∈ faces)
    (d e : T.Dart) (hd : T.faceOf d = f ∨ T.faceOf (T.edgeInv d) = f)
    (he : T.faceOf e = g ∨ T.faceOf (T.edgeInv e) = g)
    (hedge : T.edgeOf d = T.edgeOf e) : f = g := by
  rcases (T.edgeOf_eq_iff d e).mp hedge with rfl | rfl
  · rcases hd with hd | hd <;> rcases he with he | he
    · exact hd.symm.trans he
    · exact (hfaces e ⟨hd ▸ hf, he ▸ hg⟩).elim
    · exact (hfaces e ⟨he ▸ hg, hd ▸ hf⟩).elim
    · exact hd.symm.trans he
  · rw [T.edgeInv_involutive] at he
    rcases hd with hd | hd <;> rcases he with he | he
    · exact (hfaces d ⟨hd ▸ hf, he ▸ hg⟩).elim
    · exact hd.symm.trans he
    · exact hd.symm.trans he
    · exact (hfaces d ⟨he ▸ hg, hd ▸ hf⟩).elim

-- @node: projectSpokeDarts_edges_nodup
/-- If [the sphere map is a triangulation](hyp:hT) and
[the face coloring assigns different colors across every edge](hyp:hcol), then
for [a bounded black spoke cycle](hyp:C),
[the projected darts use no undirected edge more than once](goal). -/
lemma projectSpokeDarts_edges_nodup (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    ((projectSpokeDarts T (blackNonOuter T col t0) C.val).map T.edgeOf).Nodup := by
  let N := spokeGraphBounded T col t0 hT hcol
  have hn : ((C.val.zip (C.val.rotate 1)).map (fun p => N.vert p.2)).Nodup := by
    change ((C.val.zip (C.val.rotate 1)).map (N.vert ∘ Prod.snd)).Nodup
    rw [← List.map_map, List.map_snd_zip (by simp), List.map_rotate]
    exact List.nodup_rotate.mpr C.property.2
  have hpw := List.pairwise_map.mp hn
  unfold projectSpokeDarts
  rw [List.map_filterMap]
  apply List.pairwise_filterMap.mpr
  apply hpw.imp_of_mem
  rintro ⟨a, b⟩ ⟨c, d⟩ hab hcd hne x hx y hy hxy
  by_cases ha : a.2 = true
  swap
  · simpa [ha] using hx
  by_cases hc : c.2 = true
  swap
  · simpa [hc] using hy
  have hex := spoke_shortcut_exists T col t0 hT hcol C a b hab ha
  have hex' := spoke_shortcut_exists T col t0 hT hcol C c d hcd hc
  simp only [ha, ↓reduceIte, dif_pos hex, Option.map_some, Option.some.injEq] at hx
  simp only [hc, ↓reduceIte, dif_pos hex', Option.map_some, Option.some.injEq] at hy
  have hf : T.faceOf a.1.val = T.faceOf c.1.val :=
    selected_edge_face_unique T _ (bounded_faces_disjoint T col t0 hcol)
      _ _ a.1.property c.1.property _ _ (Classical.choose_spec hex).2.2
      (Classical.choose_spec hex').2.2 (hx.trans (hxy.trans hy.symm))
  have hs := cyclic_zip_map_step C.val _ _ (spoke_cycle_head_map T col t0 hT hcol C) a b hab
  have hs' := cyclic_zip_map_step C.val _ _ (spoke_cycle_head_map T col t0 hT hcol C) c d hcd
  apply hne
  change N.vert b = N.vert d
  rw [← hs, ← hs']
  change spokeVert T _ ((spokeRotation T hT _ _).edgeInv a) =
    spokeVert T _ ((spokeRotation T hT _ _).edgeInv c)
  rw [spokeRotation_edgeInv, spokeRotation_edgeInv]
  simp only [spokeVert, ha, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Sum.inr.injEq, Subtype.ext_iff]
  exact hf

-- @node: project_spoke_cycle
/-- If [the sphere map is a triangulation](hyp:hT) and
[the face coloring assigns different colors across every edge](hyp:hcol), then
[a bounded black spoke cycle](hyp:C) [projects to a simple cycle in the original
map](goal). -/
lemma project_spoke_cycle (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (C : (spokeGraphBounded T col t0 hT hcol).Cycle) :
    T.IsSimpleCycle (projectSpokeDarts T (blackNonOuter T col t0) C.val) := by
  refine ⟨⟨projectSpokeDarts_nonempty T col t0 hT hcol C,
    projectSpokeDarts_edges_nodup T col t0 hT hcol C, ?_⟩,
    projectSpokeDarts_vertices_nodup T col t0 hT hcol C⟩
  intro i
  have h := projectSpokeDarts_head_map T col t0 hT hcol C
  have he := congrArg (fun ds => ds[i.val]?) h
  have hi : i.val < ((projectSpokeDarts T (blackNonOuter T col t0) C.val).rotate 1).length :=
    by simpa using i.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at he
  simpa only [List.getElem_rotate, List.get_eq_getElem] using he

end OaiPairedStatesHamiltonian
