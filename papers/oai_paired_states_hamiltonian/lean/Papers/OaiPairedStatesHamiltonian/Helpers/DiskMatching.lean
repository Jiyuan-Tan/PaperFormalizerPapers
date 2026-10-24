module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleIncidence

/-! The state bijection counts the black faces in a cycle-side disk. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

-- @node: chosenEdges_state_witness
/-- In a [sphere triangulation](hyp:hT), if [a directed edge is selected by the state's edge choice](hyp:hd), then [there is a non-outer black face matched by the state to its tail and incident to one of its two sides](goal). -/
lemma chosenEdges_state_witness (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face) (r : State T col t0)
    (choice : EdgeChoice T col t0 r) (d : T.Dart)
    (hd : d ∈ ChosenEdges T col t0 hT r choice) :
    ∃ t : blackNonOuter T col t0, T.vert d = (r.val t).val ∧
      (T.faceOf d = t.val ∨ T.faceOf (T.edgeInv d) = t.val) := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hd
  have hs := Classical.choose_spec (exists_faceDart T hT t.val (r.val t).val (choice t).val
    (r.property.incident t) (choice t).property.1 (Ne.symm (choice t).property.2))
  exact ⟨t, hs.1, hs.2.2⟩

-- @node: cycle_chosen_black_face_side
/-- In a [sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hcol), suppose [the outer face lies outside a simple cycle's left region](hyp:hout), [a directed edge lies on that cycle](hyp:hd), and [a non-outer black face is incident to one of its sides](hyp:hf). Then [that black face lies in the left region exactly when the directed edge's left face is black in the coloring normalized at the outer face](goal). -/
lemma cycle_chosen_black_face_side (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (C : T.Cycle) (hout : t0 ∉ T.leftRegion C) (d : T.Dart) (hd : d ∈ C.val)
    (t : blackNonOuter T col t0)
    (hf : T.faceOf d = t.val ∨ T.faceOf (T.edgeInv d) = t.val) :
    t.val ∈ T.leftRegion C ↔ normalizedColoring T col t0 (T.faceOf d) = true := by
  have ht : normalizedColoring T col t0 t.val = true := (Finset.mem_filter.mp t.property).2.1
  rcases hf with hf | hf
  · rw [hf]
    exact ⟨fun _ => ht, fun _ => hf ▸ T.cycle_face_mem_leftRegion C d hd⟩
  · have hi : normalizedColoring T col t0 (T.faceOf (T.edgeInv d)) = true := hf.symm ▸ ht
    have hn : normalizedColoring T col t0 (T.faceOf d) ≠ true := fun he =>
      normalizedColoring_partition T col hcol t0 d (he.trans hi.symm)
    constructor
    · intro hin
      exact (T.cycle_boundary_opposite_outside hT.props.1 C t0 hout d hd (hf.symm ▸ hin)).elim
    · intro he
      exact (hn he).elim

-- @node: state_cycle_matching_side_iff
/-- In a [sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hcol), assume [every directed edge of a simple cycle is state-selected](hyp:hC) and [the outer face is outside its left region](hyp:hout). Then [a non-outer black face lies in the left region exactly when its state-matched vertex is strictly inside that region or is the tail of a boundary dart whose left face is black in the coloring normalized at the outer face](goal). -/
lemma state_cycle_matching_side_iff (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r : State T col t0) (choice : EdgeChoice T col t0 r) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice)
    (hout : t0 ∉ T.leftRegion C) (t : blackNonOuter T col t0) :
    t.val ∈ T.leftRegion C ↔ T.strictlyOnSide (T.leftRegion C) C (r.val t).val ∨
      ∃ d ∈ C.val, T.vert d = (r.val t).val ∧
        normalizedColoring T col t0 (T.faceOf d) = true := by
  have boundary (d : T.Dart) (hd : d ∈ C.val) (hv : T.vert d = (r.val t).val) :
      t.val ∈ T.leftRegion C ↔ normalizedColoring T col t0 (T.faceOf d) = true := by
    obtain ⟨u, hu, hface⟩ := chosenEdges_state_witness T hT col t0 r choice d (hC d hd)
    have hut : u = t := r.property.bijective.1 (Subtype.ext (hu.symm.trans hv))
    subst u
    exact cycle_chosen_black_face_side T hT col hcol t0 C hout d hd t hface
  constructor
  · intro ht
    by_cases hv : (r.val t).val ∈ C.val.map T.vert
    · obtain ⟨d, hd, hv⟩ := List.mem_map.mp hv
      exact Or.inr ⟨d, hd, hv, (boundary d hd hv).mp ht⟩
    · exact Or.inl ⟨hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        t.val, ht, r.property.incident t⟩⟩
  · rintro (hi | ⟨d, hd, hv, hc⟩)
    · obtain ⟨_, f, hf, hv⟩ := Finset.mem_filter.mp hi.2
      exact (T.cycle_nonboundary_face_side hT C _ hi.1 f t.val hv
        (r.property.incident t)).mp hf
    · exact (boundary d hd hv).mpr hc

-- @node: SphereMap.cycle_interior_nonRoot
/-- In a [sphere triangulation](hyp:hT), if [the outer face is outside a simple cycle's left region](hyp:hout) and [a vertex is strictly inside that region](hyp:hv), then [the vertex is not incident to the outer face](goal). -/
lemma SphereMap.cycle_interior_nonRoot (T : SphereMap) (hT : IsSphereTriangulation T)
    (C : T.Cycle) (t0 : T.Face) (hout : t0 ∉ T.leftRegion C)
    (v : T.Vertex) (hv : T.strictlyOnSide (T.leftRegion C) C v) : v ∉ roots T t0 := by
  intro hr
  obtain ⟨_, f, hf, hi⟩ := Finset.mem_filter.mp hv.2
  exact hout ((T.cycle_nonboundary_face_side hT C v hv.1 f t0 hi hr).mp hf)

-- @node: state_disk_matching_count
/-- In a [sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hcol), suppose [every directed edge of a simple cycle is state-selected](hyp:hC) and [the cycle is counterclockwise relative to the outer face](hyp:hccw). Then [the number of black faces in the left region equals the number of strictly interior vertices plus the number of boundary darts with a black left face, using the coloring normalized at the outer face](goal). -/
lemma state_disk_matching_count (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r : State T col t0) (choice : EdgeChoice T col t0 r) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice)
    (hccw : T.IsCounterclockwise t0 C) :
    (Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧
      normalizedColoring T col t0 f = true)).card =
      (Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)).card +
        (C.val.filter (fun d => normalizedColoring T col t0 (T.faceOf d) = true)).length := by
  have hout : t0 ∉ T.leftRegion C := fun hin =>
    Set.disjoint_left.mp (T.cycle_sides_partition C).1 hin hccw
  let interior := Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)
  let boundary := ((C.val.filter (fun d =>
    normalizedColoring T col t0 (T.faceOf d) = true)).map T.vert).toFinset
  let faces := Finset.univ.filter (fun t : blackNonOuter T col t0 => t.val ∈ T.leftRegion C)
  have hblack : (Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧
      normalizedColoring T col t0 f = true)).card = faces.card := by
    symm
    apply Finset.card_bij (fun t _ => t.val)
    · intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2,
        (Finset.mem_filter.mp t.property).2.1⟩
    · intro t ht u hu heq
      exact Subtype.ext heq
    · intro f hf
      obtain ⟨_, hin, hc⟩ := Finset.mem_filter.mp hf
      have hne : f ≠ t0 := fun he => hout (he ▸ hin)
      let t : blackNonOuter T col t0 := ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hne⟩⟩
      exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩, rfl⟩
  have hboundary (v : T.Vertex) : v ∈ boundary ↔
      ∃ d ∈ C.val, T.vert d = v ∧ normalizedColoring T col t0 (T.faceOf d) = true := by
    simp only [boundary, List.mem_toFinset, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨d, ⟨hd, hc⟩, hv⟩
      exact ⟨d, hd, hv, by simpa using hc⟩
    · rintro ⟨d, hd, hv, hc⟩
      exact ⟨d, ⟨hd, by simpa using hc⟩, hv⟩
  have hmatch : faces.card = (interior ∪ boundary).card := by
    apply Finset.card_bij (fun t _ => (r.val t).val)
    · intro t ht
      rw [Finset.mem_union, hboundary]
      exact ((state_cycle_matching_side_iff T hT col hcol t0 r choice C hC hout t).mp
        (Finset.mem_filter.mp ht).2).imp
        (fun hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) id
    · intro t ht u hu heq
      exact r.property.bijective.1 (Subtype.ext heq)
    · intro v hv
      have hnr : v ∈ nonRoot T t0 := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases Finset.mem_union.mp hv with hi | hb
        · exact T.cycle_interior_nonRoot hT C t0 hout v (Finset.mem_filter.mp hi).2
        · obtain ⟨d, hd, rfl, hc⟩ := (hboundary v).mp hb
          obtain ⟨t, ht, _⟩ := chosenEdges_state_witness T hT col t0 r choice d (hC d hd)
          rw [ht]
          exact (Finset.mem_sdiff.mp (r.val t).property).2
      obtain ⟨t, ht⟩ := r.property.bijective.2 ⟨v, hnr⟩
      have htv : (r.val t).val = v := congrArg Subtype.val ht
      refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, htv⟩
      apply (state_cycle_matching_side_iff T hT col hcol t0 r choice C hC hout t).mpr
      rw [htv]
      rcases Finset.mem_union.mp hv with hi | hb
      · exact Or.inl (Finset.mem_filter.mp hi).2
      · exact Or.inr ((hboundary v).mp hb)
  have hdisjoint : Disjoint interior boundary := by
    apply Finset.disjoint_left.mpr
    intro v hi hb
    obtain ⟨d, hd, hv, _⟩ := (hboundary v).mp hb
    exact (Finset.mem_filter.mp hi).2.1 (List.mem_map.mpr ⟨d, hd, hv⟩)
  have hlength : boundary.card =
      (C.val.filter (fun d => normalizedColoring T col t0 (T.faceOf d) = true)).length := by
    have hn : ((C.val.filter (fun d =>
        normalizedColoring T col t0 (T.faceOf d) = true)).map T.vert).Nodup :=
      (C.property.2.of_map T.vert).filter _ |>.map_on
        (fun d hd e he hv => List.inj_on_of_nodup_map C.property.2
          (List.mem_filter.mp hd).1 (List.mem_filter.mp he).1 hv)
    rw [List.toFinset_card_of_nodup hn, List.length_map]
  rw [hblack, hmatch, Finset.card_union_of_disjoint hdisjoint, hlength]

end OaiPairedStatesHamiltonian
