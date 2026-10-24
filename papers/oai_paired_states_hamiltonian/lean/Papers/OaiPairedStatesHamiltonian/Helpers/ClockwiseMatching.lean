module

public import Papers.OaiPairedStatesHamiltonian.Helpers.DiskMatching

/-! State matching counts on either side, with the outer face and roots removed. -/

public section
namespace OaiPairedStatesHamiltonian
open Classical
attribute [local instance] propDecidable
set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false

-- @node: cycle_chosen_black_face_side_of_exterior
/-- If [the map is a sphere triangulation](hyp:hT), [its coloring is a partition coloring](hyp:hcol),
[the outer face is outside the cycle's left region](hyp:hout), [the dart lies on the cycle](hyp:hd),
and [the chosen black non-outer face lies on one side of that dart](hyp:hf), then
[that black face is in the left region exactly when the face on the dart's left is black under the normalized coloring](goal). -/
lemma cycle_chosen_black_face_side_of_exterior (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C) (d : T.Dart) (hd : d ∈ C.val)
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
      exact (T.cycle_boundary_opposite_outside hT.props.1 C outer hout d hd (hf.symm ▸ hin)).elim
    · intro he
      exact (hn he).elim

-- @node: state_cycle_matching_side_iff_of_exterior
/-- If [the map is a sphere triangulation](hyp:hT), [its coloring is a partition coloring](hyp:hcol),
[every cycle dart is an edge selected by the state and its edge choice](hyp:hC), and
[the outer face lies outside the cycle's left region](hyp:hout), then [a black non-outer
face lies in that region exactly when its state-matched vertex is strictly on that side,
or is the vertex of a cycle dart whose left face is black under the normalized coloring](goal). -/
lemma state_cycle_matching_side_iff_of_exterior (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r : State T col t0) (choice : EdgeChoice T col t0 r) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C) (t : blackNonOuter T col t0) :
    t.val ∈ T.leftRegion C ↔ T.strictlyOnSide (T.leftRegion C) C (r.val t).val ∨
      ∃ d ∈ C.val, T.vert d = (r.val t).val ∧
        normalizedColoring T col t0 (T.faceOf d) = true := by
  have boundary (d : T.Dart) (hd : d ∈ C.val) (hv : T.vert d = (r.val t).val) :
      t.val ∈ T.leftRegion C ↔ normalizedColoring T col t0 (T.faceOf d) = true := by
    obtain ⟨u, hu, hface⟩ := chosenEdges_state_witness T hT col t0 r choice d (hC d hd)
    have hut : u = t := r.property.bijective.1 (Subtype.ext (hu.symm.trans hv))
    subst u
    exact cycle_chosen_black_face_side_of_exterior T hT col hcol t0 C outer hout d hd t hface
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

-- @node: state_cycle_matching_count_of_exterior
/-- If [the map is a sphere triangulation](hyp:hT), [its coloring is a partition coloring](hyp:hcol),
[every cycle dart is selected by the state and its edge choice](hyp:hC), and
[the outer face is outside the cycle's left region](hyp:hout), then [the number of
normalized black faces in the left region, excluding the distinguished face, equals
the number of strictly left-side vertices excluding roots plus the number of cycle
darts with a normalized black face on their left](goal). -/
lemma state_cycle_matching_count_of_exterior (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r : State T col t0) (choice : EdgeChoice T col t0 r) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, d ∈ ChosenEdges T col t0 hT r choice)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C) :
    ((Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧
      normalizedColoring T col t0 f = true)).erase t0).card =
      ((Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)) \ roots T t0).card +
        (C.val.filter (fun d => normalizedColoring T col t0 (T.faceOf d) = true)).length := by
  let interior := (Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)) \ roots T t0
  let boundary := ((C.val.filter (fun d =>
    normalizedColoring T col t0 (T.faceOf d) = true)).map T.vert).toFinset
  let faces := Finset.univ.filter (fun t : blackNonOuter T col t0 => t.val ∈ T.leftRegion C)
  have hblack : ((Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧
      normalizedColoring T col t0 f = true)).erase t0).card = faces.card := by
    symm
    apply Finset.card_bij (fun t _ => t.val)
    · intro t ht
      exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp t.property).2.2,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2,
          (Finset.mem_filter.mp t.property).2.1⟩⟩
    · intro t ht u hu heq
      exact Subtype.ext heq
    · intro f hf
      obtain ⟨hne, hf⟩ := Finset.mem_erase.mp hf
      obtain ⟨_, hin, hc⟩ := Finset.mem_filter.mp hf
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
      exact ((state_cycle_matching_side_iff_of_exterior T hT col hcol t0 r choice C hC outer hout t).mp
        (Finset.mem_filter.mp ht).2).imp
        (fun hi => Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
          (Finset.mem_sdiff.mp (r.val t).property).2⟩) id
    · intro t ht u hu heq
      exact r.property.bijective.1 (Subtype.ext heq)
    · intro v hv
      have hnr : v ∈ nonRoot T t0 := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases Finset.mem_union.mp hv with hi | hb
        · exact (Finset.mem_sdiff.mp hi).2
        · obtain ⟨d, hd, rfl, hc⟩ := (hboundary v).mp hb
          obtain ⟨t, ht, _⟩ := chosenEdges_state_witness T hT col t0 r choice d (hC d hd)
          rw [ht]
          exact (Finset.mem_sdiff.mp (r.val t).property).2
      obtain ⟨t, ht⟩ := r.property.bijective.2 ⟨v, hnr⟩
      have htv : (r.val t).val = v := congrArg Subtype.val ht
      refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, htv⟩
      apply (state_cycle_matching_side_iff_of_exterior T hT col hcol t0 r choice C hC outer hout t).mpr
      rw [htv]
      rcases Finset.mem_union.mp hv with hi | hb
      · exact Or.inl (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2
      · exact Or.inr ((hboundary v).mp hb)
  have hdisjoint : Disjoint interior boundary := by
    apply Finset.disjoint_left.mpr
    intro v hi hb
    obtain ⟨d, hd, hv, _⟩ := (hboundary v).mp hb
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2.1 (List.mem_map.mpr ⟨d, hd, hv⟩)
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
