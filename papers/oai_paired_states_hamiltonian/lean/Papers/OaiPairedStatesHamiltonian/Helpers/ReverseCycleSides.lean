module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleSeparation
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleReversal

/-! Reversing a cycle exchanges its two face regions. -/

public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

variable (T : SphereMap)

-- @node: SphereMap.mem_reverseCycle_iff
/-- For a cycle and a directed edge in a sphere map, [the directed edge belongs to the reversed
cycle exactly when its reversal belongs to the original cycle](goal). -/
lemma mem_reverseCycle_iff (C : T.Cycle) (d : T.Dart) :
    d ∈ (reverseCycle T C).val ↔ T.edgeInv d ∈ C.val := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    rw [T.edgeInv_involutive]
    exact List.mem_reverse.mp he
  · intro h
    exact List.mem_map.mpr ⟨T.edgeInv d, List.mem_reverse.mpr h, T.edgeInv_involutive d⟩

-- @node: SphereMap.reverseCycle_edge_mem_iff
/-- [An edge belongs to the reversed cycle exactly when it belongs to the original cycle](goal). -/
lemma reverseCycle_edge_mem_iff (C : T.Cycle) (d : T.Dart) :
    T.edgeOf d ∈ (reverseCycle T C).val.map T.edgeOf ↔ T.edgeOf d ∈ C.val.map T.edgeOf := by
  have hedge (e : T.Dart) : T.edgeOf (T.edgeInv e) = T.edgeOf e :=
    ((T.edgeOf_eq_iff e (T.edgeInv e)).mpr (Or.inr rfl)).symm
  constructor
  · rintro h
    obtain ⟨e, he, hed⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨T.edgeInv e, (T.mem_reverseCycle_iff C e).mp he,
      (hedge e).trans hed⟩
  · rintro h
    obtain ⟨e, he, hed⟩ := List.mem_map.mp h
    refine List.mem_map.mpr ⟨T.edgeInv e, (T.mem_reverseCycle_iff C _).mpr ?_,
      (hedge e).trans hed⟩
    rwa [T.edgeInv_involutive]

-- @node: SphereMap.reverseCycle_vertices
/-- [Reversing a cycle preserves its set of vertices](goal). -/
lemma reverseCycle_vertices (C : T.Cycle) :
    ((reverseCycle T C).val.map T.vert).toFinset = (C.val.map T.vert).toFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have he := (T.mem_reverseCycle_iff C d).mp hd
    have hh := T.cycle_head_mem_vertices C (T.edgeInv d) he
    change T.vert (T.edgeInv (T.edgeInv d)) ∈ C.val.map T.vert at hh
    rw [T.edgeInv_involutive] at hh
    exact List.mem_toFinset.mpr hh
  · rw [List.toFinset_card_of_nodup (reverseCycle T C).property.2,
      List.toFinset_card_of_nodup C.property.2]
    simp [reverseCycle, reverseDarts]

-- @node: SphereMap.reverseCycle_leftRegion_disjoint
/-- If [the sphere map is a sphere triangulation](hyp:hT), then [the face regions to the left
of a cycle and to the left of its reversal are disjoint](goal). -/
lemma reverseCycle_leftRegion_disjoint (hT : IsSphereTriangulation T) (C : T.Cycle) :
    Disjoint (T.leftRegion C) (T.leftRegion (reverseCycle T C)) := by
  obtain ⟨outer, hout⟩ := T.exists_face_outside_cycle_leftRegion hT.props.1 C
  apply Set.disjoint_left.mpr
  intro f hf hg
  obtain ⟨b, ⟨d, hd, hp⟩, hbf⟩ := hg
  have hstart : T.faceOf d ∉ T.leftRegion C := by
    have h := T.cycle_boundary_opposite_outside hT.props.1 C outer hout (T.edgeInv d)
      ((T.mem_reverseCycle_iff C d).mp hd)
    rwa [T.edgeInv_involutive] at h
  have hpath : T.boundaryFace b ∉ T.leftRegion C := by
    have step {a b : T.LocalBoundary}
        (p : T.localBoundariesJoinedAvoiding (reverseCycle T C).val a b) :
        T.boundaryFace a ∉ T.leftRegion C → T.boundaryFace b ∉ T.leftRegion C := by
      induction p with
      | refl => exact id
      | tail p h ih =>
        obtain ⟨e, he, rfl, rfl⟩ := h
        intro ha
        exact fun hb => ih ha ((T.leftRegion_across_noncycle hT.props.1 C e
          (fun hc => he ((T.reverseCycle_edge_mem_iff C e).mpr hc))).mpr hb)
    exact step hp hstart
  exact hpath ((T.faceBehind_connected hT.props.1 _ b f hbf).symm ▸ hf)

-- @node: SphereMap.reverseCycle_leftRegion_cover
/-- If [the sphere map is a sphere triangulation](hyp:hT), then [the face regions to the left
of a cycle and to the left of its reversal together contain every face](goal). -/
lemma reverseCycle_leftRegion_cover (hT : IsSphereTriangulation T) (C : T.Cycle) :
    T.leftRegion C ∪ T.leftRegion (reverseCycle T C) = Set.univ := by
  obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  have step {f g : T.Face} (hfg : (T.dualRotation hT.props.1).toSimpleGraph.Adj f g)
      (hf : f ∈ T.leftRegion C ∪ T.leftRegion (reverseCycle T C)) :
      g ∈ T.leftRegion C ∪ T.leftRegion (reverseCycle T C) := by
    obtain ⟨_, e, he, hi⟩ := hfg
    change T.faceOf e = f at he
    change T.faceOf (T.edgeInv e) = g at hi
    rw [← he] at hf
    rw [← hi]
    by_cases hb : T.edgeOf e ∈ C.val.map T.edgeOf
    · obtain ⟨a, ha, hae⟩ := List.mem_map.mp hb
      rcases (T.edgeOf_eq_iff a e).mp hae with h | h
      · right
        apply T.cycle_face_mem_leftRegion
        apply (T.mem_reverseCycle_iff C _).mpr
        rw [T.edgeInv_involutive]
        exact h.symm ▸ ha
      · left
        rw [h, T.edgeInv_involutive]
        exact T.cycle_face_mem_leftRegion C a ha
    · rcases hf with hf | hf
      · exact Or.inl ((T.leftRegion_across_noncycle hT.props.1 C e hb).mp hf)
      · exact Or.inr ((T.leftRegion_across_noncycle hT.props.1 (reverseCycle T C) e
          (fun h => hb ((T.reverseCycle_edge_mem_iff C e).mp h))).mp hf)
  have all_faces (f : T.Face) : f ∈ T.leftRegion C ∪ T.leftRegion (reverseCycle T C) := by
    have hc : (T.dualRotation hT.props.1).toSimpleGraph.connectedComponentMk (T.faceOf d0) =
        (T.dualRotation hT.props.1).toSimpleGraph.connectedComponentMk f :=
      (T.dual_component_subsingleton hT.props.1).elim _ _
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hc
    have walk {f g : T.Face} (p : (T.dualRotation hT.props.1).toSimpleGraph.Walk f g) :
        f ∈ T.leftRegion C ∪ T.leftRegion (reverseCycle T C) →
          g ∈ T.leftRegion C ∪ T.leftRegion (reverseCycle T C) := by
      induction p with
      | nil => exact id
      | cons h p ih => exact fun hf => ih (step h hf)
    exact walk p (Or.inl (T.cycle_face_mem_leftRegion C d0 hd0))
  exact Set.eq_univ_of_forall all_faces

-- @node: SphereMap.reverseCycle_leftRegion
/-- If [the sphere map is a sphere triangulation](hyp:hT), then [the face region to the left
of a reversed cycle is the complement of the original cycle's left region](goal). -/
lemma reverseCycle_leftRegion (hT : IsSphereTriangulation T) (C : T.Cycle) :
    T.leftRegion (reverseCycle T C) = (T.leftRegion C)ᶜ := by
  ext f
  constructor
  · intro hf hg
    exact Set.disjoint_left.mp (T.reverseCycle_leftRegion_disjoint hT C) hg hf
  · intro hf
    have h : f ∈ T.leftRegion C ∪ T.leftRegion (reverseCycle T C) :=
      (T.reverseCycle_leftRegion_cover hT C).symm ▸ Set.mem_univ f
    exact h.resolve_left hf

-- @node: SphereMap.cycle_rightRegion_eq_compl
/-- [The face region to the right of a cycle is the complement of its left region](goal). -/
lemma cycle_rightRegion_eq_compl (C : T.Cycle) :
    T.rightRegion C = (T.leftRegion C)ᶜ := by
  ext f
  constructor
  · intro hr hl
    exact Set.disjoint_left.mp (T.cycle_sides_partition C).1 hl hr
  · intro hn
    have h : f ∈ T.leftRegion C ∪ T.rightRegion C :=
      (T.cycle_sides_partition C).2.symm ▸ Set.mem_univ f
    exact h.resolve_left hn

-- @node: SphereMap.reverseCycle_rightRegion
/-- If [the sphere map is a sphere triangulation](hyp:hT), then [the face region to the right
of a reversed cycle equals the original cycle's left region](goal). -/
lemma reverseCycle_rightRegion (hT : IsSphereTriangulation T) (C : T.Cycle) :
    T.rightRegion (reverseCycle T C) = T.leftRegion C := by
  rw [T.cycle_rightRegion_eq_compl, T.reverseCycle_leftRegion hT C, compl_compl]

-- @node: SphereMap.reverseCycle_strictlyOnSide
/-- For any set of faces and any vertex, [the vertex lies off the cycle and is incident to a
face in that set after reversing the cycle exactly when it does before reversal](goal). -/
lemma reverseCycle_strictlyOnSide (C : T.Cycle) (R : Set T.Face) (v : T.Vertex) :
    T.strictlyOnSide R (reverseCycle T C) v ↔ T.strictlyOnSide R C v := by
  have hvertices : v ∈ (reverseCycle T C).val.map T.vert ↔ v ∈ C.val.map T.vert := by
    rw [← List.mem_toFinset, T.reverseCycle_vertices, List.mem_toFinset]
  exact and_congr (not_congr hvertices) Iff.rfl

-- @node: SphereMap.reverseCycle_isSeparatingTriangle
/-- If [the sphere map is a sphere triangulation](hyp:hT) and [a cycle is a triangle with a
vertex strictly on each side](hyp:hC), then [its reversal is also a separating triangle](goal). -/
lemma reverseCycle_isSeparatingTriangle (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hC : IsSeparatingTriangle T C) :
    IsSeparatingTriangle T (reverseCycle T C) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [reverseCycle, reverseDarts, List.length_map, List.length_reverse] using hC.props.1
  · obtain ⟨v, hv⟩ := hC.props.2.2
    refine ⟨v, (T.reverseCycle_strictlyOnSide C _ v).mpr ?_⟩
    rw [T.reverseCycle_leftRegion hT C, ← T.cycle_rightRegion_eq_compl]
    exact hv
  · obtain ⟨v, hv⟩ := hC.props.2.1
    refine ⟨v, (T.reverseCycle_strictlyOnSide C _ v).mpr ?_⟩
    rw [T.reverseCycle_rightRegion hT C]
    exact hv

-- @node: SphereMap.exists_separatingTriangle_with_face_left
/-- If [the sphere map is a sphere triangulation](hyp:hT) and [it has a separating
triangle](hyp:hsep), then [there is a separating triangle oriented so that the prescribed
face lies in its left region](goal). -/
lemma exists_separatingTriangle_with_face_left (hT : IsSphereTriangulation T)
    (hsep : ¬ TreesNoSeparatingTriangle T) (f : T.Face) :
    ∃ C : T.Cycle, IsSeparatingTriangle T C ∧ f ∈ T.leftRegion C := by
  obtain ⟨C, hC⟩ : ∃ C : T.Cycle, IsSeparatingTriangle T C := by
    simpa only [TreesNoSeparatingTriangle, not_forall, not_not] using hsep
  by_cases hf : f ∈ T.leftRegion C
  · exact ⟨C, hC, hf⟩
  · exact ⟨reverseCycle T C, T.reverseCycle_isSeparatingTriangle hT C hC,
      (T.reverseCycle_leftRegion hT C).symm ▸ hf⟩

end SphereMap
end OaiPairedStatesHamiltonian
