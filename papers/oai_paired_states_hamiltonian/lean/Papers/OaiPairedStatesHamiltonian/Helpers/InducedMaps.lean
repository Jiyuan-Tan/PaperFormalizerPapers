module

public import Papers.OaiPairedStatesHamiltonian.Helpers.InducedPlacement

/-! Induced sphere maps and retained-edge and cycle maps. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace SphereMap
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
open Classical
attribute [local instance] propDecidable
variable (M : SphereMap) (U : Set M.Vertex)

-- @node: def:induced-subgraph
/-- For [a sphere map](hyp:M) and [a chosen set of its vertices](hyp:U), the
[induced sphere map](goal) retains precisely the edges with both endpoints in that set,
with the resulting rotation system, merged faces, and face placement. -/
noncomputable def induce : SphereMap where
  toRotationSystem := M.inducedRotation U
  genusZero := M.induced_genus U
  Face := M.InducedFace U
  boundaryFace := M.inducedBoundaryFace U
  placement_connected := M.induced_placement_connected U
  placement_card := M.induced_placement_card U

-- @node: SphereMap.inducedBoundaryFace_dart
/-- [The face incident to a retained directed edge in the induced sphere map is the
merged-face class of its original incident face](goal). -/
lemma inducedBoundaryFace_dart (d : M.KeptDart U) :
    (M.induce U).faceOf d = M.inducedFaceClass U (M.faceOf d.val) := by
  exact (Classical.choose_spec (M.exists_inducedBoundaryFace U)).1 d
-- @node: SphereMap.induce_toSimpleGraph
/-- [The underlying simple graph of the induced sphere map equals the subgraph of the
original simple graph induced by the chosen vertices](goal). -/
lemma induce_toSimpleGraph :
    (M.induce U).toSimpleGraph = M.toSimpleGraph.induce U := by
  ext v w
  change U at v w
  constructor
  · rintro ⟨hne, d, hd, he⟩
    change M.KeptDart U at d
    refine ⟨fun h => hne (Subtype.ext h), d.val, congrArg Subtype.val hd, ?_⟩
    have hi := Classical.choose_spec (M.exists_inducedInv U) d
    have hv := congrArg Subtype.val he
    change M.vert ((M.inducedInv U d).val) = w.val at hv
    exact (congrArg M.vert hi).symm.trans hv
  · rintro ⟨hne, d, hd, he⟩
    change M.vert d = v.val at hd
    change M.head d = w.val at he
    let e : M.KeptDart U := ⟨d, hd.symm ▸ v.property, he.symm ▸ w.property⟩
    refine ⟨fun h => hne (congrArg Subtype.val h), e, Subtype.ext hd, ?_⟩
    apply Subtype.ext
    change M.vert ((M.inducedInv U e).val) = w.val
    exact (congrArg M.vert (Classical.choose_spec (M.exists_inducedInv U) e)).trans he

-- @node: SphereMap.inducedEdgeMap
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[edge inclusion](goal) sends each edge of the induced sphere map to its original edge. -/
noncomputable def inducedEdgeMap : (M.induce U).Edge → M.Edge :=
  Quotient.map Subtype.val (fun {d e} h => (M.inducedInv_sameCycle_iff U d e).mp h)

-- @node: SphereMap.inducedEdgeMap_injective
/-- [Distinct edges of the induced sphere map map to distinct original edges](goal). -/
lemma inducedEdgeMap_injective : Function.Injective (M.inducedEdgeMap U) := by
  intro e f
  induction e using Quotient.inductionOn with
  | h d =>
    induction f using Quotient.inductionOn with
    | h e =>
      intro h
      exact Quotient.sound ((M.inducedInv_sameCycle_iff U d e).mpr (Quotient.exact h))

-- @node: SphereMap.induce_head_val
/-- [The head of a retained directed edge in the induced sphere map, viewed as an original
vertex, equals its original head](goal). -/
lemma induce_head_val (d : M.KeptDart U) :
    ((M.induce U).head d).val = M.head d.val := by
  exact congrArg M.vert (Classical.choose_spec (M.exists_inducedInv U) d)

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.induce_cycle_isSimple
/-- [A simple cycle of the induced sphere map remains a simple cycle of the original map
when its directed edges are viewed as original directed edges](goal). -/
lemma induce_cycle_isSimple (C : (M.induce U).Cycle) :
    M.IsSimpleCycle (C.val.map Subtype.val) := by
  let ds : List (M.KeptDart U) := C.val
  have hC : (M.induce U).IsSimpleCycle ds := C.property
  change M.IsSimpleCycle (ds.map Subtype.val)
  unfold IsSimpleCycle IsClosedTrail
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro h
    exact hC.1.1 (List.map_eq_nil_iff.mp h)
  · have h := hC.1.2.1.map (M.inducedEdgeMap_injective U)
    simpa only [List.map_map, induce, inducedRotation, inducedVert,
      SphereMap.edgeOf, RotationSystem.edgeOf, inducedEdgeMap, orbitOf,
      Quotient.map_mk, Function.comp_def] using h
  · intro i
    have h := congrArg Subtype.val (hC.1.2.2
      ⟨i.val, by simpa only [List.length_map] using i.isLt⟩)
    simp only [M.induce_head_val U] at h
    simpa only [List.length_map, List.get_eq_getElem, List.getElem_map,
      induce, inducedRotation, inducedVert] using h
  · have h := hC.2.map (Subtype.val_injective (p := fun v => v ∈ U))
    simpa only [List.map_map, induce, inducedRotation, inducedVert,
      SphereMap.edgeOf, RotationSystem.edgeOf, inducedEdgeMap, orbitOf,
      Quotient.map_mk, Function.comp_def] using h

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.induce_cycle_of_mem
/-- If [both endpoints of every directed edge of a simple cycle belong to the chosen
vertex set](hyp:hU), then [there is a simple cycle in the induced sphere map whose
ordered list of original directed edges is exactly the given cycle](goal). -/
lemma induce_cycle_of_mem (C : M.Cycle)
    (hU : ∀ d ∈ C.val, M.vert d ∈ U ∧ M.head d ∈ U) :
    ∃ D : (M.induce U).Cycle, D.val.map Subtype.val = C.val := by
  let lift : {d // d ∈ C.val} → M.KeptDart U := fun d => ⟨d.val, hU d.val d.property⟩
  let ds : List (M.KeptDart U) := C.val.attach.map lift
  have hval : ds.map Subtype.val = C.val := by
    simp [ds, lift, List.map_map]
  have hlen : ds.length = C.val.length := by
    simpa only [List.length_map] using congrArg List.length hval
  have hget (i : Fin ds.length) :
      (ds.get i).val = C.val.get ⟨i.val, hlen ▸ i.isLt⟩ := by
    have h := List.getElem_of_eq hval (by simpa only [List.length_map] using i.isLt)
    simpa only [List.get_eq_getElem, List.getElem_map] using h
  have hsimple : (M.induce U).IsSimpleCycle ds := by
    unfold IsSimpleCycle IsClosedTrail
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro hz
      exact C.property.1.1 (by simpa only [hz, List.map_nil] using hval.symm)
    · apply List.Nodup.of_map (M.inducedEdgeMap U)
      have he : (ds.map (M.induce U).edgeOf).map (M.inducedEdgeMap U) =
          C.val.map M.edgeOf := by
        rw [← hval]
        simp only [List.map_map, induce, inducedRotation, SphereMap.edgeOf,
          RotationSystem.edgeOf, RotationSystem.Edge, inducedEdgeMap, orbitOf, Quotient.map_mk,
          Function.comp_def]
      rw [he]
      exact C.property.1.2.1
    · intro i
      apply Subtype.ext
      rw [M.induce_head_val U, hget]
      have hc := C.property.1.2.2 ⟨i.val, hlen ▸ i.isLt⟩
      change M.head (C.val.get _) = M.vert ((ds.get _).val)
      rw [hget]
      simpa only [hlen] using hc
    · apply List.Nodup.of_map (Subtype.val : U → M.Vertex)
      have hv : (ds.map (M.induce U).vert).map Subtype.val = C.val.map M.vert := by
        rw [← hval]
        simp only [List.map_map]
        rfl
      rw [hv]
      exact C.property.2
  exact ⟨⟨ds, hsimple⟩, hval⟩


end SphereMap


end OaiPairedStatesHamiltonian
