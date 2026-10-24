module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleExterior

/-! Face-side incidence at vertices away from a simple cycle. -/

public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (M : SphereMap)

-- @node: SphereMap.cycle_head_mem_vertices
/-- If [a directed edge belongs to the cycle](hyp:hd), then [its head is one of
the cycle's vertices](goal). -/
lemma cycle_head_mem_vertices (C : M.Cycle) (d : M.Dart) (hd : d ∈ C.val) :
    M.head d ∈ C.val.map M.vert := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  rw [C.property.1.2.2 i]
  exact List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩

-- @node: SphereMap.cycle_edge_not_mem_of_nonboundary_tail
/-- If [the tail of a directed edge is not a cycle vertex](hyp:hd), then [its
underlying undirected edge does not occur in the cycle](goal). -/
lemma cycle_edge_not_mem_of_nonboundary_tail (C : M.Cycle) (d : M.Dart)
    (hd : M.vert d ∉ C.val.map M.vert) : M.edgeOf d ∉ C.val.map M.edgeOf := by
  intro he
  obtain ⟨e, he, heq⟩ := List.mem_map.mp he
  rcases (M.edgeOf_eq_iff e d).mp heq with h | h
  · exact hd (h ▸ List.mem_map.mpr ⟨e, he, rfl⟩)
  · exact hd (h ▸ M.cycle_head_mem_vertices C e he)

-- @node: SphereMap.cycle_nonboundary_rot_side
/-- If [the map is connected](hyp:hM) and [a directed edge's tail is not on the
cycle](hyp:hd), then [the face of the next directed edge in the rotation around
that tail lies in the cycle's left region exactly when the original face does](goal). -/
lemma cycle_nonboundary_rot_side (hM : M.IsConnectedMap) (C : M.Cycle) (d : M.Dart)
    (hd : M.vert d ∉ C.val.map M.vert) :
    M.faceOf (M.rot d) ∈ M.leftRegion C ↔ M.faceOf d ∈ M.leftRegion C := by
  have hf : M.faceOf (M.rot d) = M.faceOf (M.edgeInv d) := by
    have hf := M.dual_rot_vertex (M.edgeInv d)
    change M.faceOf (M.rot (M.edgeInv (M.edgeInv d))) = _ at hf
    rw [M.edgeInv_involutive] at hf
    exact hf
  rw [hf]
  exact (M.leftRegion_across_noncycle hM C d
    (M.cycle_edge_not_mem_of_nonboundary_tail C d hd)).symm

-- @node: SphereMap.cycle_nonboundary_dart_side
/-- If [the map is connected](hyp:hM), [two directed edges have the same
tail](hyp:hv), and [that tail is not a cycle vertex](hyp:hd), then [their faces
either both belong to the cycle's left region or both lie outside it](goal). -/
lemma cycle_nonboundary_dart_side (hM : M.IsConnectedMap) (C : M.Cycle)
    (d e : M.Dart) (hv : M.vert d = M.vert e)
    (hd : M.vert d ∉ C.val.map M.vert) :
    M.faceOf d ∈ M.leftRegion C ↔ M.faceOf e ∈ M.leftRegion C := by
  obtain ⟨n, rfl⟩ := ((M.rot_fibre (M.vert d)).2 rfl hv.symm).exists_nat_pow_eq
  have hpow (n : ℕ) : M.vert ((M.rot ^ n) d) = M.vert d ∧
      (M.faceOf ((M.rot ^ n) d) ∈ M.leftRegion C ↔ M.faceOf d ∈ M.leftRegion C) := by
    induction n with
    | zero => exact ⟨rfl, Iff.rfl⟩
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨(M.rot_vertex _).trans ih.1,
        (M.cycle_nonboundary_rot_side hM C _ (ih.1 ▸ hd)).trans ih.2⟩
  exact (hpow n).2.symm

-- @node: SphereMap.cycle_nonboundary_face_side
/-- In [a triangulation of the sphere](hyp:hM), suppose [a vertex is not on the
cycle](hyp:hv), [the vertex belongs to the first face](hyp:hf), and [it also
belongs to the second face](hyp:hg).
Then [the two faces either both belong to the cycle's left region or both lie
outside it](goal). -/
lemma cycle_nonboundary_face_side (hM : IsSphereTriangulation M) (C : M.Cycle)
    (v : M.Vertex) (hv : v ∉ C.val.map M.vert) (f g : M.Face)
    (hf : v ∈ M.faceVertices f) (hg : v ∈ M.faceVertices g) :
    f ∈ M.leftRegion C ↔ g ∈ M.leftRegion C := by
  rw [triangulation_faceVertices_eq_image M hM] at hf hg
  obtain ⟨d, hd, hdv⟩ := Finset.mem_image.mp hf
  obtain ⟨e, he, hev⟩ := Finset.mem_image.mp hg
  have hdf : M.faceOf d = f := (Finset.mem_filter.mp hd).2
  have hef : M.faceOf e = g := (Finset.mem_filter.mp he).2
  rw [← hdf, ← hef]
  exact M.cycle_nonboundary_dart_side hM.props.1 C d e (hdv.trans hev.symm) (hdv ▸ hv)

end SphereMap
end OaiPairedStatesHamiltonian
