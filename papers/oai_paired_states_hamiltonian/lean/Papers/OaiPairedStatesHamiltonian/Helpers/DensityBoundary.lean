module

public import Papers.OaiPairedStatesHamiltonian.Helpers.ShortFaces

/-! Triangular induced faces retain an original face. Opposite triangular
orbits exhaust a connected map on at most three vertices. -/

public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

-- @node: SphereMap.induce_isSimple
/-- If [a sphere map has no loops or parallel edges](hyp:hs), then
[its induced map on any vertex set also has no loops or parallel edges](goal). -/
lemma induce_isSimple (T : SphereMap) (hs : T.IsSimple) (U : Set T.Vertex) :
    (T.induce U).IsSimple := by
  constructor
  · intro d he
    exact hs.1 d.val ((congrArg Subtype.val he).trans (T.induce_head_val U d))
  · intro d e he
    apply T.inducedEdgeMap_injective U
    apply hs.2
    have h := congrArg (Sym2.map (Subtype.val : (T.induce U).Vertex → T.Vertex)) he
    change s(T.vert d.val, ((T.induce U).head d).val) =
      s(T.vert e.val, ((T.induce U).head e).val) at h
    simpa only [T.induce_head_val] using h

-- @node: SphereMap.induce_vertex_card
/-- [The number of vertices in the map induced by a finite vertex set equals
the size of that set](goal). -/
lemma induce_vertex_card (T : SphereMap) (U : Finset T.Vertex) :
    Fintype.card (T.induce (↑U : Set T.Vertex)).Vertex = U.card := by
  simp only [induce, inducedRotation, Fintype.card_subtype,
    Finset.mem_coe, Finset.filter_mem_eq_inter, Finset.univ_inter]

-- @node: SphereMap.perm_mem_iff_of_closed
/-- If [a permutation sends every member of a finite set back into that
set](hyp:h), then [an element's image belongs to the set exactly when the
element itself does](goal). -/
lemma perm_mem_iff_of_closed {α : Type} (p : Equiv.Perm α)
    (s : Finset α) (h : ∀ a ∈ s, p a ∈ s) (a : α) : p a ∈ s ↔ a ∈ s := by
  have he : s.image p = s := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.image_subset_iff.mpr h
    · rw [Finset.card_image_of_injective _ p.injective]
  have hp : p a ∈ s.image p ↔ a ∈ s := by
    simp only [Finset.mem_image, p.injective.eq_iff, exists_eq_right]
  rwa [he] at hp

-- @node: SphereMap.vertex_card_le_of_opposite_triangle_faces
/-- In [a connected sphere map](hyp:hc), suppose [a simple cycle has length
three](hyp:hlen), [its darts are exactly those of one face](hyp:hC),
[a second face has length three](hyp:hlen'), and [the reverse of every dart
of the first face belongs to the second face](hyp:hop). Then
[the entire map has at most three vertices](goal). -/
lemma vertex_card_le_of_opposite_triangle_faces (M : SphereMap) (hc : M.IsConnectedMap)
    (q q' : M.Face) (C : M.Cycle) (hlen : C.val.length = 3)
    (hC : ∀ d, d ∈ C.val ↔ d ∈ M.faceDarts q)
    (hlen' : M.faceLength q' = 3)
    (hop : ∀ d ∈ M.faceDarts q, M.edgeInv d ∈ M.faceDarts q') :
    Fintype.card M.Vertex ≤ 3 := by
  let A := M.faceDarts q
  let B := A.image M.edgeInv
  have hA : A.card = 3 := by
    have he : A = C.val.toFinset := by ext d; simp [A, ← hC]
    rw [he, List.toFinset_card_of_nodup]
    · exact hlen
    · exact List.Nodup.of_map M.vert C.property.2
  have hB : B = M.faceDarts q' := by
    apply Finset.eq_of_subset_of_card_le
    · intro d hd
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
      exact hop e he
    · rw [← M.faceLength_eq_card_faceDarts, hlen']
      change 3 ≤ (A.image M.edgeInv).card
      rw [Finset.card_image_of_injective _ M.edgeInv.injective, hA]
  let s := A ∪ B
  have hi (d : M.Dart) : M.edgeInv d ∈ s ↔ d ∈ s := by
    simp only [s, B, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (hd | ⟨e, he, hed⟩)
      · exact Or.inr ⟨M.edgeInv d, hd, M.edgeInv_involutive d⟩
      · exact Or.inl (M.edgeInv.injective hed ▸ he)
    · rintro (hd | ⟨e, he, rfl⟩)
      · exact Or.inr ⟨d, hd, rfl⟩
      · left
        rw [M.edgeInv_involutive]
        exact he
  have hf (d : M.Dart) (hd : d ∈ s) : M.facePerm d ∈ s := by
    change M.facePerm d ∈ A ∪ B
    change d ∈ A ∪ B at hd
    rw [hB] at hd ⊢
    simpa only [A, faceDarts, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, M.dual_rot_vertex] using hd
  have hr (d : M.Dart) (hd : d ∈ s) : M.rot d ∈ s := by
    have h := hf (M.edgeInv d) ((hi d).mpr hd)
    change M.rot (M.edgeInv (M.edgeInv d)) ∈ s at h
    rwa [M.edgeInv_involutive] at h
  have hne : s.Nonempty := by
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
    exact ⟨d, Finset.mem_union_left _ hd⟩
  have hv := M.vertex_card_le_of_closed_dart_set hc s hne
    (perm_mem_iff_of_closed M.rot s hr) hi
  have hsub : s.image M.vert ⊆ (C.val.map M.vert).toFinset := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hd with hd | hd
    · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨d, (hC d).mpr hd, rfl⟩)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
      exact List.mem_toFinset.mpr (M.cycle_head_mem_vertices C e ((hC e).mpr he))
  have hle := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup C.property.2, List.length_map, hlen] at hle
  exact hv.trans hle

-- @node: SphereMap.induced_triangle_face_retained
/-- For [a sphere triangulation](hyp:hT) with [no simple three-edge cycle having
vertices strictly on both sides](hyp:hsep), suppose [the map induced by a vertex set is
connected](hyp:hc), [the set has at least four vertices](hyp:hv), and
[a face of the induced map has length three](hyp:hq). Then [that face is the
induced face class of an original face all of whose vertices lie in the set](goal). -/
lemma induced_triangle_face_retained (T : SphereMap) (hT : IsSphereTriangulation T)
    (hsep : PairsNoSeparatingTriangle T) (U : Finset T.Vertex)
    (hc : (T.induce (↑U : Set T.Vertex)).IsConnectedMap) (hv : 4 ≤ U.card)
    (q : (T.induce (↑U : Set T.Vertex)).Face)
    (hq : (T.induce (↑U : Set T.Vertex)).faceLength q = 3) :
    ∃ f : T.Face, T.faceVertices f ⊆ U ∧ T.inducedFaceClass (↑U : Set T.Vertex) f = q := by
  let N := T.induce (↑U : Set T.Vertex)
  obtain ⟨C, hlen, hC⟩ := N.exists_face_triangle_cycle hc
    (T.induce_isSimple hT.props.2.1 _) q hq
  let D : T.Cycle := ⟨C.val.map Subtype.val, T.induce_cycle_isSimple _ C⟩
  have hD : D.val.length = 3 := by simpa [D] using hlen
  have hsub : (D.val.map T.vert).toFinset ⊆ U := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact e.property.1
  obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  have hq0 : N.faceOf d0 = q := (Finset.mem_filter.mp ((hC d0).mp hd0)).2
  have hval (d : N.Dart) (hd : d ∈ C.val) : d.val ∈ D.val :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rcases T.triangle_has_singleton_side hT hsep D hD with ⟨f, hf⟩ | ⟨f, hf⟩
  · have hret : T.faceVertices f ⊆ U := by
      rw [← T.cycle_vertices_eq_face_of_singleton_left hT D hD f hf]
      exact hsub
    refine ⟨f, hret, ?_⟩
    have hdf : T.faceOf d0.val = f := by
      have h := T.cycle_face_mem_leftRegion D d0.val (hval d0 hd0)
      simpa only [hf, Set.mem_singleton_iff] using h
    exact (congrArg (T.inducedFaceClass (↑U : Set T.Vertex)) hdf).symm.trans
      ((T.inducedBoundaryFace_dart _ d0).symm.trans hq0)
  · have hf' : T.leftRegion (reverseCycle T D) = {f} := by
      rwa [T.reverseCycle_leftRegion hT D, ← T.cycle_rightRegion_eq_compl D]
    have hrev : (reverseCycle T D).val.length = 3 := by
      simpa [reverseCycle, reverseDarts] using hD
    have hret : T.faceVertices f ⊆ U := by
      rw [← T.cycle_vertices_eq_face_of_singleton_left hT _ hrev f hf',
        T.reverseCycle_vertices D]
      exact hsub
    have hlenf : N.faceLength (T.inducedFaceClass (↑U : Set T.Vertex) f) = 3 := by
      rw [← T.regionSides_card_eq_induced_faceLength]
      exact T.regionSides_card_of_retained_face hT U f hret
    have hop (d : N.Dart) (hd : d ∈ N.faceDarts q) :
        N.edgeInv d ∈ N.faceDarts (T.inducedFaceClass (↑U : Set T.Vertex) f) := by
      have hdi : T.edgeInv d.val ∈ (reverseCycle T D).val := by
        apply (T.mem_reverseCycle_iff D _).mpr
        rw [T.edgeInv_involutive]
        exact hval d ((hC d).mpr hd)
      have hdf : T.faceOf (T.edgeInv d.val) = f := by
        have h := T.cycle_face_mem_leftRegion _ _ hdi
        simpa only [hf', Set.mem_singleton_iff] using h
      have hi : (N.edgeInv d).val = T.edgeInv d.val :=
        Classical.choose_spec (T.exists_inducedInv _) d
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [T.inducedBoundaryFace_dart, hi, hdf]
    have hle := N.vertex_card_le_of_opposite_triangle_faces hc q _ C hlen hC hlenf hop
    rw [T.induce_vertex_card U] at hle
    omega

end SphereMap
end OaiPairedStatesHamiltonian
