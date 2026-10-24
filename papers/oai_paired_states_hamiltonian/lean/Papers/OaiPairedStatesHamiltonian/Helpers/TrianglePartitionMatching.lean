module

public import Papers.OaiPairedStatesHamiltonian.Helpers.TriangleCapIncidence
public import Papers.OaiPairedStatesHamiltonian.Helpers.TreeGluing
public import Papers.OaiPairedStatesHamiltonian.Helpers.PartitionAssembly

/-! Matching the two tree labels on a triangular cap. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

-- @node: three_vertices_same_label_pair
/-- If [a finite set has exactly three vertices](hyp:hS), then [two distinct vertices in it
either both belong to the designated set or both lie outside it](goal). -/
lemma three_vertices_same_label_pair {V : Type} (A : Set V) (S : Finset V)
    (hS : S.card = 3) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ (u ∈ A ↔ v ∈ A) := by
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp hS
  by_cases hu : u ∈ A
  · by_cases hv : v ∈ A
    · exact ⟨u, by simp, v, by simp, huv, iff_of_true hu hv⟩
    · by_cases hw : w ∈ A
      · exact ⟨u, by simp, w, by simp, huw, iff_of_true hu hw⟩
      · exact ⟨v, by simp, w, by simp, hvw, iff_of_false hv hw⟩
  · by_cases hv : v ∈ A
    · by_cases hw : w ∈ A
      · exact ⟨v, by simp, w, by simp, hvw, iff_of_true hv hw⟩
      · exact ⟨u, by simp, w, by simp, huw, iff_of_false hu hw⟩
    · exact ⟨u, by simp, v, by simp, huv, iff_of_false hu hv⟩

namespace SphereMap

-- @node: SphereMap.triangulation_face_isClique
/-- If [the sphere map is a triangulation](hyp:hT), then [every two distinct vertices of
the given face are adjacent in its underlying simple graph](goal). -/
lemma triangulation_face_isClique (T : SphereMap) (hT : IsSphereTriangulation T)
    (f : T.Face) : T.toSimpleGraph.IsClique (↑(T.faceVertices f) : Set T.Vertex) := by
  intro u hu v hv huv
  obtain ⟨d, hd⟩ := exists_faceDart T hT f u v hu hv huv
  exact ⟨huv, d, hd.1, hd.2.1⟩

-- @node: SphereMap.triangulation_face_not_monochromatic
/-- If [the sphere map is a triangulation](hyp:hT), [the graph induced by the designated
vertex set is acyclic](hyp:hA), and [the graph induced by its complement is acyclic](hyp:hAc),
then [the given face has vertices both inside and outside that set](goal). -/
lemma triangulation_face_not_monochromatic (T : SphereMap) (hT : IsSphereTriangulation T)
    (f : T.Face) (A : Set T.Vertex)
    (hA : (T.toSimpleGraph.induce A).IsAcyclic)
    (hAc : (T.toSimpleGraph.induce Aᶜ).IsAcyclic) :
    ¬ (↑(T.faceVertices f) : Set T.Vertex) ⊆ A ∧
      ¬ (↑(T.faceVertices f) : Set T.Vertex) ⊆ Aᶜ := by
  obtain ⟨u, v, w, huv, huw, hvw, hface⟩ :=
    Finset.card_eq_three.mp (hT.props.2.2.2 f).2
  have hu : u ∈ T.faceVertices f := by simp [hface]
  have hv : v ∈ T.faceVertices f := by simp [hface]
  have hw : w ∈ T.faceVertices f := by simp [hface]
  have hc := T.triangulation_face_isClique hT f
  have hab := hc hu hv huv
  have hac := hc hu hw huw
  have hbc := hc hv hw hvw
  have hs : (↑(T.faceVertices f) : Set T.Vertex) = {u, v, w} := by
    simp [hface]
  rw [hs]
  exact ⟨triangle_not_subset_tree_label T.toSimpleGraph A hA u v w hab hac hbc,
    triangle_not_subset_tree_label T.toSimpleGraph Aᶜ hAc u v w hab hac hbc⟩

-- @node: SphereMap.exists_face_label_prescription
/-- If [the sphere map is a triangulation](hyp:hT) and [the given face has vertices both
inside and outside the designated set](hyp:hmono), then [there are an edge on that face
and a Boolean choice such that membership in the set, on the face, is exactly membership
among the edge's endpoints when the choice is true and nonmembership when it is false](goal). -/
lemma exists_face_label_prescription (T : SphereMap) (hT : IsSphereTriangulation T)
    (f : T.Face) (A : Set T.Vertex)
    (hmono : ¬ (↑(T.faceVertices f) : Set T.Vertex) ⊆ A ∧
      ¬ (↑(T.faceVertices f) : Set T.Vertex) ⊆ Aᶜ) :
    ∃ e : T.Edge, T.edgeOnFace e f ∧ ∃ b : Bool,
      ∀ x ∈ T.faceVertices f,
        (x ∈ A ↔ if b then x ∈ T.edgeEndpoints e else x ∉ T.edgeEndpoints e) := by
  obtain ⟨u, hu, v, hv, huv, hlabels⟩ :=
    three_vertices_same_label_pair A (T.faceVertices f) (hT.props.2.2.2 f).2
  obtain ⟨w, hw, hwu, hwv⟩ := exists_thirdVertex T hT f u v hu hv huv
  have hface : T.faceVertices f = {u, v, w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hu, hv, hw⟩
    · rw [(hT.props.2.2.2 f).2]
      simp [huv, Ne.symm hwu, Ne.symm hwv]
  obtain ⟨d, hd⟩ := exists_faceDart T hT f u v hu hv huv
  have hdf : T.edgeOnFace (T.edgeOf d) f := by
    rcases hd.2.2 with hf | hf
    · exact ⟨d, rfl, hf⟩
    · exact ⟨T.edgeInv d,
        ((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm, hf⟩
  have hedge : T.edgeEndpoints (T.edgeOf d) = {u, v} := by
    rw [T.edgeEndpoints_edgeOf, hd.1, hd.2.1]
  by_cases hua : u ∈ A
  · have hva := hlabels.mp hua
    have hwa : w ∉ A := by
      intro hwA
      apply hmono.1
      intro x hx
      simp only [Finset.mem_coe, hface, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hua
      · exact hva
      · exact hwA
    refine ⟨T.edgeOf d, hdf, true, ?_⟩
    intro x hx
    simp only [Finset.mem_coe, hface, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [hedge, hua, hva, hwa, hwu, hwv]
  · have hva : v ∉ A := fun h => hua (hlabels.mpr h)
    have hwa : w ∈ A := by
      by_contra hwA
      apply hmono.2
      intro x hx
      simp only [Finset.mem_coe, hface, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hua
      · exact hva
      · exact hwA
    refine ⟨T.edgeOf d, hdf, false, ?_⟩
    intro x hx
    simp only [Finset.mem_coe, hface, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [hedge, hua, hva, hwa, hwu, hwv]

-- @node: SphereMap.exists_partition_matching_face
/-- Suppose [the sphere map is a triangulation](hyp:hT), [the given face meets both the
designated vertex set and its complement](hyp:hmono), and [each edge on that face admits
a partition into two induced trees with its endpoints in the first part and all other
vertices of the face in the second](hyp:hpartition). Then [there is a partition into two
induced trees whose first part agrees with the designated set on every vertex of the face](goal). -/
lemma exists_partition_matching_face (T : SphereMap) (hT : IsSphereTriangulation T)
    (f : T.Face) (A : Set T.Vertex)
    (hmono : ¬ (↑(T.faceVertices f) : Set T.Vertex) ⊆ A ∧
      ¬ (↑(T.faceVertices f) : Set T.Vertex) ⊆ Aᶜ)
    (hpartition : ∀ e : T.Edge, T.edgeOnFace e f →
      ∃ B : Set T.Vertex, (T.toSimpleGraph.induce B).IsTree ∧
        (T.toSimpleGraph.induce Bᶜ).IsTree ∧
        (∀ v ∈ T.edgeEndpoints e, v ∈ B) ∧
        (∀ v ∈ T.faceVertices f, v ∉ T.edgeEndpoints e → v ∉ B)) :
    ∃ B : Set T.Vertex, (T.toSimpleGraph.induce B).IsTree ∧
      (T.toSimpleGraph.induce Bᶜ).IsTree ∧
      ∀ v ∈ T.faceVertices f, v ∈ A ↔ v ∈ B := by
  obtain ⟨e, he, b, hlabels⟩ := T.exists_face_label_prescription hT f A hmono
  obtain ⟨B, hBT, hBcT, hends, hthird⟩ := hpartition e he
  have hB (v : T.Vertex) (hv : v ∈ T.faceVertices f) :
      v ∈ B ↔ v ∈ T.edgeEndpoints e := by
    constructor
    · intro hb
      by_contra hn
      exact hthird v hv hn hb
    · exact hends v
  cases b with
  | false =>
    refine ⟨Bᶜ, hBcT, (compl_compl B).symm ▸ hBT, ?_⟩
    intro v hv
    exact (hlabels v hv).trans (not_congr (hB v hv)).symm
  | true =>
    exact ⟨B, hBT, hBcT, fun v hv => (hlabels v hv).trans (hB v hv).symm⟩

-- @node: SphereMap.exists_cycleCap_boundary_face
/-- If [the sphere map is a triangulation](hyp:hT) and [the chosen outer face lies outside
the cycle's left region](hyp:hout), then [the map obtained by capping that region has a face
whose vertices, viewed as original vertices, are exactly the cycle's vertices](goal). -/
lemma exists_cycleCap_boundary_face (T : SphereMap) (hT : IsSphereTriangulation T)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C) :
    ∃ f : (T.cycleCappedMap hT C outer hout).Face,
      ((T.cycleCappedMap hT C outer hout).faceVertices f).image Subtype.val =
        (C.val.map T.vert).toFinset := by
  obtain ⟨d, hd⟩ := T.exists_cycle_exterior_dart hT.props.1 C outer hout
  let N := T.cycleCappedMap hT C outer hout
  let f := N.faceOf d
  have hf (e : T.RegionDart (T.leftRegion C)) :
      N.faceOf e = f ↔ T.edgeInv e.val ∈ C.val := by
    change Sum.inl (orbitOf (T.cycleLeftRotation C).facePerm e) =
      Sum.inl (orbitOf (T.cycleLeftRotation C).facePerm d) ↔ _
    rw [Sum.inl.injEq]
    exact ⟨fun h => (T.cycle_exterior_orbit_iff hT.props.1 C d hd e).mp
      (Quotient.exact h).symm,
      fun h => Quotient.sound ((T.cycle_exterior_orbit_iff hT.props.1 C d hd e).mpr h).symm⟩
  have heads : (C.val.map T.head).toFinset = (C.val.map T.vert).toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      exact List.mem_toFinset.mpr (T.cycle_head_mem_vertices C e he)
    · rw [List.toFinset_card_of_nodup (cycle_heads_nodup T C),
        List.toFinset_card_of_nodup C.property.2, List.length_map, List.length_map]
  refine ⟨f, ?_⟩
  rw [T.cycleCap_faceVertices_eq_image hT C outer hout, ← heads]
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
    have hmem := (hf e).mp (Finset.mem_filter.mp he).2
    apply List.mem_toFinset.mpr
    refine List.mem_map.mpr ⟨T.edgeInv e.val, hmem, ?_⟩
    exact congrArg T.vert (T.edgeInv_involutive e.val)
  · intro hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    let a : T.RegionDart (T.leftRegion C) := ⟨T.edgeInv e, Or.inr (by
      rw [T.edgeInv_involutive]
      exact T.cycle_face_mem_leftRegion C e he)⟩
    have ha : N.faceOf a = f := (hf a).mpr (by
      change T.edgeInv (T.edgeInv e) ∈ C.val
      rwa [T.edgeInv_involutive])
    exact Finset.mem_image.mpr ⟨N.vert a,
      Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩, rfl⟩

-- @node: SphereMap.triangleCap_label_acyclic_preimage
/-- If [the sphere map is a triangulation](hyp:hT), [the cycle has length three](hyp:hthree),
[the chosen outer face lies outside its left region](hyp:hout), and [the graph induced by
the designated vertex set is acyclic](hyp:hA), then [the graph induced in the capped left
region by vertices belonging to that set is also acyclic](goal). -/
lemma triangleCap_label_acyclic_preimage (T : SphereMap) (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hthree : C.val.length = 3)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (A : Set T.Vertex) (hA : (T.toSimpleGraph.induce A).IsAcyclic) :
    ((T.cycleCappedMap hT C outer hout).toSimpleGraph.induce
      (Subtype.val ⁻¹' A)).IsAcyclic := by
  rw [T.triangleCap_toSimpleGraph hT C hthree outer hout]
  let g : (T.toSimpleGraph.induce (T.regionVertexSet (T.leftRegion C))).induce
      (Subtype.val ⁻¹' A) →g T.toSimpleGraph.induce A :=
    ⟨fun v => ⟨v.val.val, v.property⟩, fun h => h⟩
  have hg : Function.Injective g := by
    intro u v h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => z.val) h))
  exact hA.comap g hg

-- @node: SphereMap.exists_triangleCap_partition_matching
/-- Suppose [the original sphere map is a triangulation](hyp:hT), [the cycle has length
three](hyp:hthree), [the outer face lies outside its left region](hyp:hout), and [the capped
left region is also a sphere triangulation](hyp:hN). If [the cycle has vertices both inside
and outside the designated set](hyp:hboundary) and [every edge on every face of the capped
map admits a partition into two induced trees with its endpoints in the first part and
the other face vertices in the second](hyp:hpartition), then [the left region can be
partitioned into two induced trees whose first part agrees with the designated set on
all cycle vertices](goal). -/
lemma exists_triangleCap_partition_matching (T : SphereMap) (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hthree : C.val.length = 3)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (hN : IsSphereTriangulation (T.cycleCappedMap hT C outer hout))
    (A : Set T.Vertex)
    (hboundary : ¬ (↑(C.val.map T.vert).toFinset : Set T.Vertex) ⊆ A ∧
      ¬ (↑(C.val.map T.vert).toFinset : Set T.Vertex) ⊆ Aᶜ)
    (hpartition : ∀ (f : (T.cycleCappedMap hT C outer hout).Face)
      (e : (T.cycleCappedMap hT C outer hout).Edge),
      (T.cycleCappedMap hT C outer hout).edgeOnFace e f →
      ∃ B : Set (T.cycleCappedMap hT C outer hout).Vertex,
        ((T.cycleCappedMap hT C outer hout).toSimpleGraph.induce B).IsTree ∧
        ((T.cycleCappedMap hT C outer hout).toSimpleGraph.induce Bᶜ).IsTree ∧
        (∀ v ∈ (T.cycleCappedMap hT C outer hout).edgeEndpoints e, v ∈ B) ∧
        (∀ v ∈ (T.cycleCappedMap hT C outer hout).faceVertices f,
          v ∉ (T.cycleCappedMap hT C outer hout).edgeEndpoints e → v ∉ B)) :
    ∃ B : Set T.Vertex, B ⊆ T.regionVertexSet (T.leftRegion C) ∧
      (T.toSimpleGraph.induce B).IsTree ∧
      (T.toSimpleGraph.induce (T.regionVertexSet (T.leftRegion C) \ B)).IsTree ∧
      ∀ v ∈ C.val.map T.vert, v ∈ A ↔ v ∈ B := by
  let N := T.cycleCappedMap hT C outer hout
  obtain ⟨f, hf⟩ := T.exists_cycleCap_boundary_face hT C outer hout
  have hmono : ¬ (↑(N.faceVertices f) : Set N.Vertex) ⊆ (Subtype.val ⁻¹' A) ∧
      ¬ (↑(N.faceVertices f) : Set N.Vertex) ⊆ (Subtype.val ⁻¹' A)ᶜ := by
    constructor
    · intro h
      apply hboundary.1
      intro v hv
      have hv' : v ∈ (N.faceVertices f).image Subtype.val := hf.symm ▸ hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv'
      exact h hw
    · intro h
      apply hboundary.2
      intro v hv
      have hv' : v ∈ (N.faceVertices f).image Subtype.val := hf.symm ▸ hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv'
      exact h hw
  obtain ⟨B, hBT, hBcT, hagree⟩ := N.exists_partition_matching_face hN f
    (Subtype.val ⁻¹' A) hmono (hpartition f)
  have hcompl : Subtype.val '' Bᶜ = T.regionVertexSet (T.leftRegion C) \ Subtype.val '' B := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.property, ?_⟩
      rintro ⟨z, hz, he⟩
      exact hw ((Subtype.ext he : z = w) ▸ hz)
    · rintro ⟨hv, hn⟩
      exact ⟨⟨v, hv⟩, fun hb => hn ⟨⟨v, hv⟩, hb, rfl⟩, rfl⟩
  refine ⟨Subtype.val '' B, ?_, T.triangleCap_label_tree_image hT C hthree outer hout B hBT,
    hcompl ▸ T.triangleCap_label_tree_image hT C hthree outer hout Bᶜ hBcT, ?_⟩
  · rintro v ⟨w, hw, rfl⟩
    exact w.property
  · intro v hv
    have hvf : v ∈ (N.faceVertices f).image Subtype.val := hf.symm ▸ List.mem_toFinset.mpr hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hvf
    constructor
    · intro ha
      exact ⟨w, (hagree w hw).mp ha, rfl⟩
    · rintro ⟨z, hz, he⟩
      exact (hagree w hw).mpr ((Subtype.ext he : z = w) ▸ hz)

-- @node: SphereMap.triangle_cycle_vertex_triangle
/-- If [the sphere map is a triangulation](hyp:hT) and [the cycle has length three](hyp:hthree),
then [its vertex set consists of three pairwise adjacent vertices in the underlying simple graph](goal). -/
lemma triangle_cycle_vertex_triangle (T : SphereMap) (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hthree : C.val.length = 3) :
    ∃ u v w : T.Vertex,
      (↑(C.val.map T.vert).toFinset : Set T.Vertex) = {u, v, w} ∧
      T.toSimpleGraph.Adj u v ∧ T.toSimpleGraph.Adj u w ∧ T.toSimpleGraph.Adj v w := by
  obtain ⟨a, b, c, hlist⟩ : ∃ a b c, C.val = [a, b, c] := by
    cases h : C.val with
    | nil => simp [h] at hthree
    | cons a ds =>
      cases ds with
      | nil => simp [h] at hthree
      | cons b ds =>
        cases ds with
        | nil => simp [h] at hthree
        | cons c ds =>
          have hn : ds = [] := List.length_eq_zero_iff.mp (by simp_all)
          exact ⟨a, b, c, by simpa [hn] using h⟩
  have hab : T.head a = T.vert b := by
    simpa [hlist] using C.property.1.2.2 ⟨0, by omega⟩
  have hbc : T.head b = T.vert c := by
    simpa [hlist] using C.property.1.2.2 ⟨1, by omega⟩
  have hca : T.head c = T.vert a := by
    simpa [hlist] using C.property.1.2.2 ⟨2, by omega⟩
  have adj (d : T.Dart) : T.toSimpleGraph.Adj (T.vert d) (T.head d) :=
    ⟨hT.props.2.1.1 d, d, rfl, rfl⟩
  refine ⟨T.vert a, T.vert b, T.vert c, ?_, ?_, ?_, ?_⟩
  · ext v
    simp [hlist]
  · exact hab ▸ adj a
  · exact (hca ▸ adj c).symm
  · exact hbc ▸ adj b

-- @node: SphereMap.triangle_cycle_labels_not_monochromatic
/-- If [the sphere map is a triangulation](hyp:hT), [the cycle has length three](hyp:hthree),
[the graph induced by the designated vertex set is acyclic](hyp:hA), and [the graph induced
by vertices in the left region outside that set is acyclic](hyp:hAc), then [the cycle has
vertices both inside and outside the designated set](goal). -/
lemma triangle_cycle_labels_not_monochromatic (T : SphereMap) (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hthree : C.val.length = 3) (A : Set T.Vertex)
    (hA : (T.toSimpleGraph.induce A).IsAcyclic)
    (hAc : (T.toSimpleGraph.induce (T.regionVertexSet (T.leftRegion C) \ A)).IsAcyclic) :
    ¬ (↑(C.val.map T.vert).toFinset : Set T.Vertex) ⊆ A ∧
      ¬ (↑(C.val.map T.vert).toFinset : Set T.Vertex) ⊆ Aᶜ := by
  obtain ⟨u, v, w, hboundary, huv, huw, hvw⟩ := T.triangle_cycle_vertex_triangle hT C hthree
  have hnA := triangle_not_subset_tree_label T.toSimpleGraph A hA u v w huv huw hvw
  have hnAc := triangle_not_subset_tree_label T.toSimpleGraph
    (T.regionVertexSet (T.leftRegion C) \ A) hAc u v w huv huw hvw
  constructor
  · rwa [hboundary]
  · intro h
    apply hnAc
    intro x hx
    have hxb : x ∈ (C.val.map T.vert).toFinset := by
      change x ∈ (↑(C.val.map T.vert).toFinset : Set T.Vertex)
      rw [hboundary]
      exact hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hxb)
    exact ⟨⟨d, Or.inl (T.cycle_face_mem_leftRegion C d hd), rfl⟩, h hxb⟩

end SphereMap
end OaiPairedStatesHamiltonian
