module

public import Papers.OaiPairedStatesHamiltonian.Helpers.TriangleCaps

/-! Incidence preservation and induced graphs for triangular caps. -/

public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

variable (T : SphereMap)

/-- If [T is a sphere triangulation](hyp:hT), [C has length three](hyp:hthree),
[the tail of an oriented edge d lies on C](hyp:hv), and [its head lies on
C](hyp:hw), then [the unoriented edge underlying d is an edge of C](goal). -/
-- @node: SphereMap.triangle_cycle_edge_of_boundary_endpoints
lemma triangle_cycle_edge_of_boundary_endpoints (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hthree : C.val.length = 3) (d : T.Dart)
    (hv : T.vert d ∈ C.val.map T.vert) (hw : T.head d ∈ C.val.map T.vert) :
    T.edgeOf d ∈ C.val.map T.edgeOf := by
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
  have hedge (e : T.Dart) (h : s(T.vert d, T.head d) = s(T.vert e, T.head e)) :
      T.edgeOf d = T.edgeOf e := hT.props.2.1.2 d e h
  simp only [hlist, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hv hw ⊢
  rcases hv with hv | hv | hv <;> rcases hw with hw | hw | hw
  · exact (hT.props.2.1.1 d (hv.trans hw.symm)).elim
  · exact Or.inl (hedge a (by rw [hv, hw, hab]))
  · exact Or.inr (Or.inr (hedge c (by rw [hv, hw, hca]; exact Sym2.eq_swap)))
  · exact Or.inl (hedge a (by rw [hv, hw, hab]; exact Sym2.eq_swap))
  · exact (hT.props.2.1.1 d (hv.trans hw.symm)).elim
  · exact Or.inr (Or.inl (hedge b (by rw [hv, hw, hbc])))
  · exact Or.inr (Or.inr (hedge c (by rw [hv, hw, hca])))
  · exact Or.inr (Or.inl (hedge b (by rw [hv, hw, hbc]; exact Sym2.eq_swap)))
  · exact (hT.props.2.1.1 d (hv.trans hw.symm)).elim

/-- If [T is a sphere triangulation](hyp:hT), [the tail of an oriented edge d
belongs to the vertices retained on the left of C](hyp:hv), and [that tail is
not on C](hyp:hboundary), then [d is retained on the left of C](goal). -/
-- @node: SphereMap.cycle_keeps_of_nonboundary_tail
lemma cycle_keeps_of_nonboundary_tail (hT : IsSphereTriangulation T)
    (C : T.Cycle) (d : T.Dart)
    (hv : T.regionVertexSet (T.leftRegion C) (T.vert d))
    (hboundary : T.vert d ∉ C.val.map T.vert) :
    T.regionKeeps (T.leftRegion C) d := by
  obtain ⟨f, hf, hfv⟩ := (T.regionVertexSet_iff_face_incidence hT _ _).mp hv
  have hdv : T.vert d ∈ T.faceVertices (T.faceOf d) :=
    by
    rw [triangulation_faceVertices_eq_image T hT]
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  exact Or.inl ((T.cycle_nonboundary_face_side hT C _ hboundary f _ hfv hdv).mp hf)

/-- If [T is a sphere triangulation](hyp:hT) and [C has length three](hyp:hthree),
then [an oriented edge is retained on the left of C if and only if both of its
endpoints belong to the retained vertex set](goal). -/
-- @node: SphereMap.triangle_cycle_keeps_iff_endpoints
lemma triangle_cycle_keeps_iff_endpoints (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hthree : C.val.length = 3) (d : T.Dart) :
    T.regionKeeps (T.leftRegion C) d ↔
      T.regionVertexSet (T.leftRegion C) (T.vert d) ∧
        T.regionVertexSet (T.leftRegion C) (T.head d) := by
  constructor
  · intro hd
    exact ⟨⟨d, hd, rfl⟩, ⟨T.edgeInv d, (T.regionKeeps_inv _ d).mpr hd, rfl⟩⟩
  · rintro ⟨hv, hw⟩
    by_cases hb : T.vert d ∈ C.val.map T.vert
    · by_cases hc : T.head d ∈ C.val.map T.vert
      · obtain ⟨e, he, hed⟩ := List.mem_map.mp
          (T.triangle_cycle_edge_of_boundary_endpoints hT C hthree d hb hc)
        exact (T.region_keeps_edgeOf_eq _ e d hed).mp
          (Or.inl (T.cycle_face_mem_leftRegion C e he))
      · have hi := T.cycle_keeps_of_nonboundary_tail hT C (T.edgeInv d) hw hc
        exact (T.regionKeeps_inv _ d).mp hi
    · exact T.cycle_keeps_of_nonboundary_tail hT C d hv hb

/-- If [T is a sphere triangulation](hyp:hT), [C has length three](hyp:hthree),
and [the chosen outer face lies outside the left region of C](hyp:hout), then
[the simple graph of the capped map equals the original simple graph induced
on the vertices retained on the left of C](goal). -/
-- @node: SphereMap.triangleCap_toSimpleGraph
lemma triangleCap_toSimpleGraph (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hthree : C.val.length = 3)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C) :
    (T.cycleCappedMap hT C outer hout).toSimpleGraph =
      T.toSimpleGraph.induce (T.regionVertexSet (T.leftRegion C)) := by
  ext v w
  constructor
  · rintro ⟨hne, d, hd, hh⟩
    exact ⟨fun h => hne (Subtype.ext h), d.val,
      congrArg Subtype.val hd, congrArg Subtype.val hh⟩
  · rintro ⟨hne, d, hd, hh⟩
    change T.vert d = v.val at hd
    change T.head d = w.val at hh
    have hk : T.regionKeeps (T.leftRegion C) d :=
      (T.triangle_cycle_keeps_iff_endpoints hT C hthree d).mpr
        ⟨hd.symm ▸ v.property, hh.symm ▸ w.property⟩
    exact ⟨fun h => hne (congrArg Subtype.val h), ⟨d, hk⟩,
      Subtype.ext hd, Subtype.ext hh⟩

/-- If [T is a sphere triangulation](hyp:hT), [the chosen outer face lies outside
the left region of C](hyp:hout), and [f lies in that region](hyp:hf), then
[there is a cap face whose incident oriented edges are exactly the retained
oriented edges that originally belonged to f](goal). -/
-- @node: SphereMap.exists_cycleCap_original_face
lemma exists_cycleCap_original_face (hT : IsSphereTriangulation T)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (f : T.Face) (hf : f ∈ T.leftRegion C) :
    ∃ f' : (T.cycleCappedMap hT C outer hout).Face,
      ∀ d : T.RegionDart (T.leftRegion C),
        (T.cycleCappedMap hT C outer hout).faceOf d = f' ↔ T.faceOf d.val = f := by
  have hpos : 0 < (T.faceDarts f).card := by
    rw [← T.faceLength_eq_card_faceDarts, (hT.props.2.2.2 f).1]
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have haf : T.faceOf a = f := (Finset.mem_filter.mp ha).2
  let e : T.RegionDart (T.leftRegion C) := ⟨a, Or.inl (haf.symm ▸ hf)⟩
  refine ⟨(T.cycleCappedMap hT C outer hout).faceOf e, ?_⟩
  intro d
  change Sum.inl (orbitOf (T.cycleLeftRotation C).facePerm d) =
    Sum.inl (orbitOf (T.cycleLeftRotation C).facePerm e) ↔ _
  rw [Sum.inl.injEq]
  have hiff := T.region_face_sameCycle_iff hT.props.1 (T.leftRegion C) e d
    (haf.symm ▸ hf)
  constructor
  · intro he
    exact ((hiff.mp (Quotient.exact he.symm)).symm).trans haf
  · intro hd
    exact (Quotient.sound (hiff.mpr (haf.trans hd.symm))).symm

/-- If [T is a sphere triangulation](hyp:hT) and [the chosen outer face lies
outside the left region of C](hyp:hout), then [the vertices of any cap face are
exactly the tails of the oriented edges incident to that face](goal). -/
-- @node: SphereMap.cycleCap_faceVertices_eq_image
lemma cycleCap_faceVertices_eq_image (hT : IsSphereTriangulation T)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (f : (T.cycleCappedMap hT C outer hout).Face) :
    (T.cycleCappedMap hT C outer hout).faceVertices f =
      ((T.cycleCappedMap hT C outer hout).faceDarts f).image
        (T.cycleCappedMap hT C outer hout).vert := by
  let N := T.cycleCappedMap hT C outer hout
  have hempty : (Finset.univ.filter (fun v : N.Vertex =>
      ∃ hv : ∀ d, N.vert d ≠ v, N.boundaryFace (Sum.inr ⟨v, hv⟩) = f)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hn, _⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨d, hd⟩ := T.cycleCappedMap_has_dart hT C outer hout v
    exact hn d hd
  change (N.faceDarts f).image N.vert ∪ _ = _
  rw [hempty, Finset.union_empty]

/-- Suppose [T is a sphere triangulation](hyp:hT), [the chosen outer face lies
outside the left region of C](hyp:hout), and [f lies in that region](hyp:hf).
If [a retained oriented edge belongs to cap face f' exactly when its original
edge orientation belongs to f](hyp:hface), then [including the vertices of f'
in the original map gives exactly the vertices of f](goal). -/
-- @node: SphereMap.cycleCap_original_face_vertices
lemma cycleCap_original_face_vertices (hT : IsSphereTriangulation T)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (f : T.Face) (hf : f ∈ T.leftRegion C)
    (f' : (T.cycleCappedMap hT C outer hout).Face)
    (hface : ∀ d : T.RegionDart (T.leftRegion C),
      (T.cycleCappedMap hT C outer hout).faceOf d = f' ↔ T.faceOf d.val = f) :
    ((T.cycleCappedMap hT C outer hout).faceVertices f').image Subtype.val =
      T.faceVertices f := by
  rw [T.cycleCap_faceVertices_eq_image, triangulation_faceVertices_eq_image T hT]
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨d.val,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hface d).mp (Finset.mem_filter.mp hd).2⟩, rfl⟩
  · intro hv
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hv
    have hdf := (Finset.mem_filter.mp hd).2
    let e : T.RegionDart (T.leftRegion C) := ⟨d, Or.inl (hdf.symm ▸ hf)⟩
    exact Finset.mem_image.mpr ⟨(T.cycleCappedMap hT C outer hout).vert e,
      Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hface e).mpr hdf⟩, rfl⟩, rfl⟩

/-- If [T is a sphere triangulation](hyp:hT) and [the chosen outer face lies
outside the left region of C](hyp:hout), then [including the endpoints of any
cap edge in the original map gives exactly the endpoints of its corresponding
original edge](goal). -/
-- @node: SphereMap.cycleCap_edge_endpoints
lemma cycleCap_edge_endpoints (hT : IsSphereTriangulation T)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (e : (T.cycleCappedMap hT C outer hout).Edge) :
    ((T.cycleCappedMap hT C outer hout).edgeEndpoints e).image Subtype.val =
      T.edgeEndpoints (T.regionEdgeMap (T.leftRegion C) e) := by
  induction e using Quotient.inductionOn with
  | h a =>
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
      have he := congrArg (T.regionEdgeMap (T.leftRegion C)) (Finset.mem_filter.mp hd).2
      exact Finset.mem_image.mpr ⟨d.val,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
    · intro hv
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hv
      have he : T.edgeOf d = T.edgeOf a.val := (Finset.mem_filter.mp hd).2
      have hk := (T.region_keeps_edgeOf_eq (T.leftRegion C) d a.val he).mpr a.property
      let b : T.RegionDart (T.leftRegion C) := ⟨d, hk⟩
      have hba : (T.cycleLeftRotation C).edgeOf b = (T.cycleLeftRotation C).edgeOf a :=
        T.regionEdgeMap_injective (T.leftRegion C) he
      exact Finset.mem_image.mpr ⟨(T.cycleLeftRotation C).vert b,
        Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba⟩, rfl⟩, rfl⟩

/-- Suppose [T is a sphere triangulation](hyp:hT) and [the chosen outer face lies
outside the left region of C](hyp:hout). If [u belongs to the left region's
vertex set but not to the vertex set of the complementary region](hyp:hu) and
[v belongs to the complementary region's vertex set but not to the left
region's vertex set](hyp:hv), then [u and v are not adjacent in the original
simple graph](goal). -/
-- @node: SphereMap.cycle_side_no_cross_edges
lemma cycle_side_no_cross_edges (hT : IsSphereTriangulation T)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (u : T.Vertex)
    (hu : u ∈ T.regionVertexSet (T.leftRegion C) \ T.regionVertexSet (T.leftRegion C)ᶜ)
    (v : T.Vertex)
    (hv : v ∈ T.regionVertexSet (T.leftRegion C)ᶜ \ T.regionVertexSet (T.leftRegion C)) :
    ¬ T.toSimpleGraph.Adj u v := by
  rintro ⟨_, d, hd, hh⟩
  have hb : u ∉ C.val.map T.vert := by
    intro hb
    exact hu.2 ((T.cycle_region_vertices_inter hT C outer hout u).mpr hb).2
  have hk := T.cycle_keeps_of_nonboundary_tail hT C d (hd.symm ▸ hu.1) (hd.symm ▸ hb)
  apply hv.2
  exact ⟨T.edgeInv d, (T.regionKeeps_inv _ d).mpr hk, hh⟩

/-- Suppose [T is a sphere triangulation](hyp:hT), [the chosen outer face lies
outside the left region of C](hyp:hout), [f lies in that region](hyp:hf), and
[e is an edge of f](hyp:he). Then [there are a cap face and an edge incident to
it such that the edge maps to e, the face vertices map exactly to the vertices
of f, and the edge endpoints map exactly to the endpoints of e](goal). -/
-- @node: SphereMap.exists_cycleCap_original_prescription
lemma exists_cycleCap_original_prescription (hT : IsSphereTriangulation T)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (f : T.Face) (hf : f ∈ T.leftRegion C) (e : T.Edge) (he : T.edgeOnFace e f) :
    ∃ (f' : (T.cycleCappedMap hT C outer hout).Face)
      (e' : (T.cycleCappedMap hT C outer hout).Edge),
      (T.cycleCappedMap hT C outer hout).edgeOnFace e' f' ∧
      T.regionEdgeMap (T.leftRegion C) e' = e ∧
      ((T.cycleCappedMap hT C outer hout).faceVertices f').image Subtype.val =
        T.faceVertices f ∧
      ((T.cycleCappedMap hT C outer hout).edgeEndpoints e').image Subtype.val =
        T.edgeEndpoints e := by
  obtain ⟨f', hface⟩ := T.exists_cycleCap_original_face hT C outer hout f hf
  obtain ⟨d, hde, hdf⟩ := he
  let a : T.RegionDart (T.leftRegion C) := ⟨d, Or.inl (hdf.symm ▸ hf)⟩
  let e' := (T.cycleCappedMap hT C outer hout).edgeOf a
  refine ⟨f', e', ⟨a, rfl, (hface a).mpr hdf⟩, hde,
    T.cycleCap_original_face_vertices hT C outer hout f hf f' hface, ?_⟩
  rw [T.cycleCap_edge_endpoints]
  exact congrArg T.edgeEndpoints hde

/-- If [T is a sphere triangulation](hyp:hT), [C has length three](hyp:hthree),
[the chosen outer face lies outside the left region of C](hyp:hout), and
[the cap graph induced by A is a tree](hyp:hA), then [the original graph
induced by the image of A under vertex inclusion is a tree](goal). -/
-- @node: SphereMap.triangleCap_label_tree_image
lemma triangleCap_label_tree_image (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hthree : C.val.length = 3)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (A : Set (T.cycleCappedMap hT C outer hout).Vertex)
    (hA : ((T.cycleCappedMap hT C outer hout).toSimpleGraph.induce A).IsTree) :
    (T.toSimpleGraph.induce (Subtype.val '' A)).IsTree := by
  rw [T.triangleCap_toSimpleGraph hT C hthree outer hout] at hA
  let g : A → Subtype.val '' A := fun v => ⟨v.val.val, v.val, v.property, rfl⟩
  have hg : Function.Bijective g := by
    constructor
    · intro v w h
      have hvw : v.val.val = w.val.val := congrArg (fun z : Subtype.val '' A => z.val) h
      exact Subtype.ext (Subtype.ext hvw)
    · rintro ⟨v, w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  let i : (T.toSimpleGraph.induce (T.regionVertexSet (T.leftRegion C))).induce A ≃g
      T.toSimpleGraph.induce (Subtype.val '' A) :=
    { toEquiv := Equiv.ofBijective g hg
      map_rel_iff' := Iff.rfl }
  exact i.isTree_iff.mp hA

/-- Suppose [T is a sphere triangulation](hyp:hT), [C has length three](hyp:hthree),
[the chosen outer face lies outside the left region of C](hyp:hout), and
[f lies in that region](hyp:hf). Suppose [the vertices of cap face f' map
exactly to those of f](hyp:hface), [the endpoints of cap edge e' map exactly
to those of e](hyp:hedge), [A induces a tree in the cap graph](hyp:hA),
[its complement also induces a tree](hyp:hAc), [both endpoints of e' belong
to A](hyp:hends), and [all vertices of f' outside those endpoints lie outside
A](hyp:hthird). Then [there is a set B of retained original vertices such that
B and its complement within the retained vertices induce trees, B contains
the endpoints of e, and B excludes every vertex of f outside those
endpoints](goal). -/
-- @node: SphereMap.triangleCap_partition_lift
lemma triangleCap_partition_lift (hT : IsSphereTriangulation T)
    (C : T.Cycle) (hthree : C.val.length = 3)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (f : T.Face) (hf : f ∈ T.leftRegion C) (e : T.Edge)
    (f' : (T.cycleCappedMap hT C outer hout).Face)
    (e' : (T.cycleCappedMap hT C outer hout).Edge)
    (hface : ((T.cycleCappedMap hT C outer hout).faceVertices f').image Subtype.val =
      T.faceVertices f)
    (hedge : ((T.cycleCappedMap hT C outer hout).edgeEndpoints e').image Subtype.val =
      T.edgeEndpoints e)
    (A : Set (T.cycleCappedMap hT C outer hout).Vertex)
    (hA : ((T.cycleCappedMap hT C outer hout).toSimpleGraph.induce A).IsTree)
    (hAc : ((T.cycleCappedMap hT C outer hout).toSimpleGraph.induce Aᶜ).IsTree)
    (hends : ∀ v ∈ (T.cycleCappedMap hT C outer hout).edgeEndpoints e', v ∈ A)
    (hthird : ∀ v ∈ (T.cycleCappedMap hT C outer hout).faceVertices f',
      v ∉ (T.cycleCappedMap hT C outer hout).edgeEndpoints e' → v ∉ A) :
    ∃ B : Set T.Vertex, B ⊆ T.regionVertexSet (T.leftRegion C) ∧
      (T.toSimpleGraph.induce B).IsTree ∧
      (T.toSimpleGraph.induce (T.regionVertexSet (T.leftRegion C) \ B)).IsTree ∧
      (∀ v ∈ T.edgeEndpoints e, v ∈ B) ∧
      (∀ v ∈ T.faceVertices f, v ∉ T.edgeEndpoints e → v ∉ B) := by
  let B : Set T.Vertex := Subtype.val '' A
  have hcompl : Subtype.val '' Aᶜ = T.regionVertexSet (T.leftRegion C) \ B := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.property, ?_⟩
      rintro ⟨x, hx, he⟩
      exact hw ((Subtype.ext he : x = w) ▸ hx)
    · rintro ⟨hv, hn⟩
      exact ⟨⟨v, hv⟩, fun ha => hn ⟨⟨v, hv⟩, ha, rfl⟩, rfl⟩
  refine ⟨B, ?_, T.triangleCap_label_tree_image hT C hthree outer hout A hA,
    hcompl ▸ T.triangleCap_label_tree_image hT C hthree outer hout Aᶜ hAc, ?_, ?_⟩
  · rintro v ⟨w, hw, rfl⟩
    exact w.property
  · intro v hv
    rw [← hedge] at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨w, hends w hw, rfl⟩
  · intro v hv hn hB
    rw [← hface] at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hwn : w ∉ (T.cycleCappedMap hT C outer hout).edgeEndpoints e' := by
      intro he
      exact hn (hedge ▸ Finset.mem_image.mpr ⟨w, he, rfl⟩)
    obtain ⟨x, hx, he⟩ := hB
    exact hthird w hw hwn ((Subtype.ext he : x = w) ▸ hx)

end SphereMap
end OaiPairedStatesHamiltonian
