module

public import Papers.OaiPairedStatesHamiltonian.Helpers.PForest

/-! Passing from the selected forest to the prescribed induced tree partition. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

namespace SphereMap

-- @node: SphereMap.face_component_representatives
/-- If [the map is a sphere triangulation](hyp:hT), [the dart belongs to the
specified face](hyp:hdf), [its edge is unselected](hyp:hd), and [the face has a
selected edge](hyp:hf), then [every vertex of that face lies in the same selected
component as one of the dart's two endpoints](goal). -/
lemma face_component_representatives (T : SphereMap) (hT : IsSphereTriangulation T)
    (S : Set T.Edge) (f : T.Face) (d : T.Dart)
    (hdf : T.faceOf d = f) (hd : T.edgeOf d ∉ S)
    (hf : ∃ e ∈ S, T.edgeOnFace e f) :
    ∀ x ∈ T.faceVertices f,
      (T.spanningGraph S).connectedComponentMk x =
        (T.spanningGraph S).connectedComponentMk (T.vert d) ∨
      (T.spanningGraph S).connectedComponentMk x =
        (T.spanningGraph S).connectedComponentMk (T.head d) := by
  obtain ⟨e, he, a, rfl, haf⟩ := hf
  have ha := faceDart_endpoints_incident T hT a
  rw [haf] at ha
  have hh := faceDart_endpoints_incident T hT d
  rw [hdf] at hh
  have hc : (T.spanningGraph S).connectedComponentMk (T.vert a) =
      (T.spanningGraph S).connectedComponentMk (T.head a) :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      ⟨hT.props.2.1.1 a, a, he, rfl, rfl⟩
  intro x hx
  by_cases hxu : x = T.vert d
  · exact Or.inl (congrArg _ hxu)
  by_cases hxv : x = T.head d
  · exact Or.inr (congrArg _ hxv)
  have hset : T.faceVertices f = {T.vert d, T.head d, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hh.1, hh.2, hx⟩
    · rw [(hT.props.2.2.2 f).2]
      simp [hT.props.2.1.1 d, Ne.symm hxu, Ne.symm hxv]
  rw [hset] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha.1 with hu | hv | hx <;> rcases ha.2 with hu' | hv' | hx'
  · exact (hT.props.2.1.1 a (hu.trans hu'.symm)).elim
  · exact (hd ((hT.props.2.1.2 a d (by rw [hu, hv'])).symm ▸ he)).elim
  · exact Or.inl ((congrArg _ hx').symm.trans (hc.symm.trans (congrArg _ hu)))
  · exact (hd ((hT.props.2.1.2 a d (by rw [hv, hu']; exact Sym2.eq_swap)).symm ▸ he)).elim
  · exact (hT.props.2.1.1 a (hv.trans hv'.symm)).elim
  · exact Or.inr ((congrArg _ hx').symm.trans (hc.symm.trans (congrArg _ hv)))
  · exact Or.inl ((congrArg _ hx).symm.trans (hc.trans (congrArg _ hu')))
  · exact Or.inr ((congrArg _ hx).symm.trans (hc.trans (congrArg _ hv')))
  · exact (hT.props.2.1.1 a (hx.trans hx'.symm)).elim

-- @node: SphereMap.forest_face_label_propagation
/-- If [the map is a sphere triangulation](hyp:hT), [the selected edges form a
spanning forest](hyp:hS), [every face has a selected edge](hyp:hfaces), and [the
components containing vertices of the initial face all satisfy the given
property](hyp:h0), then [the component containing every vertex satisfies that
property](goal). -/
lemma forest_face_label_propagation (T : SphereMap) (hT : IsSphereTriangulation T)
    (S : Set T.Edge) (hS : IsSpanningForest T S)
    (hfaces : ∀ f, ∃ e ∈ S, T.edgeOnFace e f)
    (P : (T.spanningGraph S).ConnectedComponent → Prop) (f0 : T.Face)
    (h0 : ∀ x ∈ T.faceVertices f0, P ((T.spanningGraph S).connectedComponentMk x)) :
    ∀ x, P ((T.spanningGraph S).connectedComponentMk x) := by
  let D := (T.dual hT.props.1).spanningGraph Sᶜ
  have hD : D.Connected := T.dual_compl_connected hT.props.1 S hS
  have step {f g : T.Face} (hfg : D.Adj f g)
      (hf : ∀ x ∈ T.faceVertices f, P ((T.spanningGraph S).connectedComponentMk x)) :
      ∀ x ∈ T.faceVertices g, P ((T.spanningGraph S).connectedComponentMk x) := by
    obtain ⟨_, d, hd, hdf, hdg⟩ := hfg
    change T.edgeOf d ∉ S at hd
    change T.faceOf d = f at hdf
    change T.faceOf (T.edgeInv d) = g at hdg
    have hdi : T.edgeOf (T.edgeInv d) ∉ S := by
      simpa only [show T.edgeOf (T.edgeInv d) = T.edgeOf d from
        ((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm] using hd
    have hends := faceDart_endpoints_incident T hT d
    rw [hdf] at hends
    intro x hx
    rcases T.face_component_representatives hT S g (T.edgeInv d) hdg hdi
      (hfaces g) x hx with h | h
    · rw [h]
      exact hf _ hends.2
    · rw [h]
      change P ((T.spanningGraph S).connectedComponentMk (T.vert (T.edgeInv (T.edgeInv d))))
      rw [T.edgeInv_involutive]
      exact hf _ hends.1
  have walk {f g : T.Face} (p : D.Walk f g) :
      (∀ x ∈ T.faceVertices f, P ((T.spanningGraph S).connectedComponentMk x)) →
      ∀ x ∈ T.faceVertices g, P ((T.spanningGraph S).connectedComponentMk x) := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hf => ih (step h hf)
  intro x
  obtain ⟨d, hd⟩ := triangulation_has_dart_at_vertex T hT x
  obtain ⟨p⟩ := hD.preconnected f0 (T.faceOf d)
  exact walk p h0 x (hd ▸ (faceDart_endpoints_incident T hT d).1)

-- @node: SphereMap.forest_not_connected_of_card_add_two
/-- If [the selected edges form a spanning forest](hyp:hS) and [their number is
two less than the number of vertices](hyp:hcard), then [the selected spanning
graph is not connected](goal). -/
lemma forest_not_connected_of_card_add_two (T : SphereMap) (S : Set T.Edge)
    (hS : IsSpanningForest T S)
    (hcard : (Finset.univ.filter (fun e => e ∈ S)).card + 2 = Fintype.card T.Vertex) :
    ¬ (T.spanningGraph S).Connected := by
  intro hc
  have ht := T.spanningTree_edge_card S ⟨hS, hc⟩
  omega

-- @node: SphereMap.forest_component_edge_iff
/-- If [the map is a sphere triangulation](hyp:hT), [the selected edges form a
spanning forest](hyp:hS), [every face has a selected edge](hyp:hfaces), and [there
are two fewer selected edges than vertices](hyp:hcard), then [a dart's endpoints
lie in the same selected component exactly when its edge is selected](goal). -/
lemma forest_component_edge_iff (T : SphereMap) (hT : IsSphereTriangulation T)
    (S : Set T.Edge) (hS : IsSpanningForest T S)
    (hfaces : ∀ f, ∃ e ∈ S, T.edgeOnFace e f)
    (hcard : (Finset.univ.filter (fun e => e ∈ S)).card + 2 = Fintype.card T.Vertex)
    (d : T.Dart) :
    (T.spanningGraph S).connectedComponentMk (T.vert d) =
      (T.spanningGraph S).connectedComponentMk (T.head d) ↔ T.edgeOf d ∈ S := by
  constructor
  · intro heq
    by_contra hd
    have hf : ∀ x ∈ T.faceVertices (T.faceOf d),
        (T.spanningGraph S).connectedComponentMk x =
          (T.spanningGraph S).connectedComponentMk (T.vert d) := by
      intro x hx
      exact (T.face_component_representatives hT S (T.faceOf d) d rfl hd
        (hfaces _) x hx).elim id (fun h => h.trans heq.symm)
    have hall := T.forest_face_label_propagation hT S hS hfaces
      (fun K => K = (T.spanningGraph S).connectedComponentMk (T.vert d)) _ hf
    apply T.forest_not_connected_of_card_add_two S hS hcard
    let : Nonempty T.Vertex := hT.props.1.nonempty
    refine ⟨?_⟩
    intro x y
    exact SimpleGraph.ConnectedComponent.exact ((hall x).trans (hall y).symm)
  · intro hd
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      ⟨hT.props.2.1.1 d, d, hd, rfl, rfl⟩

-- @node: SphereMap.forest_component_induced_tree
/-- If [the map is a sphere triangulation](hyp:hT), [the selected edges form a
spanning forest](hyp:hS), [every face has a selected edge](hyp:hfaces), and [there
are two fewer selected edges than vertices](hyp:hcard), then [the original graph
induced on any selected component is a tree](goal). -/
lemma forest_component_induced_tree (T : SphereMap) (hT : IsSphereTriangulation T)
    (S : Set T.Edge) (hS : IsSpanningForest T S)
    (hfaces : ∀ f, ∃ e ∈ S, T.edgeOnFace e f)
    (hcard : (Finset.univ.filter (fun e => e ∈ S)).card + 2 = Fintype.card T.Vertex)
    (K : (T.spanningGraph S).ConnectedComponent) :
    (T.toSimpleGraph.induce K.supp).IsTree := by
  have hgraph : T.toSimpleGraph.induce K.supp = K.toSimpleGraph := by
    ext u v
    constructor
    · rintro ⟨hne, d, hd, he⟩
      change T.vert d = u.val at hd
      change T.head d = v.val at he
      refine ⟨hne, d, (T.forest_component_edge_iff hT S hS hfaces hcard d).mp ?_, hd, he⟩
      rw [hd, he]
      exact u.property.trans v.property.symm
    · rintro ⟨hne, d, hs, hd, he⟩
      exact ⟨hne, d, hd, he⟩
  rw [hgraph]
  exact (T.isAcyclic_spanningGraph S hS).isTree_connectedComponent K

-- @node: SphereMap.edgeEndpoints_edgeOf
/-- [The endpoints of the edge represented by a dart are precisely its initial
and terminal vertices](goal). -/
lemma edgeEndpoints_edgeOf (T : SphereMap) (d : T.Dart) :
    T.edgeEndpoints (T.edgeOf d) = {T.vert d, T.head d} := by
  ext x
  constructor
  · rintro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rcases (T.edgeOf_eq_iff d a).mp (Finset.mem_filter.mp ha).2.symm with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    · have hx := Finset.mem_singleton.mp hx
      exact Finset.mem_image.mpr ⟨T.edgeInv d, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm⟩, hx.symm⟩

-- @node: SphereMap.face_component_representatives_of_incident
/-- If [the map is a sphere triangulation](hyp:hT), [the dart runs from the first
specified vertex to the second along the specified face in either
orientation](hyp:h), [its edge is unselected](hyp:hd), and [that face has a selected
edge](hyp:hf), then [each vertex of the face belongs to the selected component of
one of the two specified vertices](goal). -/
lemma face_component_representatives_of_incident (T : SphereMap)
    (hT : IsSphereTriangulation T) (S : Set T.Edge) (f : T.Face)
    (v w : T.Vertex) (d : T.Dart) (h : FaceDart T f v w d)
    (hd : T.edgeOf d ∉ S) (hf : ∃ e ∈ S, T.edgeOnFace e f) :
    ∀ x ∈ T.faceVertices f,
      (T.spanningGraph S).connectedComponentMk x = (T.spanningGraph S).connectedComponentMk v ∨
      (T.spanningGraph S).connectedComponentMk x = (T.spanningGraph S).connectedComponentMk w := by
  rcases h.2.2 with hdf | hdf
  · simpa only [h.1, h.2.1] using T.face_component_representatives hT S f d hdf hd hf
  · have hi : T.edgeOf (T.edgeInv d) ∉ S := by
      simpa only [show T.edgeOf (T.edgeInv d) = T.edgeOf d from
        ((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm] using hd
    intro x hx
    have hr := T.face_component_representatives hT S f (T.edgeInv d) hdf hi hf x hx
    have hh : T.head (T.edgeInv d) = v := by
      change T.vert (T.edgeInv (T.edgeInv d)) = v
      rw [T.edgeInv_involutive, h.1]
    simpa only [show T.vert (T.edgeInv d) = w from h.2.1, hh, or_comm] using hr

-- @node: SphereMap.exists_tree_partition_of_face_forest
/-- If [the map is a sphere triangulation](hyp:hT), [the selected edges form a
spanning forest](hyp:hS), [each face has exactly one selected edge](hyp:hfaces),
[there are two fewer selected edges than vertices](hyp:hcard), and [the
designated edge lies on the designated face](hyp:he0) and [is selected](hyp:hsel),
then [there is a vertex set such that it and its complement induce trees, it
contains both endpoints of the designated edge, and it excludes every other
vertex of the designated face](goal). -/
lemma exists_tree_partition_of_face_forest (T : SphereMap) (hT : IsSphereTriangulation T)
    (S : Set T.Edge) (hS : IsSpanningForest T S)
    (hfaces : ∀ f, ∃! e, e ∈ S ∧ T.edgeOnFace e f)
    (hcard : (Finset.univ.filter (fun e => e ∈ S)).card + 2 = Fintype.card T.Vertex)
    (f0 : T.Face) (e0 : T.Edge) (he0 : T.edgeOnFace e0 f0) (hsel : e0 ∈ S) :
    ∃ U : Set T.Vertex, (T.toSimpleGraph.induce U).IsTree ∧
      (T.toSimpleGraph.induce Uᶜ).IsTree ∧
      (∀ v ∈ T.edgeEndpoints e0, v ∈ U) ∧
      (∀ v ∈ T.faceVertices f0, v ∉ T.edgeEndpoints e0 → v ∉ U) := by
  have hex (f : T.Face) : ∃ e ∈ S, T.edgeOnFace e f := (hfaces f).exists
  obtain ⟨a, rfl, haf⟩ := he0
  have ha := faceDart_endpoints_incident T hT a
  rw [haf] at ha
  obtain ⟨w, hw, hwu, hwv⟩ := exists_thirdVertex T hT f0 _ _ ha.1 ha.2 (hT.props.2.1.1 a)
  obtain ⟨d, hd⟩ := exists_faceDart T hT f0 (T.vert a) w ha.1 hw hwu.symm
  have hdf : T.edgeOnFace (T.edgeOf d) f0 := by
    rcases hd.2.2 with hf | hf
    · exact ⟨d, rfl, hf⟩
    · exact ⟨T.edgeInv d, ((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm, hf⟩
  have hnot : T.edgeOf d ∉ S := by
    intro hs
    have he := (hfaces f0).unique ⟨hs, hdf⟩ ⟨hsel, a, rfl, haf⟩
    have hwmem : w ∈ T.edgeEndpoints (T.edgeOf d) := by
      rw [T.edgeEndpoints_edgeOf, hd.2.1]
      simp
    rw [he, T.edgeEndpoints_edgeOf] at hwmem
    simp [hwu, hwv] at hwmem
  let c := (T.spanningGraph S).connectedComponentMk
  have hne : c (T.vert a) ≠ c w := by
    intro he
    apply hnot
    apply (T.forest_component_edge_iff hT S hS hex hcard d).mp
    simpa only [hd.1, hd.2.1] using he
  have hcover : ∀ x, c x = c (T.vert a) ∨ c x = c w :=
    T.forest_face_label_propagation hT S hS hex
      (fun K => K = c (T.vert a) ∨ K = c w) f0
      (T.face_component_representatives_of_incident hT S f0 _ _ d hd hnot (hex f0))
  let U := (c (T.vert a)).supp
  have hcompl : Uᶜ = (c w).supp := by
    ext x
    change (¬ c x = c (T.vert a)) ↔ c x = c w
    exact ⟨fun hx => (hcover x).resolve_left hx, fun hx he => hne (he.symm.trans hx)⟩
  refine ⟨U, T.forest_component_induced_tree hT S hS hex hcard _, ?_, ?_, ?_⟩
  · rw [hcompl]
    exact T.forest_component_induced_tree hT S hS hex hcard _
  · intro x hx
    rw [T.edgeEndpoints_edgeOf] at hx
    change c x = c (T.vert a)
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rfl
    · rw [Finset.mem_singleton.mp hx]
      exact ((T.forest_component_edge_iff hT S hS hex hcard a).mpr hsel).symm
  · intro x hx hxe
    have hset : T.faceVertices f0 = {T.vert a, T.head a, w} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨ha.1, ha.2, hw⟩
      · rw [(hT.props.2.2.2 f0).2]
        simp [hT.props.2.1.1 a, Ne.symm hwu, Ne.symm hwv]
    have hxw : x = w := by
      rw [hset] at hx
      rw [T.edgeEndpoints_edgeOf] at hxe
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hxe
      exact hx.resolve_left (fun he => hxe (Or.inl he)) |>.resolve_left
        (fun he => hxe (Or.inr he))
    change c x ≠ c (T.vert a)
    rw [hxw]
    exact hne.symm

end SphereMap

-- @node: exists_tree_partition_of_noSeparatingTriangle
/-- If [the map is a sphere triangulation](hyp:hT), [its face coloring is a
partition coloring](hyp:hcol), [it has no separating triangle](hyp:hsep), and [the
designated edge lies on the designated face](hyp:he0), then [there is a vertex
set such that it and its complement induce trees, it contains both endpoints of
the designated edge, and it excludes every other vertex of the designated
face](goal). -/
lemma exists_tree_partition_of_noSeparatingTriangle (T : SphereMap)
    (hT : IsSphereTriangulation T) (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (hsep : TreesNoSeparatingTriangle T)
    (t0 : T.Face) (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) :
    ∃ U : Set T.Vertex, (T.toSimpleGraph.induce U).IsTree ∧
      (T.toSimpleGraph.induce Uᶜ).IsTree ∧
      (∀ v ∈ T.edgeEndpoints e0, v ∈ U) ∧
      (∀ v ∈ T.faceVertices t0, v ∉ T.edgeEndpoints e0 → v ∉ U) := by
  let p := forestPair T hT col hcol hsep t0
  have hp : IsPair T col t0 p.1 p.2 := forestPair_isPair T hT col hcol hsep t0
  have hf : QsForest T col t0 p.2 := forestPair_qsForest T hT col hcol hsep t0
  let S := selectedSet T hT col hcol t0 p.2 e0 he0
  have hS : IsSpanningForest T {e | e ∈ S} :=
    selectedSet_isForest_of_pair T hT col hcol t0 p.1 p.2 hp hf hsep e0 he0
  have hfaces (f : T.Face) : ∃! e, e ∈ S ∧ T.edgeOnFace e f := by
    cases hc : normalizedColoring T col t0 f with
    | false =>
      exact selectedSet_white_face_existsUnique T hT col hcol t0 p.1 p.2 hp hf hsep e0 he0 f hc
    | true => exact selectedSet_black_face_existsUnique_of_color T hT col hcol t0 p.2 e0 he0 f hc
  have hcard : S.card + 2 = Fintype.card T.Vertex := by
    have hs := selectedSet_card T hT col hcol t0 p.2 e0 he0
    have hr : (roots T t0).card = 3 := (hT.props.2.2.2 t0).2
    have hnon := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (roots T t0))
    change (nonRoot T t0).card + (roots T t0).card = (Finset.univ : Finset T.Vertex).card at hnon
    rw [Finset.card_univ, hr] at hnon
    change S.card = _ at hs
    omega
  apply T.exists_tree_partition_of_face_forest hT {e | e ∈ S} hS hfaces ?_ t0 e0 he0
    (Finset.mem_insert_self _ _)
  simpa only [Set.mem_ofPred_eq, Finset.filter_mem_eq_inter, Finset.univ_inter] using hcard

end OaiPairedStatesHamiltonian
