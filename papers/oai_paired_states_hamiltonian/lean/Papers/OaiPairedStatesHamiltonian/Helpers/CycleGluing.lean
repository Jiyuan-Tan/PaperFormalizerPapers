module

public import Papers.OaiPairedStatesHamiltonian.Helpers.EulerBound
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleIncidence

/-! Finite incidence and connectivity for gluing the two sides of a cycle. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (M : SphereMap)

-- @node: SphereMap.cycle_right_boundary_keeps
/-- If [the map is connected](hyp:hM), [a chosen face lies outside the cycle's
left region](hyp:hout), and [a directed edge occurs in the cycle](hyp:hd), then
[the complement of the left region retains that directed edge](goal). -/
lemma cycle_right_boundary_keeps (hM : M.IsConnectedMap) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) (d : M.Dart) (hd : d ∈ C.val) :
    M.regionKeeps (M.leftRegion C)ᶜ d := by
  exact Or.inr (M.cycle_boundary_opposite_outside hM C outer hout d hd)

-- @node: SphereMap.region_vertices_cover
/-- In [a triangulation of the sphere](hyp:hM), [every vertex is retained by a
given face region or by its complement](goal). -/
lemma region_vertices_cover (hM : IsSphereTriangulation M) (R : Set M.Face) (v : M.Vertex) :
    M.regionVertexSet R v ∨ M.regionVertexSet Rᶜ v := by
  obtain ⟨d, hd⟩ := triangulation_has_dart_at_vertex M hM v
  by_cases hf : M.faceOf d ∈ R
  · exact Or.inl ⟨d, Or.inl hf, hd⟩
  · exact Or.inr ⟨d, Or.inl hf, hd⟩

-- @node: SphereMap.cycle_region_vertices_inter
/-- If [the map is a triangulation of the sphere](hyp:hM) and [a chosen face
lies outside the cycle's left region](hyp:hout), then [a vertex is retained by
both the left region and its complement exactly when it is a cycle vertex](goal). -/
lemma cycle_region_vertices_inter (hM : IsSphereTriangulation M) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) (v : M.Vertex) :
    M.regionVertexSet (M.leftRegion C) v ∧ M.regionVertexSet (M.leftRegion C)ᶜ v ↔
      v ∈ C.val.map M.vert := by
  constructor
  · rintro ⟨hl, hr⟩
    by_contra hv
    obtain ⟨f, hf, hfv⟩ := (M.regionVertexSet_iff_face_incidence hM _ v).mp hl
    obtain ⟨g, hg, hgv⟩ := (M.regionVertexSet_iff_face_incidence hM _ v).mp hr
    exact hg ((M.cycle_nonboundary_face_side hM C v hv f g hfv hgv).mp hf)
  · intro hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    exact ⟨⟨d, Or.inl (M.cycle_face_mem_leftRegion C d hd), rfl⟩,
      ⟨d, M.cycle_right_boundary_keeps hM.props.1 C outer hout d hd, rfl⟩⟩

-- @node: SphereMap.cycle_region_vertex_card_add
/-- If [the map is a triangulation of the sphere](hyp:hM) and [a chosen face
lies outside the cycle's left region](hyp:hout), then [the sum of the vertex
counts in the restrictions to that region and its complement equals the original
vertex count plus the cycle length](goal). -/
lemma cycle_region_vertex_card_add (hM : IsSphereTriangulation M) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) :
    Fintype.card (M.regionRotation (M.leftRegion C)).Vertex +
      Fintype.card (M.regionRotation (M.leftRegion C)ᶜ).Vertex =
        Fintype.card M.Vertex + C.val.length := by
  let L := Finset.univ.filter (M.regionVertexSet (M.leftRegion C))
  let R := Finset.univ.filter (M.regionVertexSet (M.leftRegion C)ᶜ)
  have hu : L ∪ R = Finset.univ := by
    ext v
    simp only [L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    exact M.region_vertices_cover hM _ v
  have hi : L ∩ R = (C.val.map M.vert).toFinset := by
    ext v
    simp only [L, R, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset]
    exact M.cycle_region_vertices_inter hM C outer hout v
  have hc := Finset.card_union_add_card_inter L R
  rw [hu, hi, Finset.card_univ, List.toFinset_card_of_nodup C.property.2,
    List.length_map] at hc
  change Fintype.card {v : M.Vertex // M.regionVertexSet (M.leftRegion C) v} +
    Fintype.card {v : M.Vertex // M.regionVertexSet (M.leftRegion C)ᶜ v} = _
  rw [Fintype.card_subtype, Fintype.card_subtype]
  exact hc.symm

-- @node: SphereMap.region_keeps_edgeOf_eq
/-- If [two directed edges represent the same undirected edge](hyp:h), then
[a face region retains one exactly when it retains the other](goal). -/
lemma region_keeps_edgeOf_eq (R : Set M.Face) (d e : M.Dart)
    (h : M.edgeOf d = M.edgeOf e) : M.regionKeeps R d ↔ M.regionKeeps R e := by
  rcases (M.edgeOf_eq_iff d e).mp h with rfl | rfl
  · rfl
  · exact (M.regionKeeps_inv R d).symm

-- @node: SphereMap.regionEdgeMap
/-- For [a sphere map](hyp:M) and [a region of its faces](hyp:R), the [map from
restricted edges to original edges](goal) sends each edge of the region's
restriction to its underlying undirected edge in the original map. -/
noncomputable def regionEdgeMap (R : Set M.Face) : (M.regionRotation R).Edge → M.Edge :=
  Quotient.lift (fun d : M.RegionDart R => M.edgeOf d.val) (by
    intro d e h
    rcases ((M.regionRotation R).edgeOf_eq_iff d e).mp (Quotient.sound h) with h | h
    · exact congrArg M.edgeOf (congrArg Subtype.val h).symm
    · exact (M.edgeOf_eq_iff d.val e.val).mpr (Or.inr (congrArg Subtype.val h)))

-- @node: SphereMap.regionEdgeMap_injective
/-- [Distinct edges in a face region's restriction map to distinct edges of
the original map](goal). -/
lemma regionEdgeMap_injective (R : Set M.Face) : Function.Injective (M.regionEdgeMap R) := by
  intro a b
  induction a using Quotient.inductionOn with | h d =>
    induction b using Quotient.inductionOn with | h e =>
      intro h
      apply ((M.regionRotation R).edgeOf_eq_iff d e).mpr
      rcases (M.edgeOf_eq_iff d.val e.val).mp h with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)

-- @node: SphereMap.region_edge_card
/-- [The number of edges in a face region's restriction equals the number of
original undirected edges having a directed representative retained by that
region](goal). -/
lemma region_edge_card (R : Set M.Face) :
    Fintype.card (M.regionRotation R).Edge =
      (Finset.univ.filter (fun e : M.Edge => ∃ d, M.regionKeeps R d ∧ M.edgeOf d = e)).card := by
  apply Finset.card_bij (fun e _ => M.regionEdgeMap R e)
  · intro e he
    induction e using Quotient.inductionOn with | h d =>
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.val, d.property, rfl⟩
  · intro a ha b hb hab
    exact M.regionEdgeMap_injective R hab
  · intro e he
    obtain ⟨d, hd, rfl⟩ := (Finset.mem_filter.mp he).2
    exact ⟨(M.regionRotation R).edgeOf ⟨d, hd⟩, Finset.mem_univ _, rfl⟩

-- @node: SphereMap.cycle_region_keeps_inter
/-- If [the map is connected](hyp:hM) and [a chosen face lies outside the cycle's
left region](hyp:hout), then [a directed edge is retained by both that region
and its complement exactly when its underlying undirected edge occurs in the
cycle](goal). -/
lemma cycle_region_keeps_inter (hM : M.IsConnectedMap) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) (d : M.Dart) :
    M.regionKeeps (M.leftRegion C) d ∧ M.regionKeeps (M.leftRegion C)ᶜ d ↔
      M.edgeOf d ∈ C.val.map M.edgeOf := by
  constructor
  · rintro ⟨hl, hr⟩
    by_contra he
    have hi := M.leftRegion_across_noncycle hM C d he
    rcases hl with hl | hl <;> rcases hr with hr | hr
    · exact hr hl
    · exact hr (hi.mp hl)
    · exact hr (hi.mpr hl)
    · exact hr hl
  · intro he
    obtain ⟨e, he, hed⟩ := List.mem_map.mp he
    exact ⟨(M.region_keeps_edgeOf_eq _ e d hed).mp
        (Or.inl (M.cycle_face_mem_leftRegion C e he)),
      (M.region_keeps_edgeOf_eq _ e d hed).mp
        (M.cycle_right_boundary_keeps hM C outer hout e he)⟩

-- @node: SphereMap.cycle_region_edge_card_add
/-- If [the map is connected](hyp:hM) and [a chosen face lies outside the cycle's
left region](hyp:hout), then [the sum of the edge counts in the restrictions to
that region and its complement equals the original edge count plus the cycle
length](goal). -/
lemma cycle_region_edge_card_add (hM : M.IsConnectedMap) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) :
    Fintype.card (M.regionRotation (M.leftRegion C)).Edge +
      Fintype.card (M.regionRotation (M.leftRegion C)ᶜ).Edge =
        Fintype.card M.Edge + C.val.length := by
  let L := Finset.univ.filter (fun e : M.Edge =>
    ∃ d, M.regionKeeps (M.leftRegion C) d ∧ M.edgeOf d = e)
  let R := Finset.univ.filter (fun e : M.Edge =>
    ∃ d, M.regionKeeps (M.leftRegion C)ᶜ d ∧ M.edgeOf d = e)
  have hmem (S : Set M.Face) (d : M.Dart) :
      (∃ e, M.regionKeeps S e ∧ M.edgeOf e = M.edgeOf d) ↔ M.regionKeeps S d := by
    constructor
    · rintro ⟨e, he, hed⟩
      exact (M.region_keeps_edgeOf_eq S e d hed).mp he
    · intro hd
      exact ⟨d, hd, rfl⟩
  have hu : L ∪ R = Finset.univ := by
    ext e
    obtain ⟨d, rfl⟩ := Quotient.exists_rep e
    change (M.edgeOf d ∈ L ∪ R ↔ M.edgeOf d ∈ (Finset.univ : Finset M.Edge))
    simp only [L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      hmem, iff_true]
    by_cases hd : M.faceOf d ∈ M.leftRegion C
    · exact Or.inl (Or.inl hd)
    · exact Or.inr (Or.inl hd)
  have hi : L ∩ R = (C.val.map M.edgeOf).toFinset := by
    ext e
    obtain ⟨d, rfl⟩ := Quotient.exists_rep e
    change (M.edgeOf d ∈ L ∩ R ↔ M.edgeOf d ∈ (C.val.map M.edgeOf).toFinset)
    simp only [L, R, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      hmem, List.mem_toFinset]
    exact M.cycle_region_keeps_inter hM C outer hout d
  have hc := Finset.card_union_add_card_inter L R
  rw [hu, hi, Finset.card_univ, List.toFinset_card_of_nodup C.property.1.2.1,
    List.length_map] at hc
  rw [M.region_edge_card, M.region_edge_card]
  exact hc.symm

-- @node: SphereMap.cycle_region_component_eq_of_keeps
/-- If [a face region retains every directed edge of the cycle](hyp:hkeep),
[a first retained directed edge occurs in that cycle](hyp:hd), and [a second
retained directed edge also occurs in that cycle](hyp:he), then [they belong to
the same connected component of the region's
restriction](goal). -/
lemma cycle_region_component_eq_of_keeps (C : M.Cycle) (R : Set M.Face)
    (hkeep : ∀ d ∈ C.val, M.regionKeeps R d) (d e : M.RegionDart R)
    (hd : d.val ∈ C.val) (he : e.val ∈ C.val) :
    M.regionComponent R d = M.regionComponent R e := by
  have hpos : 0 < C.val.length := List.length_pos_iff.mpr C.property.1.1
  let cd (i : Fin C.val.length) : M.RegionDart R :=
    ⟨C.val.get i, hkeep _ (List.get_mem _ _)⟩
  have hindex (n : ℕ) (hn : n < C.val.length) :
      M.regionComponent R (cd ⟨n, hn⟩) = M.regionComponent R (cd ⟨0, hpos⟩) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hprev := ih (by omega)
      have hs := C.property.1.2.2 ⟨n, by omega⟩
      simp only [Nat.mod_eq_of_lt hn] at hs
      have heq : (M.regionRotation R).head (cd ⟨n, by omega⟩) =
          (M.regionRotation R).vert (cd ⟨n + 1, hn⟩) := Subtype.ext hs
      have ht := (M.regionRotation R).dart_component_eq_head (cd ⟨n, by omega⟩)
      exact ((ht.trans (congrArg (M.regionRotation R).toSimpleGraph.connectedComponentMk
        heq)).symm).trans hprev
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
  have hdi : d = cd i := Subtype.ext hi.symm
  have hej : e = cd j := Subtype.ext hj.symm
  rw [hdi, hej]
  exact (hindex i.val i.isLt).trans (hindex j.val j.isLt).symm

-- @node: SphereMap.cycle_region_connected_of_nonboundary
/-- If [the original map is connected](hyp:hM), [a face region retains every
directed edge of the cycle](hyp:hkeep), and [every directed edge with its tail at
a retained vertex outside the cycle is retained](hyp:hall), then [the underlying
graph of the region's restriction is connected](goal). -/
lemma cycle_region_connected_of_nonboundary (hM : M.IsConnectedMap) (C : M.Cycle)
    (R : Set M.Face) (hkeep : ∀ d ∈ C.val, M.regionKeeps R d)
    (hall : ∀ v, v ∉ C.val.map M.vert → M.regionVertexSet R v →
      ∀ d, M.vert d = v → M.regionKeeps R d) :
    (M.regionRotation R).toSimpleGraph.Connected := by
  obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  let base : M.RegionDart R := ⟨d0, hkeep d0 hd0⟩
  let N := M.regionRotation R
  have boundary (v : N.Vertex) (hv : v.val ∈ C.val.map M.vert) :
      N.toSimpleGraph.connectedComponentMk v = M.regionComponent R base := by
    obtain ⟨d, hd, htail⟩ := List.mem_map.mp hv
    let e : M.RegionDart R := ⟨d, hkeep d hd⟩
    have he : N.vert e = v := Subtype.ext htail
    rw [← he]
    exact M.cycle_region_component_eq_of_keeps C R hkeep e base hd hd0
  have path {u w : M.Vertex} (p : M.toSimpleGraph.Walk u w) :
      w = M.vert d0 → ∀ hu : M.regionVertexSet R u,
        N.toSimpleGraph.connectedComponentMk ⟨u, hu⟩ = M.regionComponent R base := by
    induction p with
    | nil =>
      intro hw hu
      exact boundary ⟨_, hu⟩ (List.mem_map.mpr ⟨d0, hd0, hw.symm⟩)
    | @cons u v w hadj p ih =>
      intro hw hu
      by_cases hb : u ∈ C.val.map M.vert
      · exact boundary ⟨u, hu⟩ hb
      · obtain ⟨hne, d, hd, hv⟩ := hadj
        have hk := hall u hb hu d hd
        let e : M.RegionDart R := ⟨d, hk⟩
        have hvR : M.regionVertexSet R v :=
          ⟨M.edgeInv d, (M.regionKeeps_inv R d).mpr hk, hv⟩
        have htail : N.vert e = ⟨u, hu⟩ := Subtype.ext hd
        have hhead : N.head e = ⟨v, hvR⟩ := Subtype.ext hv
        have hc := N.dart_component_eq_head e
        rw [htail, hhead] at hc
        exact hc.trans (ih hw hvR)
  let : Nonempty N.Vertex := ⟨N.vert base⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨pu⟩ := hM.preconnected u.val (M.vert d0)
  obtain ⟨pv⟩ := hM.preconnected v.val (M.vert d0)
  apply SimpleGraph.ConnectedComponent.exact
  exact (path pu rfl u.property).trans (path pv rfl v.property).symm

-- @node: SphereMap.cycleRightRotation_connected
/-- If [the map is a triangulation of the sphere](hyp:hM) and [a chosen face
lies outside the cycle's left region](hyp:hout), then [the underlying graph of
the restriction to the complement of that region is connected](goal). -/
lemma cycleRightRotation_connected (hM : IsSphereTriangulation M) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) :
    (M.regionRotation (M.leftRegion C)ᶜ).toSimpleGraph.Connected := by
  apply M.cycle_region_connected_of_nonboundary hM.props.1 C (M.leftRegion C)ᶜ
    (M.cycle_right_boundary_keeps hM.props.1 C outer hout)
  intro v hv hright d hd
  obtain ⟨f, hf, hvf⟩ := (M.regionVertexSet_iff_face_incidence hM _ v).mp hright
  have hvd : v ∈ M.faceVertices (M.faceOf d) := by
    rw [triangulation_faceVertices_eq_image M hM]
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hd⟩
  apply Or.inl
  intro hleft
  exact hf ((M.cycle_nonboundary_face_side hM C v hv (M.faceOf d) f hvd hvf).mp hleft)

-- @node: SphereMap.cycle_region_euler_eq
/-- If [the map is a triangulation of the sphere](hyp:hM) and [a chosen face
lies outside the cycle's left region](hyp:hout), then [the vertex count of the
left-region restriction plus the number of original faces in that region equals
the restricted edge count plus one](goal). -/
lemma cycle_region_euler_eq (hM : IsSphereTriangulation M) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) :
    Fintype.card (M.cycleLeftRotation C).Vertex +
      (Finset.univ.filter (fun f : M.Face => f ∈ M.leftRegion C)).card =
        Fintype.card (M.cycleLeftRotation C).Edge + 1 := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  let dl : M.RegionDart (M.leftRegion C) := ⟨M.edgeInv d, Or.inr (by
    rw [M.edgeInv_involutive]
    exact M.cycle_face_mem_leftRegion C d hd)⟩
  let dr : M.RegionDart (M.leftRegion C)ᶜ :=
    ⟨d, M.cycle_right_boundary_keeps hM.props.1 C outer hout d hd⟩
  have hleft := M.region_euler_upper_bound hM (M.leftRegion C)
    (M.cycleLeftRotation_connected hM C) dl
    (M.cycle_boundary_opposite_outside hM.props.1 C outer hout d hd)
  have hright := M.region_euler_upper_bound hM (M.leftRegion C)ᶜ
    (M.cycleRightRotation_connected hM C outer hout) dr
    (show M.faceOf dr.val ∉ (M.leftRegion C)ᶜ from
      fun hn => hn (M.cycle_face_mem_leftRegion C d hd))
  have hfaces : (Finset.univ.filter (fun f : M.Face => f ∈ M.leftRegion C)).card +
      (Finset.univ.filter (fun f : M.Face => f ∈ (M.leftRegion C)ᶜ)).card =
        Fintype.card M.Face := by
    simpa only [Finset.card_univ, Set.mem_compl_iff] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun f : M.Face => f ∈ M.leftRegion C))
  exact (two_sides_euler_squeeze _ _ _ _ _ _ _ _ _ _
    (M.connected_euler hM.props.1) (M.cycle_region_vertex_card_add hM C outer hout)
    (M.cycle_region_edge_card_add hM.props.1 C outer hout) hfaces hleft (by simpa only [Set.mem_compl_iff] using hright)).1

end SphereMap

namespace RotationSystem

-- @node: RotationSystem.componentEuler_of_connected_card
/-- If [a rotation system's underlying graph is connected](hyp:hR), [every vertex
is the tail of a directed edge](hyp:hd), and [its vertex count plus its facial
orbit count equals its edge count plus two](hyp:he), then [each connected
component satisfies the Euler identity: vertices plus local boundaries equal
edges plus two](goal). -/
lemma componentEuler_of_connected_card (R : RotationSystem)
    (hR : R.toSimpleGraph.Connected) (hd : ∀ v, ∃ d, R.vert d = v)
    (he : Fintype.card R.Vertex + Fintype.card R.FaceOrbit = Fintype.card R.Edge + 2) :
    R.componentEuler := by
  classical
  let : Subsingleton R.Component := hR.preconnected.subsingleton_connectedComponent
  let : IsEmpty R.Puncture := ⟨fun v => by
    obtain ⟨d, h⟩ := hd v.val
    exact v.property d h⟩
  intro K
  have fibre_card {α : Type} [Fintype α] (f : α → R.Component) :
      Fintype.card {a // f a = K} = Fintype.card α := by
    have h (a : α) : f a = K := Subsingleton.elim _ _
    simp [Fintype.card_subtype, h]
  change Fintype.card {v : R.Vertex // R.toSimpleGraph.connectedComponentMk v = K} +
    Fintype.card {b : R.LocalBoundary // R.compOf b = K} =
      Fintype.card {e : R.Edge // R.edgeComponent e = K} + 2
  rw [fibre_card, fibre_card, fibre_card]
  simpa only [LocalBoundary, Fintype.card_sum, Fintype.card_eq_zero,
    Nat.add_zero] using he

end RotationSystem

namespace SphereMap
variable (M : SphereMap)

-- @node: SphereMap.cycleLeftRotation_componentEuler
/-- If [the map is a triangulation of the sphere](hyp:hM) and [a chosen face
lies outside the cycle's left region](hyp:hout), then [each connected component
of the left-region restriction satisfies the Euler identity: vertices plus local
boundaries equal edges plus two](goal). -/
lemma cycleLeftRotation_componentEuler (hM : IsSphereTriangulation M) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) :
    (M.cycleLeftRotation C).componentEuler := by
  classical
  apply (M.cycleLeftRotation C).componentEuler_of_connected_card
    (M.cycleLeftRotation_connected hM C)
  · intro v
    obtain ⟨d, hd, hv⟩ := v.property
    exact ⟨⟨d, hd⟩, Subtype.ext hv⟩
  · obtain ⟨q, _⟩ := M.exists_cycle_face_orbit_equiv hM C outer hout
    have hc := Fintype.card_congr q
    rw [Fintype.card_sum, Fintype.card_subtype, Fintype.card_unit] at hc
    have he := M.cycle_region_euler_eq hM C outer hout
    omega

end SphereMap
end OaiPairedStatesHamiltonian
