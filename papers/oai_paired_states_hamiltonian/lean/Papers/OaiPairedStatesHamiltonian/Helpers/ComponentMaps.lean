module

public import Papers.OaiPairedStatesHamiltonian.Helpers.InducedMaps

/-! Component embeddings and the correspondence with their original local boundaries. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable

namespace SphereMap
variable (M : SphereMap)

/-- For [a sphere map](hyp:M) and [one of its connected components](hyp:K),
the [component map](goal) is the sphere map induced by the vertices in that component. -/
noncomputable def componentMap (K : M.Component) : SphereMap :=
  M.induce {v | M.toSimpleGraph.connectedComponentMk v = K}
-- @node: SphereMap.componentMap_connected
/-- For a sphere map and [one of its connected components](hyp:K),
[the induced component map is connected](goal). -/
lemma componentMap_connected (K : M.Component) : (M.componentMap K).IsConnectedMap := by
  change (M.induce {v | M.toSimpleGraph.connectedComponentMk v = K}).toSimpleGraph.Connected
  rw [M.induce_toSimpleGraph]
  exact K.connected_toSimpleGraph
/-- For [a sphere map](hyp:M), [a connected component](hyp:K), and [a face](hyp:outer),
the [boundary behind the face](goal) is the unique local boundary of that component
whose incident face can be joined to the chosen face in the placement graph
without passing through the component. -/
noncomputable def boundaryBehind (K : M.Component) (outer : M.Face) :
    {b : M.LocalBoundary // M.compOf b = K} :=
  ⟨Classical.choose (M.faceBehind_existsUnique K outer),
    (Classical.choose_spec (M.faceBehind_existsUnique K outer)).1.1⟩

-- @node: SphereMap.boundaryBehind_eq_of_faceBehind
/-- In a sphere map, take [a connected component](hyp:K), [a face](hyp:f),
and [a local boundary](hyp:b). If [the boundary belongs to the component and its
incident face can reach the chosen face without passing through that component
in the placement graph](hyp:hb), then [it equals the boundary behind that face](goal). -/
lemma boundaryBehind_eq_of_faceBehind (K : M.Component) (f : M.Face)
    (b : M.LocalBoundary) (hb : M.FaceBehind K b f) :
    (M.boundaryBehind K f).val = b := by
  exact (M.faceBehind_existsUnique K f).unique
    (Classical.choose_spec (M.faceBehind_existsUnique K f)).1 hb

-- @node: SphereMap.boundaryBehind_across_deleted
/-- In a sphere map, for [a connected component](hyp:K) and [a directed
edge](hyp:d), if [its endpoints do not both belong to the component](hyp:hd), then
[the faces on its two sides have the same boundary behind them in that component](goal). -/
lemma boundaryBehind_across_deleted (K : M.Component) (d : M.Dart)
    (hd : ¬ (M.toSimpleGraph.connectedComponentMk (M.vert d) = K ∧
      M.toSimpleGraph.connectedComponentMk (M.head d) = K)) :
    M.boundaryBehind K (M.faceOf d) = M.boundaryBehind K (M.faceOf (M.edgeInv d)) := by
  have hne : M.toSimpleGraph.connectedComponentMk (M.vert d) ≠ K := by
    intro h
    exact hd ⟨h, (M.toRotationSystem.dart_component_eq_head d).symm.trans h⟩
  have hb := (Classical.choose_spec (M.faceBehind_existsUnique K (M.faceOf d))).1
  apply Subtype.ext
  symm
  apply M.boundaryBehind_eq_of_faceBehind
  refine ⟨hb.1, ?_⟩
  apply Relation.ReflTransGen.tail (b := Sum.inl
    (M.toSimpleGraph.connectedComponentMk (M.vert d)))
    (Relation.ReflTransGen.tail hb.2 ?_) ?_
  · refine ⟨by simp, ?_, ?_⟩
    · exact fun h => hne (Sum.inl.inj h)
    · exact ⟨Sum.inl (orbitOf M.facePerm d), rfl, rfl⟩
  · refine ⟨?_, by simp, ?_⟩
    · exact fun h => hne (Sum.inl.inj h)
    · refine ⟨Sum.inl (orbitOf M.facePerm (M.edgeInv d)), ?_, rfl⟩
      exact (M.toRotationSystem.dart_component_eq_head d).symm

-- @node: SphereMap.componentEdgeEquiv
/-- For [a sphere map](hyp:M) and [a connected component](hyp:K), the
[component edge correspondence](goal) is a bijection between edges of the induced
component map and original edges belonging to that component. -/
noncomputable def componentEdgeEquiv (K : M.Component) :
    (M.componentMap K).Edge ≃ {e : M.Edge // M.edgeComponent e = K} := by
  let U := {v | M.toSimpleGraph.connectedComponentMk v = K}
  let f : (M.componentMap K).Edge → {e : M.Edge // M.edgeComponent e = K} := fun e =>
    ⟨M.inducedEdgeMap U e, by
      induction e using Quotient.inductionOn with
      | h d => exact d.property.1⟩
  apply Equiv.ofBijective f
  constructor
  · intro e g h
    exact M.inducedEdgeMap_injective U (congrArg Subtype.val h)
  · rintro ⟨e, he⟩
    induction e using Quotient.inductionOn with
    | h d =>
      have hd : M.toSimpleGraph.connectedComponentMk (M.vert d) = K := he
      let a : M.KeptDart U := ⟨d, hd,
        (M.toRotationSystem.dart_component_eq_head d).symm.trans hd⟩
      exact ⟨(M.componentMap K).edgeOf a, Subtype.ext rfl⟩

-- @node: SphereMap.component_face_card
/-- For a sphere map and [a connected component](hyp:K),
[the number of faces of the induced component map equals the number of original
local boundaries belonging to that component](goal). -/
lemma component_face_card (K : M.Component) :
    Fintype.card (M.componentMap K).Face =
      Fintype.card {b : M.LocalBoundary // M.compOf b = K} := by
  let N := M.componentMap K
  let : Nonempty N.Vertex := (M.componentMap_connected K).nonempty
  let : Subsingleton N.Component :=
    (M.componentMap_connected K).preconnected.subsingleton_connectedComponent
  let : Unique N.Component := uniqueOfSubsingleton
    (N.toSimpleGraph.connectedComponentMk (Classical.arbitrary N.Vertex))
  have hc : Fintype.card N.Component = 1 := Fintype.card_unique
  have he := N.global_euler
  rw [hc] at he
  have hm := M.genusZero K
  have hv : Fintype.card N.Vertex =
      Fintype.card {v : M.Vertex // M.toSimpleGraph.connectedComponentMk v = K} := rfl
  have hedge := Fintype.card_congr (M.componentEdgeEquiv K)
  change Fintype.card N.Edge = _ at hedge
  rw [← hv, ← hedge] at hm
  change Fintype.card N.Face = _
  apply Nat.add_left_cancel (n := Fintype.card N.Vertex)
  calc
    _ = Fintype.card N.Edge + 2 := by simpa only [Nat.add_assoc] using he
    _ = _ := hm.symm

-- @node: SphereMap.exists_componentFaceEquiv
/-- For a sphere map and [a connected component](hyp:K), [there is a
bijection from faces of the induced component map to original local boundaries
of the component, such that each original face lies behind the boundary assigned
to its induced face class](goal). -/
lemma exists_componentFaceEquiv (K : M.Component) :
    ∃ q : (M.componentMap K).Face ≃ {b : M.LocalBoundary // M.compOf b = K},
      ∀ f : M.Face, M.FaceBehind K (q (M.inducedFaceClass _ f)).val f := by
  let U := {v | M.toSimpleGraph.connectedComponentMk v = K}
  have invariant (f g : M.Face) (h : Relation.EqvGen (M.inducedFaceRelation U) f g) :
      M.boundaryBehind K f = M.boundaryBehind K g := by
    induction h with
    | rel f g h =>
      obtain ⟨d, hd, rfl, rfl⟩ := h
      exact M.boundaryBehind_across_deleted K d hd
    | refl => rfl
    | symm f g h ih => exact ih.symm
    | trans f g k h h' ih ih' => exact ih.trans ih'
  let q : (M.componentMap K).Face → {b : M.LocalBoundary // M.compOf b = K} :=
    Quotient.lift (M.boundaryBehind K) invariant
  have hsurj : Function.Surjective q := by
    intro b
    refine ⟨M.inducedFaceClass U (M.boundaryFace b.val), ?_⟩
    apply Subtype.ext
    exact M.boundaryBehind_eq_of_faceBehind K _ b.val ⟨b.property, .refl⟩
  let e := Equiv.ofBijective q
    ((Fintype.bijective_iff_surjective_and_card q).mpr ⟨hsurj, M.component_face_card K⟩)
  exact ⟨e, fun f => (Classical.choose_spec (M.faceBehind_existsUnique K f)).1⟩
/-- For [a sphere map](hyp:M) and [a connected component](hyp:K), the
[component face correspondence](goal) is a chosen bijection from induced faces
to original local boundaries of that component, assigning to each original face's
induced class the boundary behind that face. -/
noncomputable def componentFaceEquiv (K : M.Component) :
    (M.componentMap K).Face ≃ {b : M.LocalBoundary // M.compOf b = K} :=
  Classical.choose (M.exists_componentFaceEquiv K)
/-- For [a sphere map](hyp:M), [a connected component](hyp:K), and [a chosen outer
face](hyp:outer), the [component outer face](goal) is the induced face corresponding
to the component's local boundary behind the chosen outer face. -/
noncomputable def componentOuter (K : M.Component) (outer : M.Face) : (M.componentMap K).Face :=
  (M.componentFaceEquiv K).symm (M.boundaryBehind K outer)

-- @node: SphereMap.component_cycle_isSimple
/-- For a sphere map, [a connected component](hyp:K), and [a cycle in its
induced map](hyp:C), [the same directed edges form a simple cycle in the original
map](goal). -/
lemma component_cycle_isSimple (K : M.Component) (C : (M.componentMap K).Cycle) :
    M.IsSimpleCycle (C.val.map Subtype.val) := by
  exact M.induce_cycle_isSimple _ C
/-- For [a sphere map](hyp:M), [a connected component](hyp:K), and [a cycle in its
induced map](hyp:C), the [corresponding original cycle](goal) consists of the same
directed edges viewed in the original map. -/
noncomputable def ofComponentCycle (K : M.Component) (C : (M.componentMap K).Cycle) : M.Cycle :=
  ⟨C.val.map Subtype.val, M.component_cycle_isSimple K C⟩
-- @node: SphereMap.componentBoundaryEquiv
/-- For [a sphere map](hyp:M) and [a connected component](hyp:K), the
[component boundary correspondence](goal) is a bijection from local boundaries
of the induced map to original local boundaries belonging to the component,
obtained by identifying induced boundaries with induced faces and then with
original boundaries. -/
noncomputable def componentBoundaryEquiv (K : M.Component) :
    (M.componentMap K).LocalBoundary ≃ {b : M.LocalBoundary // M.compOf b = K} := by
  let N := M.componentMap K
  let : Nonempty N.Vertex := (M.componentMap_connected K).nonempty
  have hinj : Function.Injective N.boundaryFace := by
    intro b c h
    exact N.boundary_unique_in_component b c
      ((M.componentMap_connected K).preconnected.subsingleton_connectedComponent.elim _ _) h
  exact (Equiv.ofBijective N.boundaryFace ⟨hinj, N.face_has_boundary⟩).trans
    (M.componentFaceEquiv K)

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.componentBoundaryEquiv_dart
/-- For a sphere map, [a connected component](hyp:K), and [a directed edge
in the induced component map](hyp:d), [the boundary traced by that edge in the
induced map corresponds to the boundary traced by the same edge in the original
map](goal). -/
lemma componentBoundaryEquiv_dart (K : M.Component) (d : (M.componentMap K).Dart) :
    (M.componentBoundaryEquiv K (Sum.inl (orbitOf (M.componentMap K).facePerm d))).val =
      Sum.inl (orbitOf M.facePerm d.val) := by
  change (M.componentFaceEquiv K ((M.componentMap K).faceOf d)).val = _
  have hd : (M.componentMap K).faceOf d = M.inducedFaceClass _ (M.faceOf d.val) :=
    M.inducedBoundaryFace_dart _ d
  rw [hd]
  have h := (Classical.choose_spec (M.exists_componentFaceEquiv K)) (M.faceOf d.val)
  apply (M.faceBehind_existsUnique K (M.faceOf d.val)).unique h
  exact ⟨d.property.1, .refl⟩

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.component_cycle_edge_mem
/-- For a sphere map, [a connected component](hyp:K), [a cycle in the
induced map](hyp:C), and [a directed edge of that map](hyp:d), [the edge belongs
to the induced cycle exactly when its original edge belongs to the corresponding
original cycle](goal). -/
lemma component_cycle_edge_mem (K : M.Component) (C : (M.componentMap K).Cycle)
    (d : (M.componentMap K).Dart) :
    (M.componentMap K).edgeOf d ∈ C.val.map (M.componentMap K).edgeOf ↔
      M.edgeOf d.val ∈ (M.ofComponentCycle K C).val.map M.edgeOf := by
  change _ ↔ M.edgeOf d.val ∈ (C.val.map Subtype.val).map M.edgeOf
  rw [List.map_map]
  simp only [List.mem_map, Function.comp_apply]
  constructor
  · rintro ⟨e, he, hed⟩
    exact ⟨e, he, congrArg (M.inducedEdgeMap _) hed⟩
  · rintro ⟨e, he, hed⟩
    exact ⟨e, he, M.inducedEdgeMap_injective _ hed⟩

/- A path avoiding the cycle lifts because restriction retains every dart of a component. -/
set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.component_joined_avoiding_iff
/-- For a sphere map, [a connected component](hyp:K), [a cycle in the
induced map](hyp:C), and [two local boundaries of that map](hyp:b,c), [the boundaries
can be joined without crossing the cycle in the induced map exactly when their
corresponding original boundaries can be joined without crossing the corresponding
original cycle](goal). -/
lemma component_joined_avoiding_iff (K : M.Component) (C : (M.componentMap K).Cycle)
    (b c : (M.componentMap K).LocalBoundary) :
    (M.componentMap K).localBoundariesJoinedAvoiding C.val b c ↔
      M.localBoundariesJoinedAvoiding (M.ofComponentCycle K C).val
        (M.componentBoundaryEquiv K b).val (M.componentBoundaryEquiv K c).val := by
  let N := M.componentMap K
  let q := M.componentBoundaryEquiv K
  have qinj : Function.Injective (fun b => (q b).val) := by
    intro b c h
    exact q.injective (Subtype.ext h)
  have qdart (d : N.Dart) := M.componentBoundaryEquiv_dart K d
  have inv (d : N.Dart) : (N.edgeInv d).val = M.edgeInv d.val :=
    Classical.choose_spec (M.exists_inducedInv _) d
  constructor
  · intro h
    apply Relation.ReflTransGen.lift (fun b => (q b).val) ?_ _ _ h
    intro a b hab
    obtain ⟨d, hd, rfl, rfl⟩ := hab
    refine ⟨d.val, ?_, (qdart d).symm, ?_⟩
    · exact fun he => hd ((M.component_cycle_edge_mem K C d).mpr he)
    · exact ((qdart (N.edgeInv d)).trans (congrArg
        (fun d => Sum.inl (orbitOf M.facePerm d)) (inv d))).symm
  · intro h
    have lift_path {a : M.LocalBoundary}
        (h : M.localBoundariesJoinedAvoiding (M.ofComponentCycle K C).val (q b).val a) :
        ∀ c, (q c).val = a → N.localBoundariesJoinedAvoiding C.val b c := by
      induction h with
      | refl =>
        intro c hc
        exact qinj hc ▸ Relation.ReflTransGen.refl
      | @tail a z h step ih =>
        intro c hc
        obtain ⟨d, hd, ha, hz⟩ := step
        have hK : M.toSimpleGraph.connectedComponentMk (M.vert d) = K := by
          have he := M.localBoundariesJoinedAvoiding_compOf _ _ _ h
          rw [← ha] at he
          exact he.symm.trans (q b).property
        let e : N.Dart := ⟨d, hK,
          (M.toRotationSystem.dart_component_eq_head d).symm.trans hK⟩
        have he : (q (Sum.inl (orbitOf N.facePerm e))).val = a := (qdart e).trans ha
        have hc' : Sum.inl (orbitOf N.facePerm (N.edgeInv e)) = c := by
          apply qinj
          exact (qdart (N.edgeInv e)).trans ((congrArg
            (fun d => Sum.inl (orbitOf M.facePerm d)) (inv e)).trans (hz.trans hc.symm))
        rw [← hc']
        exact (ih _ he).tail ⟨e, fun hm => hd ((M.component_cycle_edge_mem K C e).mp hm),
          rfl, rfl⟩
    exact lift_path h c rfl

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.component_leftLocalRegion_iff
/-- For a sphere map, [a connected component](hyp:K), [a cycle in the
induced map](hyp:C), and [a local boundary of that map](hyp:b), [the boundary lies
in the cycle's left local region exactly when its corresponding original boundary
lies in the left local region of the corresponding original cycle](goal). -/
lemma component_leftLocalRegion_iff (K : M.Component) (C : (M.componentMap K).Cycle)
    (b : (M.componentMap K).LocalBoundary) :
    b ∈ (M.componentMap K).leftLocalRegion C ↔
      (M.componentBoundaryEquiv K b).val ∈ M.leftLocalRegion (M.ofComponentCycle K C) := by
  constructor
  · rintro ⟨d, hd, hp⟩
    refine ⟨d.val, List.mem_map.mpr ⟨d, hd, rfl⟩, ?_⟩
    rw [← M.componentBoundaryEquiv_dart K d]
    exact (M.component_joined_avoiding_iff K C _ b).mp hp
  · rintro ⟨d, hd, hp⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    refine ⟨e, he, ?_⟩
    apply (M.component_joined_avoiding_iff K C _ b).mpr
    rwa [M.componentBoundaryEquiv_dart]

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.counterclockwise_iff_boundaryBehind
/-- For a sphere map, [a connected component](hyp:K), [a chosen outer
face](hyp:outer), and [a cycle](hyp:C), suppose [every directed edge of the cycle
starts in that component](hyp:hK). Then [the cycle is counterclockwise relative
to the outer face exactly when the component's boundary behind that face lies
outside the cycle's left local region](goal). -/
lemma counterclockwise_iff_boundaryBehind (K : M.Component) (outer : M.Face) (C : M.Cycle)
    (hK : ∀ d ∈ C.val, M.toSimpleGraph.connectedComponentMk (M.vert d) = K) :
    M.IsCounterclockwise outer C ↔ (M.boundaryBehind K outer).val ∉ M.leftLocalRegion C := by
  constructor
  · rintro ⟨b, ⟨⟨d, hd, hb⟩, hn⟩, hf⟩
    have hbK := hb.trans (hK d hd)
    have hbehind : M.FaceBehind K b outer := by simpa only [hbK] using hf
    rwa [M.boundaryBehind_eq_of_faceBehind K outer b hbehind]
  · intro hn
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
    have hb := (Classical.choose_spec (M.faceBehind_existsUnique K outer)).1
    refine ⟨(M.boundaryBehind K outer).val, ⟨⟨d, hd, ?_⟩, hn⟩, ?_⟩
    · exact (M.boundaryBehind K outer).property.trans (hK d hd).symm
    · rw [(M.boundaryBehind K outer).property]
      exact hb

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.connected_counterclockwise_iff_boundary
/-- For a sphere map that [is connected](hyp:hM), take [a chosen outer
face](hyp:outer), [a cycle](hyp:C), and [a local boundary](hyp:b) whose [incident
face is the outer face](hyp:hb). Then [the cycle is counterclockwise relative to
that outer face exactly when the boundary lies outside the cycle's left local
region](goal). -/
lemma connected_counterclockwise_iff_boundary (hM : M.IsConnectedMap)
    (outer : M.Face) (C : M.Cycle) (b : M.LocalBoundary) (hb : M.boundaryFace b = outer) :
    M.IsCounterclockwise outer C ↔ b ∉ M.leftLocalRegion C := by
  let K := M.compOf b
  have he : (M.boundaryBehind K outer).val = b :=
    M.boundaryBehind_eq_of_faceBehind K outer b ⟨rfl, hb ▸ Relation.ReflTransGen.refl⟩
  rw [M.counterclockwise_iff_boundaryBehind K outer C (fun d hd =>
    hM.preconnected.subsingleton_connectedComponent.elim _ _), he]

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.component_cycle_orientation
/-- For a sphere map, [a connected component](hyp:K), [a chosen outer
face](hyp:outer), and [a cycle in the induced component map](hyp:C), [the induced
cycle is counterclockwise relative to the component outer face exactly when the
corresponding original cycle is counterclockwise relative to the chosen original
outer face](goal). -/
lemma component_cycle_orientation (K : M.Component) (outer : M.Face)
    (C : (M.componentMap K).Cycle) :
    (M.componentMap K).IsCounterclockwise (M.componentOuter K outer) C ↔
      M.IsCounterclockwise outer (M.ofComponentCycle K C) := by
  let N := M.componentMap K
  let q := M.componentBoundaryEquiv K
  let b := q.symm (M.boundaryBehind K outer)
  have hq : q b = M.boundaryBehind K outer := q.apply_symm_apply _
  have hb : N.boundaryFace b = M.componentOuter K outer := by
    apply (M.componentFaceEquiv K).injective
    exact hq.trans ((M.componentFaceEquiv K).apply_symm_apply _).symm
  rw [N.connected_counterclockwise_iff_boundary (M.componentMap_connected K) _ C b hb,
    M.counterclockwise_iff_boundaryBehind K outer (M.ofComponentCycle K C) ?_]
  · rw [← hq]
    exact not_congr (M.component_leftLocalRegion_iff K C b)
  · intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact e.property.1
-- @node: SphereMap.cycle_in_component
/-- For a sphere map and [a cycle in it](hyp:C), [there is a connected
component and a cycle in its induced map whose corresponding original cycle is
the given cycle](goal). -/
lemma cycle_in_component (C : M.Cycle) :
    ∃ K : M.Component, ∃ D : (M.componentMap K).Cycle, M.ofComponentCycle K D = C := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  let K := M.toSimpleGraph.connectedComponentMk (M.vert d)
  have hK (e : M.Dart) (he : e ∈ C.val) :
      M.toSimpleGraph.connectedComponentMk (M.vert e) = K :=
    M.cycle_component_eq C e d he hd
  obtain ⟨D, hD⟩ := M.induce_cycle_of_mem
    {v | M.toSimpleGraph.connectedComponentMk v = K} C (by
      intro e he
      exact ⟨hK e he, (M.toRotationSystem.dart_component_eq_head e).symm.trans (hK e he)⟩)
  exact ⟨K, D, Subtype.ext hD⟩
-- @node: SphereMap.head_component
/-- For a sphere map and [a directed edge](hyp:d), [the head and the
starting vertex of the edge belong to the same connected component](goal). -/
lemma head_component (d : M.Dart) :
    M.toSimpleGraph.connectedComponentMk (M.head d) = M.toSimpleGraph.connectedComponentMk (M.vert d) := by
  by_cases h : M.vert d = M.head d
  · exact congrArg M.toSimpleGraph.connectedComponentMk h.symm
  · exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := M.toSimpleGraph) ⟨h, d, rfl, rfl⟩).symm
/-- For [a sphere map](hyp:M) and [a directed edge](hyp:d), the [component directed
edge](goal) is that same edge viewed in the map induced by the connected component
of its starting vertex. -/
noncomputable def componentDart (d : M.Dart) :
    (M.componentMap (M.toSimpleGraph.connectedComponentMk (M.vert d))).Dart :=
  ⟨d, rfl, M.head_component d⟩

end SphereMap

end OaiPairedStatesHamiltonian
