module

public import Papers.OaiPairedStatesHamiltonian.Helpers.States

/-! Opposite edges of a pair are indexed bijectively by the black triangles. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false

open Classical
attribute [local instance] propDecidable
set_option linter.unusedVariables false

-- @node: faceDart_endpoints_incident
/-- In [a sphere triangulation](hyp:hT), [both endpoints of a directed edge belong to
the vertex set of its incident face](goal). -/
lemma faceDart_endpoints_incident (T : SphereMap) (hT : IsSphereTriangulation T)
    (d : T.Dart) : T.vert d ∈ T.faceVertices (T.faceOf d) ∧
      T.head d ∈ T.faceVertices (T.faceOf d) := by
  have ht : T.faceOf (T.facePerm d) = T.faceOf d := T.dual_rot_vertex d
  constructor
  · rw [triangulation_faceVertices_eq_image T hT]
    exact Finset.mem_image.mpr ⟨d, by simp [SphereMap.faceDarts], rfl⟩
  · rw [triangulation_faceVertices_eq_image T hT]
    exact Finset.mem_image.mpr ⟨T.facePerm d, by simp [SphereMap.faceDarts, ht],
      T.rot_vertex (T.edgeInv d)⟩

-- @node: black_face_of_edge_unique
/-- Suppose [the face coloring assigns different colors across every edge](hyp:hcol).
If [one face is black](hyp:hf), [another face is black](hyp:hg), and [a given edge lies
on the first face](hyp:hef) and [on the second face](hyp:heg), then
[the two faces are equal](goal). -/
lemma black_face_of_edge_unique (T : SphereMap) (col : T.Face → Bool)
    (hcol : PartitionColoring T col) (e : T.Edge) (f g : T.Face)
    (hf : col f = true) (hg : col g = true)
    (hef : T.edgeOnFace e f) (heg : T.edgeOnFace e g) : f = g := by
  obtain ⟨d, hd, rfl⟩ := hef
  obtain ⟨a, ha, rfl⟩ := heg
  rcases (T.edgeOf_eq_iff d a).mp (hd.trans ha.symm) with h | h
  · rw [h]
  · have hc := hcol d
    rw [h] at hg
    exact False.elim (hc (hf.trans hg.symm))

-- @node: faceVertices_eq_three
/-- In [a sphere triangulation](hyp:hT), suppose [the first vertex belongs to a given
face](hyp:ha), [the second vertex belongs to that face](hyp:hb), and [the third vertex
belongs to that face](hyp:hc),
with [the first two distinct](hyp:hab), [the third distinct from the first](hyp:hca), and
[the third distinct from the second](hyp:hcb). Then [the face's vertex set consists
exactly of these three vertices](goal). -/
lemma faceVertices_eq_three (T : SphereMap) (hT : IsSphereTriangulation T)
    (t : T.Face) (a b c : T.Vertex)
    (ha : a ∈ T.faceVertices t) (hb : b ∈ T.faceVertices t)
    (hc : c ∈ T.faceVertices t) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    T.faceVertices t = {a, b, c} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  · rw [(hT.props.2.2.2 t).2]
    simp [hab, Ne.symm hca, Ne.symm hcb]

-- @node: oppositeVertex
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT), [a face coloring](hyp:col),
[a designated outer face](hyp:t0), [two states assigning vertices to black nonouter
faces](hyp:r,s) that [choose distinct vertices on each such face](hyp:hp), and
[a black nonouter triangle](hyp:t), the [opposite vertex](goal) is the triangle's third
vertex, distinct from both state choices. -/
noncomputable def oppositeVertex (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face) (r s : State T col t0)
    (hp : IsPair T col t0 r s) (t : blackNonOuter T col t0) : T.Vertex :=
  (thirdVertex T hT t.val (r.val t).val (s.val t).val
    (r.property.incident t) (s.property.incident t) (pair_vertex_ne T col t0 r s hp t)).val

-- @node: oppositeVertex_spec
/-- In [a sphere triangulation](hyp:hT), if [the two states choose distinct vertices on
each black nonouter triangle](hyp:hp), then [the opposite vertex belongs to the given
triangle and differs from both vertices selected there by the states](goal). -/
lemma oppositeVertex_spec (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face) (r s : State T col t0)
    (hp : IsPair T col t0 r s) (t : blackNonOuter T col t0) :
    oppositeVertex T hT col t0 r s hp t ∈ T.faceVertices t.val ∧
    oppositeVertex T hT col t0 r s hp t ≠ (r.val t).val ∧
    oppositeVertex T hT col t0 r s hp t ≠ (s.val t).val :=
  (thirdVertex T hT t.val (r.val t).val (s.val t).val
    (r.property.incident t) (s.property.incident t) (pair_vertex_ne T col t0 r s hp t)).property

-- @node: oppositeEdge
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT), [a face coloring](hyp:col),
[a designated outer face](hyp:t0), [two states assigning vertices to black nonouter
faces](hyp:r,s) that [choose distinct vertices on each such face](hyp:hp), and
[a black nonouter triangle](hyp:t), the [opposite edge](goal) is the unordered pair
joining the first state's chosen vertex to the triangle's third vertex, opposite the
second state's chosen vertex. -/
noncomputable def oppositeEdge (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face) (r s : State T col t0)
    (hp : IsPair T col t0 r s) (t : blackNonOuter T col t0) : Sym2 T.Vertex :=
  s((r.val t).val, oppositeVertex T hT col t0 r s hp t)

-- @node: oppositeEdge_dart
/-- In [a sphere triangulation](hyp:hT), if [the two states choose distinct vertices on
each black nonouter triangle](hyp:hp), then [the opposite edge of a given such triangle
has a directed representative incident to that triangle, with neither endpoint equal
to the second state's chosen vertex](goal). -/
lemma oppositeEdge_dart (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face) (r s : State T col t0)
    (hp : IsPair T col t0 r s) (t : blackNonOuter T col t0) :
    ∃ d : T.Dart, T.faceOf d = t.val ∧ T.vert d ≠ (s.val t).val ∧
      T.head d ≠ (s.val t).val ∧ oppositeEdge T hT col t0 r s hp t = s(T.vert d, T.head d) := by
  have hu := oppositeVertex_spec T hT col t0 r s hp t
  let d := faceDart T hT t.val (r.val t).val (oppositeVertex T hT col t0 r s hp t)
    (r.property.incident t) hu.1 hu.2.1.symm
  have hd : FaceDart T t.val (r.val t).val (oppositeVertex T hT col t0 r s hp t) d :=
    Classical.choose_spec (exists_faceDart T hT t.val _ _ (r.property.incident t) hu.1 hu.2.1.symm)
  rcases hd.2.2 with hf | hf
  · exact ⟨d, hf, hd.1 ▸ pair_vertex_ne T col t0 r s hp t,
      hd.2.1 ▸ hu.2.2, by rw [hd.1, hd.2.1]; rfl⟩
  · refine ⟨T.edgeInv d, hf, ?_, ?_, ?_⟩
    · change T.head d ≠ (s.val t).val
      rw [hd.2.1]
      exact hu.2.2
    · change T.vert (T.edgeInv (T.edgeInv d)) ≠ (s.val t).val
      rw [T.edgeInv_involutive, hd.1]
      exact pair_vertex_ne T col t0 r s hp t
    · change s((r.val t).val, oppositeVertex T hT col t0 r s hp t) =
        s(T.head d, T.vert (T.edgeInv (T.edgeInv d)))
      rw [T.edgeInv_involutive, hd.1, hd.2.1, Sym2.eq_swap]

-- @node: oppositeEdge_injective
/-- In [a sphere triangulation](hyp:hT) with [different face colors across every
edge](hyp:hcol), if [two states choose distinct vertices on every black nonouter
triangle](hyp:hp), then [distinct black nonouter triangles have distinct opposite edges](goal). -/
lemma oppositeEdge_injective (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r s : State T col t0) (hp : IsPair T col t0 r s) :
    Function.Injective (oppositeEdge T hT col t0 r s hp) := by
  intro t u he
  obtain ⟨d, hd, _, _, hed⟩ := oppositeEdge_dart T hT col t0 r s hp t
  obtain ⟨a, ha, _, _, hea⟩ := oppositeEdge_dart T hT col t0 r s hp u
  have heda := hT.props.2.1.2 d a (hed.symm.trans (he.trans hea))
  apply Subtype.ext
  exact black_face_of_edge_unique T (normalizedColoring T col t0)
    (normalizedColoring_partition T col hcol t0) (T.edgeOf d) t.val u.val
    (Finset.mem_filter.mp t.property).2.1 (Finset.mem_filter.mp u.property).2.1
    ⟨d, rfl, hd⟩ ⟨a, heda.symm, ha⟩

-- @node: oppositeEdge_mem
/-- In [a sphere triangulation](hyp:hT), if [two states choose distinct vertices on every
black nonouter triangle](hyp:hp), then [the opposite edge of each such triangle belongs
to the opposite-edge graph associated with the second state](goal). -/
lemma oppositeEdge_mem (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face) (r s : State T col t0)
    (hp : IsPair T col t0 r s) (t : blackNonOuter T col t0) :
    oppositeEdge T hT col t0 r s hp t ∈ (Qs T col t0 s).edgeSet := by
  obtain ⟨d, hd, hv, hw, he⟩ := oppositeEdge_dart T hT col t0 r s hp t
  change (Qs T col t0 s).Adj (r.val t).val (oppositeVertex T hT col t0 r s hp t)
  rw [Qs, SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨t, d, hd, hv, hw, he⟩, (oppositeVertex_spec T hT col t0 r s hp t).2.1.symm⟩

-- @node: oppositeEdge_surjective
/-- In [a sphere triangulation](hyp:hT), suppose [two states choose distinct vertices on
every black nonouter triangle](hyp:hp). If [an unordered vertex pair is an edge of the
second state's opposite-edge graph](hyp:he), then [it is the opposite edge of some
black nonouter triangle](goal). -/
lemma oppositeEdge_surjective (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (t0 : T.Face) (r s : State T col t0)
    (hp : IsPair T col t0 r s) (e : Sym2 T.Vertex) (he : e ∈ (Qs T col t0 s).edgeSet) :
    ∃ t, oppositeEdge T hT col t0 r s hp t = e := by
  induction e using Sym2.ind with
  | _ v w =>
    simp only [SimpleGraph.mem_edgeSet, Qs, SimpleGraph.fromEdgeSet_adj,
      Set.mem_ofPred_eq] at he
    obtain ⟨⟨t, d, hd, hv, hw, hed⟩, hne⟩ := he
    have hends := faceDart_endpoints_incident T hT d
    rw [hd, faceVertices_eq_three T hT t.val _ _ _
      (r.property.incident t) (s.property.incident t)
      (oppositeVertex_spec T hT col t0 r s hp t).1
      (pair_vertex_ne T col t0 r s hp t)
      (oppositeVertex_spec T hT col t0 r s hp t).2.1
      (oppositeVertex_spec T hT col t0 r s hp t).2.2] at hends
    simp only [Finset.mem_insert, Finset.mem_singleton] at hends
    have hdne := hT.props.2.1.1 d
    refine ⟨t, hed.trans ?_ |>.symm⟩
    rcases hends.1 with h | h | h <;> rcases hends.2 with k | k | k
    all_goals first
      | exact False.elim (hv h)
      | exact False.elim (hw k)
      | exact False.elim (hdne (h.trans k.symm))
      | (rw [h, k]; rfl)
      | (rw [h, k]; exact Sym2.eq_swap)

set_option backward.isDefEq.respectTransparency false in
-- @node: qs_component_root_count_by_edges
/-- In [a sphere triangulation](hyp:hT) with [different face colors across every
edge](hyp:hcol), suppose [two states choose distinct vertices on every black nonouter
triangle](hyp:hpair) and [the second state's opposite-edge graph is a forest](hyp:hforest).
Then [each connected component contains exactly one outer-face vertex and has one
fewer induced edges than vertices](goal). -/
lemma qs_component_root_count_by_edges (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s)
    (component : (Qs T col t0 s).ConnectedComponent) :
    let KV := Finset.univ.filter (fun v => (Qs T col t0 s).connectedComponentMk v = component)
    let q := KV.card -- @realizes q(number of vertices in an opposite-edge component)
    let a := (KV ∩ roots T t0).card -- @realizes a(number of roots in that component)
    a = 1 ∧ ((Qs T col t0 s).induce {v | v ∈ KV}).edgeFinset.card = q - 1 := by
  let G := Qs T col t0 s
  let KV := Finset.univ.filter (fun v => G.connectedComponentMk v = component)
  let A := (Finset.univ : Finset (blackNonOuter T col t0)).filter
    (fun t => (r.val t).val ∈ KV)
  let E := A.image (oppositeEdge T hT col t0 r s hpair)
  let H := G.induce {v | v ∈ KV}
  have hcomponent : {v | v ∈ KV} = component.supp := by
    ext v
    simp [KV, G, SimpleGraph.ConnectedComponent.mem_supp_iff]
  -- A forest component has one fewer edge than vertices.
  have htree : H.IsTree := by
    change (G.induce {v | v ∈ KV}).IsTree
    rw [hcomponent]
    exact hforest.isTree_connectedComponent component
  have htreecard := htree.card_edgeFinset
  have hvertices : Fintype.card {v // v ∈ KV} = KV.card := Fintype.card_coe _
  -- The incident black triangles index exactly the edges in this component.
  have hedge : H.edgeFinset.card = E.card := by
    have hm := SimpleGraph.map_edgeFinset_induce (G := G) (s := {v | v ∈ KV})
    have heq : G.edgeFinset ∩ KV.sym2 = E := by
      ext e
      induction e using Sym2.ind with
      | _ v w =>
        simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, Finset.mem_sym2_iff,
          Sym2.ball, E, Finset.mem_image]
        constructor
        · rintro ⟨he, hv, hw⟩
          obtain ⟨t, ht⟩ := oppositeEdge_surjective T hT col t0 r s hpair s(v, w) he
          refine ⟨t, ?_, ht⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          have hr : (r.val t).val ∈ s(v, w) := by
            rw [← ht]
            exact Sym2.mem_mk_left _ _
          rcases Sym2.mem_iff.mp hr with h | h
          · exact h ▸ hv
          · exact h ▸ hw
        · rintro ⟨t, htA, ht⟩
          have hr := (Finset.mem_filter.mp htA).2
          have ha : G.Adj (r.val t).val (oppositeVertex T hT col t0 r s hpair t) :=
            oppositeEdge_mem T hT col t0 r s hpair t
          have hc := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha
          have hu : oppositeVertex T hT col t0 r s hpair t ∈ KV := by
            simp only [KV, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            exact hc.symm.trans hr
          refine ⟨ht ▸ oppositeEdge_mem T hT col t0 r s hpair t, ?_⟩
          change s((r.val t).val, oppositeVertex T hT col t0 r s hpair t) = s(v, w) at ht
          rcases Sym2.eq_iff.mp ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hr, hu⟩
          · exact ⟨hu, hr⟩
    have hc := congrArg Finset.card hm
    rw [Finset.card_map] at hc
    have hc' : H.edgeFinset.card = (G.edgeFinset ∩ KV.sym2).card := by
      convert hc using 1 <;> congr 1 <;> ext e <;> simp [H]
    exact hc'.trans (congrArg Finset.card heq)
  have hE : E.card = A.card :=
    Finset.card_image_iff.mpr (oppositeEdge_injective T hT col hcol t0 r s hpair).injOn
  -- The state bijection indexes these triangles by the component's nonroots.
  have hA : A.card = (KV \ roots T t0).card := by
    apply Finset.card_bij (fun t _ => (r.val t).val)
    · intro t ht
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp ht).2,
        (Finset.mem_sdiff.mp (r.val t).property).2⟩
    · intro t ht u hu heq
      exact r.property.bijective.injective (Subtype.ext heq)
    · intro v hv
      have hvX : v ∈ nonRoot T t0 := by
        simp only [nonRoot, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact (Finset.mem_sdiff.mp hv).2
      obtain ⟨t, ht⟩ := r.property.bijective.surjective ⟨v, hvX⟩
      refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, congrArg Subtype.val ht⟩
      rw [congrArg Subtype.val ht]
      exact (Finset.mem_sdiff.mp hv).1
  have hsplit := Finset.card_sdiff_add_card_inter KV (roots T t0)
  change (KV ∩ roots T t0).card = 1 ∧ H.edgeFinset.card = KV.card - 1
  have htreecard' : H.edgeFinset.card + 1 = KV.card := htreecard.trans hvertices
  constructor
  · rw [hedge, hE, hA] at htreecard'
    omega
  · omega

end OaiPairedStatesHamiltonian
