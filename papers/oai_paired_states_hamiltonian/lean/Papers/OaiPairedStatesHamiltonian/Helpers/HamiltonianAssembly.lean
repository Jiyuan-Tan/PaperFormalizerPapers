module

public import Papers.OaiPairedStatesHamiltonian.Helpers.EdgeCuts
public import Papers.OaiPairedStatesHamiltonian.Helpers.TrianglePartitionMatching

/-! From an induced tree partition to complementary Hamiltonian cycles. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

-- @node: isAcyclic_of_induced_partition
/-- If [every edge of the subgraph belongs to the original graph](hyp:hle),
[each subgraph edge has both endpoints on the same side of the vertex partition](hyp:hside),
and the original graph induces acyclic graphs [on the chosen vertices](hyp:hU)
and [on their complement](hyp:hUc), then [the subgraph is acyclic](goal). -/
lemma isAcyclic_of_induced_partition {V : Type} (G H : SimpleGraph V) (U : Set V)
    (hle : H ≤ G) (hside : ∀ u v, H.Adj u v → (u ∈ U ↔ v ∈ U))
    (hU : (G.induce U).IsAcyclic) (hUc : (G.induce Uᶜ).IsAcyclic) : H.IsAcyclic := by
  classical
  have support_side {u v : V} (p : H.Walk u v) :
      ∀ w ∈ p.support, (w ∈ U ↔ u ∈ U) := by
    induction p with
    | nil => simp
    | @cons u v w huv p ih =>
      intro x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact (ih x hx).trans (hside u v huv).symm
  intro u p hp
  have lift_cycle (S : Set V) (hs : ∀ w ∈ p.support, w ∈ S)
      (ha : (G.induce S).IsAcyclic) : False := by
    let q := (p.mapLe hle).induce S (by simpa using hs)
    apply ha q
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce S).toHom)
    simpa only [q, SimpleGraph.Walk.map_induce] using hp.mapLe hle
  by_cases hu : u ∈ U
  · exact lift_cycle U (fun w hw => (support_side p w hw).mpr hu) hU
  · exact lift_cycle Uᶜ (fun w hw hwu => hu ((support_side p w hw).mp hwu)) hUc

-- @node: exists_hamiltonianCycle_of_connected_degree_two
/-- A finite graph that [is connected](hyp:hc) and [has exactly two neighbors at
every vertex](hyp:hdeg) [has a cycle visiting every vertex exactly once](goal). -/
lemma exists_hamiltonianCycle_of_connected_degree_two {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (hc : G.Connected)
    (hdeg : ∀ v, (G.neighborSet v).ncard = 2) :
    ∃ v, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  classical
  obtain ⟨v⟩ := hc.nonempty
  have hn : (G.neighborSet v).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hdeg]; decide)
  obtain ⟨p, hp, hverts⟩ :=
    (show G.IsCycles from fun {_} _ => hdeg _).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := G.connectedComponentMk v) (by simp) hn
  have hall (w : V) : w ∈ p.support := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hverts]
    exact SimpleGraph.ConnectedComponent.sound (hc.preconnected w v)
  refine ⟨v, p, hp, ?_⟩
  apply hp.isPath_tail.isHamiltonian_iff.mpr
  intro w
  rw [SimpleGraph.Walk.support_tail_of_not_nil p hp.not_nil]
  have he : p.support = v :: p.support.tail := p.cons_tail_support.symm
  by_cases hw : w = v
  · subst w
    exact p.end_mem_tail_support hp.not_nil
  · have hm := hall w
    rw [he] at hm
    exact (List.mem_cons.mp hm).resolve_left hw

namespace SphereMap

-- @node: SphereMap.monochromaticEdges
/-- For [a sphere map](hyp:M) and [a chosen set of its vertices](hyp:U), the
[monochromatic edges](goal) are those whose endpoints either both belong to the
chosen set or both lie outside it. -/
noncomputable def monochromaticEdges (M : SphereMap) (U : Set M.Vertex) : Set M.Edge :=
  {e | ∀ d, M.edgeOf d = e → (M.vert d ∈ U ↔ M.head d ∈ U)}

-- @node: SphereMap.mem_monochromaticEdges
/-- [The edge represented by a dart is monochromatic exactly when its tail and
head either both belong to the chosen vertex set or both lie outside it](goal). -/
lemma mem_monochromaticEdges (M : SphereMap) (U : Set M.Vertex) (d : M.Dart) :
    M.edgeOf d ∈ M.monochromaticEdges U ↔ (M.vert d ∈ U ↔ M.head d ∈ U) := by
  constructor
  · intro h
    exact h d rfl
  · intro h e he
    rcases (M.edgeOf_eq_iff e d).mp he with he | he
    · simpa only [he] using h
    · subst d
      change M.vert (M.edgeInv e) ∈ U ↔ M.vert (M.edgeInv (M.edgeInv e)) ∈ U at h
      rw [M.edgeInv_involutive] at h
      exact h.symm

-- @node: SphereMap.monochromaticEdges_isSpanningForest
/-- If [a sphere map has no loops or parallel edges](hyp:hs) and its underlying
graph is acyclic when restricted [to a chosen vertex set](hyp:hU) and
[to its complement](hyp:hUc), then [the monochromatic edges form a spanning
forest of the map](goal). -/
lemma monochromaticEdges_isSpanningForest (M : SphereMap) (hs : M.IsSimple)
    (U : Set M.Vertex) (hU : (M.toSimpleGraph.induce U).IsAcyclic)
    (hUc : (M.toSimpleGraph.induce Uᶜ).IsAcyclic) :
    IsSpanningForest M (M.monochromaticEdges U) := by
  apply M.isSpanningForest_of_isAcyclic _ (fun d _ => hs.1 d)
    (fun d e _ _ h => hs.2 d e h)
  apply isAcyclic_of_induced_partition M.toSimpleGraph (M.spanningGraph (M.monochromaticEdges U)) U
    (fun u v ⟨hne, d, hd, hu, hv⟩ => ⟨hne, d, hu, hv⟩) _ hU hUc
  rintro u v ⟨hne, d, hd, rfl, rfl⟩
  exact (M.mem_monochromaticEdges U d).mp hd

-- @node: SphereMap.face_bichromatic_dart_card
/-- If [a sphere map is a simple triangulation](hyp:hT) and the graphs induced
[by a chosen vertex set](hyp:hU) and [by its complement](hyp:hUc) are acyclic,
then [each face has exactly two boundary darts whose endpoints lie on opposite
sides of that partition](goal). -/
lemma face_bichromatic_dart_card (T : SphereMap) (hT : IsSphereTriangulation T)
    (U : Set T.Vertex) (hU : (T.toSimpleGraph.induce U).IsAcyclic)
    (hUc : (T.toSimpleGraph.induce Uᶜ).IsAcyclic) (f : T.Face) :
    ((T.faceDarts f).filter (fun d => ¬ (T.vert d ∈ U ↔ T.head d ∈ U))).card = 2 := by
  have hcard : (T.faceDarts f).card = 3 :=
    (T.faceLength_eq_card_faceDarts f).symm.trans (hT.props.2.2.2 f).1
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < (T.faceDarts f).card by omega)
  let p := T.facePerm
  have hcyc : p.IsCycleOn (↑(T.faceDarts f) : Set T.Dart) := by
    simpa [p, SphereMap.faceDarts] using T.dual_rot_fibre hT.props.1 f
  have hpow : (p ^ 3) d = d := by
    simpa only [hcard] using hcyc.pow_card_apply hd
  have hmem (n : ℕ) : (p ^ n) d ∈ T.faceDarts f := hcyc.1.mapsTo.perm_pow n hd
  have hall : T.faceDarts f = {d, p d, p (p d)} := by
    ext e
    constructor
    · intro he
      obtain ⟨n, hn, rfl⟩ := hcyc.exists_pow_eq hd he
      rw [hcard] at hn
      have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hn' with rfl | rfl | rfl <;> simp [pow_succ, Equiv.Perm.mul_apply]
    · intro he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact hd
      · simpa using hmem 1
      · simpa [pow_succ, Equiv.Perm.mul_apply] using hmem 2
  have distinct (a b c : T.Dart) (hc : ({a, b, c} : Finset T.Dart).card = 3) :
      a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;>
      simp_all
  have hdist : d ≠ p d ∧ d ≠ p (p d) ∧ p d ≠ p (p d) :=
    distinct d (p d) (p (p d)) (hall ▸ hcard)
  have hhead (e : T.Dart) : T.head e = T.vert (p e) := (T.rot_vertex _).symm
  have hlast : p (p (p d)) = d := by
    simpa [pow_succ, Equiv.Perm.mul_apply] using hpow
  have hverts : T.faceVertices f = {T.vert d, T.vert (p d), T.vert (p (p d))} := by
    rw [triangulation_faceVertices_eq_image T hT f, hall]
    simp
  have hnon := T.triangulation_face_not_monochromatic hT f U hU hUc
  rw [hverts] at hnon
  rw [hall]
  simp only [hhead, hlast]
  by_cases ha : T.vert d ∈ U <;>
    by_cases hb : T.vert (p d) ∈ U <;>
    by_cases hc : T.vert (p (p d)) ∈ U
  all_goals simp_all [Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, Set.subset_def]

-- @node: SphereMap.spanningGraph_neighbor_card
/-- If [a sphere map has no loops or parallel edges](hyp:hs), then [the number
of neighbors of a vertex in the graph formed by a chosen edge set equals the
number of darts with that tail whose edges belong to the set](goal). -/
lemma spanningGraph_neighbor_card (M : SphereMap) (hs : M.IsSimple) (S : Set M.Edge)
    (v : M.Vertex) :
    ((M.spanningGraph S).neighborSet v).ncard =
      (Finset.univ.filter (fun d : M.Dart => M.vert d = v ∧ M.edgeOf d ∈ S)).card := by
  rw [Set.ncard_eq_toFinset_card']
  symm
  apply Finset.card_bij (fun d _ => M.head d)
  · intro d hd
    obtain ⟨hv, he⟩ := (Finset.mem_filter.mp hd).2
    exact Set.mem_toFinset.mpr ⟨hv ▸ hs.1 d, d, he, hv, rfl⟩
  · intro d hd e he hh
    exact M.dart_eq_of_endpoints hs d e
      ((Finset.mem_filter.mp hd).2.1.trans (Finset.mem_filter.mp he).2.1.symm) hh
  · intro w hw
    obtain ⟨hne, d, he, hd, hh⟩ := Set.mem_toFinset.mp hw
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, he⟩, hh⟩

-- @node: SphereMap.dual_dual_spanningGraph
/-- If [a sphere map is connected](hyp:hM) and [its dual is connected](hyp:hD),
then [the graph formed by any chosen edge set in the double dual is the same
as the graph formed by that edge set in the original map](goal). -/
lemma dual_dual_spanningGraph (M : SphereMap) (hM : M.IsConnectedMap)
    (hD : (M.dual hM).IsConnectedMap) (S : Set M.Edge) :
    ((M.dual hM).dual hD).spanningGraph S = M.spanningGraph S := by
  ext u v
  change (u ≠ v ∧ ∃ d, M.edgeOf d ∈ S ∧
    (M.dual hM).faceOf d = u ∧ (M.dual hM).faceOf (M.edgeInv d) = v) ↔ _
  simp only [M.dual_faceOf hM]
  rfl

-- @node: SphereMap.dual_partition_complement_degree_two
/-- Suppose [a sphere map is connected](hyp:hM), [has no loops or parallel
edges](hyp:hs), and [its dual is a simple sphere triangulation](hyp:hT).
If the dual graphs induced [by a chosen vertex set](hyp:hU) and [by its
complement](hyp:hUc) are acyclic, then [each vertex of the original map has
exactly two neighbors using the edges that are not monochromatic in the dual](goal). -/
lemma dual_partition_complement_degree_two (M : SphereMap) (hM : M.IsConnectedMap)
    (hs : M.IsSimple) (hT : IsSphereTriangulation (M.dual hM))
    (U : Set (M.dual hM).Vertex)
    (hU : ((M.dual hM).toSimpleGraph.induce U).IsAcyclic)
    (hUc : ((M.dual hM).toSimpleGraph.induce Uᶜ).IsAcyclic) (v : M.Vertex) :
    ((M.spanningGraph ((M.dual hM).monochromaticEdges U)ᶜ).neighborSet v).ncard = 2 := by
  rw [M.spanningGraph_neighbor_card hs]
  have hc := (M.dual hM).face_bichromatic_dart_card hT U hU hUc v
  convert hc using 1
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SphereMap.faceDarts,
    M.dual_faceOf hM, Set.mem_compl_iff]
  exact and_congr_right (fun _ => not_congr ((M.dual hM).mem_monochromaticEdges U d))

-- @node: SphereMap.exists_cycle_of_dual_tree_partition
/-- Suppose [a sphere map is connected](hyp:hM), [has no loops or parallel
edges](hyp:hs), and [its dual is a simple sphere triangulation](hyp:hT).
If the dual graphs induced [by a chosen vertex set](hyp:hU) and [by its
complement](hyp:hUc) are trees, then [the original graph formed by the edges
that are not monochromatic in the dual has a Hamiltonian cycle](goal). -/
lemma exists_cycle_of_dual_tree_partition (M : SphereMap) (hM : M.IsConnectedMap)
    (hs : M.IsSimple) (hT : IsSphereTriangulation (M.dual hM))
    (U : Set (M.dual hM).Vertex)
    (hU : ((M.dual hM).toSimpleGraph.induce U).IsTree)
    (hUc : ((M.dual hM).toSimpleGraph.induce Uᶜ).IsTree) :
    ∃ v, ∃ p : (M.spanningGraph ((M.dual hM).monochromaticEdges U)ᶜ).Walk v v,
      p.IsHamiltonianCycle := by
  have hf := (M.dual hM).monochromaticEdges_isSpanningForest hT.props.2.1 U
    hU.isAcyclic hUc.isAcyclic
  have hc := ((M.dual hM).dual_compl_spanning hT.props.1
    ⟨inferInstance, inferInstance⟩).2 _ hf
  rw [M.dual_dual_spanningGraph hM hT.props.1] at hc
  exact exists_hamiltonianCycle_of_connected_degree_two _ hc
    (M.dual_partition_complement_degree_two hM hs hT U hU.isAcyclic hUc.isAcyclic)

end SphereMap
end OaiPairedStatesHamiltonian
