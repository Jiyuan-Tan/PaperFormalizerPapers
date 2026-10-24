module

public import Papers.OaiPairedStatesHamiltonian.Helpers.ForestExtension

/-! Edge counts for spanning trees with the original multigraph edge identities. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

-- @node: SphereMap.edgeEndpointPair
/-- For a [sphere map](hyp:M), the [edge-endpoint map](goal) assigns to each original edge the
unordered pair of its endpoints, independently of its chosen direction. -/
noncomputable def edgeEndpointPair (M : SphereMap) : M.Edge → Sym2 M.Vertex :=
  Quotient.lift (fun d => s(M.vert d, M.head d)) (by
    intro d e h
    rcases (M.edgeOf_eq_iff d e).mp (Quotient.sound h) with rfl | rfl
    · rfl
    · change s(M.vert d, M.head d) = s(M.head d, M.vert (M.edgeInv (M.edgeInv d)))
      rw [M.edgeInv_involutive]
      exact Sym2.eq_swap)

-- @node: SphereMap.edgeEndpointPair_edgeOf
/-- [The unordered endpoints of the edge represented by a dart are the dart's starting and
ending vertices](goal). -/
lemma edgeEndpointPair_edgeOf (M : SphereMap) (d : M.Dart) :
    M.edgeEndpointPair (M.edgeOf d) = s(M.vert d, M.head d) := rfl

-- @node: SphereMap.forest_edge_card
/-- If [a selected edge set is a spanning forest](hyp:hS), then [the number of selected original
edges equals the number of edges in its associated spanning simple graph](goal). -/
lemma forest_edge_card (M : SphereMap) (S : Set M.Edge) (hS : IsSpanningForest M S) :
    (Finset.univ.filter (fun e => e ∈ S)).card = (M.spanningGraph S).edgeFinset.card := by
  apply Finset.card_bij (fun e _ => M.edgeEndpointPair e)
  · intro e he
    obtain ⟨d, rfl⟩ := Quotient.exists_rep e
    apply SimpleGraph.mem_edgeFinset.mpr
    exact ⟨M.forest_no_loop S hS d (Finset.mem_filter.mp he).2,
      d, (Finset.mem_filter.mp he).2, rfl, rfl⟩
  · intro e he f hf hef
    obtain ⟨d, rfl⟩ := Quotient.exists_rep e
    obtain ⟨a, rfl⟩ := Quotient.exists_rep f
    exact M.forest_no_parallel S hS d a (Finset.mem_filter.mp he).2
      (Finset.mem_filter.mp hf).2 hef
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨hne, d, hd, hu, hv⟩ := SimpleGraph.mem_edgeFinset.mp he
      exact ⟨M.edgeOf d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩,
        by simp only [M.edgeEndpointPair_edgeOf, hu, hv]⟩

-- @node: SphereMap.spanningTree_edge_card
/-- If [a selected edge set is a spanning tree](hyp:hS), then [its number of original edges plus
one equals the number of vertices of the map](goal). -/
lemma spanningTree_edge_card (M : SphereMap) (S : Set M.Edge) (hS : M.IsSpanningTree S) :
    (Finset.univ.filter (fun e => e ∈ S)).card + 1 = Fintype.card M.Vertex := by
  rw [M.forest_edge_card S hS.1]
  exact (IsSpanningTree.isTree M S hS).card_edgeFinset

-- @node: SphereMap.exists_spanningTree_subset_of_connected
/-- If [the spanning simple graph associated with a selected edge set is connected](hyp:hS),
then [some subset of the selected original edges is a spanning tree of the map](goal). -/
lemma exists_spanningTree_subset_of_connected (M : SphereMap) (S : Set M.Edge)
    (hS : (M.spanningGraph S).Connected) :
    ∃ A : Set M.Edge, A ⊆ S ∧ M.IsSpanningTree A := by
  obtain ⟨H, hHS, hH⟩ := hS.exists_isTree_le
  have hex (a : H.edgeSet) : ∃ d : M.Dart,
      M.edgeOf d ∈ S ∧ s(M.vert d, M.head d) = a.val := by
    obtain ⟨a, ha⟩ := a
    induction a using Sym2.ind with
    | _ u v =>
      obtain ⟨hne, d, hd, hu, hv⟩ := hHS (H.mem_edgeSet.mp ha)
      exact ⟨d, hd, by rw [hu, hv]⟩
  choose rep hrep using hex
  let A : Set M.Edge := {e | ∃ a, e = M.edgeOf (rep a)}
  have hAS : A ⊆ S := by
    rintro e ⟨a, rfl⟩
    exact (hrep a).1
  have ends (d : M.Dart) (hd : M.edgeOf d ∈ A) :
      s(M.vert d, M.head d) ∈ H.edgeSet := by
    obtain ⟨a, ha⟩ := hd
    have hp : s(M.vert d, M.head d) = a.val := by
      calc
        _ = M.edgeEndpointPair (M.edgeOf d) := rfl
        _ = M.edgeEndpointPair (M.edgeOf (rep a)) := congrArg M.edgeEndpointPair ha
        _ = a.val := (hrep a).2
    exact hp.symm ▸ a.property
  have loop (d : M.Dart) (hd : M.edgeOf d ∈ A) : M.vert d ≠ M.head d :=
    (H.mem_edgeSet.mp (ends d hd)).ne
  have parallel (d e : M.Dart) (hd : M.edgeOf d ∈ A) (he : M.edgeOf e ∈ A)
      (hp : s(M.vert d, M.head d) = s(M.vert e, M.head e)) :
      M.edgeOf d = M.edgeOf e := by
    obtain ⟨a, ha⟩ := hd
    obtain ⟨b, hb⟩ := he
    have hab : a = b := by
      apply Subtype.ext
      calc
        a.val = M.edgeEndpointPair (M.edgeOf d) :=
          (hrep a).2.symm.trans (congrArg M.edgeEndpointPair ha.symm)
        _ = M.edgeEndpointPair (M.edgeOf e) := hp
        _ = b.val := (congrArg M.edgeEndpointPair hb).trans (hrep b).2
    exact ha.trans (hab ▸ hb.symm)
  have graph : M.spanningGraph A = H := by
    ext u v
    constructor
    · rintro ⟨hne, d, hd, rfl, rfl⟩
      exact H.mem_edgeSet.mp (ends d hd)
    · intro huv
      let a : H.edgeSet := ⟨s(u, v), H.mem_edgeSet.mpr huv⟩
      have hd : M.edgeOf (rep a) ∈ A := ⟨a, rfl⟩
      rcases Sym2.eq_iff.mp (hrep a).2 with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact ⟨huv.ne, rep a, hd, hu, hv⟩
      · exact M.subgraph_symm A v u ⟨huv.ne.symm, rep a, hd, hv, hu⟩
  refine ⟨A, hAS, M.isSpanningForest_of_isAcyclic A loop parallel ?_, ?_⟩
  · rw [graph]
    exact hH.isAcyclic
  · rw [graph]
    exact hH.connected

-- @node: SphereMap.isSpanningTree_of_connected_card
/-- If [the spanning simple graph associated with a selected edge set is connected](hyp:hS) and
[the number of selected original edges plus one equals the number of vertices](hyp:hcard), then
[the selected edge set is a spanning tree of the map](goal). -/
lemma isSpanningTree_of_connected_card (M : SphereMap) (S : Set M.Edge)
    (hS : (M.spanningGraph S).Connected)
    (hcard : (Finset.univ.filter (fun e => e ∈ S)).card + 1 = Fintype.card M.Vertex) :
    M.IsSpanningTree S := by
  obtain ⟨A, hAS, hA⟩ := M.exists_spanningTree_subset_of_connected S hS
  have hAcard := M.spanningTree_edge_card A hA
  have heq : Finset.univ.filter (fun e => e ∈ A) =
      Finset.univ.filter (fun e => e ∈ S) := by
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAS (Finset.mem_filter.mp he).2⟩
    · omega
  have hset : A = S := by
    ext e
    have := Finset.ext_iff.mp heq e
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using this
  exact hset ▸ hA

end SphereMap
end OaiPairedStatesHamiltonian
