module

public import Papers.OaiPairedStatesHamiltonian.Helpers.TreeCardinality
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleDisk
public import Papers.OaiPairedStatesHamiltonian.Helpers.DualConnectivity

/-! Complementary primal and dual trees and forests. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable


namespace SphereMap

-- @node: SphereMap.dual_compl_edge_card
/-- For a [connected sphere map](hyp:hM), if [a set of primal edges is a spanning tree](hyp:hS), then [the number of complementary dual edges plus one equals the number of dual vertices](goal). -/
lemma dual_compl_edge_card (M : SphereMap) (hM : M.IsConnectedMap)
    (S : Set M.Edge) (hS : M.IsSpanningTree S) :
    (Finset.univ.filter (fun e : (M.dual hM).Edge => e ∈ Sᶜ)).card + 1 =
      Fintype.card (M.dual hM).Vertex := by
  have htree := M.spanningTree_edge_card S hS
  have heuler := M.connected_euler hM
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun e : M.Edge => e ∈ S)
  simp only [Finset.card_univ] at hsplit
  change (Finset.univ.filter (fun e : M.Edge => e ∈ Sᶜ)).card + 1 =
    Fintype.card M.Face
  simpa only [Set.mem_compl_iff] using (show
    (Finset.univ.filter (fun e : M.Edge => e ∉ S)).card + 1 =
      Fintype.card M.Face from by omega)

-- @node: lem:duality
/-- For a [connected](hyp:hM), [finite sphere map](hyp:hfin), [the complement of every primal spanning tree is a dual spanning tree, and the complement of every primal spanning forest gives a connected dual spanning graph](goal). -/
lemma dual_compl_spanning (M : SphereMap) (hM : M.IsConnectedMap) (hfin : M.FiniteMap) :
    (∀ S : Set M.Edge, M.IsSpanningTree S → (M.dual hM).IsSpanningTree Sᶜ) ∧
    (∀ S : Set M.Edge, IsSpanningForest M S → ((M.dual hM).spanningGraph Sᶜ).Connected) := by
  -- Contraction connectivity and Euler give the complementary dual tree.
  have htree : ∀ S : Set M.Edge, M.IsSpanningTree S →
      (M.dual hM).IsSpanningTree Sᶜ := by
    intro S hS
    apply (M.dual hM).isSpanningTree_of_connected_card Sᶜ ?_
      (by simpa only [dual, dualRotation] using M.dual_compl_edge_card hM S hS)
    exact M.dual_compl_connected hM S hS.1
  refine ⟨htree, ?_⟩
  intro S hS
  obtain ⟨A, hSA, hA⟩ := M.exists_spanningTree_superset hM S hS
  have hle : (M.dual hM).spanningGraph Aᶜ ≤ (M.dual hM).spanningGraph Sᶜ := by
    intro u v h
    obtain ⟨hne, d, hd, hu, hv⟩ := h
    exact ⟨hne, d, (fun hs => hd (hSA hs)), hu, hv⟩
  exact SimpleGraph.Connected.mono hle (htree A hA).2
end SphereMap


end OaiPairedStatesHamiltonian
