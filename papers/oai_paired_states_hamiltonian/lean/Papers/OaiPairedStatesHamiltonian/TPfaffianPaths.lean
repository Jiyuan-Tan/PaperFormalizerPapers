module

public import Papers.OaiPairedStatesHamiltonian.TMain
public import Papers.OaiPairedStatesHamiltonian.Helpers.CitedGates

/-! The conditional Pfaffian path corollary, with both external gates explicit. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


-- @node: exists_length_three_path_of_cubic
/-- If a [finite simple graph](hyp:G) [has degree three at every vertex](hyp:hG), then
[from any chosen vertex](hyp:u) [there is a simple path of exactly three edges](goal). -/
lemma exists_length_three_path_of_cubic {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (u : V) :
    ∃ v, ∃ p : G.Walk u v, p.IsPath ∧ p.length = 3 := by
  have next (v : V) (S : Finset V) (hS : S.card < 3) :
      ∃ w, G.Adj v w ∧ w ∉ S := by
    have hcard : S.card < (G.neighborFinset v).card := by
      rw [G.card_neighborFinset_eq_degree, hG.degree_eq]
      exact hS
    obtain ⟨w, hw, hwS⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨w, (G.mem_neighborFinset v w).mp hw, hwS⟩
  obtain ⟨v, huv, _⟩ := next u ∅ (by simp)
  obtain ⟨w, hvw, hwu⟩ := next v {u} (by simp)
  obtain ⟨z, hwz, hz⟩ := next w {u, v} (by
    have hcard := Finset.card_insert_le u {v}
    simp only [Finset.card_singleton] at hcard
    omega)
  have hwu' : w ≠ u := by simpa using hwu
  have hz' : z ≠ u ∧ z ≠ v := by simpa using hz
  refine ⟨z, .cons huv (.cons hvw (.cons hwz .nil)), ?_, rfl⟩
  simp [SimpleGraph.Walk.cons_isPath_iff, huv.ne, hvw.ne, hwz.ne,
    Ne.symm hwu', Ne.symm hz'.1, Ne.symm hz'.2]

-- @node: thm:pfaffian-paths
/-- Assume [the cited equivalence between Hamiltonicity of all finite cubic, bipartite,
planar, three-vertex-connected graphs and the property that every three-edge simple path
in every finite cubic, three-vertex-connected, bipartite Pfaffian graph lies in a
Hamiltonian cycle](hyp:hGSW416_of_gate), and [the cited assertion that every finite planar
graph admits a Pfaffian orientation](hyp:hGSW46_of_gate). If a [finite simple graph](hyp:G)
[is cubic, three-vertex-connected, and Pfaffian](hyp:hG) and [is bipartite](hyp:hbip),
then [every three-edge simple path in it lies in a Hamiltonian cycle, and the graph
has a Hamiltonian cycle](goal). -/
theorem p4Hamiltonian_of_pfaffian (hGSW416_of_gate : GSW2023Thm416)
    (hGSW46_of_gate : GSW2023Thm46) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PfaffianPathsGraph G) (hbip : PfaffianPathsBipartite G) :
    IsP4Hamiltonian G ∧ G.IsHamiltonian := by
  have hmain : ∀ n (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      MainDomain H → H.IsHamiltonian := by
    intro n H _ hH
    exact isHamiltonian_of_mainDomain H hH singletonTreeEdgeless_of_mathlib
  have hp4 : IsP4Hamiltonian G := hGSW416_of_gate.mp hmain n G hG hbip
  refine ⟨hp4, ?_⟩
  have hn : 0 < n := by
    have hcard := hG.2.1.1
    simpa using (lt_trans (by decide : 0 < 3) hcard)
  obtain ⟨v, p, hp, hlen⟩ := exists_length_three_path_of_cubic G hG.1 ⟨0, hn⟩
  obtain ⟨a, C, hC, _⟩ := hp4 _ _ p hp hlen
  intro _
  exact ⟨a, C, hC⟩


end OaiPairedStatesHamiltonian
