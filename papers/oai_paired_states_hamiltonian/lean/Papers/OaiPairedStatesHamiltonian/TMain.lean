module

public import Papers.OaiPairedStatesHamiltonian.TPartition
public import Papers.OaiPairedStatesHamiltonian.Helpers.HamiltonianAssembly

/-! Hamiltonicity of finite cubic bipartite planar three-connected graphs. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


-- @node: thm:main
/-- If a [finite simple graph](hyp:G) [is cubic, bipartite, planar, and
three-vertex-connected](hyp:hG), and [every simple graph on a single vertex is a tree
with no edges](hyp:hpin), then [the graph has a Hamiltonian cycle](goal). -/
theorem isHamiltonian_of_mainDomain {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : MainDomain G)
    (hpin : SingletonTreeEdgeless) : G.IsHamiltonian := by
  obtain ⟨M, hM, i, hs, hT, col, hcol⟩ := exists_main_colored_dual_triangulation G hG
  obtain ⟨v⟩ := hM.nonempty
  have hdart : Nonempty M.Dart := by
    have hd : 0 < (Finset.univ.filter (fun d : M.Dart => M.vert d = v)).card := by
      rw [M.dart_fibre_card_eq_degree hs, ← i.degree_eq v, hG.1.degree_eq]
      decide
    obtain ⟨d, _⟩ := Finset.card_pos.mp hd
    exact ⟨d⟩
  obtain ⟨d⟩ := hdart
  let T := M.dual hM
  obtain ⟨U, hU, hUc, _, _⟩ := exists_tree_partition T hT col hcol
    (show Finite T.Vertex from inferInstance) hpin (T.faceOf d) (T.edgeOf d) ⟨d, rfl, rfl⟩
  obtain ⟨a, p, hp⟩ := M.exists_cycle_of_dual_tree_partition hM hs hT U hU hUc
  let f : M.spanningGraph (T.monochromaticEdges U)ᶜ →g G :=
    { toFun := i
      map_rel' := by
        rintro u v ⟨hne, d, hd, hu, hv⟩
        exact i.map_rel_iff.mpr ⟨hne, d, hu, hv⟩ }
  intro _
  exact ⟨i a, p.map f, hp.map i.bijective⟩


end OaiPairedStatesHamiltonian
