module

public import Papers.OaiPairedStatesHamiltonian.TMain

/-! A Hamiltonian cycle avoiding an arbitrary prescribed edge. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


-- @node: thm:edge-avoidance
/-- For a [finite simple graph](hyp:G) and a [prescribed unordered vertex pair](hyp:e),
assume [the graph is cubic, bipartite, planar, and three-vertex-connected and the pair
is an edge](hyp:hG), [the graph is cubic, bipartite, planar, and three-vertex-connected](hyp:hmain),
and [the same graph properties and membership of the pair in the edge set hold as the
pinned condition](hyp:hpin). Then [there is a Hamiltonian cycle that avoids the prescribed edge](goal). -/
theorem exists_hamiltonian_avoiding_edge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V)
    (hG : EdgeAvoidanceDomain G e) (hmain : MainDomain G) (hpin : EdgeAvoidancePinned G e) :
    ∃ a, ∃ C : G.Walk a a, C.IsHamiltonianCycle ∧ e ∉ C.edges := by
  obtain ⟨M, hM, i, hs, hT, col, hcol⟩ := exists_main_colored_dual_triangulation G hmain
  induction e using Sym2.ind with
  | _ u v =>
    have hadj : M.toSimpleGraph.Adj (i.symm u) (i.symm v) :=
      i.symm.map_rel_iff.mpr (G.mem_edgeSet.mp hG.2)
    obtain ⟨hne, d, hd, hh⟩ := hadj
    let T := M.dual hM
    obtain ⟨U, hU, hUc, hends, _⟩ := exists_tree_partition T hT col hcol
      (show Finite T.Vertex from inferInstance) singletonTreeEdgeless_of_mathlib
      (T.faceOf d) (T.edgeOf d) ⟨d, rfl, rfl⟩
    have hm : T.edgeOf d ∈ T.monochromaticEdges U := by
      apply (T.mem_monochromaticEdges U d).mpr
      have he := hends
      rw [T.edgeEndpoints_edgeOf d] at he
      exact ⟨fun _ => he _ (by simp), fun _ => he _ (by simp)⟩
    obtain ⟨a, p, hp⟩ := M.exists_cycle_of_dual_tree_partition hM hs hT U hU hUc
    let f : M.spanningGraph (T.monochromaticEdges U)ᶜ →g G :=
      { toFun := i
        map_rel' := by
          rintro u v ⟨hne, d, hd, hu, hv⟩
          exact i.map_rel_iff.mpr ⟨hne, d, hu, hv⟩ }
    refine ⟨i a, p.map f, hp.map i.bijective, ?_⟩
    intro hmem
    rw [SimpleGraph.Walk.edges_map] at hmem
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    have hpairs : Sym2.map i s(M.vert d, M.head d) = s(u, v) := by
      simp only [Sym2.map_pair_eq, hd, hh, i.apply_symm_apply]
    have he' : e = s(M.vert d, M.head d) :=
      Sym2.map.injective i.injective (heq.trans hpairs.symm)
    rw [he'] at he
    obtain ⟨hne, b, hb, hu, hv⟩ :=
      (M.spanningGraph (T.monochromaticEdges U)ᶜ).mem_edgeSet.mp (p.edges_subset_edgeSet he)
    have hedge : M.edgeOf b = M.edgeOf d := hs.2 b d (by rw [hu, hv])
    exact hb (hedge.symm ▸ hm)


end OaiPairedStatesHamiltonian
