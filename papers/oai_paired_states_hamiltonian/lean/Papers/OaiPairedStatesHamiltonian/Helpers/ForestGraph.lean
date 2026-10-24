module

public import Papers.OaiPairedStatesHamiltonian.Helpers.Triangulation
public import Mathlib.Data.List.FinRange

/-! Passing from forests with retained edge identities to simple graph forests. -/

public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

open Classical
attribute [local instance] propDecidable

-- @node: SphereMap.isAcyclic_spanningGraph
/-- If [an edge set is a spanning forest of a sphere map](hyp:hS), then [the
spanning simple graph formed by those edges is acyclic](goal). -/
lemma isAcyclic_spanningGraph (M : SphereMap) (S : Set M.Edge)
    (hS : IsSpanningForest M S) : (M.spanningGraph S).IsAcyclic := by
  intro v p hp
  have hd (i : Fin p.length) : ∃ d : M.Dart,
      M.edgeOf d ∈ S ∧ M.vert d = p.getVert i.val ∧
        M.head d = p.getVert (i.val + 1) := (p.adj_getVert_succ i.isLt).2
  let d (i : Fin p.length) := Classical.choose (hd i)
  have spec (i : Fin p.length) : M.edgeOf (d i) ∈ S ∧
      M.vert (d i) = p.getVert i.val ∧ M.head (d i) = p.getVert (i.val + 1) :=
    Classical.choose_spec (hd i)
  let ds := List.ofFn d
  have hlen : ds.length = p.length := List.length_ofFn
  have hget (i : Fin ds.length) : ds.get i = d ⟨i.val, hlen ▸ i.isLt⟩ := by
    simp [ds, List.get_eq_getElem]
  have hpos : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 3) hp.three_le_length
  have hne : ds ≠ [] := by
    intro he
    have := congrArg List.length he
    simp only [hlen, List.length_nil] at this
    omega
  have hnodup : (ds.map M.edgeOf).Nodup := by
    rw [show ds.map M.edgeOf = List.ofFn (fun i => M.edgeOf (d i)) by
      simp only [ds, List.map_ofFn]; rfl]
    apply List.nodup_ofFn.mpr
    intro i j hij
    have hs : s(M.vert (d i), M.head (d i)) = s(M.vert (d j), M.head (d j)) := by
      rcases (M.edgeOf_eq_iff _ _).mp hij with he | he
      · rw [he]
      · rw [he]
        change s(M.vert (d i), M.vert (M.edgeInv (d i))) =
          s(M.vert (M.edgeInv (d i)), M.vert (M.edgeInv (M.edgeInv (d i))))
        rw [M.edgeInv_involutive]
        exact Sym2.eq_swap
    rw [(spec i).2.1, (spec i).2.2, (spec j).2.1, (spec j).2.2] at hs
    have he : p.edges[i.val]'(by simpa using i.isLt) =
        p.edges[j.val]'(by simpa using j.isLt) := by
      simpa only [SimpleGraph.Walk.getElem_edges] using hs
    exact Fin.ext (hp.isTrail.edges_nodup.getElem_inj_iff.mp he)
  have hclosed : M.IsClosedTrail ds := by
    refine ⟨hne, hnodup, ?_⟩
    intro i
    rw [hget, hget, (spec _).2.2, (spec _).2.1]
    dsimp only
    by_cases hi : i.val + 1 < p.length
    · have hm : (i.val + 1) % ds.length = i.val + 1 := by
        simpa only [hlen] using Nat.mod_eq_of_lt hi
      rw [hm]
    · have hi' : i.val + 1 = p.length := by omega
      have hm : (i.val + 1) % ds.length = 0 := by
        simp only [hlen, hi', Nat.mod_self]
      rw [hm, hi', p.getVert_length, p.getVert_zero]
  apply hS.acyclic ds hclosed
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact (spec i).1

-- @node: SphereMap.IsSpanningTree.isTree
/-- If [an edge set is a spanning tree of a sphere map](hyp:hS), then [the
spanning simple graph formed by those edges is a tree](goal). -/
lemma IsSpanningTree.isTree (M : SphereMap) (S : Set M.Edge)
    (hS : M.IsSpanningTree S) : (M.spanningGraph S).IsTree :=
  ⟨hS.2, M.isAcyclic_spanningGraph S hS.1⟩

end SphereMap
end OaiPairedStatesHamiltonian
