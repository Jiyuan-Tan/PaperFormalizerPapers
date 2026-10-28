module
public import Papers.OaiGraphDecompositionsIntegral.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! # Deterministic assignment of covered edges to typical members -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

omit [Fintype V] in
/-- If [every edge of H belongs to some graph in the family G](hyp:hcover),
[there is a family of subgraphs of H that partitions its edges, with each piece
contained in the corresponding graph of G](goal). -/
-- @node: edge_partition_subordinate_cover
lemma edge_partition_subordinate_cover {I : Type} [Nonempty I]
    (H : SimpleGraph V) (G : I → SimpleGraph V)
    (hcover : ∀ e ∈ H.edgeSet, ∃ i, e ∈ (G i).edgeSet) :
    ∃ P : I → SimpleGraph V, (∀ i, P i ≤ H) ∧
      (∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, P i ≤ G i := by
  classical
  let color : Sym2 V → I := fun e =>
    if he : e ∈ H.edgeSet then (hcover e he).choose else Classical.choice inferInstance
  let P : I → SimpleGraph V := fun i => {
    Adj u v := H.Adj u v ∧ color s(u, v) = i
    symm := ⟨by intro u v h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
    loopless := ⟨by intro v h; exact H.irrefl h.1⟩ }
  refine ⟨P, fun _ _ _ h => h.1, ?_, ?_⟩
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      exact ⟨color s(u, v), ⟨he, rfl⟩, fun i hi => hi.2.symm⟩
  · intro i u v h
    have hc : s(u, v) ∈ (G (color s(u, v))).edgeSet := by
      dsimp only [color]
      rw [dif_pos (show s(u, v) ∈ H.edgeSet from h.1)]
      exact (hcover s(u, v) h.1).choose_spec
    rwa [h.2] at hc

/-- [A host edge belongs to the graph formed from T exactly when it belongs to T](goal). -/
-- @node: graphOfEdges_mem_edgeSet
lemma graphOfEdges_mem_edgeSet {n : ℕ} (T : Finset (KEdge n)) (e : KEdge n) :
    e.val ∈ (graphOfEdges T).edgeSet ↔ e ∈ T := by
  classical
  simp [graphOfEdges, hostGraph, SimpleGraph.edgeSet_fromEdgeSet, e.property]

/-- If [K is positive](hyp:hK) and [the labelled copy of H is covered by K
members of D](hyp:hcover), [one can choose K members of D and partition the
edges of H into corresponding subgraphs whose labelled images lie in those
members](goal). -/
-- @node: covered_copy_edge_partition
lemma covered_copy_edge_partition {n K : ℕ} (hK : 0 < K)
    (H : SimpleGraph V) (f : V ↪ Fin n) (D : Set (Finset (KEdge n)))
    (hcover : CoveredByMembers K D (copyEdges H f)) :
    ∃ (T : Fin K → Finset (KEdge n)) (P : Fin K → SimpleGraph V),
      (∀ i, T i ∈ D) ∧ (∀ i, P i ≤ H) ∧
      (∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, (P i).map f ≤ graphOfEdges (T i) := by
  classical
  let : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  obtain ⟨T, hT, hcovered⟩ := hcover
  have hsub : ∀ e ∈ H.edgeSet,
      ∃ i, e ∈ ((graphOfEdges (T i)).comap f).edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadj : (H.map f).Adj (f u) (f v) :=
        SimpleGraph.map_adj_apply.mpr he
      let a : KEdge n := ⟨s(f u, f v), (H.map f).not_isDiag_of_mem_edgeSet hadj⟩
      have ha : a ∈ copyEdges H f := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hcovered ha)
      exact ⟨i, (graphOfEdges_mem_edgeSet (T i) a).mpr hi⟩
  obtain ⟨P, hP, hpart, hPG⟩ := edge_partition_subordinate_cover H
    (fun i => (graphOfEdges (T i)).comap f) hsub
  exact ⟨T, P, hT, hP, hpart,
    fun i => (SimpleGraph.map_le_iff_le_comap f _ _).mpr (hPG i)⟩

end Papers.OaiGraphDecompositionsIntegral
