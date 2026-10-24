module

public import Papers.OaiPairedStatesHamiltonian.Helpers.ForestGraph

/-! Extending forests while retaining the original multigraph edge identities. -/

public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

-- @node: SphereMap.forest_no_loop
/-- If [an edge set is a spanning forest of a sphere map](hyp:hS) and [a dart's
edge belongs to that set](hyp:hd), then [the dart has different initial and
terminal vertices](goal). -/
lemma forest_no_loop (M : SphereMap) (S : Set M.Edge) (hS : IsSpanningForest M S)
    (d : M.Dart) (hd : M.edgeOf d ∈ S) : M.vert d ≠ M.head d := by
  intro h
  apply hS.acyclic [d]
  · refine ⟨by simp, by simp, ?_⟩
    intro i
    have hi : i.val = 0 := by have := i.isLt; simp only [List.length_singleton] at this; omega
    simpa [List.get_eq_getElem, hi] using h.symm
  · simpa using hd

-- @node: SphereMap.forest_no_parallel_ordered
/-- If [an edge set is a spanning forest](hyp:hS), [the first dart's edge is
retained](hyp:hd), [the second dart's edge is retained](hyp:he), [the darts have
the same initial vertex](hyp:hv), and [they have the same terminal
vertex](hyp:hh), then [they represent the same edge](goal). -/
lemma forest_no_parallel_ordered (M : SphereMap) (S : Set M.Edge)
    (hS : IsSpanningForest M S) (d e : M.Dart)
    (hd : M.edgeOf d ∈ S) (he : M.edgeOf e ∈ S)
    (hv : M.vert d = M.vert e) (hh : M.head d = M.head e) :
    M.edgeOf d = M.edgeOf e := by
  by_contra hne
  have hinv : M.edgeOf (M.edgeInv e) = M.edgeOf e :=
    ((M.edgeOf_eq_iff e (M.edgeInv e)).mpr (Or.inr rfl)).symm
  have hhead : M.head (M.edgeInv e) = M.vert e :=
    congrArg M.vert (M.edgeInv_involutive e)
  apply hS.acyclic [d, M.edgeInv e]
  · refine ⟨by simp, by simpa [hinv] using hne, ?_⟩
    intro i
    have hi : i.val < 2 := i.isLt
    have hi' : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi' with hi' | hi'
    · simpa [List.get_eq_getElem, hi'] using
        (show M.head d = M.vert (M.edgeInv e) from hh)
    · simpa [List.get_eq_getElem, hi', hhead] using hv.symm
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hd
    · simpa [hinv] using he

-- @node: SphereMap.forest_no_parallel
/-- If [an edge set is a spanning forest](hyp:hS), [the first dart's edge is
retained](hyp:hd), [the second dart's edge is retained](hyp:he), and [the darts
have the same unordered pair of endpoints](hyp:h), then [they represent the
same edge](goal). -/
lemma forest_no_parallel (M : SphereMap) (S : Set M.Edge) (hS : IsSpanningForest M S)
    (d e : M.Dart) (hd : M.edgeOf d ∈ S) (he : M.edgeOf e ∈ S)
    (h : s(M.vert d, M.head d) = s(M.vert e, M.head e)) :
    M.edgeOf d = M.edgeOf e := by
  rcases Sym2.eq_iff.mp h with ⟨hv, hh⟩ | ⟨hv, hh⟩
  · exact M.forest_no_parallel_ordered S hS d e hd he hv hh
  · have hinv : M.edgeOf (M.edgeInv e) = M.edgeOf e :=
      ((M.edgeOf_eq_iff e (M.edgeInv e)).mpr (Or.inr rfl)).symm
    have he' : M.edgeOf (M.edgeInv e) ∈ S := hinv.symm ▸ he
    exact (M.forest_no_parallel_ordered S hS d (M.edgeInv e) hd he' hv
      (hh.trans (congrArg M.vert (M.edgeInv_involutive e)).symm)).trans hinv

-- @node: SphereMap.isSpanningForest_of_isAcyclic
/-- If [no retained edge is a loop](hyp:hloop), [any two retained edges with
the same unordered endpoints are the same edge](hyp:hparallel), and [the
spanning simple graph formed by the retained edges is acyclic](hyp:hS), then
[the retained edge set is a spanning forest of the sphere map](goal). -/
lemma isSpanningForest_of_isAcyclic (M : SphereMap) (S : Set M.Edge)
    (hloop : ∀ d, M.edgeOf d ∈ S → M.vert d ≠ M.head d)
    (hparallel : ∀ d e, M.edgeOf d ∈ S → M.edgeOf e ∈ S →
      s(M.vert d, M.head d) = s(M.vert e, M.head e) → M.edgeOf d = M.edgeOf e)
    (hS : (M.spanningGraph S).IsAcyclic) : IsSpanningForest M S := by
  constructor
  intro ds ht hs
  have hpos : 0 < ds.length := List.length_pos_iff.mpr ht.1
  let dart (i : Fin ds.length) : (M.spanningGraph S).Dart :=
    ⟨(M.vert (ds.get i), M.head (ds.get i)),
      hloop _ (hs _ (List.get_mem _ _)), ds.get i, hs _ (List.get_mem _ _), rfl, rfl⟩
  let l := List.ofFn dart
  have hne : l ≠ [] := by
    intro he
    have := congrArg List.length he
    simp only [l, List.length_ofFn, List.length_nil] at this
    omega
  have hc : l.IsChain (M.spanningGraph S).DartAdj := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have ht' := ht.2.2 ⟨i, by simpa only [l, List.length_ofFn] using Nat.lt_of_succ_lt hi⟩
    have hi' : i + 1 < ds.length := by simpa only [l, List.length_ofFn] using hi
    simpa only [l, List.getElem_ofFn, dart, SimpleGraph.DartAdj,
      List.get_eq_getElem,
      Nat.mod_eq_of_lt hi'] using ht'
  let p := SimpleGraph.Walk.ofDarts l hne hc
  have hclosed : (l.getLast hne).snd = (l.head hne).fst := by
    have ht' := ht.2.2 ⟨ds.length - 1, by omega⟩
    have he : ds.length - 1 + 1 = ds.length := by omega
    simpa only [l, List.getLast_eq_getElem, List.head_eq_getElem_zero,
      List.length_ofFn, List.getElem_ofFn, dart, List.get_eq_getElem, he, Nat.mod_self] using ht'
  have hn : p.edges.Nodup := by
    rw [SimpleGraph.Walk.edges_ofDarts]
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hi : i.val < ds.length := by simpa only [List.length_map, l, List.length_ofFn] using i.isLt
    have hj : j.val < ds.length := by simpa only [List.length_map, l, List.length_ofFn] using j.isLt
    have he : M.edgeOf (ds.get ⟨i.val, hi⟩) = M.edgeOf (ds.get ⟨j.val, hj⟩) := by
      apply hparallel _ _ (hs _ (List.get_mem _ _)) (hs _ (List.get_mem _ _))
      simpa only [List.getElem_map, l, List.getElem_ofFn, dart, SimpleGraph.Dart.edge,
        List.get_eq_getElem] using hij
    have he' : (ds.map M.edgeOf).get ⟨i.val, by simpa using hi⟩ =
        (ds.map M.edgeOf).get ⟨j.val, by simpa using hj⟩ := by
      simpa only [List.get_eq_getElem, List.getElem_map] using he
    exact Fin.ext (congrArg (fun x : Fin (ds.map M.edgeOf).length => x.val)
      (ht.2.1.get_inj_iff.mp he'))
  have hp : p.IsPath := (hS.isPath_iff_isTrail p).mpr ⟨hn⟩
  have closed_length {u v : M.Vertex} (q : (M.spanningGraph S).Walk u v)
      (hq : q.IsPath) (huv : u = v) : q.length = 0 := by
    subst v
    exact (SimpleGraph.Walk.isPath_iff_nil.mp hq).length_eq_zero
  have hz : p.length = 0 := closed_length p hp hclosed.symm
  have hlen : p.length = ds.length := by
    simp only [p, SimpleGraph.Walk.length_ofDarts, l, List.length_ofFn]
  omega

-- @node: SphereMap.exists_spanningTree_superset
/-- If [a sphere map is connected](hyp:hM) and [a given edge set is a spanning
forest](hyp:hS), then [there exists a spanning tree whose edge set contains
every edge of that forest](goal). -/
lemma exists_spanningTree_superset (M : SphereMap) (hM : M.IsConnectedMap)
    (S : Set M.Edge) (hS : IsSpanningForest M S) :
    ∃ A : Set M.Edge, S ⊆ A ∧ M.IsSpanningTree A := by
  have hle : M.spanningGraph S ≤ M.toSimpleGraph := by
    intro u v h
    exact ⟨h.1, h.2.choose, h.2.choose_spec.2⟩
  obtain ⟨H, hSH, hHM, hH⟩ := hM.exists_isTree_le_of_le_of_isAcyclic hle
    (M.isAcyclic_spanningGraph S hS)
  have exists_rep (a : H.edgeSet) : ∃ d : M.Dart,
      s(M.vert d, M.head d) = a.val ∧
        ((∃ e : M.Dart, s(M.vert e, M.head e) = a.val ∧ M.edgeOf e ∈ S) →
          M.edgeOf d ∈ S) := by
    by_cases hs : ∃ e : M.Dart, s(M.vert e, M.head e) = a.val ∧ M.edgeOf e ∈ S
    · obtain ⟨e, he, hs⟩ := hs
      exact ⟨e, he, fun _ => hs⟩
    · obtain ⟨a, ha⟩ := a
      induction a using Sym2.ind with
      | _ u v =>
        obtain ⟨hne, d, hd, hv⟩ := hHM (H.mem_edgeSet.mp ha)
        exact ⟨d, Sym2.eq_iff.mpr (Or.inl ⟨hd, hv⟩), fun he => (hs he).elim⟩
  let rep (a : H.edgeSet) : M.Dart := Classical.choose (exists_rep a)
  have spec (a : H.edgeSet) := Classical.choose_spec (exists_rep a)
  let A : Set M.Edge := S ∪ {e | ∃ a : H.edgeSet, e = M.edgeOf (rep a)}
  have ends (d : M.Dart) (hd : M.edgeOf d ∈ A) :
      s(M.vert d, M.head d) ∈ H.edgeSet := by
    rcases hd with hd | ⟨a, ha⟩
    · exact H.mem_edgeSet.mpr (hSH ⟨M.forest_no_loop S hS d hd, d, hd, rfl, rfl⟩)
    · have hp : s(M.vert d, M.head d) = s(M.vert (rep a), M.head (rep a)) := by
        rcases (M.edgeOf_eq_iff d (rep a)).mp ha with h | h
        · rw [h]
        · rw [h]
          change s(M.vert d, M.head d) = s(M.head d, M.vert (M.edgeInv (M.edgeInv d)))
          rw [M.edgeInv_involutive]
          exact Sym2.eq_swap
      exact hp.trans (spec a).1 ▸ a.property
  have loop (d : M.Dart) (hd : M.edgeOf d ∈ A) : M.vert d ≠ M.head d :=
    (H.mem_edgeSet.mp (ends d hd)).ne
  have rep_eq (d : M.Dart) (hd : M.edgeOf d ∈ A) (a : H.edgeSet)
      (ha : s(M.vert d, M.head d) = a.val) : M.edgeOf d = M.edgeOf (rep a) := by
    rcases hd with hd | ⟨b, hb⟩
    · have hs : M.edgeOf (rep a) ∈ S := (spec a).2 ⟨d, ha, hd⟩
      exact M.forest_no_parallel S hS d (rep a) hd hs (ha.trans (spec a).1.symm)
    · have hba : b = a := by
        apply Subtype.ext
        have hp : s(M.vert d, M.head d) = s(M.vert (rep b), M.head (rep b)) := by
          rcases (M.edgeOf_eq_iff d (rep b)).mp hb with h | h
          · rw [h]
          · rw [h]
            change s(M.vert d, M.head d) = s(M.head d, M.vert (M.edgeInv (M.edgeInv d)))
            rw [M.edgeInv_involutive]
            exact Sym2.eq_swap
        exact (spec b).1.symm.trans (hp.symm.trans ha)
      simpa only [hba] using hb
  have parallel (d e : M.Dart) (hd : M.edgeOf d ∈ A) (he : M.edgeOf e ∈ A)
      (h : s(M.vert d, M.head d) = s(M.vert e, M.head e)) :
      M.edgeOf d = M.edgeOf e := by
    let a : H.edgeSet := ⟨s(M.vert d, M.head d), ends d hd⟩
    exact (rep_eq d hd a rfl).trans (rep_eq e he a h.symm).symm
  have graph : M.spanningGraph A = H := by
    ext u v
    constructor
    · rintro ⟨hne, d, hd, rfl, rfl⟩
      exact H.mem_edgeSet.mp (ends d hd)
    · intro huv
      let a : H.edgeSet := ⟨s(u, v), H.mem_edgeSet.mpr huv⟩
      have hd : M.edgeOf (rep a) ∈ A := Or.inr ⟨a, rfl⟩
      rcases Sym2.eq_iff.mp (spec a).1 with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact ⟨huv.ne, rep a, hd, hu, hv⟩
      · exact M.subgraph_symm A v u ⟨huv.ne.symm, rep a, hd, hv, hu⟩
  refine ⟨A, Set.subset_union_left, ?_, ?_⟩
  · apply M.isSpanningForest_of_isAcyclic A loop parallel
    rw [graph]
    exact hH.isAcyclic
  · rw [graph]
    exact hH.connected

end SphereMap
end OaiPairedStatesHamiltonian
