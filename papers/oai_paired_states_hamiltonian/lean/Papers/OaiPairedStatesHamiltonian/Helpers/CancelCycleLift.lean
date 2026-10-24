module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CancelSwitch
public import Papers.OaiPairedStatesHamiltonian.Helpers.OppositeEdges

/-! Orienting simple opposite-edge cycles by their unique outgoing darts. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable

-- @node: cyclic_pred_closed
/-- On [a cyclic index set of positive size](hyp:hn), suppose [whenever a property holds at the next index it holds at the current index](hyp:hstep), and [the property holds somewhere](hyp:hex). Then [the property holds at every index](goal). -/
lemma cyclic_pred_closed {n : ℕ} (hn : 0 < n) (P : Fin n → Prop)
    (hstep : ∀ i, P ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ → P i)
    (hex : ∃ i, P i) : ∀ i, P i := by
  obtain ⟨j, hj⟩ := hex
  intro i
  have hback (k : ℕ) : P ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩ → P i := by
    induction k with
    | zero => simpa only [Nat.add_zero, Nat.mod_eq_of_lt i.isLt] using id (α := P i)
    | succ k ih =>
      intro h
      apply ih
      apply hstep ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩
      convert h using 1
      congr 1
      change ((i.val + k) % n + 1) % n = (i.val + (k + 1)) % n
      rw [Nat.mod_add_mod, Nat.add_assoc]
  by_cases hij : i.val ≤ j.val
  · apply hback (j.val - i.val)
    simpa only [Nat.add_sub_of_le hij, Nat.mod_eq_of_lt j.isLt] using hj
  · apply hback (j.val + n - i.val)
    have he : i.val + (j.val + n - i.val) = j.val + n := by omega
    simpa only [he, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt] using hj

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

-- @node: SphereMap.edge_endpoints_eq_of_edgeOf_eq
/-- If [two darts represent the same undirected edge](hyp:he), then [their unordered pairs of endpoints are equal](goal). -/
lemma SphereMap.edge_endpoints_eq_of_edgeOf_eq (d e : T.Dart)
    (he : T.edgeOf d = T.edgeOf e) : s(T.vert d, T.head d) = s(T.vert e, T.head e) := by
  rcases (T.edgeOf_eq_iff d e).mp he with he | he
  · rw [he]
  · rw [he]
    have hh : T.head (T.edgeInv d) = T.vert d := congrArg T.vert (T.edgeInv_involutive d)
    change s(T.vert d, T.head d) = s(T.head d, T.head (T.edgeInv d))
    rw [hh, Sym2.eq_swap]

-- @node: exists_dart_cycle_lift
/-- Suppose [every adjacent ordered pair of vertices in a graph can be realized as the starting and ending vertices of a dart](hyp:hlift), and [a closed graph walk is a simple cycle](hyp:hc). Then [there is a simple directed cycle of darts whose ordered list of unordered endpoint pairs equals the walk's edge list](goal). -/
lemma exists_dart_cycle_lift (G : SimpleGraph T.Vertex)
    (hlift : ∀ v w, G.Adj v w → ∃ d : T.Dart, T.vert d = v ∧ T.head d = w)
    (v : T.Vertex) (C : G.Walk v v) (hc : C.IsCycle) :
    ∃ D : T.Cycle, D.val.map (fun d => s(T.vert d, T.head d)) = C.edges := by
  have hn : 0 < C.length := by
    have hh := (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mp hc).2
    omega
  let a : Fin C.length → T.Dart := fun i =>
    Classical.choose (hlift (C.getVert i.val) (C.getVert (i.val + 1)) (C.adj_getVert_succ i.isLt))
  have ha (i : Fin C.length) :
      T.vert (a i) = C.getVert i.val ∧ T.head (a i) = C.getVert (i.val + 1) :=
    Classical.choose_spec (hlift _ _ (C.adj_getVert_succ i.isLt))
  let ds := List.ofFn a
  have hlen : ds.length = C.length := List.length_ofFn
  have hget (i : ℕ) (hi : i < ds.length) : ds[i] = a ⟨i, hlen ▸ hi⟩ :=
    List.getElem_ofFn _
  have heq : ds.map (fun d => s(T.vert d, T.head d)) = C.edges := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      rw [List.getElem_map, hget i (by simpa using hi),
        (ha _).1, (ha _).2, SimpleGraph.Walk.getElem_edges]
  have hsimple : T.IsSimpleCycle ds := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro he
      have hz := congrArg List.length he
      simp only [List.length_nil, hlen] at hz
      omega
    · apply List.nodup_iff_injective_getElem.mpr
      intro i j hij
      have hie : s(T.vert ds[i.val], T.head ds[i.val]) =
          s(T.vert ds[j.val], T.head ds[j.val]) :=
        T.edge_endpoints_eq_of_edgeOf_eq _ _ (by simpa using hij)
      have hp := hc.isTrail.edges_nodup.get_inj_iff.mp (show
        C.edges.get ⟨i.val, by simpa [hlen] using i.isLt⟩ =
          C.edges.get ⟨j.val, by simpa [hlen] using j.isLt⟩ from by
            simpa only [← heq, List.get_eq_getElem, List.getElem_map] using hie)
      have hp' : i.val = j.val := congrArg (fun k : Fin C.edges.length => k.val) hp
      exact Fin.ext hp'
    · intro i
      have hi : i.val < C.length := hlen ▸ i.isLt
      have hnext : (i.val + 1) % C.length < C.length := Nat.mod_lt _ hn
      simp only [List.get_eq_getElem]
      rw [hget i.val i.isLt, (ha _).2]
      have hnext' : (i.val + 1) % ds.length < ds.length := by simpa [hlen] using hnext
      rw [hget _ hnext', (ha _).1]
      change C.getVert (i.val + 1) = C.getVert ((i.val + 1) % ds.length)
      rw [congrArg (fun n => (i.val + 1) % n) hlen]
      by_cases hlast : i.val + 1 = C.length
      · rw [hlast, Nat.mod_self, C.getVert_zero, C.getVert_length]
      · rw [Nat.mod_eq_of_lt (by omega)]
    · apply List.nodup_iff_injective_getElem.mpr
      intro i j hij
      have hi : i.val < ds.length := by simpa using i.isLt
      have hj : j.val < ds.length := by simpa using j.isLt
      simp only [List.getElem_map, hget, (ha _).1] at hij
      exact Fin.ext (hc.getVert_injOn' (by simp; omega) (by simp; omega) hij)
  exact ⟨⟨ds, hsimple⟩, heq⟩

-- @node: opposite_cycle_orientation
/-- In [a sphere triangulation](hyp:hT), let [r and s be paired states](hyp:h) and suppose [each dart of a simple directed cycle, or its reversal, is an opposite dart for this pair](hyp:hcover). Then [either every cycle dart is an opposite dart, or every reversed cycle dart is an opposite dart](goal). -/
lemma opposite_cycle_orientation (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (C : T.Cycle)
    (hcover : ∀ d ∈ C.val,
      (∃ t, oppositeDart T col t0 hT r s h t = d) ∨
      (∃ t, oppositeDart T col t0 hT r s h t = T.edgeInv d)) :
    (∀ d ∈ C.val, ∃ t, oppositeDart T col t0 hT r s h t = d) ∨
      (∀ d ∈ C.val, ∃ t, oppositeDart T col t0 hT r s h t = T.edgeInv d) := by
  let E (d : T.Dart) := ∃ t, oppositeDart T col t0 hT r s h t = d
  have htail (d e : T.Dart) (hd : E d) (he : E e)
      (hv : T.vert d = T.vert e) : d = e := by
    obtain ⟨t, rfl⟩ := hd
    obtain ⟨u, rfl⟩ := he
    exact congrArg (oppositeDart T col t0 hT r s h)
      (oppositeDart_tail_injective T col t0 hT r s h t u hv)
  have hn : 0 < C.val.length := List.length_pos_iff.mpr C.property.1.1
  let P (i : Fin C.val.length) := E C.val[i.val]
  have hstep (i : Fin C.val.length)
      (hi : P ⟨(i.val + 1) % C.val.length, Nat.mod_lt _ hn⟩) : P i := by
    have hi' : (i.val + 1) % C.val.length < C.val.length := Nat.mod_lt _ hn
    by_contra hnot
    have hinv : E (T.edgeInv C.val[i.val]) :=
      (hcover C.val[i.val] (List.getElem_mem i.isLt)).resolve_left hnot
    have he : T.edgeInv C.val[i.val] =
        C.val[(i.val + 1) % C.val.length] := htail _ _ hinv hi (C.property.1.2.2 i)
    have hedge : T.edgeOf C.val[i.val] =
        T.edgeOf C.val[(i.val + 1) % C.val.length] :=
      (T.edgeOf_eq_iff _ _).mpr (Or.inr he.symm)
    have hind := C.property.1.2.1.get_inj_iff.mp (show
      (C.val.map T.edgeOf).get ⟨i.val, by simpa using i.isLt⟩ =
        (C.val.map T.edgeOf).get ⟨(i.val + 1) % C.val.length,
          by simpa using Nat.mod_lt (i.val + 1) hn⟩ from by simpa using hedge)
    have hindex := congrArg Fin.val hind
    change i.val = (i.val + 1) % C.val.length at hindex
    have hdart : C.val[(i.val + 1) % C.val.length] = C.val[i.val] := by
      exact congrArg (fun k : Fin C.val.length => C.val[k.val])
        (show (⟨(i.val + 1) % C.val.length, hi'⟩ : Fin C.val.length) = i from
          Fin.ext hindex.symm)
    exact T.edgeInv_fixedPointFree _ (he.trans hdart)
  by_cases hex : ∃ i, P i
  · apply Or.inl
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
    exact cyclic_pred_closed hn P hstep hex ⟨i, hi⟩
  · apply Or.inr
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
    exact (hcover _ (List.getElem_mem hi)).resolve_left (fun hp => hex ⟨⟨i, hi⟩, hp⟩)

-- @node: oppositeDart_endpoints
/-- In [a sphere triangulation](hyp:hT), for [paired states r and s](hyp:h), [the unordered endpoints of the opposite dart at a black face other than the outer face form exactly that face's opposite edge](goal). -/
lemma oppositeDart_endpoints (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (t : blackNonOuter T col t0) :
    s(T.vert (oppositeDart T col t0 hT r s h t),
      T.head (oppositeDart T col t0 hT r s h t)) = oppositeEdge T hT col t0 r s h t := by
  rw [(oppositeDart_spec T col t0 hT r s h t).1,
    (oppositeDart_spec T col t0 hT r s h t).2.1]
  rfl

-- @node: qs_adjacency_dart_lift
/-- In [a sphere triangulation](hyp:hT), given [paired states r and s](hyp:h), if [v and w are adjacent in the opposite-edge graph of s](hyp:hadj), then [there is a dart starting at v and ending at w](goal). -/
lemma qs_adjacency_dart_lift (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (v w : T.Vertex)
    (hadj : (Qs T col t0 s).Adj v w) :
    ∃ d : T.Dart, T.vert d = v ∧ T.head d = w := by
  obtain ⟨t, ht⟩ := oppositeEdge_surjective T hT col t0 r s h s(v, w) hadj
  have he := (oppositeDart_endpoints T col t0 hT r s h t).trans ht
  rcases Sym2.eq_iff.mp he with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · exact ⟨_, hv, hw⟩
  · refine ⟨T.edgeInv (oppositeDart T col t0 hT r s h t), hw, ?_⟩
    exact (congrArg T.vert (T.edgeInv_involutive _)).trans hv

-- @node: qs_dart_opposite
/-- In [a sphere triangulation](hyp:hT), given [paired states r and s](hyp:h), if [a dart's unordered endpoint pair is an edge of the opposite-edge graph of s](hyp:hd), then [either that dart or its reversal is the opposite dart of some black face other than the outer face](goal). -/
lemma qs_dart_opposite (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (d : T.Dart)
    (hd : s(T.vert d, T.head d) ∈ (Qs T col t0 s).edgeSet) :
    (∃ t, oppositeDart T col t0 hT r s h t = d) ∨
      (∃ t, oppositeDart T col t0 hT r s h t = T.edgeInv d) := by
  obtain ⟨t, ht⟩ := oppositeEdge_surjective T hT col t0 r s h _ hd
  have he := hT.props.2.1.2 _ _ ((oppositeDart_endpoints T col t0 hT r s h t).trans ht)
  rcases (T.edgeOf_eq_iff _ _).mp he with he | he
  · exact Or.inl ⟨t, he.symm⟩
  · exact Or.inr ⟨t, by rw [he, T.edgeInv_involutive]⟩

-- @node: opposite_cycle_edge_membership
/-- In [a sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hc), let [r and s be paired states](hyp:h) and assume [every dart of a simple directed cycle is an opposite dart for this pair](hyp:hD). Then [a black face's opposite edge occurs in the cycle's list of unordered endpoint pairs if and only if its opposite dart occurs in the cycle](goal). -/
lemma opposite_cycle_edge_membership (hT : IsSphereTriangulation T)
    (hc : PartitionColoring T col) (r s : State T col t0) (h : IsPair T col t0 r s)
    (D : T.Cycle) (hD : ∀ d ∈ D.val, ∃ t, oppositeDart T col t0 hT r s h t = d)
    (t : blackNonOuter T col t0) :
    oppositeEdge T hT col t0 r s h t ∈ D.val.map (fun d => s(T.vert d, T.head d)) ↔
      oppositeDart T col t0 hT r s h t ∈ D.val := by
  constructor
  · intro ht
    obtain ⟨d, hd, he⟩ := List.mem_map.mp ht
    obtain ⟨u, rfl⟩ := hD d hd
    rw [oppositeDart_endpoints] at he
    have hut := oppositeEdge_injective T hT col hc t0 r s h he
    simpa only [hut] using hd
  · intro ht
    exact List.mem_map.mpr ⟨_, ht, oppositeDart_endpoints T col t0 hT r s h t⟩

-- @node: exists_directed_opposite_cycle_lift
/-- In [a sphere triangulation](hyp:hT) with [opposite face colors across every edge](hyp:hc), let [r and s be paired states](hyp:h) and let [a closed walk in the opposite-edge graph of s be a simple cycle](hyp:hcycle). Then [there is a simple directed cycle consisting entirely of opposite darts, such that each black face's opposite edge belongs to the original walk exactly when its opposite dart belongs to the directed cycle](goal).

The undirected cycle is fixed first; only its orientation depends on the partner. -/
lemma exists_directed_opposite_cycle_lift (hT : IsSphereTriangulation T)
    (hc : PartitionColoring T col) (r s : State T col t0) (h : IsPair T col t0 r s)
    (v : T.Vertex) (C : (Qs T col t0 s).Walk v v) (hcycle : C.IsCycle) :
    ∃ D : T.Cycle,
      (∀ d ∈ D.val, ∃ t, oppositeDart T col t0 hT r s h t = d) ∧
      (∀ t, oppositeEdge T hT col t0 r s h t ∈ C.edges ↔
        oppositeDart T col t0 hT r s h t ∈ D.val) := by
  obtain ⟨D, hDedges⟩ := exists_dart_cycle_lift T (Qs T col t0 s)
    (qs_adjacency_dart_lift T col t0 hT r s h) v C hcycle
  have hcover : ∀ d ∈ D.val,
      (∃ t, oppositeDart T col t0 hT r s h t = d) ∨
      (∃ t, oppositeDart T col t0 hT r s h t = T.edgeInv d) := by
    intro d hd
    apply qs_dart_opposite T col t0 hT r s h d
    apply C.edges_subset_edgeSet
    rw [← hDedges]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  rcases opposite_cycle_orientation T col t0 hT r s h D hcover with hD | hD
  · refine ⟨D, hD, ?_⟩
    intro t
    rw [← hDedges]
    exact opposite_cycle_edge_membership T col t0 hT hc r s h D hD t
  · have hrev : ∀ d ∈ (reverseCycle T D).val,
        ∃ t, oppositeDart T col t0 hT r s h t = d := by
      intro d hd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
      exact hD e (List.mem_reverse.mp he)
    refine ⟨reverseCycle T D, hrev, ?_⟩
    intro t
    rw [← opposite_cycle_edge_membership T col t0 hT hc r s h _ hrev t, ← hDedges]
    have hh (d : T.Dart) : s(T.vert (T.edgeInv d), T.head (T.edgeInv d)) =
        s(T.vert d, T.head d) := by
      have hd : T.head (T.edgeInv d) = T.vert d := congrArg T.vert (T.edgeInv_involutive d)
      change s(T.head d, T.head (T.edgeInv d)) = s(T.vert d, T.head d)
      rw [hd, Sym2.eq_swap]
    simp only [reverseCycle, reverseDarts, List.map_map, Function.comp_def, hh,
      List.map_reverse, List.mem_reverse]

end OaiPairedStatesHamiltonian
