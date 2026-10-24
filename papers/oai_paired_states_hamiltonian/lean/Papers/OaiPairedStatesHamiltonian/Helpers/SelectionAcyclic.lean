module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SelectionCounting
public import Papers.OaiPairedStatesHamiltonian.Helpers.SelectionWhite

/-! The disk contradiction and the selected forest, retaining original edge identities. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

namespace SphereMap

-- @node: SphereMap.isSpanningForest_of_no_cycle
/-- If [the map is simple](hyp:hM) and [no simple cycle has all its edges in the
chosen edge set](hyp:hcycles), then [that edge set is a spanning forest](goal). -/
lemma isSpanningForest_of_no_cycle (M : SphereMap) (hM : M.IsSimple) (S : Set M.Edge)
    (hcycles : ∀ C : M.Cycle, ¬ ∀ d ∈ C.val, M.edgeOf d ∈ S) : IsSpanningForest M S := by
  apply M.isSpanningForest_of_isAcyclic S (fun d _ => hM.1 d)
    (fun d e _ _ he => hM.2 d e he)
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
  have hverts : (ds.map M.vert).Nodup := by
    rw [show ds.map M.vert = List.ofFn (fun i => M.vert (d i)) by
      simp only [ds, List.map_ofFn]; rfl]
    apply List.nodup_ofFn.mpr
    intro i j hij
    apply Fin.ext
    apply hp.getVert_injOn' (show i.val ≤ p.length - 1 by omega)
      (show j.val ≤ p.length - 1 by omega)
    simpa only [(spec i).2.1, (spec j).2.1] using hij
  apply hcycles ⟨ds, hclosed, hverts⟩
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact (spec i).1

end SphereMap

-- @node: selectedSet_no_cycle
/-- Suppose [the map is a sphere triangulation](hyp:hT), [adjacent faces have
opposite colors](hyp:hcol), [the two states assign different vertices to every
nonouter black triangle](hyp:hpair), [the edges opposite the second state's
assigned vertices form a forest](hyp:hforest), and [the map has no separating
triangle](hyp:hsep).
If [the prescribed edge lies on the outer face](hyp:he0), then [a simple cycle
whose every edge belongs to the selected set](hyp:hC) [cannot exist](goal). -/
lemma selectedSet_no_cycle (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T)
    (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ selectedSet T hT col hcol t0 s e0 he0) : False := by
  let d0 := outerEdgeDart T t0 e0 he0
  let O := orientedP0 T hT col hcol t0 s e0 he0
  have hd0 : T.edgeOf d0 = e0 :=
    (Classical.choose_spec (exists_outerEdgeDart T t0 e0 he0)).1
  have hf0 : T.faceOf d0 = t0 := outerEdgeDart_face T t0 e0 he0
  have hr0 : T.vert d0 ∈ roots T t0 ∧ T.head d0 ∈ roots T t0 := by
    have h := faceDart_endpoints_incident T hT d0
    rw [hf0] at h
    exact h
  have hnonroot (d : T.Dart) (hd : d ∈ O) : T.vert d ∉ roots T t0 :=
    (Finset.mem_sdiff.mp (orientedP0_tail_nonRoot T hT col hcol t0 s e0 he0 d hd)).2
  have root_only (d : T.Dart) (hd : d ∈ insert d0 O) (hr : T.vert d ∈ roots T t0) : d = d0 := by
    rcases Finset.mem_insert.mp hd with he | he
    · exact he
    · exact (hnonroot d he hr).elim
  have htail : ∀ d ∈ insert d0 O, ∀ e ∈ insert d0 O, T.vert d = T.vert e → d = e := by
    intro d hd e he h
    rcases Finset.mem_insert.mp hd with hd | hd
    · subst d
      exact (root_only e he (h ▸ hr0.1)).symm
    · rcases Finset.mem_insert.mp he with he | he
      · subst e
        exact (hnonroot d hd (h.symm ▸ hr0.1)).elim
      · exact orientedP0_tail_injective T hT col hcol t0 s e0 he0 d e hd he h
  have hcover (d : T.Dart) (hd : d ∈ C.val) : d ∈ insert d0 O ∨ T.edgeInv d ∈ insert d0 O := by
    by_cases he : T.edgeOf d = e0
    · rcases (T.edgeOf_eq_iff d0 d).mp (hd0.trans he.symm) with he | he
      · exact Or.inl (he.symm ▸ Finset.mem_insert_self _ _)
      · right
        have hi : T.edgeInv d = d0 := (congrArg T.edgeInv he).trans (T.edgeInv_involutive d0)
        exact hi.symm ▸ Finset.mem_insert_self _ _
    · have hp : T.edgeOf d ∈ selectedSet0 T hT col hcol t0 s e0 he0 :=
        Finset.mem_erase.mpr ⟨he, hC d hd⟩
      rcases selectedSet0_edge_orientation T hT col hcol t0 s e0 he0 d hp with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · exact Or.inr (Finset.mem_insert_of_mem h)
  have hdirected : ∃ D : T.Cycle, ∀ d ∈ D.val, d ∈ insert d0 O := by
    rcases T.cycle_directed_or_reverse (insert d0 O) htail C hcover with h | h
    · exact ⟨C, h⟩
    · refine ⟨reverseCycle T C, ?_⟩
      intro d hd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
      exact h e (List.mem_reverse.mp he)
  obtain ⟨D, hD⟩ := hdirected
  have hO (d : T.Dart) (hd : d ∈ D.val) : d ∈ O := by
    rcases Finset.mem_insert.mp (hD d hd) with he | he
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
      have hs := D.property.1.2.2 i
      let j : Fin D.val.length := ⟨(i.val + 1) % D.val.length, T.nextIndex_lt D.val i⟩
      have hnext := root_only (D.val.get j) (hD _ (List.get_mem _ _)) (by
        rw [← hs, hi, he]
        exact hr0.2)
      rw [hi, he, hnext] at hs
      exact (hT.props.2.1.1 d0 hs.symm).elim
    · exact he
  have hnonzero : (D.val.map (delta T (normalizedColoring T col t0))).sum ≠ 0 := by
    rcases orientedP0_cycle_delta_sum T hT col hcol t0 s e0 he0 D hO with h | h <;>
      rw [h] <;> norm_num
  obtain ⟨outer, hout⟩ := T.exists_face_outside_cycle_leftRegion hT.props.1 D
  apply hnonzero
  apply cycle_delta_zero_of_unique_selected_faces T hT (normalizedColoring T col t0)
    (normalizedColoring_partition T col hcol t0) D outer hout
    {e | e ∈ selectedSet T hT col hcol t0 s e0 he0}
  · intro d hd
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (hO d hd)).1
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, congrArg T.edgeOf ht⟩)
  · intro f hf
    cases hc : normalizedColoring T col t0 f with
    | false =>
      exact selectedSet_white_face_existsUnique T hT col hcol t0
        r s hpair hforest hsep e0 he0 f hc
    | true => exact selectedSet_black_face_existsUnique_of_color T hT col hcol t0 s e0 he0 f hc

-- @node: selectedSet_isForest_of_pair
/-- If [the map is a sphere triangulation](hyp:hT), [adjacent faces have opposite
colors](hyp:hcol), [the two states assign different vertices to every nonouter
black triangle](hyp:hpair), [the edges opposite the second state's assigned
vertices form a forest](hyp:hforest), [the map has no separating
triangle](hyp:hsep), and [the
prescribed edge lies on the outer face](hyp:he0), then [the selected edges form
a spanning forest](goal). -/
lemma selectedSet_isForest_of_pair (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (r s : State T col t0) (hpair : IsPair T col t0 r s)
    (hforest : QsForest T col t0 s) (hsep : TreesNoSeparatingTriangle T)
    (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) :
    IsSpanningForest T {e | e ∈ selectedSet T hT col hcol t0 s e0 he0} := by
  apply T.isSpanningForest_of_no_cycle hT.props.2.1
  intro C hC
  exact selectedSet_no_cycle T hT col hcol t0 r s hpair hforest hsep e0 he0 C hC

end OaiPairedStatesHamiltonian
