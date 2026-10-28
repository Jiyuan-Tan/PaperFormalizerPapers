module
public import Papers.OaiGraphDecompositionsIntegral.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! # Splitting a graph by degeneracy -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

-- @node: degeneracy_mono
/-- If [G is a subgraph of H](hyp:h), then [the degeneracy of G is at most
the degeneracy of H](goal). -/
lemma degeneracy_mono {G H : SimpleGraph V} (h : G ≤ H) :
    degeneracy G ≤ degeneracy H := by
  classical
  unfold degeneracy
  apply Finset.sup_le
  intro S hS
  exact (SimpleGraph.minDegree_le_minDegree
      (G := G.induce (S : Set V)) (H := H.induce (S : Set V)) (fun _ _ hxy => h hxy)).trans
    (Finset.le_sup (f := fun S : Finset V => (H.induce (S : Set V)).minDegree) hS)

open Classical in
-- @node: degeneracy_le_of_delete
/-- If [removing all edges incident to v leaves a graph of degeneracy at most
k](hyp:hdel) and [v has degree at most k in the original graph](hyp:hv), then
[the original graph has degeneracy at most k](goal). -/
lemma degeneracy_le_of_delete (G : SimpleGraph V) (v : V) (k : ℕ)
    (hdel : degeneracy (G.deleteIncidenceSet v) ≤ k) (hv : G.degree v ≤ k) :
    degeneracy G ≤ k := by
  classical
  let : DecidableRel (G.deleteIncidenceSet v).Adj := fun _ _ => Classical.propDecidable _
  unfold degeneracy at hdel ⊢
  apply Finset.sup_le
  intro S hS
  by_cases hvs : v ∈ S
  · have hdeg : (G.induce (S : Set V)).degree ⟨v, hvs⟩ ≤ G.degree v := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_le_of_injective
        (fun w : (G.induce (S : Set V)).neighborSet ⟨v, hvs⟩ =>
          (⟨w.val.val, w.property⟩ : G.neighborSet v))
        (fun a b hab => Subtype.ext (Subtype.ext
          (congrArg (fun w : G.neighborSet v => w.val) hab)))
    exact ((G.induce (S : Set V)).minDegree_le_degree ⟨v, hvs⟩).trans
      (hdeg.trans hv)
  · have hmin : (G.induce (S : Set V)).minDegree =
        ((G.deleteIncidenceSet v).induce (S : Set V)).minDegree := by
      simp only [G.induce_deleteIncidenceSet_of_notMem hvs]
    rw [hmin]
    exact (Finset.le_sup (f := fun S : Finset V =>
      ((G.deleteIncidenceSet v).induce (S : Set V)).minDegree) hS).trans hdel

omit [Fintype V] in
-- @node: split_neighbor_groups
/-- If [m is positive](hyp:hm) and [A has at most m times k elements](hyp:hA),
then [all vertices can be assigned to m groups so that each group contains at
most k elements of A](goal). -/
lemma split_neighbor_groups (A : Finset V) (m k : ℕ)
    (hm : 0 < m) (hA : A.card ≤ m * k) :
    ∃ c : V → Fin m, ∀ i, (A.filter (fun x => c x = i)).card ≤ k := by
  classical
  obtain ⟨e⟩ : Nonempty (A ↪ Fin m × Fin k) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hA)
  let c : V → Fin m := fun x => if hx : x ∈ A then (e ⟨x, hx⟩).1 else ⟨0, hm⟩
  refine ⟨c, fun i => ?_⟩
  let f : (A.filter (fun x => c x = i)) → Fin k :=
    fun x => (e ⟨x.val, (Finset.mem_filter.mp x.property).1⟩).2
  have hf : Function.Injective f := by
    intro a b hab
    have hfirst (x : (A.filter (fun x => c x = i))) :
        (e ⟨x.val, (Finset.mem_filter.mp x.property).1⟩).1 = i := by
      simpa [c, (Finset.mem_filter.mp x.property).1] using
        (Finset.mem_filter.mp x.property).2
    have heq := e.injective (Prod.ext ((hfirst a).trans (hfirst b).symm) hab)
    exact Subtype.ext (congrArg (fun x : A => x.val) heq)
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

-- @node: split_supported_graph
/-- If [m is positive](hyp:hm), then [every graph whose degeneracy is at most
m times k and whose nonisolated vertices lie in S admits m subgraphs that assign
each edge exactly once and each have degeneracy at most k](goal). -/
lemma split_supported_graph (m k : ℕ) (hm : 0 < m) (S : Finset V) :
    ∀ H : SimpleGraph V, degeneracy H ≤ m * k → H.support ⊆ (S : Set V) →
    ∃ P : Fin m → SimpleGraph V,
      (∀ i, P i ≤ H) ∧
      (∀ u w, H.Adj u w → ∃! i, (P i).Adj u w) ∧
      ∀ i, degeneracy (P i) ≤ k := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro H hd hsupport
    by_cases hS : S.Nonempty
    · let : Nonempty (S : Set V) := hS.to_subtype
      obtain ⟨v, hvdeg⟩ := (H.induce (S : Set V)).exists_minimal_degree_vertex
      have hmin : (H.induce (S : Set V)).minDegree ≤ degeneracy H :=
        Finset.le_sup (f := fun S : Finset V => (H.induce (S : Set V)).minDegree)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩)
      have hv : H.degree v.val ≤ m * k := by
        have heq := H.degree_induce_of_support_subset hsupport v
        have heq' : (H.induce (S : Set V)).degree v = H.degree v.val := by
          convert heq using 1
          congr 1
          exact Subsingleton.elim _ _
        rw [← heq', ← hvdeg]
        exact hmin.trans hd
      have hdel : degeneracy (H.deleteIncidenceSet v.val) ≤ m * k :=
        (degeneracy_mono (H.deleteIncidenceSet_le v.val)).trans hd
      have hsdel : (H.deleteIncidenceSet v.val).support ⊆ (↑(S.erase v.val) : Set V) := by
        intro x hx
        have hh := H.support_deleteIncidenceSet_subset v.val hx
        exact Finset.mem_erase.mpr ⟨hh.2, hsupport hh.1⟩
      obtain ⟨P, hP, hpart, hdeg⟩ := ih (S.erase v.val)
        (Finset.erase_ssubset v.property) (H.deleteIncidenceSet v.val) hdel hsdel
      obtain ⟨c, hc⟩ := split_neighbor_groups (H.neighborFinset v.val) m k hm
        (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hv)
      have hPv (i : Fin m) (x : V) : ¬ (P i).Adj v.val x := by
        intro hx
        exact (SimpleGraph.deleteIncidenceSet_adj.mp (hP i hx)).2.1 rfl
      let G : Fin m → SimpleGraph V := fun i => {
        Adj := fun u w => (P i).Adj u w ∨
          H.Adj u w ∧ ((u = v.val ∧ c w = i) ∨ (w = v.val ∧ c u = i))
        symm := ⟨by
          intro u w huw
          rcases huw with hp | ⟨hh, hcol⟩
          · exact Or.inl hp.symm
          · exact Or.inr ⟨hh.symm, hcol.elim Or.inr Or.inl⟩⟩
        loopless := ⟨by
          intro u hu
          exact hu.elim (fun hp => (P i).irrefl hp) (fun hu => H.irrefl hu.1)⟩ }
      have hGP (i : Fin m) : (G i).deleteIncidenceSet v.val = P i := by
        ext u w
        simp only [SimpleGraph.deleteIncidenceSet_adj]
        change ((P i).Adj u w ∨ _) ∧ _ ↔ (P i).Adj u w
        constructor
        · rintro ⟨hp | ⟨_, hcol⟩, hu, hw⟩
          · exact hp
          · rcases hcol with ⟨huv, _⟩ | ⟨hwv, _⟩
            · exact (hu huv).elim
            · exact (hw hwv).elim
        · intro hp
          exact ⟨Or.inl hp, (SimpleGraph.deleteIncidenceSet_adj.mp (hP i hp)).2⟩
      refine ⟨G, ?_, ?_, ?_⟩
      · intro i u w huw
        exact huw.elim (fun hp => H.deleteIncidenceSet_le v.val (hP i hp)) And.left
      · intro u w huw
        by_cases hu : u = v.val
        · subst u
          refine ⟨c w, Or.inr ⟨huw, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
          intro i hi
          rcases hi with hp | ⟨_, hcol⟩
          · exact (hPv i w hp).elim
          · rcases hcol with ⟨_, hci⟩ | ⟨hw, _⟩
            · exact hci.symm
            · exact (H.ne_of_adj huw hw.symm).elim
        · by_cases hw : w = v.val
          · subst w
            refine ⟨c u, Or.inr ⟨huw, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
            intro i hi
            rcases hi with hp | ⟨_, hcol⟩
            · exact (hPv i u hp.symm).elim
            · rcases hcol with ⟨huv, _⟩ | ⟨_, hci⟩
              · exact (hu huv).elim
              · exact hci.symm
          · obtain ⟨i, hi, huniq⟩ := hpart u w
              (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨huw, hu, hw⟩)
            refine ⟨i, Or.inl hi, ?_⟩
            intro j hj
            apply huniq j
            rcases hj with hp | ⟨_, hcol⟩
            · exact hp
            · exact (hcol.elim (fun h => hu h.1) (fun h => hw h.1)).elim
      · intro i
        apply degeneracy_le_of_delete (G i) v.val k
        · simpa only [hGP] using hdeg i
        · have hN : (G i).neighborFinset v.val =
              (H.neighborFinset v.val).filter (fun x => c x = i) := by
            ext x
            simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
            change ((P i).Adj v.val x ∨ _) ↔ _
            simp only [hPv, false_or, true_and]
            constructor
            · rintro ⟨hh, hci | ⟨hx, _⟩⟩
              · exact ⟨hh, hci⟩
              · exact (H.ne_of_adj hh hx.symm).elim
            · exact fun hh => ⟨hh.1, Or.inl hh.2⟩
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          convert hc i using 1
          congr 1
          ext x
          simpa only [SimpleGraph.mem_neighborFinset, Finset.mem_filter] using
            (Finset.ext_iff.mp hN x)
    · refine ⟨fun _ => ⊥, fun _ => bot_le, ?_, ?_⟩
      · intro u w huw
        have hu := hsupport (H.mem_support.mpr ⟨w, huw⟩)
        exact (hS ⟨u, hu⟩).elim
      · intro i
        unfold degeneracy
        apply Finset.sup_le
        intro T hT
        simpa only [SimpleGraph.induce_bot, SimpleGraph.minDegree_bot_eq_zero] using
          (Nat.zero_le k)

-- @node: lem:split
/-- If [the vertex set is finite](hyp:hfinite), [the number m of pieces is
positive](hyp:hm), and [H has degeneracy at most d](hyp:hd), then [H admits
m subgraphs assigning each edge exactly once, each with degeneracy at most
the ceiling of d divided by m](goal). -/
lemma degeneracy_split (H : SimpleGraph V) (d m : ℕ)
    (hfinite : FiniteSimpleGraphs V) (hm : SplitCount m) (hd : SplitDegeneracy H d) :
    ∃ P : Fin m → SimpleGraph V,
      (∀ i, P i ≤ H) ∧
      (∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, degeneracy (P i) ≤ (d + m - 1) / m := by
  classical
  have hmpos : 0 < m := hm
  have hceil : d ≤ m * ((d + m - 1) / m) := by
    have hdiv := Nat.div_add_mod (d + m - 1) m
    have hmod := Nat.mod_lt (d + m - 1) hmpos
    omega
  obtain ⟨P, hP, hpart, hdeg⟩ := split_supported_graph m ((d + m - 1) / m) hmpos
    Finset.univ H ((show degeneracy H ≤ d from hd).trans hceil)
    (by simp only [Finset.coe_univ, Set.subset_univ])
  refine ⟨P, hP, ?_, hdeg⟩
  intro e he
  induction e using Sym2.inductionOn with
  | hf u w => exact hpart u w he

end Papers.OaiGraphDecompositionsIntegral
