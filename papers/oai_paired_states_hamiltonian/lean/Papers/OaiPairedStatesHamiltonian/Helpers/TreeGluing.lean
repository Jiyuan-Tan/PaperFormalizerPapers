module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Finite gluing of induced trees along a connected common subtree. -/

public section

namespace OaiPairedStatesHamiltonian

open Classical
attribute [local instance] propDecidable
set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false

variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- [The number of edges induced by a vertex set A equals the number of original
graph edges whose endpoints both belong to A](goal). -/
-- @node: induced_edge_card_filter
lemma induced_edge_card_filter (A : Set V) :
    Nat.card (G.induce A).edgeSet =
      (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ A)).card := by
  classical
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  apply Finset.card_bij (fun e _ => Sym2.map Subtype.val e)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      apply Finset.mem_filter.mpr
      refine ⟨G.mem_edgeFinset.mpr ((G.induce A).mem_edgeFinset.mp he), ?_⟩
      simp only [Sym2.map_pair_eq, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
      exact ⟨u.property, v.property⟩
  · intro e he f hf h
    exact Sym2.map.injective Subtype.val_injective h
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨he, hA⟩ := Finset.mem_filter.mp he
      have hu := hA u (by simp)
      have hv := hA v (by simp)
      exact ⟨s((⟨u, hu⟩ : A), (⟨v, hv⟩ : A)),
        (G.induce A).mem_edgeFinset.mpr (G.mem_edgeFinset.mp he), rfl⟩

-- @node: induced_vertex_card_union_inter
/-- [The sizes of the union and intersection of two finite vertex sets sum to
the sum of the sizes of the two sets](goal). -/
lemma induced_vertex_card_union_inter (A B : Set V) :
    Nat.card ↥(A ∪ B) + Nat.card ↥(A ∩ B) =
      Nat.card A + Nat.card B := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hu : (Finset.univ.filter (fun v => v ∈ A)) ∪
      (Finset.univ.filter (fun v => v ∈ B)) =
        Finset.univ.filter (fun v => v ∈ A ∪ B) := by
    ext v
    simp
  have hi : (Finset.univ.filter (fun v => v ∈ A)) ∩
      (Finset.univ.filter (fun v => v ∈ B)) =
        Finset.univ.filter (fun v => v ∈ A ∩ B) := by
    ext v
    simp
  simpa only [hu, hi] using Finset.card_union_add_card_inter
    (Finset.univ.filter (fun v => v ∈ A)) (Finset.univ.filter (fun v => v ∈ B))

/-- If [no edge joins a vertex in A outside B to a vertex in B outside A](hyp:hsep),
[the edge counts induced by the union and intersection of A and B sum to the
sum of their individual induced edge counts](goal). -/
-- @node: induced_edge_card_union_inter
lemma induced_edge_card_union_inter (A B : Set V)
    (hsep : ∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬ G.Adj u v) :
    Nat.card (G.induce (A ∪ B)).edgeSet + Nat.card (G.induce (A ∩ B)).edgeSet =
      Nat.card (G.induce A).edgeSet + Nat.card (G.induce B).edgeSet := by
  classical
  let E (S : Set V) := G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)
  have hu : E A ∪ E B = E (A ∪ B) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [E, Finset.mem_union, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        Sym2.mem_iff, forall_eq_or_imp, forall_eq]
      constructor
      · rintro (⟨h, hu, hv⟩ | ⟨h, hu, hv⟩)
        · exact ⟨h, Or.inl hu, Or.inl hv⟩
        · exact ⟨h, Or.inr hu, Or.inr hv⟩
      · rintro ⟨h, hu, hv⟩
        by_cases hua : u ∈ A
        · by_cases hva : v ∈ A
          · exact Or.inl ⟨h, hua, hva⟩
          · have hvb : v ∈ B := hv.resolve_left hva
            have hub : u ∈ B := by
              by_contra hn
              exact hsep u ⟨hua, hn⟩ v ⟨hvb, hva⟩ h
            exact Or.inr ⟨h, hub, hvb⟩
        · have hub : u ∈ B := hu.resolve_left hua
          by_cases hvb : v ∈ B
          · exact Or.inr ⟨h, hub, hvb⟩
          · exact (hsep v ⟨hv.resolve_right hvb, hvb⟩ u ⟨hub, hua⟩ h.symm).elim
  have hi : E A ∩ E B = E (A ∩ B) := by
    ext e
    simp only [E, Finset.mem_inter, Finset.mem_filter, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨he, ha⟩, _, hb⟩
      exact ⟨he, fun v hv => ⟨ha v hv, hb v hv⟩⟩
    · rintro ⟨he, h⟩
      exact ⟨⟨he, fun v hv => (h v hv).1⟩, he, fun v hv => (h v hv).2⟩
  rw [induced_edge_card_filter G (A ∪ B), induced_edge_card_filter G (A ∩ B),
    induced_edge_card_filter G A, induced_edge_card_filter G B]
  change (E (A ∪ B)).card + (E (A ∩ B)).card = (E A).card + (E B).card
  rw [← hu, ← hi]
  exact Finset.card_union_add_card_inter (E A) (E B)

/-- If [A induces a tree](hyp:hA), [B induces a tree](hyp:hB),
[their intersection induces a connected graph](hyp:hI), and
[no edge joins A outside B to B outside A](hyp:hsep), then
[their union induces a tree](goal). -/
-- @node: induced_tree_gluing
lemma induced_tree_gluing (A B : Set V)
    (hA : (G.induce A).IsTree) (hB : (G.induce B).IsTree)
    (hI : (G.induce (A ∩ B)).Connected)
    (hsep : ∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬ G.Adj u v) :
    (G.induce (A ∪ B)).IsTree := by
  classical
  have hIT : (G.induce (A ∩ B)).IsTree := by
    refine ⟨hI, ?_⟩
    let f : G.induce (A ∩ B) →g G.induce A :=
      ⟨fun v => ⟨v.val, v.property.1⟩, fun h => h⟩
    have hf : Function.Injective f := by
      intro u v h
      exact Subtype.ext (congrArg (fun z : A => (z.val : V)) h)
    exact hA.isAcyclic.comap f hf
  have hc : (G.induce (A ∪ B)).Connected :=
    SimpleGraph.induce_union_connected hA.connected.preconnected hB.connected.preconnected
      (by obtain ⟨v⟩ := hI.nonempty; exact ⟨v.val, v.property⟩)
  have hvertices := induced_vertex_card_union_inter A B
  have hedges := induced_edge_card_union_inter G A B hsep
  have ha := (SimpleGraph.isTree_iff_connected_and_card.mp hA).2
  have hb := (SimpleGraph.isTree_iff_connected_and_card.mp hB).2
  have hi := (SimpleGraph.isTree_iff_connected_and_card.mp hIT).2
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hc, ?_⟩
  omega

/-- If [A is contained in L](hyp:hA), [B is contained in R](hyp:hB), and
[membership in A and B agrees on the intersection of L and R](hyp:hagree), then
[A outside B is contained in L outside R, and B outside A is contained in R
outside L](goal). -/
-- @node: label_difference_subset_piece_difference
lemma label_difference_subset_piece_difference (L R A B : Set V)
    (hA : A ⊆ L) (hB : B ⊆ R)
    (hagree : ∀ v ∈ L ∩ R, v ∈ A ↔ v ∈ B) :
    A \ B ⊆ L \ R ∧ B \ A ⊆ R \ L := by
  constructor
  · rintro v ⟨ha, hb⟩
    exact ⟨hA ha, fun hr => hb ((hagree v ⟨hA ha, hr⟩).mp ha)⟩
  · rintro v ⟨hb, ha⟩
    exact ⟨hB hb, fun hl => ha ((hagree v ⟨hl, hB hb⟩).mpr hb)⟩

/-- Suppose [L and R cover all vertices](hyp:hcover), [A is contained in L](hyp:hA),
[B is contained in R](hyp:hB), [membership in A and B agrees on their pieces'
overlap](hyp:hagree), and [no edge joins L outside R to R outside L](hyp:hsep).
If [A and B each induce a tree](hyp:hAT,hBT), [the remaining vertices in each
piece also induce trees](hyp:hAT',hBT'), [the intersection of A and B induces a
connected graph](hyp:hI), and [the intersection of the two remaining sets
induces a connected graph](hyp:hI'), then [the union of A and B and its complement
both induce trees, and restricting that union to L and R recovers A and B,
respectively](goal). -/
-- @node: tree_partition_gluing
lemma tree_partition_gluing (L R A B : Set V)
    (hcover : L ∪ R = Set.univ) (hA : A ⊆ L) (hB : B ⊆ R)
    (hagree : ∀ v ∈ L ∩ R, v ∈ A ↔ v ∈ B)
    (hsep : ∀ u ∈ L \ R, ∀ v ∈ R \ L, ¬ G.Adj u v)
    (hAT : (G.induce A).IsTree) (hBT : (G.induce B).IsTree)
    (hAT' : (G.induce (L \ A)).IsTree) (hBT' : (G.induce (R \ B)).IsTree)
    (hI : (G.induce (A ∩ B)).Connected)
    (hI' : (G.induce ((L \ A) ∩ (R \ B))).Connected) :
    (G.induce (A ∪ B)).IsTree ∧ (G.induce (A ∪ B)ᶜ).IsTree ∧
      (A ∪ B) ∩ L = A ∧ (A ∪ B) ∩ R = B := by
  have hdiff := label_difference_subset_piece_difference L R A B hA hB hagree
  have hpos := induced_tree_gluing G A B hAT hBT hI
    (fun u hu v hv => hsep u (hdiff.1 hu) v (hdiff.2 hv))
  have hagree' : ∀ v ∈ L ∩ R, v ∈ L \ A ↔ v ∈ R \ B := by
    intro v hv
    exact ⟨fun ha => ⟨hv.2, fun hb => ha.2 ((hagree v hv).mpr hb)⟩,
      fun hb => ⟨hv.1, fun ha => hb.2 ((hagree v hv).mp ha)⟩⟩
  have hdiff' := label_difference_subset_piece_difference L R (L \ A) (R \ B)
    (fun _ h => h.1) (fun _ h => h.1) hagree'
  have hneg := induced_tree_gluing G (L \ A) (R \ B) hAT' hBT' hI'
    (fun u hu v hv => hsep u (hdiff'.1 hu) v (hdiff'.2 hv))
  have hcompl : (L \ A) ∪ (R \ B) = (A ∪ B)ᶜ := by
    ext v
    constructor
    · rintro (⟨hl, ha⟩ | ⟨hr, hb⟩)
      · exact fun h => h.elim ha (fun hb => ha ((hagree v ⟨hl, hB hb⟩).mpr hb))
      · exact fun h => h.elim (fun ha => hb ((hagree v ⟨hA ha, hr⟩).mp ha)) hb
    · intro hn
      have hv : v ∈ L ∪ R := hcover.symm ▸ Set.mem_univ v
      rcases hv with hl | hr
      · exact Or.inl ⟨hl, fun ha => hn (Or.inl ha)⟩
      · exact Or.inr ⟨hr, fun hb => hn (Or.inr hb)⟩
  refine ⟨hpos, hcompl ▸ hneg, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨ha | hb, hl⟩
      · exact ha
      · exact (hagree v ⟨hl, hB hb⟩).mpr hb
    · intro ha
      exact ⟨Or.inl ha, hA ha⟩
  · ext v
    constructor
    · rintro ⟨ha | hb, hr⟩
      · exact (hagree v ⟨hA ha, hr⟩).mp ha
      · exact hb
    · intro hb
      exact ⟨Or.inr hb, hB hb⟩

/-- If [S consists of one vertex or of the endpoints of an edge](hyp:hS), then
[the graph induced by S is connected](goal). -/
-- @node: boundary_label_connected
lemma boundary_label_connected (S : Set V)
    (hS : (∃ u, S = {u}) ∨ (∃ u v, G.Adj u v ∧ S = {u, v})) :
    (G.induce S).Connected := by
  rcases hS with ⟨u, rfl⟩ | ⟨u, v, huv, rfl⟩
  · exact SimpleGraph.IsTree.of_subsingleton.connected
  · exact SimpleGraph.induce_pair_connected_of_adj huv

/-- If [A induces an acyclic graph](hyp:hA) and [u is adjacent to v](hyp:huv),
[u is adjacent to w](hyp:huw), and [v is adjacent to w](hyp:hvw), then
[A cannot contain all three vertices u, v, and w](goal). -/
-- @node: triangle_not_subset_tree_label
lemma triangle_not_subset_tree_label (A : Set V) (hA : (G.induce A).IsAcyclic)
    (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    ¬ ({u, v, w} : Set V) ⊆ A := by
  classical
  intro hsub
  let a : A := ⟨u, hsub (by simp)⟩
  let b : A := ⟨v, hsub (by simp)⟩
  let c : A := ⟨w, hsub (by simp)⟩
  exact hA.cliqueFree (by decide : 3 ≤ 3) {a, b, c}
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩)

-- @node: nonempty_clique_induce_connected
/-- If [S is nonempty](hyp:hne) and [every two distinct vertices in S are
adjacent](hyp:hcl), then [the graph induced by S is connected](goal). -/
lemma nonempty_clique_induce_connected (S : Set V) (hne : S.Nonempty)
    (hcl : G.IsClique S) : (G.induce S).Connected := by
  let : Nonempty S := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.refl _
  · have h : (G.induce S).Adj u v :=
      hcl u.property v.property (fun h => huv (Subtype.ext h))
    exact h.reachable

/-- Suppose [L and R cover all vertices](hyp:hcover), [A is contained in L](hyp:hA),
[B is contained in R](hyp:hB), [membership in A and B agrees on the overlap](hyp:hagree),
and [no edge joins L outside R to R outside L](hyp:hsep). If [A and B induce
trees](hyp:hAT,hBT), [their respective complements within L and R induce
trees](hyp:hAT',hBT'), [u is adjacent to v](hyp:huv), [u is adjacent to w](hyp:huw),
[v is adjacent to w](hyp:hvw), and [the overlap consists exactly of u, v, and
w](hyp:hboundary), then [the union of A and B and its complement induce trees,
and its restrictions to L and R are A and B, respectively](goal). -/
-- @node: tree_partition_gluing_triangle
lemma tree_partition_gluing_triangle (L R A B : Set V)
    (hcover : L ∪ R = Set.univ) (hA : A ⊆ L) (hB : B ⊆ R)
    (hagree : ∀ x ∈ L ∩ R, x ∈ A ↔ x ∈ B)
    (hsep : ∀ u ∈ L \ R, ∀ v ∈ R \ L, ¬ G.Adj u v)
    (hAT : (G.induce A).IsTree) (hBT : (G.induce B).IsTree)
    (hAT' : (G.induce (L \ A)).IsTree) (hBT' : (G.induce (R \ B)).IsTree)
    (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hboundary : L ∩ R = {u, v, w}) :
    (G.induce (A ∪ B)).IsTree ∧ (G.induce (A ∪ B)ᶜ).IsTree ∧
      (A ∪ B) ∩ L = A ∧ (A ∪ B) ∩ R = B := by
  have hcl : G.IsClique (L ∩ R) := by
    rw [hboundary]
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩).isClique
  have hne : (A ∩ B).Nonempty := by
    have hn := triangle_not_subset_tree_label G (L \ A) hAT'.isAcyclic u v w huv huw hvw
    obtain ⟨x, hx, hn⟩ := Set.not_subset.mp hn
    have hxLR : x ∈ L ∩ R := hboundary.symm ▸ hx
    have hxA : x ∈ A := by
      by_contra ha
      exact hn ⟨hxLR.1, ha⟩
    exact ⟨x, hxA, (hagree x hxLR).mp hxA⟩
  have hne' : ((L \ A) ∩ (R \ B)).Nonempty := by
    have hn := triangle_not_subset_tree_label G A hAT.isAcyclic u v w huv huw hvw
    obtain ⟨x, hx, ha⟩ := Set.not_subset.mp hn
    have hxLR : x ∈ L ∩ R := hboundary.symm ▸ hx
    exact ⟨x, ⟨hxLR.1, ha⟩, hxLR.2, fun hb => ha ((hagree x hxLR).mpr hb)⟩
  apply tree_partition_gluing G L R A B hcover hA hB hagree hsep hAT hBT hAT' hBT'
  · exact nonempty_clique_induce_connected G _ hne
      (hcl.subset (show A ∩ B ⊆ L ∩ R from fun _ h => ⟨hA h.1, hB h.2⟩))
  · exact nonempty_clique_induce_connected G _ hne'
      (hcl.subset (show (L \ A) ∩ (R \ B) ⊆ L ∩ R from
        fun _ h => ⟨h.1.1, h.2.1⟩))

end OaiPairedStatesHamiltonian
