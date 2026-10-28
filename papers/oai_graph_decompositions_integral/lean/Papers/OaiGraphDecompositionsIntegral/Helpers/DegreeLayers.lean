module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Degeneracy
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Deterministic selection steps for the layered degree embedding

The independent-set estimate applies both to a low-degree residual graph
and to the graph of intersecting requirements in the Hall argument.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

open scoped BigOperators

variable {V : Type} [Fintype V]

/-- If H embeds into G preserving both adjacency and nonadjacency, then
[the degeneracy of H is at most the degeneracy of G](goal). -/
-- @node: degeneracy_le_of_embedding
lemma degeneracy_le_of_embedding {W : Type} [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : H ↪g G) :
    degeneracy H ≤ degeneracy G := by
  classical
  unfold degeneracy
  apply Finset.sup_le
  intro T hT
  have hTne := (Finset.mem_filter.mp hT).2
  let g : H.induce (T : Set W) ↪g G := f.comp (SimpleGraph.Embedding.induce _)
  let U : Finset V := (Set.range g).toFinset
  have hU : U.Nonempty := by
    obtain ⟨v, hv⟩ := hTne
    exact ⟨g ⟨v, hv⟩, by simp [U]⟩
  have heq : (H.induce (T : Set W)).minDegree = (G.induce (U : Set V)).minDegree := by
    let e : (Set.range g) ≃ (U : Set V) := {
      toFun := fun x => ⟨x.val, by simpa [U] using x.property⟩
      invFun := fun x => ⟨x.val, by simpa [U] using x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let iso : G.induce (Set.range g) ≃g G.induce (U : Set V) := {
      toEquiv := e
      map_rel_iff' := by intro a b; rfl }
    exact g.isoInduceRange.minDegree_eq.trans iso.minDegree_eq
  rw [heq]
  exact Finset.le_sup (f := fun S : Finset V => (G.induce (S : Set V)).minDegree)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩)

/-- [The degeneracy of the graph induced by G on S is at most the degeneracy
of G](goal). -/
-- @node: degeneracy_induce_le
lemma degeneracy_induce_le (G : SimpleGraph V) (S : Finset V) :
    degeneracy (G.induce (S : Set V)) ≤ degeneracy G := by
  classical
  exact degeneracy_le_of_embedding G _ (SimpleGraph.Embedding.induce _)

open Classical in
/-- [Every graph of degeneracy at most s whose nonisolated vertices all
belong to S has at most s times the number of vertices in S edges](goal). -/
-- @node: degree_edges_supported
lemma degree_edges_supported (s : ℕ) (S : Finset V) :
    ∀ G : SimpleGraph V, degeneracy G ≤ s → G.support ⊆ (S : Set V) →
      G.edgeFinset.card ≤ s * S.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro G hd hs
    by_cases hS : S.Nonempty
    · let : Nonempty (S : Set V) := hS.to_subtype
      obtain ⟨v, hvdeg⟩ := (G.induce (S : Set V)).exists_minimal_degree_vertex
      have hmin : (G.induce (S : Set V)).minDegree ≤ degeneracy G :=
        Finset.le_sup (f := fun S : Finset V => (G.induce (S : Set V)).minDegree)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩)
      have hv : G.degree v.val ≤ s := by
        have heq := G.degree_induce_of_support_subset hs v
        have heq' : (G.induce (S : Set V)).degree v = G.degree v.val := by
          convert heq using 1
          congr 1
          exact Subsingleton.elim _ _
        rw [← heq', ← hvdeg]
        exact hmin.trans hd
      have hsdel : (G.deleteIncidenceSet v.val).support ⊆ (↑(S.erase v.val) : Set V) := by
        intro x hx
        have hh := G.support_deleteIncidenceSet_subset v.val hx
        exact Finset.mem_erase.mpr ⟨hh.2, hs hh.1⟩
      have hdel := ih (S.erase v.val) (Finset.erase_ssubset v.property)
        (G.deleteIncidenceSet v.val) ((degeneracy_mono (G.deleteIncidenceSet_le v.val)).trans hd)
        hsdel
      have heq := G.card_edgeFinset_deleteIncidenceSet v.val
      have hle := G.degree_le_card_edgeFinset v.val
      have hScard := Finset.card_erase_add_one v.property
      calc
        G.edgeFinset.card =
            (G.deleteIncidenceSet v.val).edgeFinset.card + G.degree v.val := by omega
        _ ≤ s * (S.erase v.val).card + s := by
          apply Nat.add_le_add _ hv
          convert hdel using 1
          congr 1
          ext e
          simp only [SimpleGraph.mem_edgeFinset]
        _ = s * S.card := by nlinarith
    · have hbot : G = ⊥ := by
        ext u w
        constructor
        · intro huw
          exact (hS ⟨u, hs (G.mem_support.mpr ⟨w, huw⟩)⟩).elim
        · simp
      subst G
      simp [SimpleGraph.edgeFinset]

open Classical in
/-- If [G has degeneracy at most s](hyp:hd), then [the sum of its vertex
degrees is at most 2s times its number of vertices](goal). -/
-- @node: degree_sum_le_of_degeneracy
lemma degree_sum_le_of_degeneracy (G : SimpleGraph V) (s : ℕ) (hd : degeneracy G ≤ s) :
    (∑ v, G.degree v) ≤ 2 * s * Fintype.card V := by
  classical
  have he := degree_edges_supported s Finset.univ G hd (by simp)
  rw [G.sum_degrees_eq_twice_card_edges]
  simpa only [Finset.card_univ, Nat.mul_assoc] using Nat.mul_le_mul_left 2 he

/-- If [every vertex of G has degree at most D](hyp:hD), then [G has an
independent set I such that its total number of vertices is at most
(D + 1) times the size of I](goal). -/
-- @node: degree_independent_set_size
lemma degree_independent_set_size (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀ v, G.degree v ≤ D) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      Fintype.card V ≤ (D + 1) * I.card := by
  classical
  obtain ⟨I, hI⟩ := G.maximumIndepSet_exists
  have hcover : Finset.univ ⊆ I.biUnion (fun v => insert v (G.neighborFinset v)) := by
    intro v hv
    by_contra hnot
    have hvi : v ∉ I := by
      intro hvi
      exact hnot (Finset.mem_biUnion.mpr ⟨v, hvi, Finset.mem_insert_self _ _⟩)
    have hnonadj : ∀ w ∈ I, ¬ G.Adj w v := by
      intro w hw hadj
      exact hnot (Finset.mem_biUnion.mpr
        ⟨w, hw, Finset.mem_insert_of_mem ((G.mem_neighborFinset w v).mpr hadj)⟩)
    have hext : G.IsIndepSet (↑(insert v I) : Set V) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | hai
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (hab rfl).elim
        · exact fun hadj => hnonadj b hb hadj.symm
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hnonadj a hai
        · exact hI.isIndepSet hai hb hab
    have := hI.maximum (insert v I) hext
    rw [Finset.card_insert_of_notMem hvi] at this
    omega
  refine ⟨I, hI.isIndepSet, ?_⟩
  calc
    Fintype.card V = Finset.univ.card := (Finset.card_univ).symm
    _ ≤ (I.biUnion (fun v => insert v (G.neighborFinset v))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ v ∈ I, (insert v (G.neighborFinset v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ I, (D + 1) := by
      apply Finset.sum_le_sum
      intro v hv
      exact (Finset.card_insert_le _ _).trans (by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
          Nat.add_le_add_right (hD v) 1)
    _ = (D + 1) * I.card := by simp [Nat.mul_comm]

omit [Fintype V] in
open Classical in
/-- If [every vertex in the graph induced on S has degree at most D](hyp:hD),
then [S contains an independent set I of G such that the size of S is at
most (D + 1) times the size of I](goal). -/
-- @node: degree_independent_subset_size
lemma degree_independent_subset_size (G : SimpleGraph V) (S : Finset V)
    (D : ℕ) (hD : ∀ v : S, (G.induce (S : Set V)).degree v ≤ D) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet (I : Set V) ∧
      S.card ≤ (D + 1) * I.card := by
  classical
  obtain ⟨I, hI, hcard⟩ := degree_independent_set_size (G.induce (S : Set V)) D hD
  let e : S ↪ V := Function.Embedding.subtype _
  refine ⟨I.map e, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    exact w.property
  · intro v hv w hw hne hadj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hw
    exact hI ha hb (fun hab => hne (congrArg e hab)) hadj
  · simpa using hcard

open Classical in
/-- If [G has degeneracy at most s](hyp:hd), then [at least half of its
vertices have degree at most 4s](goal). -/
-- @node: degree_low_degree_half
lemma degree_low_degree_half (G : SimpleGraph V) (s : ℕ) (hd : degeneracy G ≤ s) :
    Fintype.card V ≤ 2 * (Finset.univ.filter (fun v => G.degree v ≤ 4 * s)).card := by
  classical
  let L := Finset.univ.filter (fun v => G.degree v ≤ 4 * s)
  let B := Finset.univ.filter (fun v => ¬ G.degree v ≤ 4 * s)
  have hpart : L.card + B.card = Fintype.card V := by
    simpa only [L, B, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun v => G.degree v ≤ 4 * s)
  have hsum : (4 * s + 1) * B.card ≤ ∑ v, G.degree v := by
    calc
      _ = ∑ _v ∈ B, (4 * s + 1) := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ B, G.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        have := (Finset.mem_filter.mp hv).2
        omega
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have havg := hsum.trans (degree_sum_le_of_degeneracy G s hd)
  have hhalf : B.card ≤ L.card := by
    by_contra h
    have hlt : L.card + 1 ≤ B.card := by omega
    nlinarith
  change Fintype.card V ≤ 2 * L.card
  omega

open Classical in
/-- If [G has degeneracy at most s](hyp:hd), then [it has an independent
set I whose vertices all have degree at most 4s and whose size times
2(4s + 1) is at least the total number of vertices](goal). -/
-- @node: degree_last_layer
lemma degree_last_layer (G : SimpleGraph V) (s : ℕ) (hd : degeneracy G ≤ s) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      (∀ v ∈ I, G.degree v ≤ 4 * s) ∧
      Fintype.card V ≤ 2 * (4 * s + 1) * I.card := by
  classical
  let L := Finset.univ.filter (fun v => G.degree v ≤ 4 * s)
  have hL : ∀ v : L, (G.induce (L : Set V)).degree v ≤ 4 * s := by
    intro v
    have hdeg : (G.induce (L : Set V)).degree v ≤ G.degree v.val := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_le_of_injective
        (fun w : (G.induce (L : Set V)).neighborSet v =>
          (⟨w.val.val, w.property⟩ : G.neighborSet v.val))
        (fun a b hab => Subtype.ext (Subtype.ext
          (congrArg (fun w : G.neighborSet v.val => w.val) hab)))
    exact hdeg.trans (Finset.mem_filter.mp v.property).2
  obtain ⟨I, hIL, hi, hcard⟩ := degree_independent_subset_size G L (4 * s) hL
  refine ⟨I, hi, ?_, ?_⟩
  · intro v hv
    exact (Finset.mem_filter.mp (hIL hv)).2
  · have hhalf := degree_low_degree_half G s hd
    change Fintype.card V ≤ 2 * L.card at hhalf
    nlinarith

end Papers.OaiGraphDecompositionsIntegral
