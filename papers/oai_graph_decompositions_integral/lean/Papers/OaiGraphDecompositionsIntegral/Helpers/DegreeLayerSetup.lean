module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeNumerics
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeLayerSequence
public import Papers.OaiGraphDecompositionsIntegral.Helpers.QLower
public import Mathlib.Algebra.BigOperators.Fin

/-! # Bins and uniform cutoffs for the deterministic layer certificate

This file constructs the bins before sampling the host and assembles the
numerical hypotheses needed for the subsequent conditional Hall estimates.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

open scoped BigOperators

/-- If [the sum of the prescribed bin sizes is at most n](hyp:ha), then
[there are pairwise disjoint bins among n vertices with exactly those sizes](goal). -/
-- @node: degree_disjoint_bins
lemma degree_disjoint_bins {n t : ℕ} (a : Fin t → ℕ) (ha : ∑ i, a i ≤ n) :
    ∃ bin : Fin t → Finset (Fin n),
      (∀ i, (bin i).card = a i) ∧ Pairwise (fun i j => Disjoint (bin i) (bin j)) := by
  classical
  obtain ⟨e⟩ : Nonempty ((i : Fin t) × Fin (a i) ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using ha)
  let bin : Fin t → Finset (Fin n) := fun i =>
    Finset.univ.image (fun j : Fin (a i) => e ⟨i, j⟩)
  refine ⟨bin, ?_, ?_⟩
  · intro i
    have hinj : Function.Injective (fun j : Fin (a i) => e ⟨i, j⟩) := by
      intro x y hxy
      simpa using e.injective hxy
    simp only [bin, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hxi
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hxj
    exact hij (congrArg Sigma.fst (e.injective (hu.trans hv.symm)))

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Given [a degree-layer sequence partitioning S](hyp:h), with
[at most n/4 vertices in S](hyp:hS) and [at least one layer](hyp:ht),
[there are pairwise disjoint bins among n vertices, each sized to its layer
plus the integer layer slack, whose total size is at most n/2](goal). -/
-- @node: degree_layer_bins
lemma degree_layer_bins (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) {S : Finset V} {L : List (Finset V)} (h : DegreeLayerSequence G s S L)
    (n : ℕ) (hS : (S.card : ℝ) ≤ (n : ℝ) / 4) (ht : 0 < L.length) :
    ∃ bin : Fin L.length → Finset (Fin n),
      (∀ i, (bin i).card = (L.get i).card + layerSlack n L.length ht) ∧
      Pairwise (fun i j => Disjoint (bin i) (bin j)) ∧
      2 * (∑ i, (bin i).card) ≤ n := by
  classical
  have hsum : ∑ i : Fin L.length, (L.get i).card = S.card := by
    rw [← Fin.sum_ofFn]
    rw [List.ofFn_comp' L.get Finset.card, List.ofFn_get]
    exact (degree_layer_sequence_card G s h).1
  have hslack : 4 * (L.length * layerSlack n L.length ht) ≤ n := by
    have := Nat.div_mul_le_self n (4 * L.length)
    dsimp [layerSlack]
    nlinarith
  have hScard : 4 * S.card ≤ n := by
    have : (4 : ℝ) * S.card ≤ n := by linarith
    exact_mod_cast this
  have htotal : 2 * (∑ i : Fin L.length,
      ((L.get i).card + layerSlack n L.length ht)) ≤ n := by
    rw [Finset.sum_add_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  obtain ⟨bin, hbin, hdisj⟩ := degree_disjoint_bins (n := n)
    (fun i : Fin L.length => (L.get i).card + layerSlack n L.length ht) (by omega)
  refine ⟨bin, hbin, hdisj, ?_⟩
  simpa only [hbin] using htotal

/-- [There is a cutoff N of at least two such that, for every n at least N
and every admissible density and degeneracy bound, any graph with at most n
vertices satisfying the degree-embedding bounds and having an edge admits
a nonempty degree-layer sequence on its nonisolated vertices, with at most
120 times the squared natural logarithm of n layers, integer layer slack
times r to the power 4s divided by one plus 4s times the maximum degree
at least five times that logarithm, and layer count times 2/n³ at most
one half](goal). -/
-- @node: degree_layer_setup_exists
lemma degree_layer_setup_exists :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (n : ℕ) (r : ℝ) (s : ℕ),
      N ≤ n → TransferParameters n r s →
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V ≤ n → DegreeEmbeddingBounds G n s → G.edgeSet.Nonempty →
        ∃ L : List (Finset V), DegreeLayerSequence G s (nonisolated G) L ∧
          ∃ ht : 0 < L.length,
            (L.length : ℝ) ≤ 120 * naturalLog n ^ 2 ∧
            5 * naturalLog n ≤ (layerSlack n L.length ht : ℝ) * r ^ (4 * s) /
              (1 + 4 * (s : ℝ) * G.maxDegree) ∧
            (L.length : ℝ) * (2 / (n : ℝ) ^ 3) ≤ 1 / 2 := by
  obtain ⟨N₁, hN₁two, hN₁⟩ := degree_hall_cutoff_exists 120 (by norm_num)
  obtain ⟨N₂, hN₂two, hN₂⟩ := degree_layer_failure_cutoff_exists 120 (by norm_num)
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ naturalLog n :=
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop).eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max N₀ (max N₁ N₂), by omega, ?_⟩
  intro n r s hn hp V _ _ G _ hsize hb hedge
  have hs : 1 ≤ s := (degeneracy_pos_of_edge G hedge).trans_le hb.2.1
  have hsupport : (nonisolated G).Nonempty := by
    obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp
      (SimpleGraph.edgeSet_nonempty.mp hedge)
    refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact (G.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩
  obtain ⟨L, hL, hlen⟩ := degree_layer_sequence_log_squared G s hb.2.1 hs
    (nonisolated G) n r hp (by omega) (hN₀ n (by omega))
    ((Finset.card_le_card (Finset.subset_univ _)).trans (by simpa using hsize))
  have ht := degree_layer_sequence_length_pos G s hL hsupport
  refine ⟨L, hL, ht, hlen, ?_, hN₂ n (by omega) L.length hlen⟩
  exact hN₁ n (by omega) r s L.length G.maxDegree ht hp hlen (by positivity) hb.2.2

end Papers.OaiGraphDecompositionsIntegral
