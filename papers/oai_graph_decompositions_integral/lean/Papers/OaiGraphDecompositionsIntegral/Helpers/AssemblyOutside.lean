module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyInside
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BlockPartition

/-! # Small-support pieces outside the high-degree closure

Restrict to unordered endpoint-block pairs before the degeneracy splitting.
The ambient degree bound outside the closure survives both edge deletions.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- Suppose [G is a subgraph of H](hyp:hG), [J is contained in the piece of G
outside Y for the unordered block pair a](hyp:hJ), [each block has at most c
vertices](hyp:hblock), and [every vertex outside Y has degree in H at most
the square root of n](hyp:hdegree). If [n is at least one](hyp:hn), [twice c
is at most n/100](hyp:hc), and [J has degeneracy at most s](hyp:hd), [J has at
most n/4 nonisolated vertices, degeneracy at most s, and maximum degree at
most n to the power two thirds](goal). -/
-- @node: assembly_outside_block_bounds
lemma assembly_outside_block_bounds (H G J : SimpleGraph V) (Y : Finset V)
    (n s B c : ℕ) (block : V → Fin B) (a : Sym2 (Fin B))
    (hG : G ≤ H)
    (hJ : J ≤ blockPairPiece (insideSetPiece G (Finset.univ \ Y)) block a)
    (hblock : ∀ i, (Finset.univ.filter (fun v => block v = i)).card ≤ c)
    (hdegree : ∀ v ∉ Y, (H.degree v : ℝ) ≤ Real.sqrt n)
    (hn : 1 ≤ n) (hc : (2 : ℝ) * c ≤ (n : ℝ) / 100)
    (hd : degeneracy J ≤ s) : DegreeEmbeddingBounds J n s := by
  classical
  have hsupport : nonisolated J ⊆
      nonisolated (blockPairPiece (insideSetPiece G (Finset.univ \ Y)) block a) := by
    intro v hv
    obtain ⟨w, hw⟩ := (J.degree_pos_iff_exists_adj v).mp (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (SimpleGraph.degree_pos_iff_exists_adj _ v).mpr ⟨w, hJ hw⟩⟩
  have hcard : ((nonisolated J).card : ℝ) ≤ 2 * c := by
    exact_mod_cast (Finset.card_le_card hsupport).trans
      (blockPairPiece_support_card _ block c hblock a)
  have hmax : J.maxDegree ≤ ⌊Real.sqrt (n : ℝ)⌋₊ := by
    apply J.maxDegree_le_of_forall_degree_le
    intro v
    by_cases hv : v ∈ Y
    · have hzero : J.degree v = 0 := by
        apply (J.degree_eq_zero v).mpr
        intro w hw
        exact (Finset.mem_sdiff.mp (hJ hw).1.2.1).2 hv
      rw [hzero]
      exact Nat.zero_le _
    · apply Nat.le_floor
      exact (show (J.degree v : ℝ) ≤ H.degree v by
        exact_mod_cast J.degree_le_of_le
          ((hJ.trans (blockPairPiece_le _ _ _)).trans
            ((insideSetPiece_le _ _).trans hG))).trans (hdegree v hv)
  have hmax' : (J.maxDegree : ℝ) ≤ Real.sqrt n :=
    (show (J.maxDegree : ℝ) ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) by
      exact_mod_cast hmax).trans (Nat.floor_le (Real.sqrt_nonneg _))
  refine ⟨?_, hd, ?_⟩
  · have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · apply hmax'.trans
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)

open Classical in
/-- Suppose [G is a subgraph of H](hyp:hG), [each block has at most c
vertices](hyp:hblock), [every vertex outside Y has degree in H at most the
square root of n](hyp:hdegree), [n is at least one](hyp:hn), and [twice c is
at most n/100](hyp:hc). Then [the edges of G outside Y can be partitioned into
pieces indexed by unordered block pairs and 1000 groups, each with at most
n/4 nonisolated vertices, maximum degree at most n to the power two thirds,
and degeneracy at most the ceiling of twice the degeneracy of H divided by 1000](goal). -/
-- @node: assembly_outside_partition_bounds
lemma assembly_outside_partition_bounds (H G : SimpleGraph V) (Y : Finset V)
    (n B c : ℕ) (block : V → Fin B) (hG : G ≤ H)
    (hblock : ∀ i, (Finset.univ.filter (fun v => block v = i)).card ≤ c)
    (hdegree : ∀ v ∉ Y, (H.degree v : ℝ) ≤ Real.sqrt n)
    (hn : 1 ≤ n) (hc : (2 : ℝ) * c ≤ (n : ℝ) / 100) :
    let s := ⌈2 * (degeneracy H : ℝ) / assemblySplittingFactor⌉₊
    ∃ P : Sym2 (Fin B) × Fin assemblySplittingFactor → SimpleGraph V,
      (∀ i, P i ≤ insideSetPiece G (Finset.univ \ Y)) ∧
      (∀ e ∈ (insideSetPiece G (Finset.univ \ Y)).edgeSet,
        ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, DegreeEmbeddingBounds (P i) n s := by
  classical
  dsimp only
  let s := ⌈2 * (degeneracy H : ℝ) / assemblySplittingFactor⌉₊
  let F := fun a => blockPairPiece (insideSetPiece G (Finset.univ \ Y)) block a
  have hFH (a) : F a ≤ H :=
    (blockPairPiece_le _ _ _).trans ((insideSetPiece_le _ _).trans hG)
  have hsplit (a) : ∃ P : Fin assemblySplittingFactor → SimpleGraph V,
      (∀ i, P i ≤ F a) ∧
      (∀ u v, (F a).Adj u v → ∃! i, (P i).Adj u v) ∧
      ∀ i, degeneracy (P i) ≤ s := by
    apply split_supported_graph assemblySplittingFactor s
      (by norm_num [assemblySplittingFactor]) Finset.univ (F a)
    · exact (degeneracy_mono (hFH a)).trans
        ((by omega : degeneracy H ≤ 2 * degeneracy H).trans (assembly_split_capacity _))
    · simp only [Finset.coe_univ, Set.subset_univ]
  choose P hP hpart hd using hsplit
  refine ⟨fun i => P i.1 i.2,
    fun i => (hP i.1 i.2).trans (blockPairPiece_le _ _ _), ?_, ?_⟩
  · intro e he
    obtain ⟨a, ha, hau⟩ := blockPairPiece_partition _ block e he
    have hparts : ∃! i, e ∈ (P a i).edgeSet := by
      induction e using Sym2.inductionOn with
      | hf u v => exact hpart a u v ha
    obtain ⟨i, hi, hiu⟩ := hparts
    refine ⟨(a, i), hi, ?_⟩
    rintro ⟨b, j⟩ hj
    have hb : b = a := hau b (SimpleGraph.edgeSet_mono (hP b j) hj)
    subst b
    exact Prod.ext rfl (hiu j hj)
  · rintro ⟨a, i⟩
    exact assembly_outside_block_bounds H G (P a i) Y n s B c block a hG
      (hP a i) hblock hdegree hn hc (hd a i)

end Papers.OaiGraphDecompositionsIntegral
