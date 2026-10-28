module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyParameters
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Degeneracy

/-! # The small-support pieces inside the high-degree closure

Splitting deletes edges, so both support and degree bounds survive. These
are the deterministic inputs to the direct embedding proposition.
-/

@[expose] public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V] [DecidableEq V]

/-- For [a graph H](hyp:H) and [a vertex set Y](hyp:Y), the [inside piece](goal)
retains exactly the edges of H with both endpoints in Y. -/
-- @node: insideSetPiece
def insideSetPiece (H : SimpleGraph V) (Y : Finset V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ u ∈ Y ∧ v ∈ Y
  symm := ⟨by rintro u v ⟨h, hu, hv⟩; exact ⟨h.symm, hv, hu⟩⟩
  loopless := ⟨by rintro u ⟨h, _⟩; exact H.irrefl h⟩

/-- [The piece of H inside Y is a subgraph of H](goal). -/
-- @node: insideSetPiece_le
lemma insideSetPiece_le (H : SimpleGraph V) (Y : Finset V) :
    insideSetPiece H Y ≤ H := fun _ _ h => h.1

open Classical in
/-- If [every nonisolated vertex of J lies in Y](hyp:hJ), [Y has at most
n to the power two thirds vertices](hyp:hY), [this power is at most n/4](hyp:hcut),
and [J has degeneracy at most s](hyp:hd), [J has at most n/4 nonisolated vertices,
degeneracy at most s, and maximum degree at most n to the power two thirds](goal). -/
-- @node: assembly_supported_degree_bounds
lemma assembly_supported_degree_bounds (J : SimpleGraph V) (Y : Finset V)
    (n s : ℕ) (hJ : J.support ⊆ (Y : Set V))
    (hY : (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3))
    (hcut : (n : ℝ) ^ ((2 : ℝ) / 3) ≤ (n : ℝ) / 4)
    (hd : degeneracy J ≤ s) : DegreeEmbeddingBounds J n s := by
  classical
  have hsupport : nonisolated J ⊆ Y := by
    intro v hv
    exact hJ ((J.degree_pos_iff_mem_support v).mp (Finset.mem_filter.mp hv).2)
  have hdegree : J.maxDegree ≤ Y.card := by
    apply J.maxDegree_le_of_forall_degree_le
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro w hw
    exact hJ (J.mem_support.mpr ⟨v, ((J.mem_neighborFinset v w).mp hw).symm⟩)
  refine ⟨?_, hd, ?_⟩
  · exact (show ((nonisolated J).card : ℝ) ≤ Y.card by
      exact_mod_cast Finset.card_le_card hsupport).trans (hY.trans hcut)
  · exact (show (J.maxDegree : ℝ) ≤ Y.card by exact_mod_cast hdegree).trans hY

/-- [Twice d is at most the assembly splitting factor times the ceiling of
twice d divided by that factor](goal). -/
-- @node: assembly_split_capacity
lemma assembly_split_capacity (d : ℕ) :
    2 * d ≤ assemblySplittingFactor *
      ⌈2 * (d : ℝ) / assemblySplittingFactor⌉₊ := by
  have h := Nat.le_ceil (2 * (d : ℝ) / assemblySplittingFactor)
  have hM : (0 : ℝ) < assemblySplittingFactor := by norm_num [assemblySplittingFactor]
  have hh := (div_le_iff₀ hM).mp h
  have : (2 : ℝ) * d ≤ (assemblySplittingFactor : ℝ) *
      ⌈2 * (d : ℝ) / assemblySplittingFactor⌉₊ := by nlinarith
  exact_mod_cast this

open Classical in
/-- If [G is a subgraph of H](hyp:hG), [Y has at most n to the power two thirds
vertices](hyp:hY), and [this power is at most n/4](hyp:hcut), [the edges of G
inside Y can be partitioned into 1000 subgraphs, each with at most n/4
nonisolated vertices, maximum degree at most n to the power two thirds, and
degeneracy at most the ceiling of twice the degeneracy of H divided by 1000](goal). -/
-- @node: assembly_inside_partition_bounds
lemma assembly_inside_partition_bounds (H G : SimpleGraph V) (Y : Finset V)
    (n : ℕ) (hG : G ≤ H)
    (hY : (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3))
    (hcut : (n : ℝ) ^ ((2 : ℝ) / 3) ≤ (n : ℝ) / 4) :
    let s := ⌈2 * (degeneracy H : ℝ) / assemblySplittingFactor⌉₊
    ∃ P : Fin assemblySplittingFactor → SimpleGraph V,
      (∀ i, P i ≤ insideSetPiece G Y) ∧
      (∀ e ∈ (insideSetPiece G Y).edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, DegreeEmbeddingBounds (P i) n s := by
  classical
  dsimp only
  let s := ⌈2 * (degeneracy H : ℝ) / assemblySplittingFactor⌉₊
  have hdeg : degeneracy (insideSetPiece G Y) ≤ assemblySplittingFactor * s :=
    (degeneracy_mono ((insideSetPiece_le G Y).trans hG)).trans
      ((by omega : degeneracy H ≤ 2 * degeneracy H).trans (assembly_split_capacity _))
  have hsupp : (insideSetPiece G Y).support ⊆ (Y : Set V) := by
    rintro v ⟨w, hvw⟩
    exact hvw.2.1
  obtain ⟨P, hP, hpart, hd⟩ := split_supported_graph assemblySplittingFactor s
    (by norm_num [assemblySplittingFactor]) Y (insideSetPiece G Y) hdeg hsupp
  refine ⟨P, hP, ?_, ?_⟩
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v => exact hpart u v he
  · intro i
    apply assembly_supported_degree_bounds (P i) Y n s _ hY hcut (hd i)
    rintro v ⟨w, hvw⟩
    exact (hP i hvw).2.1

end Papers.OaiGraphDecompositionsIntegral
