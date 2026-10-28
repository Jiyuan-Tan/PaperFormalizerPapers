module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.ForestSplitting
public import Mathlib.Data.Sym.Card
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Balanced vertex blocks and unordered endpoint-block pieces

All block assignments and edge pieces are deterministic. Diagonal block
pairs are included, and unused blocks and edge pieces may be empty.
-/

@[expose] public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

-- @node: vertex_blocks_of_capacity
/-- If [the number of vertices is at most B times c](hyp:hcap), then
[the vertices can be assigned to B blocks with at most c vertices in each block](goal). -/
lemma vertex_blocks_of_capacity (B c : ℕ) (hcap : Fintype.card V ≤ B * c) :
    ∃ block : V → Fin B, ∀ i,
      (Finset.univ.filter (fun v => block v = i)).card ≤ c := by
  classical
  obtain ⟨e⟩ : Nonempty (V ↪ Fin B × Fin c) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcap)
  refine ⟨fun v => (e v).1, ?_⟩
  intro i
  let S := Finset.univ.filter (fun v => (e v).1 = i)
  have hinj : Function.Injective (fun v : ↥S => (e v.val).2) := by
    intro v w h
    apply Subtype.ext
    apply e.injective
    exact Prod.ext
      (((Finset.mem_filter.mp v.property).2).trans
        ((Finset.mem_filter.mp w.property).2).symm) h
  have hc := Fintype.card_le_of_injective _ hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

-- @node: balanced_vertex_blocks
/-- If [the number B of blocks is positive](hyp:hB) and [there are at most n
vertices](hyp:hsize), then [the vertices can be assigned to B blocks, each
containing at most the ceiling of n divided by B vertices](goal). -/
lemma balanced_vertex_blocks (n B : ℕ) (hB : 0 < B) (hsize : Fintype.card V ≤ n) :
    ∃ block : V → Fin B, ∀ i,
      (Finset.univ.filter (fun v => block v = i)).card ≤ ⌈(n : ℝ) / B⌉₊ := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hc := Nat.le_ceil ((n : ℝ) / B)
  have hcap : n ≤ B * ⌈(n : ℝ) / B⌉₊ := by
    have : (n : ℝ) ≤ (B : ℝ) * ⌈(n : ℝ) / B⌉₊ := by
      have := (div_le_iff₀ hBr).mp hc
      nlinarith
    exact_mod_cast this
  exact vertex_blocks_of_capacity B _ (hsize.trans hcap)

-- @node: blockPairPiece
/-- Given [a graph G](hyp:G), [an assignment of its vertices to blocks](hyp:block),
and [an unordered pair a of blocks](hyp:a), [the block-pair piece](goal) retains
exactly the edges of G whose endpoints have block pair a. -/
def blockPairPiece {B : ℕ} (G : SimpleGraph V) (block : V → Fin B)
    (a : Sym2 (Fin B)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ s(block u, block v) = a
  symm := ⟨by intro u v h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro v h; exact G.irrefl h.1⟩

-- @node: blockPairPiece_le
/-- [The piece selected by any unordered pair of endpoint blocks is a subgraph
of the original graph](goal). -/
lemma blockPairPiece_le {B : ℕ} (G : SimpleGraph V) (block : V → Fin B)
    (a : Sym2 (Fin B)) : blockPairPiece G block a ≤ G := fun _ _ h => h.1

-- @node: blockPairPiece_partition
/-- [Every edge of the graph belongs to exactly one piece indexed by an unordered
pair of endpoint blocks, including pairs consisting of the same block twice](goal). -/
lemma blockPairPiece_partition {B : ℕ} (G : SimpleGraph V) (block : V → Fin B) :
    ∀ e ∈ G.edgeSet, ∃! a, e ∈ (blockPairPiece G block a).edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    refine ⟨s(block u, block v), ⟨he, rfl⟩, ?_⟩
    intro a ha
    exact ha.2.symm

variable [DecidableEq V]

open Classical in
-- @node: blockPairPiece_support
/-- [Every nonisolated vertex of the piece indexed by blocks i and j belongs
to block i or block j](goal). -/
lemma blockPairPiece_support {B : ℕ} (G : SimpleGraph V) (block : V → Fin B)
    (i j : Fin B) :
    nonisolated (blockPairPiece G block s(i, j)) ⊆
      (Finset.univ.filter (fun v => block v = i)) ∪
      (Finset.univ.filter (fun v => block v = j)) := by
  classical
  intro v hv
  obtain ⟨w, hvw⟩ := ((blockPairPiece G block s(i, j)).degree_pos_iff_exists_adj v).mp
    (Finset.mem_filter.mp hv).2
  rcases Sym2.eq_iff.mp hvw.2 with h | h
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩)

open Classical in
-- @node: blockPairPiece_support_card
/-- If [every block has at most c vertices](hyp:hc), then [every piece indexed
by an unordered pair of blocks has at most twice c nonisolated vertices](goal). -/
lemma blockPairPiece_support_card {B : ℕ} (G : SimpleGraph V) (block : V → Fin B)
    (c : ℕ) (hc : ∀ i, (Finset.univ.filter (fun v => block v = i)).card ≤ c)
    (a : Sym2 (Fin B)) :
    (nonisolated (blockPairPiece G block a)).card ≤ 2 * c := by
  classical
  induction a using Sym2.inductionOn with
  | hf i j =>
    calc
      _ ≤ ((Finset.univ.filter (fun v => block v = i)) ∪
          (Finset.univ.filter (fun v => block v = j))).card :=
        Finset.card_le_card (blockPairPiece_support G block i j)
      _ ≤ (Finset.univ.filter (fun v => block v = i)).card +
          (Finset.univ.filter (fun v => block v = j)).card := Finset.card_union_le _ _
      _ ≤ 2 * c := by have := hc i; have := hc j; omega

-- @node: blockPairPiece_isStarForest
/-- If [G is a star forest](hyp:hG), then [each piece obtained by selecting
an unordered pair of endpoint blocks is also a star forest](goal). -/
lemma blockPairPiece_isStarForest {B : ℕ} (G : SimpleGraph V) (block : V → Fin B)
    (hG : IsStarForest G) (a : Sym2 (Fin B)) :
    IsStarForest (blockPairPiece G block a) :=
  isStarForest_mono (blockPairPiece_le G block a) hG

open Classical in
-- @node: small_support_star_partition
/-- If [d is positive](hyp:hdpos), [H has degeneracy at most d](hyp:hd), and
[the vertex count is at most B times c](hyp:hcap), then [there is a family of
subgraphs of H indexed by one of d choices, one of two choices, and an unordered
pair of B blocks, assigning every edge exactly once, with each subgraph a star
forest having at most twice c nonisolated vertices](goal). -/
lemma small_support_star_partition (H : SimpleGraph V) (d B c : ℕ)
    (hdpos : 0 < d) (hd : degeneracy H ≤ d) (hcap : Fintype.card V ≤ B * c) :
    ∃ P : (Fin d × Fin 2) × Sym2 (Fin B) → SimpleGraph V,
      (∀ i, P i ≤ H) ∧
      (∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      (∀ i, IsStarForest (P i)) ∧
      ∀ i, (nonisolated (P i)).card ≤ 2 * c := by
  classical
  obtain ⟨F, hF, hpart, hstar⟩ := degeneracy_star_partition H d hdpos hd
  obtain ⟨block, hblock⟩ := vertex_blocks_of_capacity B c hcap
  let P := fun i : (Fin d × Fin 2) × Sym2 (Fin B) => blockPairPiece (F i.1) block i.2
  refine ⟨P, fun i => (blockPairPiece_le _ _ _).trans (hF i.1), ?_,
    fun i => blockPairPiece_isStarForest _ _ (hstar i.1) _,
    fun i => blockPairPiece_support_card _ _ c hblock _⟩
  intro e he
  obtain ⟨i, hei, hi⟩ := hpart e he
  obtain ⟨a, hea, ha⟩ := blockPairPiece_partition (F i) block e hei
  refine ⟨(i, a), hea, ?_⟩
  rintro ⟨j, b⟩ hjb
  have hj : j = i := hi j (SimpleGraph.edgeSet_mono (blockPairPiece_le _ _ _) hjb)
  subst j
  exact Prod.ext rfl (ha b hjb)

-- @node: star_block_piece_count
/-- [The number of indices consisting of one of d choices, one of two choices,
and an unordered pair of B blocks allowing repetition is the product of d, B,
and B plus one](goal). -/
lemma star_block_piece_count (d B : ℕ) :
    Fintype.card ((Fin d × Fin 2) × Sym2 (Fin B)) = d * B * (B + 1) := by
  have h := Nat.add_one_mul_choose_eq B 1
  simp only [Nat.choose_one_right] at h
  simp only [Fintype.card_prod, Fintype.card_fin, Sym2.card]
  calc
    d * 2 * (B + 1).choose 2 = d * ((B + 1).choose 2 * 2) := by ring
    _ = d * B * (B + 1) := by rw [← h]; ring

end Papers.OaiGraphDecompositionsIntegral
