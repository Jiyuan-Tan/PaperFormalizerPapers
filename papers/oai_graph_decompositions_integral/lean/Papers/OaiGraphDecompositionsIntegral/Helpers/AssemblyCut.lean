module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyInside
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BlockPartition

/-! # Splitting cut edges by outside endpoint and bounded neighbor groups -/

@[expose] public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type}

/-- For [a graph G](hyp:G) and [a vertex set Y](hyp:Y), the [cut piece](goal)
retains exactly the edges of G with one endpoint in Y and the other outside Y. -/
-- @node: cutSetPiece
def cutSetPiece (G : SimpleGraph V) (Y : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ Y ∧ v ∉ Y) ∨ (v ∈ Y ∧ u ∉ Y))
  symm := ⟨by rintro u v ⟨h, hcut⟩; exact ⟨h.symm, hcut.symm⟩⟩
  loopless := ⟨by rintro v ⟨h, _⟩; exact G.irrefl h⟩

/-- [The cut piece of G across Y is a subgraph of G](goal). -/
-- @node: cutSetPiece_le
lemma cutSetPiece_le (G : SimpleGraph V) (Y : Finset V) : cutSetPiece G Y ≤ G :=
  fun _ _ h => h.1

/-- For [a graph G](hyp:G), [a vertex set Y](hyp:Y), [an assignment of vertices
to blocks](hyp:block), [an assignment of neighbor groups for each vertex](hyp:color),
[a block b](hyp:b), and [a group i](hyp:i), the [grouped cut piece](goal)
retains the edges crossing Y whose outside endpoint has block b and assigns
the inside endpoint to group i. -/
-- @node: cutGroupedPiece
def cutGroupedPiece {B M : ℕ} (G : SimpleGraph V) (Y : Finset V)
    (block : V → Fin B) (color : V → V → Fin M) (b : Fin B) (i : Fin M) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧
    ((u ∈ Y ∧ v ∉ Y ∧ block v = b ∧ color v u = i) ∨
      (v ∈ Y ∧ u ∉ Y ∧ block u = b ∧ color u v = i))
  symm := ⟨by rintro u v ⟨h, hcut⟩; exact ⟨h.symm, hcut.symm⟩⟩
  loopless := ⟨by rintro v ⟨h, _⟩; exact G.irrefl h⟩

/-- [Each grouped cut piece is a subgraph of the full cut piece across Y](goal). -/
-- @node: cutGroupedPiece_le
lemma cutGroupedPiece_le {B M : ℕ} (G : SimpleGraph V) (Y : Finset V)
    (block : V → Fin B) (color : V → V → Fin M) (b : Fin B) (i : Fin M) :
    cutGroupedPiece G Y block color b i ≤ cutSetPiece G Y := by
  rintro u v ⟨h, hcut⟩
  exact ⟨h, hcut.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)⟩

/-- [Every edge crossing Y belongs to exactly one piece indexed by the block
of its outside endpoint and the group assigned to its inside endpoint](goal). -/
-- @node: cutGroupedPiece_partition
lemma cutGroupedPiece_partition {B M : ℕ} (G : SimpleGraph V) (Y : Finset V)
    (block : V → Fin B) (color : V → V → Fin M) :
    ∀ e ∈ (cutSetPiece G Y).edgeSet,
      ∃! a : Fin B × Fin M, e ∈ (cutGroupedPiece G Y block color a.1 a.2).edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    rcases he.2 with h | h
    · refine ⟨(block v, color v u), ⟨he.1, Or.inl ⟨h.1, h.2, rfl, rfl⟩⟩, ?_⟩
      rintro ⟨b, i⟩ ⟨_, hi⟩
      rcases hi with hi | hi
      · exact Prod.ext hi.2.2.1.symm hi.2.2.2.symm
      · exact False.elim (h.2 hi.1)
    · refine ⟨(block u, color u v), ⟨he.1, Or.inr ⟨h.1, h.2, rfl, rfl⟩⟩, ?_⟩
      rintro ⟨b, i⟩ ⟨_, hi⟩
      rcases hi with hi | hi
      · exact False.elim (h.2 hi.1)
      · exact Prod.ext hi.2.2.1.symm hi.2.2.2.symm

variable [Fintype V] [DecidableEq V]

open Classical in
/-- Suppose [G is a subgraph of H](hyp:hG), [M is positive](hyp:hM),
[each vertex block contains at most c vertices](hyp:hblock), and [each vertex
outside Y has at most M times s neighbors in Y in H](hyp:hdegree).
Then [the cut edges of G across Y admit a partition indexed by blocks and M
groups, with at most c nonisolated outside vertices per piece and outside
degrees at most s](goal). -/
-- @node: assembly_cut_partition_bounds
lemma assembly_cut_partition_bounds (H G : SimpleGraph V) (Y : Finset V)
    (B M s c : ℕ) (block : V → Fin B) (hG : G ≤ H) (hM : 0 < M)
    (hblock : ∀ b, (Finset.univ.filter (fun v => block v = b)).card ≤ c)
    (hdegree : ∀ w ∉ Y, (H.neighborFinset w ∩ Y).card ≤ M * s) :
    ∃ P : Fin B × Fin M → SimpleGraph V,
      (∀ i, P i ≤ cutSetPiece G Y) ∧
      (∀ e ∈ (cutSetPiece G Y).edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      (∀ i, ((Finset.univ \ Y).filter (fun w => 0 < (P i).degree w)).card ≤ c) ∧
      ∀ i w, w ∉ Y → (P i).degree w ≤ s := by
  classical
  let A : V → Finset V := fun w => if w ∈ Y then ∅ else H.neighborFinset w ∩ Y
  have hcap (w : V) : (A w).card ≤ M * s := by
    by_cases hw : w ∈ Y
    · simp [A, hw]
    · simpa only [A, if_neg hw] using hdegree w hw
  choose color hcolor using fun w => split_neighbor_groups (A w) M s hM (hcap w)
  let P : Fin B × Fin M → SimpleGraph V := fun i =>
    cutGroupedPiece G Y block color i.1 i.2
  have hout (i : Fin B × Fin M) (w v : V) (hw : w ∉ Y) (h : (P i).Adj w v) :
      v ∈ Y ∧ block w = i.1 ∧ color w v = i.2 := by
    rcases h.2 with h | h
    · exact False.elim (hw h.1)
    · exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  refine ⟨P, fun i => cutGroupedPiece_le _ _ _ _ _ _,
    cutGroupedPiece_partition G Y block color, ?_, ?_⟩
  · intro i
    apply (Finset.card_le_card ?_).trans (hblock i.1)
    intro w hw
    obtain ⟨v, hv⟩ := ((P i).degree_pos_iff_exists_adj w).mp (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hout i w v (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2 hv).2.1⟩
  · intro i w hw
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply (Finset.card_le_card ?_).trans (hcolor w i.2)
    intro v hv
    have hadj := ((P i).mem_neighborFinset w v).mp hv
    obtain ⟨hvY, _, hvcolor⟩ := hout i w v hw hadj
    apply Finset.mem_filter.mpr
    refine ⟨?_, hvcolor⟩
    simp only [A, if_neg hw, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hG hadj.1, hvY⟩

end Papers.OaiGraphDecompositionsIntegral
