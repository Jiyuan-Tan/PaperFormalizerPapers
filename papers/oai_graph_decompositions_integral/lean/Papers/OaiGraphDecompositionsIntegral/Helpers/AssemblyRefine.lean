module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyCut

/-! # Joining and refining deterministic edge partitions -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type}

/-- Suppose [A and B have disjoint edge sets](hyp:hdisj), [every piece P is a
subgraph of A](hyp:hP), [every piece Q is a subgraph of B](hyp:hQ), [P assigns
each edge of A to exactly one piece](hyp:hpartP), and [Q assigns each edge of
B to exactly one piece](hyp:hpartQ). If [every P piece has containment
threshold at most R in an n-vertex host](hyp:hboundP) and [every Q piece has
the same threshold bound](hyp:hboundQ), [the union of A and B admits an edge
partition indexed by the disjoint union of the two index sets, with every
piece a subgraph of the union and having containment threshold at most R](goal). -/
-- @node: edge_partition_sum
lemma edge_partition_sum {I J : Type} (A B : SimpleGraph V) (n : ℕ) (R : ℝ)
    (hdisj : ∀ e ∈ A.edgeSet, e ∉ B.edgeSet)
    (P : I → SimpleGraph V) (Q : J → SimpleGraph V)
    (hP : ∀ i, P i ≤ A) (hQ : ∀ j, Q j ≤ B)
    (hpartP : ∀ e ∈ A.edgeSet, ∃! i, e ∈ (P i).edgeSet)
    (hpartQ : ∀ e ∈ B.edgeSet, ∃! j, e ∈ (Q j).edgeSet)
    (hboundP : ∀ i, containmentThreshold (P i) n ≤ R)
    (hboundQ : ∀ j, containmentThreshold (Q j) n ≤ R) :
    ∃ S : I ⊕ J → SimpleGraph V, (∀ i, S i ≤ A ⊔ B) ∧
      (∀ e ∈ (A ⊔ B).edgeSet, ∃! i, e ∈ (S i).edgeSet) ∧
      ∀ i, containmentThreshold (S i) n ≤ R := by
  let S : I ⊕ J → SimpleGraph V := Sum.elim P Q
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact (hP i).trans le_sup_left
    | inr j => exact (hQ j).trans le_sup_right
  · intro e he
    rw [SimpleGraph.edgeSet_sup] at he
    rcases he with he | he
    · obtain ⟨i, hi, hu⟩ := hpartP e he
      refine ⟨Sum.inl i, hi, ?_⟩
      intro a ha
      cases a with
      | inl j => exact congrArg Sum.inl (hu j ha)
      | inr j => exact False.elim (hdisj e he (SimpleGraph.edgeSet_mono (hQ j) ha))
    · obtain ⟨j, hj, hu⟩ := hpartQ e he
      refine ⟨Sum.inr j, hj, ?_⟩
      intro a ha
      cases a with
      | inl i => exact False.elim (hdisj e (SimpleGraph.edgeSet_mono (hP i) ha) he)
      | inr i => exact congrArg Sum.inr (hu i ha)
  · intro i
    cases i with
    | inl i => exact hboundP i
    | inr j => exact hboundQ j

/-- Suppose [each first-stage graph G is a subgraph of H](hyp:hG), [these graphs
partition the edges of H](hyp:hpartG), [each second-stage piece is a subgraph
of its corresponding first-stage graph](hyp:hP), [the second-stage pieces
partition the edges of each first-stage graph](hyp:hpartP), and [each
second-stage piece has containment threshold at most R in an n-vertex host](hyp:hbound).
Then [H admits an edge partition into subgraphs indexed by pairs of stage
indices, all with containment threshold at most R in an n-vertex host](goal). -/
-- @node: edge_partition_refine
lemma edge_partition_refine {I J : Type} (H : SimpleGraph V) (n : ℕ) (R : ℝ)
    (G : I → SimpleGraph V) (P : I → J → SimpleGraph V)
    (hG : ∀ i, G i ≤ H)
    (hpartG : ∀ e ∈ H.edgeSet, ∃! i, e ∈ (G i).edgeSet)
    (hP : ∀ i j, P i j ≤ G i)
    (hpartP : ∀ i e, e ∈ (G i).edgeSet → ∃! j, e ∈ (P i j).edgeSet)
    (hbound : ∀ i j, containmentThreshold (P i j) n ≤ R) :
    ∃ Q : I × J → SimpleGraph V, (∀ i, Q i ≤ H) ∧
      (∀ e ∈ H.edgeSet, ∃! i, e ∈ (Q i).edgeSet) ∧
      ∀ i, containmentThreshold (Q i) n ≤ R := by
  refine ⟨fun a => P a.1 a.2, fun a => (hP a.1 a.2).trans (hG a.1), ?_,
    fun a => hbound a.1 a.2⟩
  intro e he
  obtain ⟨i, hi, hiu⟩ := hpartG e he
  obtain ⟨j, hj, hju⟩ := hpartP i e hi
  refine ⟨(i, j), hj, ?_⟩
  rintro ⟨a, b⟩ hab
  have ha : a = i := hiu a (SimpleGraph.edgeSet_mono (hP a b) hab)
  subst a
  exact Prod.ext rfl (hju b hab)

variable [Fintype V] [DecidableEq V]

/-- If [the edges of G inside Y admit a partition indexed by I into subgraphs
with containment threshold at most R in an n-vertex host](hyp:hinside), [the
edges outside Y admit such a partition indexed by O](hyp:houtside), and
[the edges crossing Y admit such a partition indexed by C](hyp:hcut), [all
edges of G admit a partition into subgraphs indexed by the disjoint union
of I, O, and C, with every piece having containment threshold at most R in
an n-vertex host](goal). -/
-- @node: edge_partition_regions
lemma edge_partition_regions {I O C : Type} (G : SimpleGraph V) (Y : Finset V)
    (n : ℕ) (R : ℝ)
    (hinside : ∃ P : I → SimpleGraph V,
      (∀ i, P i ≤ insideSetPiece G Y) ∧
      (∀ e ∈ (insideSetPiece G Y).edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, containmentThreshold (P i) n ≤ R)
    (houtside : ∃ P : O → SimpleGraph V,
      (∀ i, P i ≤ insideSetPiece G (Finset.univ \ Y)) ∧
      (∀ e ∈ (insideSetPiece G (Finset.univ \ Y)).edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, containmentThreshold (P i) n ≤ R)
    (hcut : ∃ P : C → SimpleGraph V,
      (∀ i, P i ≤ cutSetPiece G Y) ∧
      (∀ e ∈ (cutSetPiece G Y).edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, containmentThreshold (P i) n ≤ R) :
    ∃ P : I ⊕ (O ⊕ C) → SimpleGraph V,
      (∀ i, P i ≤ G) ∧
      (∀ e ∈ G.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, containmentThreshold (P i) n ≤ R := by
  classical
  obtain ⟨Pi, hPi, hparti, hbi⟩ := hinside
  obtain ⟨Po, hPo, hparto, hbo⟩ := houtside
  obtain ⟨Pc, hPc, hpartc, hbc⟩ := hcut
  have hdisjOC : ∀ e ∈ (insideSetPiece G (Finset.univ \ Y)).edgeSet,
      e ∉ (cutSetPiece G Y).edgeSet := by
    intro e
    induction e using Sym2.inductionOn with
    | hf u v =>
      rintro ⟨_, hu, hv⟩ ⟨_, h | h⟩
      · exact (Finset.mem_sdiff.mp hu).2 h.1
      · exact (Finset.mem_sdiff.mp hv).2 h.1
  obtain ⟨Poc, hPoc, hpartoc, hboc⟩ := edge_partition_sum _ _ n R hdisjOC
    Po Pc hPo hPc hparto hpartc hbo hbc
  have hdisjI : ∀ e ∈ (insideSetPiece G Y).edgeSet,
      e ∉ (insideSetPiece G (Finset.univ \ Y) ⊔ cutSetPiece G Y).edgeSet := by
    intro e
    induction e using Sym2.inductionOn with
    | hf u v =>
      rintro ⟨_, hu, hv⟩ (h | h)
      · exact (Finset.mem_sdiff.mp h.2.1).2 hu
      · rcases h.2 with h | h
        · exact h.2 hv
        · exact h.2 hu
  have hregions : insideSetPiece G Y ⊔
      (insideSetPiece G (Finset.univ \ Y) ⊔ cutSetPiece G Y) = G := by
    ext u v
    by_cases hu : u ∈ Y <;> by_cases hv : v ∈ Y <;>
      simp [insideSetPiece, cutSetPiece, hu, hv]
  obtain ⟨P, hP, hpart, hb⟩ := edge_partition_sum _ _ n R hdisjI
    Pi Poc hPi hPoc hparti hpartoc hbi hboc
  exact ⟨P, by simpa only [hregions] using hP,
    by simpa only [hregions] using hpart, hb⟩

end Papers.OaiGraphDecompositionsIntegral
