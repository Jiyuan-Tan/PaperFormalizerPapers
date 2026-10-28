module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BoundedDegeneracy
public import Papers.OaiGraphDecompositionsIntegral.Helpers.QLower
public import Mathlib.Data.Nat.Choose.Cast

/-! # Padding and elementary cases of the final edge partition -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

/-- If [H has at most n vertices](hyp:hsize), [its containment threshold in
an n-vertex host is at most one](goal). -/
-- @node: containmentThreshold_le_one
lemma containmentThreshold_le_one (H : SimpleGraph V) (n : ℕ)
    (hsize : Fintype.card V ≤ n) : containmentThreshold H n ≤ 1 := by
  classical
  by_cases he : H.edgeSet = ∅
  · simp [containmentThreshold, he]
  · simpa only [containmentThreshold, if_neg he] using
      (containmentThresholdRaw_isLeast H n hsize).1.1.2

/-- Suppose [R is nonnegative](hyp:hR), [the index set has at most k elements](hyp:hcard),
[each piece P is a subgraph of H](hyp:hP), [every edge of H belongs to exactly
one piece](hyp:hpart), and [each piece has containment threshold at most R
in an n-vertex host](hyp:hbound). Then [H admits an edge partition into k
subgraphs, each with containment threshold at most R in an n-vertex host](goal). -/
-- @node: edge_partition_pad
lemma edge_partition_pad {I : Type} [Fintype I] (H : SimpleGraph V)
    (n k : ℕ) (R : ℝ) (hR : 0 ≤ R) (hcard : Fintype.card I ≤ k)
    (P : I → SimpleGraph V) (hP : ∀ i, P i ≤ H)
    (hpart : ∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet)
    (hbound : ∀ i, containmentThreshold (P i) n ≤ R) :
    ∃ Q : Fin k → SimpleGraph V, (∀ i, Q i ≤ H) ∧
      (∀ e ∈ H.edgeSet, ∃! i, e ∈ (Q i).edgeSet) ∧
      ∀ i, containmentThreshold (Q i) n ≤ R := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card I ≤ Fintype.card (Fin k) by simpa using hcard)
  let Q : Fin k → SimpleGraph V := fun j =>
    if h : ∃ i, f i = j then P h.choose else ⊥
  have himage (i : I) : Q (f i) = P i := by
    have hi : ∃ a, f a = f i := ⟨i, rfl⟩
    have heq : hi.choose = i := f.injective hi.choose_spec
    simp only [Q, dif_pos hi, heq]
  have hpre (j : Fin k) (e : Sym2 V) (he : e ∈ (Q j).edgeSet) :
      ∃ i, f i = j ∧ e ∈ (P i).edgeSet := by
    by_cases hj : ∃ i, f i = j
    · exact ⟨hj.choose, hj.choose_spec, by simpa only [Q, dif_pos hj] using he⟩
    · simp [Q, hj] at he
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro j
    dsimp only [Q]
    split_ifs with hj
    · exact hP hj.choose
    · exact bot_le
  · intro e he
    obtain ⟨i, hi, huniq⟩ := hpart e he
    refine ⟨f i, by simpa only [himage] using hi, ?_⟩
    intro j hj
    obtain ⟨a, ha, hea⟩ := hpre j e hj
    rw [huniq a hea] at ha
    exact ha.symm
  · intro j
    dsimp only [Q]
    split_ifs with hj
    · exact hbound hj.choose
    · simpa [containmentThreshold] using hR

/-- If [k is at least one](hyp:hk), [H has at most n vertices](hyp:hsize), and
[R is at least one](hyp:hR), [H admits an edge partition into k subgraphs,
each with containment threshold at most R in an n-vertex host](goal). -/
-- @node: edge_partition_single
lemma edge_partition_single (H : SimpleGraph V) (n k : ℕ) (R : ℝ)
    (hk : 1 ≤ k) (hsize : Fintype.card V ≤ n) (hR : 1 ≤ R) :
    ∃ P : Fin k → SimpleGraph V, (∀ i, P i ≤ H) ∧
      (∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, containmentThreshold (P i) n ≤ R := by
  apply edge_partition_pad (I := Unit) H n k R (by linarith)
    (by simpa using hk) (fun _ => H) (fun _ => le_rfl)
  · intro e he
    exact ⟨(), he, fun _ _ => rfl⟩
  · intro i
    exact (containmentThreshold_le_one H n hsize).trans hR

/-- If [H has an edge](hyp:he), [n is at least two](hyp:hn), [H has at most n
vertices](hyp:hsize), [n is less than N](hyp:hN), and [L is at least N
squared](hyp:hL), [L times the expectation threshold of H in an n-vertex
host is at least one](goal). -/
-- @node: assembly_small_order_comparison
lemma assembly_small_order_comparison (H : SimpleGraph V) (n N : ℕ) (L : ℝ)
    (he : H.edgeSet.Nonempty) (hn : 2 ≤ n) (hsize : Fintype.card V ≤ n)
    (hN : n < N) (hL : (N : ℝ) ^ 2 ≤ L) :
    1 ≤ L * expectationThreshold H n := by
  have hq := (q_lower H n (by change Finite V; infer_instance) he hsize).1
  have hc : 0 < (n.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hqpos : 0 < expectationThreshold H n := (by positivity :
    0 < 1 / (2 * (n.choose 2 : ℝ))).trans_le hq
  have hcost : 1 ≤ (2 * (n.choose 2 : ℝ)) * expectationThreshold H n := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * (n.choose 2 : ℝ))).mp hq
    nlinarith
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hN.le
  have hchoose : 2 * (n.choose 2 : ℝ) = (n : ℝ) * (n - 1) := by
    rw [Nat.cast_choose_two]
    ring
  have hden : 2 * (n.choose 2 : ℝ) ≤ L := by
    rw [hchoose]
    have : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by gcongr
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  exact hcost.trans (mul_le_mul_of_nonneg_right hden hqpos.le)

end Papers.OaiGraphDecompositionsIntegral
