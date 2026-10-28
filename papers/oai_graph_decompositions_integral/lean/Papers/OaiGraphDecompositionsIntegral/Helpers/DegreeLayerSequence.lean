module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeLayers
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Iterating the independent-layer selection

Layers are listed in removal order: the head is the last layer to embed.
Its degree bound is measured in the whole current residual set, so reversing
the sequence bounds the number of earlier neighbors of every vertex.
-/

@[expose] public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A certificate of successive independent-layer removals. The empty
terminal residual ensures that every vertex is assigned exactly once. -/
-- @node: DegreeLayerSequence
inductive DegreeLayerSequence (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    Finset V → List (Finset V) → Prop
  | nil : DegreeLayerSequence G s ∅ []
  | cons {S I : Finset V} {L : List (Finset V)}
      (subset : I ⊆ S) (nonempty : I.Nonempty)
      (independent : G.IsIndepSet (I : Set V))
      (degree : ∀ v ∈ I, (G.neighborFinset v ∩ S).card ≤ 4 * s)
      (tail : DegreeLayerSequence G s (S \ I) L) :
      DegreeLayerSequence G s S (I :: L)

/-- If [G has degeneracy at most s](hyp:hd), then [every residual vertex
set S contains an independent set I whose vertices each have at most 4s
neighbors in S and whose size times 2(4s + 1) is at least the size of S](goal). -/
-- @node: degree_last_layer_on
lemma degree_last_layer_on (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hd : degeneracy G ≤ s) (S : Finset V) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet (I : Set V) ∧
      (∀ v ∈ I, (G.neighborFinset v ∩ S).card ≤ 4 * s) ∧
      S.card ≤ 2 * (4 * s + 1) * I.card := by
  classical
  obtain ⟨I, hi, hdeg, hcard⟩ := degree_last_layer (G.induce (S : Set V)) s
    ((degeneracy_induce_le G S).trans hd)
  let e : S ↪ V := Function.Embedding.subtype _
  refine ⟨I.map e, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hv
    exact w.property
  · intro v hv w hw hne hadj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hw
    exact hi ha hb (fun hab => hne (congrArg e hab)) hadj
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    have heq := congrArg Finset.card (G.map_neighborFinset_induce w)
    simp at heq
    change (G.neighborFinset w.val ∩ S).card ≤ 4 * s
    rw [← heq]
    convert hdeg w hw using 1
    congr 1
    exact Subsingleton.elim _ _
  · simpa using hcard

omit [Fintype V] in
/-- If [I is a subset of S](hyp:hI) and [the size of S is at most 2(4s + 1)
times the size of I](hyp:hcard), then [the number of vertices remaining after
removing I is at most the size of S times exp(−1/(2(4s + 1)))](goal). -/
-- @node: degree_layer_residual_contraction
lemma degree_layer_residual_contraction (s : ℕ) (S I : Finset V)
    (hI : I ⊆ S) (hcard : S.card ≤ 2 * (4 * s + 1) * I.card) :
    ((S \ I).card : ℝ) ≤
      (S.card : ℝ) * Real.exp (-1 / (2 * (4 * (s : ℝ) + 1))) := by
  have hsum : (S \ I).card + I.card = S.card := Finset.card_sdiff_add_card_eq_card hI
  have hsum' : ((S \ I).card : ℝ) + I.card = S.card := by exact_mod_cast hsum
  have hcard' : (S.card : ℝ) ≤ 2 * (4 * (s : ℝ) + 1) * I.card := by
    exact_mod_cast hcard
  have ha : 0 < 2 * (4 * (s : ℝ) + 1) := by positivity
  have hfrac : (S.card : ℝ) / (2 * (4 * (s : ℝ) + 1)) ≤ I.card :=
    (div_le_iff₀ ha).mpr (by nlinarith)
  have hexp := Real.add_one_le_exp (-1 / (2 * (4 * (s : ℝ) + 1)))
  calc
    ((S \ I).card : ℝ) ≤ (S.card : ℝ) * (1 - 1 / (2 * (4 * (s : ℝ) + 1))) := by
      rw [mul_sub, mul_one, ← div_eq_mul_one_div]
      linarith
    _ ≤ _ := by
      gcongr
      simpa only [neg_div, sub_eq_add_neg, add_comm] using hexp

/-- If [G has degeneracy at most s](hyp:hd), then [every vertex set S whose
size times exp(−k/(2(4s + 1))) is less than one admits a sequence of at most
k independent-layer removals, each with residual degree at most 4s, ending
with no vertices remaining](goal). -/
-- @node: degree_layers_of_exp_bound
lemma degree_layers_of_exp_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hd : degeneracy G ≤ s) (k : ℕ) :
    ∀ S : Finset V,
      (S.card : ℝ) * Real.exp (-(k : ℝ) / (2 * (4 * (s : ℝ) + 1))) < 1 →
      ∃ L : List (Finset V), DegreeLayerSequence G s S L ∧ L.length ≤ k := by
  classical
  induction k with
  | zero =>
    intro S hS
    have hzero : S.card = 0 := by
      simp only [Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, mul_one] at hS
      have : S.card < 1 := by exact_mod_cast hS
      omega
    rw [Finset.card_eq_zero.mp hzero]
    exact ⟨[], .nil, by simp⟩
  | succ k ih =>
    intro S hS
    by_cases hne : S.Nonempty
    · obtain ⟨I, hI, hi, hdeg, hcard⟩ := degree_last_layer_on G s hd S
      have hIne : I.Nonempty := by
        by_contra h
        have := Finset.not_nonempty_iff_eq_empty.mp h
        simp only [this, Finset.card_empty, mul_zero] at hcard
        exact (by omega : ¬ 0 < S.card) hne.card_pos
      have hsmall : ((S \ I).card : ℝ) *
          Real.exp (-(k : ℝ) / (2 * (4 * (s : ℝ) + 1))) < 1 := by
        calc
          _ ≤ ((S.card : ℝ) * Real.exp (-1 / (2 * (4 * (s : ℝ) + 1)))) *
              Real.exp (-(k : ℝ) / (2 * (4 * (s : ℝ) + 1))) := by
            gcongr
            exact degree_layer_residual_contraction s S I hI hcard
          _ = (S.card : ℝ) *
              Real.exp (-((k + 1 : ℕ) : ℝ) / (2 * (4 * (s : ℝ) + 1))) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            push_cast
            ring
          _ < 1 := hS
      obtain ⟨L, hL, hlen⟩ := ih (S \ I) hsmall
      exact ⟨I :: L, .cons hI hIne hi hdeg hL, by simpa using Nat.succ_le_succ hlen⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      exact ⟨[], .nil, by simp⟩

/-- Given [a sequence L of independent-layer removals of S with residual
degrees at most 4s](hyp:h), [the layers have union S, are pairwise disjoint,
and are nonempty independent sets; every vertex in any layer has at most 4s
neighbors in that layer together with all later layers](goal). -/
-- @node: degree_layer_sequence_partition
lemma degree_layer_sequence_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) {S : Finset V} {L : List (Finset V)} (h : DegreeLayerSequence G s S L) :
    L.foldr (· ∪ ·) ∅ = S ∧ L.Pairwise Disjoint ∧
      (∀ I ∈ L, I.Nonempty ∧ G.IsIndepSet (I : Set V)) ∧
      ∀ A I B, L = A ++ I :: B →
        ∀ v ∈ I, (G.neighborFinset v ∩ (I ∪ B.foldr (· ∪ ·) ∅)).card ≤ 4 * s := by
  induction h with
  | nil =>
    refine ⟨rfl, by simp, by simp, ?_⟩
    intro A I B heq
    have := congrArg List.length heq
    simp at this
  | @cons S I L hI hne hi hdeg htail ih =>
    have hunion : I ∪ L.foldr (· ∪ ·) ∅ = S := by
      rw [ih.1, Finset.union_sdiff_of_subset hI]
    refine ⟨hunion, List.pairwise_cons.mpr ⟨?_, ih.2.1⟩, ?_, ?_⟩
    · intro J hJ
      apply Finset.disjoint_left.mpr
      intro v hvI hvJ
      have hsub : ∀ {A : Finset V} {L : List (Finset V)}, A ∈ L →
          A ⊆ L.foldr (· ∪ ·) ∅ := by
        intro A L hA
        induction L with
        | nil => simp at hA
        | cons J L ih =>
          rcases List.mem_cons.mp hA with rfl | hA
          · exact Finset.subset_union_left
          · exact (ih hA).trans Finset.subset_union_right
      have hv := hsub hJ hvJ
      rw [ih.1] at hv
      exact (Finset.mem_sdiff.mp hv).2 hvI
    · intro J hJ
      rcases List.mem_cons.mp hJ with rfl | hJ
      · exact ⟨hne, hi⟩
      · exact ih.2.2.1 J hJ
    · intro A J B heq v hv
      cases A with
      | nil =>
        have heq' : I = J ∧ L = B := List.cons.inj heq
        rcases heq' with ⟨rfl, rfl⟩
        rw [hunion]
        exact hdeg v hv
      | cons K A =>
        have heq' : I = K ∧ L = A ++ J :: B := List.cons.inj heq
        exact ih.2.2.2 A J B heq'.2 v hv

/-- Given [a sequence L of independent-layer removals of S with residual
degrees at most 4s](hyp:h), [the sum of the layer sizes equals the size of S,
and the number of layers is at most the size of S](goal). -/
-- @node: degree_layer_sequence_card
lemma degree_layer_sequence_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) {S : Finset V} {L : List (Finset V)} (h : DegreeLayerSequence G s S L) :
    (L.map Finset.card).sum = S.card ∧ L.length ≤ S.card := by
  induction h with
  | nil => simp
  | @cons S I L hI hne hi hdeg htail ih =>
    have hcard := Finset.card_sdiff_add_card_eq_card hI
    have hpos := hne.card_pos
    constructor
    · simp only [List.map_cons, List.sum_cons, ih.1]
      omega
    · simp only [List.length_cons]
      omega

/-- If [L is a sequence of independent-layer removals covering S with residual
degrees at most 4s](hyp:h) and [S is nonempty](hyp:hS), then [L has positive
length](goal). -/
-- @node: degree_layer_sequence_length_pos
lemma degree_layer_sequence_length_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) {S : Finset V} {L : List (Finset V)}
    (h : DegreeLayerSequence G s S L) (hS : S.Nonempty) : 0 < L.length := by
  cases h with
  | nil => simp at hS
  | cons => simp

/-- If [G has degeneracy at most s](hyp:hd), [n is at least one](hyp:hn), and
[S has at most n vertices](hyp:hSn), then [S admits a sequence of independent-layer
removals with residual degrees at most 4s and at most
2(4s + 1) log n + 2 layers](goal). -/
-- @node: degree_layer_sequence_log_bound
lemma degree_layer_sequence_log_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hd : degeneracy G ≤ s) (S : Finset V) (n : ℕ)
    (hn : 1 ≤ n) (hSn : S.card ≤ n) :
    ∃ L : List (Finset V), DegreeLayerSequence G s S L ∧
      (L.length : ℝ) ≤ 2 * (4 * (s : ℝ) + 1) * naturalLog n + 2 := by
  let a : ℝ := 2 * (4 * (s : ℝ) + 1)
  let k : ℕ := ⌈a * naturalLog n⌉₊ + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ naturalLog n := Real.log_nonneg (by exact_mod_cast hn)
  have hk : naturalLog n < (k : ℝ) / a := by
    apply (lt_div_iff₀ ha).mpr
    have := Nat.le_ceil (a * naturalLog n)
    dsimp [k]
    push_cast
    nlinarith
  have hsmall : (S.card : ℝ) * Real.exp (-(k : ℝ) / a) < 1 := by
    calc
      _ ≤ (n : ℝ) * Real.exp (-(k : ℝ) / a) := by gcongr
      _ = Real.exp (naturalLog n - (k : ℝ) / a) := by
        rw [naturalLog, Real.exp_sub, Real.exp_log hnpos, neg_div, Real.exp_neg]
        rfl
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  obtain ⟨L, hL, hlen⟩ := degree_layers_of_exp_bound G s hd k S hsmall
  refine ⟨L, hL, ?_⟩
  have hceil := Nat.ceil_lt_add_one (mul_nonneg ha.le hlog)
  have hkbound : (k : ℝ) < a * naturalLog n + 2 := by
    dsimp [k]
    push_cast
    linarith
  have hlen' : (L.length : ℝ) ≤ k := by exact_mod_cast hlen
  exact hlen'.trans hkbound.le

/-- Suppose [G has degeneracy at most s](hyp:hd), [s is at least one](hyp:hs),
[0 < r < 1, s is at most 10 log n, and rˢ is at least n⁻¹ᐟ¹⁰⁰](hyp:hp), [n is at
least one](hyp:hn), [log n is at least one](hyp:hlog), and [S has at most n
vertices](hyp:hSn). Then [S admits a sequence of independent-layer removals
with residual degrees at most 4s and at most 120(log n)² layers](goal). -/
-- @node: degree_layer_sequence_log_squared
lemma degree_layer_sequence_log_squared (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hd : degeneracy G ≤ s) (hs : 1 ≤ s) (S : Finset V)
    (n : ℕ) (r : ℝ) (hp : TransferParameters n r s)
    (hn : 1 ≤ n) (hlog : 1 ≤ naturalLog n) (hSn : S.card ≤ n) :
    ∃ L : List (Finset V), DegreeLayerSequence G s S L ∧
      (L.length : ℝ) ≤ 120 * naturalLog n ^ 2 := by
  obtain ⟨L, hL, hlen⟩ := degree_layer_sequence_log_bound G s hd S n hn hSn
  refine ⟨L, hL, hlen.trans ?_⟩
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hslog : (s : ℝ) ≤ 10 * naturalLog n := hp.2.2.1
  have hcoef : 2 * (4 * (s : ℝ) + 1) ≤ 10 * s := by linarith
  have hmul : 2 * (4 * (s : ℝ) + 1) * naturalLog n ≤
      100 * naturalLog n ^ 2 := by
    calc
      _ ≤ (10 * (s : ℝ)) * naturalLog n := by gcongr
      _ ≤ (10 * (10 * naturalLog n)) * naturalLog n := by gcongr
      _ = _ := by ring
  nlinarith

end Papers.OaiGraphDecompositionsIntegral
