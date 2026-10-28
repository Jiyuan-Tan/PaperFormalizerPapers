module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Thresholds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Lower bounds for the integral expectation threshold -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

open scoped BigOperators

open Classical in
/-- [An injective relabelling of H has exactly as many edges as H](goal). -/
-- @node: copyEdges_card
lemma copyEdges_card (H : SimpleGraph V) {n : ℕ} (f : V ↪ Fin n) :
    (copyEdges H f).card = H.edgeFinset.card := by
  classical
  rw [← SimpleGraph.card_edgeFinset_map f H]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp he).2
  · intro e he e' he' h
    exact Subtype.ext h
  · intro e he
    refine ⟨⟨e, (H.map f).not_isDiag_of_mem_edgeFinset he⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.mem_edgeFinset.mp he⟩

/-- [Every edge in the copy of H specified by f belongs to the host edge set G](goal). -/
-- @node: copyEdges_subset_of_copy
lemma copyEdges_subset_of_copy (H : SimpleGraph V) {n : ℕ}
    (G : Finset (KEdge n)) (f : H.Copy (graphOfEdges G)) :
    copyEdges H f.toEmbedding ⊆ G := by
  classical
  intro e he
  have hemap : e.val ∈ (H.map f.toEmbedding).edgeSet := (Finset.mem_filter.mp he).2
  rw [SimpleGraph.edgeSet_map] at hemap
  obtain ⟨a, ha, hea⟩ := hemap
  have hehost : e.val ∈ (graphOfEdges G).edgeSet := by
    rw [← hea]
    exact f.toHom.map_mem_edgeSet ha
  have hex : ∃ h : ¬ e.val.IsDiag, decide ((⟨e.val, h⟩ : KEdge n) ∈ G) = true := by
    have hh := hehost
    simp only [graphOfEdges, hostGraph, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_sdiff, Set.mem_ofPred_eq] at hh
    exact hh.1
  obtain ⟨h, hh⟩ := hex
  exact of_decide_eq_true hh

omit [Fintype V] in
open Classical in
/-- If [p lies between zero and one](hyp:hp), then [copies of K, embedded in H
by f, cover all n-vertex host graphs containing H at cost at most n to the
number of vertices of K times p to the number of edges of K](goal). -/
-- @node: subgraph_copy_cover
lemma subgraph_copy_cover {W : Type} [Fintype W]
    (H : SimpleGraph V) (K : SimpleGraph W) (f : K.Copy H)
    (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    HasCoverOfCostLe (containmentFamily H n) p
      ((n : ℝ) ^ Fintype.card W * p ^ K.edgeFinset.card) := by
  classical
  have hp0 := hp.1
  let C := Finset.univ.image (fun g : W ↪ Fin n => copyEdges K g)
  refine ⟨C, ?_, hp, ?_⟩
  · intro G hG
    obtain ⟨g⟩ := hG
    refine ⟨copyEdges K (g.comp f).toEmbedding, Finset.mem_image.mpr
      ⟨(g.comp f).toEmbedding, Finset.mem_univ _, rfl⟩, ?_⟩
    exact copyEdges_subset_of_copy K G (g.comp f)
  · change coverPolynomial C p ≤ _
    have hcard : C.card ≤ n ^ Fintype.card W := by
      calc
        C.card ≤ Fintype.card (W ↪ Fin n) := (Finset.card_image_le).trans (by simp)
        _ ≤ Fintype.card (W → Fin n) := Fintype.card_le_of_injective
          (fun g : W ↪ Fin n => (g : W → Fin n)) (fun _ _ h => DFunLike.coe_injective h)
        _ = n ^ Fintype.card W := by simp
    calc
      coverPolynomial C p = (C.card : ℝ) * p ^ K.edgeFinset.card := by
        unfold coverPolynomial
        have hc : ∀ E ∈ C, E.card = K.edgeFinset.card := by
          intro E hE
          obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hE
          exact copyEdges_card K g
        simp_rw [Finset.sum_congr rfl (fun E hE => congrArg (fun k => p ^ k) (hc E hE))]
        simp
      _ ≤ (n : ℝ) ^ Fintype.card W * p ^ K.edgeFinset.card := by
        gcongr
        exact_mod_cast hcard

omit [Fintype V] in
/-- If [H has an edge](hyp:hedge), [p lies between zero and one](hyp:hp), and
[the n-vertex containment family of H has a cover of cost at most one half
at p](hyp:hcover), then [p is at most the expectation threshold of H on n vertices](goal). -/
-- @node: expectationThreshold_ge_of_cover
lemma expectationThreshold_ge_of_cover (H : SimpleGraph V) (n : ℕ)
    (hedge : H.edgeSet.Nonempty) {p : ℝ} (hp : p ∈ Set.Icc 0 1)
    (hcover : HasCoverOfCostLe (containmentFamily H n) p (1 / 2)) :
    p ≤ expectationThreshold H n := by
  classical
  have hne := Set.nonempty_iff_ne_empty.mp hedge
  simp only [expectationThreshold, if_neg hne]
  exact le_csSup ⟨1, fun q hq => hq.1.2⟩ ⟨hp, hcover⟩

/-- If [H has an edge](hyp:hedge) and [p lies between zero and one](hyp:hp),
then [all individual host edges form a cover of the n-vertex containment
family of H with cost at most n choose two times p](goal). -/
-- @node: single_edge_cover
lemma single_edge_cover (H : SimpleGraph V) (n : ℕ) (hedge : H.edgeSet.Nonempty)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    HasCoverOfCostLe (containmentFamily H n) p ((n.choose 2 : ℝ) * p) := by
  classical
  have hp0 := hp.1
  let C := Finset.univ.image (fun e : KEdge n => ({e} : Finset (KEdge n)))
  have hcard : Fintype.card (KEdge n) = n.choose 2 := by
    calc
      _ = Fintype.card (Sym2.diagSetᶜ : Set (Sym2 (Fin n))) :=
        Fintype.card_congr {
          toFun := fun e => ⟨e.val, e.property⟩
          invFun := fun e => ⟨e.val, e.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      _ = n.choose 2 := by simpa using (Sym2.card_diagSet_compl (α := Fin n))
  refine ⟨C, ?_, hp, ?_⟩
  · intro G hG
    obtain ⟨f⟩ := hG
    have hcopy : (copyEdges H f.toEmbedding).Nonempty := by
      rw [← Finset.card_pos, copyEdges_card]
      exact Finset.card_pos.mpr (SimpleGraph.edgeFinset_nonempty.mpr
        (SimpleGraph.edgeSet_nonempty.mp hedge))
    obtain ⟨e, he⟩ := hcopy
    refine ⟨{e}, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩, ?_⟩
    exact Finset.singleton_subset_iff.mpr (copyEdges_subset_of_copy H G f he)
  · change coverPolynomial C p ≤ _
    have hC : C.card ≤ n.choose 2 := by
      simpa only [Finset.card_univ, hcard] using
        (Finset.card_image_le (s := (Finset.univ : Finset (KEdge n)))
          (f := fun e : KEdge n => ({e} : Finset (KEdge n))))
    calc
      coverPolynomial C p = (C.card : ℝ) * p := by
        unfold coverPolynomial
        have hc : ∀ E ∈ C, E.card = 1 := by
          intro E hE
          obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hE
          exact Finset.card_singleton _
        simp_rw [Finset.sum_congr rfl (fun E hE => congrArg (fun k => p ^ k) (hc E hE))]
        simp
      _ ≤ (n.choose 2 : ℝ) * p := by gcongr

/-- If [H has an edge](hyp:hedge), then [its degeneracy is positive](goal). -/
-- @node: degeneracy_pos_of_edge
lemma degeneracy_pos_of_edge (H : SimpleGraph V) (hedge : H.edgeSet.Nonempty) :
    0 < degeneracy H := by
  classical
  obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp
    (SimpleGraph.edgeSet_nonempty.mp hedge)
  let S : Finset V := {u, v}
  have hS : S.Nonempty := ⟨u, by simp [S]⟩
  let : Nonempty (S : Set V) := hS.to_subtype
  have hmin : 1 ≤ (H.induce (S : Set V)).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro x
    apply Nat.succ_le_of_lt
    apply ((H.induce (S : Set V)).degree_pos_iff_exists_adj x).mpr
    have hx : x.val = u ∨ x.val = v := by simpa [S] using x.property
    rcases hx with hx | hx
    · exact ⟨⟨v, by simp [S]⟩, by change H.Adj x.val v; simpa [hx] using huv⟩
    · exact ⟨⟨u, by simp [S]⟩, by change H.Adj x.val u; simpa [hx] using huv.symm⟩
  exact hmin.trans (Finset.le_sup (f := fun T : Finset V =>
    (H.induce (T : Set V)).minDegree) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩))

open Classical in
/-- If [H has an edge](hyp:hedge), then [there is a nonempty vertex set S
whose induced subgraph has at least half the degeneracy of H times the
number of vertices in S edges](goal). -/
-- @node: degeneracy_dense_subgraph
lemma degeneracy_dense_subgraph (H : SimpleGraph V) (hedge : H.edgeSet.Nonempty) :
    ∃ S : Finset V, S.Nonempty ∧
      degeneracy H * S.card ≤ 2 * (H.induce (S : Set V)).edgeFinset.card := by
  classical
  obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp
    (SimpleGraph.edgeSet_nonempty.mp hedge)
  have hne : (Finset.univ.filter (fun S : Finset V => S.Nonempty)).Nonempty :=
    ⟨{u}, by simp⟩
  obtain ⟨S, hS, heq⟩ := Finset.exists_mem_eq_sup _ hne
    (fun S : Finset V => (H.induce (S : Set V)).minDegree)
  refine ⟨S, (Finset.mem_filter.mp hS).2, ?_⟩
  have heq' : degeneracy H = (H.induce (S : Set V)).minDegree := heq
  calc
    degeneracy H * S.card = ∑ x : (S : Set V), degeneracy H := by simp [mul_comm]
    _ ≤ ∑ x : (S : Set V), (H.induce (S : Set V)).degree x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [heq']
      exact SimpleGraph.minDegree_le_degree _ x
    _ = 2 * (H.induce (S : Set V)).edgeFinset.card :=
      SimpleGraph.sum_degrees_eq_twice_card_edges _

/-- If [n is at least one](hyp:hn), [a is at least one](hyp:ha), [d is
positive](hyp:hd), and [d times v is at most twice a](hyp:hda), then [setting
p to one half times n to the power −2/d gives p between zero and one and
n to the power v times p to the power a at most one half](goal). -/
-- @node: dense_cover_parameter
lemma dense_cover_parameter (n v a d : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a)
    (hd : 0 < d) (hda : d * v ≤ 2 * a) :
    let p := (1 / 2 : ℝ) * (n : ℝ) ^ (-(2 : ℝ) / (d : ℝ))
    p ∈ Set.Icc 0 1 ∧ (n : ℝ) ^ v * p ^ a ≤ (1 / 2 : ℝ) := by
  dsimp only
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hn1
    (div_nonpos_of_nonpos_of_nonneg (by norm_num : -(2 : ℝ) ≤ 0) hd0.le)
  constructor
  · constructor
    · positivity
    · nlinarith
  · have hratio : (v : ℝ) ≤ (2 : ℝ) / (d : ℝ) * (a : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd0]
      have h := (show (d : ℝ) * v ≤ 2 * a by exact_mod_cast hda)
      nlinarith
    have hexp : (v : ℝ) + (-(2 : ℝ) / (d : ℝ)) * (a : ℝ) ≤ 0 := by
      rw [neg_div, neg_mul]
      linarith
    calc
      (n : ℝ) ^ v * ((1 / 2 : ℝ) * (n : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) ^ a =
          (1 / 2 : ℝ) ^ a * (n : ℝ) ^
            ((v : ℝ) + (-(2 : ℝ) / (d : ℝ)) * (a : ℝ)) := by
        rw [mul_pow, Real.rpow_add hn0, Real.rpow_mul hn0.le,
          Real.rpow_natCast, Real.rpow_natCast]
        ring
      _ ≤ (1 / 2 : ℝ) ^ a * 1 := by
        gcongr
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1 hexp
      _ ≤ (1 / 2 : ℝ) := by
        simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) ≤ 1) ha

-- @node: lem:q-lower
/-- If [the vertex set of H is finite](hyp:hfinite), [H has an edge](hyp:hedge),
and [H has at most n vertices](hyp:hsize), then [its expectation threshold
on n vertices is at least both 1 divided by twice n choose two and one half
times n to the power −2/d, where d is the degeneracy of H](goal). -/
lemma q_lower (H : SimpleGraph V) (n : ℕ)
    (hfinite : FiniteSimpleGraphs V) (hedge : QLowerEdge H) (hsize : QLowerOrder V n) :
    1 / (2 * (n.choose 2 : ℝ)) ≤ expectationThreshold H n ∧
    (1 / 2 : ℝ) * (n : ℝ) ^ (-(2 : ℝ) / (qLowerDegeneracy H : ℝ)) ≤
      expectationThreshold H n := by
  classical
  have he : H.edgeSet.Nonempty := hedge
  have hsize' : Fintype.card V ≤ n := hsize
  obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp
    (SimpleGraph.edgeSet_nonempty.mp he)
  let : Nontrivial V := ⟨⟨u, v, huv.ne⟩⟩
  have hn2 : 2 ≤ n := (Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))).trans hsize'
  constructor
  · have hc : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos hn2
    have hc1 : (1 : ℝ) ≤ n.choose 2 := by exact_mod_cast Nat.choose_pos hn2
    have hp : 1 / (2 * (n.choose 2 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n.choose 2)).mpr
        nlinarith
    apply expectationThreshold_ge_of_cover H n he hp
    have hcover := single_edge_cover H n he (1 / (2 * (n.choose 2 : ℝ))) hp
    have hcost : (n.choose 2 : ℝ) * (1 / (2 * (n.choose 2 : ℝ))) = 1 / 2 := by
      field_simp
    rwa [hcost] at hcover
  · have hd : 0 < degeneracy H := degeneracy_pos_of_edge H he
    obtain ⟨S, hS, hda⟩ := degeneracy_dense_subgraph H he
    have ha : 1 ≤ (H.induce (S : Set V)).edgeFinset.card := by
      have hv := Nat.mul_pos hd (Finset.card_pos.mpr hS)
      omega
    have hparam := dense_cover_parameter n S.card
      (H.induce (S : Set V)).edgeFinset.card (degeneracy H) (by omega) ha hd hda
    change (1 / 2 : ℝ) * (n : ℝ) ^ (-(2 : ℝ) / (degeneracy H : ℝ)) ≤ _
    apply expectationThreshold_ge_of_cover H n he hparam.1
    obtain ⟨C, hC, hpC, hcost⟩ := subgraph_copy_cover H (H.induce (S : Set V))
      (SimpleGraph.Copy.induce H (S : Set V)) n
      ((1 / 2 : ℝ) * (n : ℝ) ^ (-(2 : ℝ) / (degeneracy H : ℝ))) hparam.1
    refine ⟨C, hC, hpC, hcost.trans ?_⟩
    convert hparam.2 using 1
    · rfl
    · congr 2
      simp

end Papers.OaiGraphDecompositionsIntegral
