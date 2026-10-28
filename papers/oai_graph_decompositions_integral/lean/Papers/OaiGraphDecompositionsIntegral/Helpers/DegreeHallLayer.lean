module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeHallProbability
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeNumerics
public import Papers.OaiGraphDecompositionsIntegral.Helpers.TransferConcentration
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Finset.Card

/-! # Hall witnesses and a uniform single-layer matching bound

The finite union bound counts both the source set and its forbidden images.
All requirements and bins in this file are fixed before drawing the edges.
-/

public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

/-- If [each coordinate belongs to at most Δ requirements](hyp:hload), then
[each coordinate still belongs to at most Δ requirements after restricting
the source vertices to U](goal). -/
-- @node: degree_requirement_load_restrict
lemma degree_requirement_load_restrict {V X : Type} [Fintype V] [DecidableEq X]
    (R : V → Finset X) (U : Finset V) (Δ : ℕ)
    (hload : ∀ x, (Finset.univ.filter (fun v => x ∈ R v)).card ≤ Δ) :
    ∀ x, (Finset.univ.filter (fun v : ↥U => x ∈ R v.val)).card ≤ Δ := by
  classical
  intro x
  let S := Finset.univ.filter (fun v : ↥U => x ∈ R v.val)
  have hsub : S.image Subtype.val ⊆ Finset.univ.filter (fun v => x ∈ R v) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩
  have h := (Finset.card_le_card hsub).trans (hload x)
  simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h

/-- Suppose [0 < r < 1](hyp:hr), [each requirement has at most k coordinates](hyp:hsize),
[each coordinate occurs in at most Δ requirements](hyp:hload), and [B has at
least b more candidates than there are source vertices](hyp:hB). If [W is
a subset of B](hyp:hW) and [W has exactly one fewer element than U](hyp:hWU),
then [in an independent Bernoulli array with success probability r, the
probability that no candidate outside W satisfies any requirement from U
is at most exp(−b |U| rᵏ/(1 + kΔ))](goal). -/
-- @node: degree_hall_pair_probability
lemma degree_hall_pair_probability {V X C : Type} [Fintype V]
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (r : ℝ) (hr : CompressionDensity r) (R : V → Finset X)
    (B : Finset C) (k Δ b : ℕ)
    (hsize : ∀ v, (R v).card ≤ k)
    (hload : ∀ x, (Finset.univ.filter (fun v => x ∈ R v)).card ≤ Δ)
    (hB : Fintype.card V + b ≤ B.card)
    (U : Finset V) (W : Finset C) (hW : W ⊆ B) (hWU : W.card + 1 = U.card) :
    (productMeasure (X × C) r).Pr
      (fun z => ∀ v ∈ U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v, z (x, c) = true) ≤
        Real.exp (-(b : ℝ) * U.card * r ^ k / (1 + (k : ℝ) * Δ)) := by
  classical
  have hUcard : U.card ≤ Fintype.card V := Finset.card_le_univ _
  have hslack : b ≤ (B \ W).card := by
    rw [Finset.card_sdiff_of_subset hW]
    omega
  have hp := degree_hall_failure_probability r hr (fun v : ↥U => R v.val)
    (B \ W) k Δ (fun v => hsize v.val) (degree_requirement_load_restrict R U Δ hload)
  have heq : (productMeasure (X × C) r).Pr
      (fun z => ∀ v ∈ U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v, z (x, c) = true) =
      (productMeasure (X × C) r).Pr
      (fun z => ∀ v : ↥U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v.val, z (x, c) = true) := by
    apply FiniteDesign.Pr_congr
    intro z
    exact ⟨fun h v => h v.val v.property, fun h v hv => h ⟨v, hv⟩⟩
  rw [heq]
  refine hp.trans ?_
  simp only [Fintype.card_coe]
  apply Real.exp_le_exp.mpr
  have hrpow : 0 ≤ r ^ k := pow_nonneg hr.1.le _
  have hslack' : (b : ℝ) ≤ (B \ W).card := by exact_mod_cast hslack
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hslack')
    (mul_nonneg (Nat.cast_nonneg U.card) hrpow)]

/-- If [B has at least as many candidates as there are source vertices](hyp:hB),
[each source vertex's candidate set lies in B](hyp:hcand), and [there is no
injective assignment choosing a candidate for each source vertex](hyp:hfail),
then [there are a nonempty source set U and a subset W of B with exactly
one fewer element than U such that every candidate for every source in U
belongs to W](goal). -/
-- @node: degree_hall_obstruction
lemma degree_hall_obstruction {V C : Type} [Fintype V]
    (B : Finset C) (cand : V → Finset C)
    (hB : Fintype.card V ≤ B.card) (hcand : ∀ v, cand v ⊆ B)
    (hfail : ¬ ∃ f : V → C, Function.Injective f ∧ ∀ v, f v ∈ cand v) :
    ∃ U : Finset V, U.Nonempty ∧ ∃ W : Finset C,
      W ⊆ B ∧ W.card + 1 = U.card ∧ ∀ v ∈ U, cand v ⊆ W := by
  classical
  have hnot : ¬ ∀ U : Finset V, U.card ≤ (U.biUnion cand).card := by
    intro h
    exact hfail ((Finset.all_card_le_biUnion_card_iff_existsInjective' cand).mp h)
  push Not at hnot
  obtain ⟨U, hU⟩ := hnot
  have hne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hsub : U.biUnion cand ⊆ B := by
    intro c hc
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hc
    exact hcand v hv
  have hUcard : U.card ≤ Fintype.card V := Finset.card_le_univ _
  obtain ⟨W, hUW, hWB, hWcard⟩ := Finset.exists_subsuperset_card_eq hsub
    (show (U.biUnion cand).card ≤ U.card - 1 by omega)
    (show U.card - 1 ≤ B.card by omega)
  refine ⟨U, hne, W, hWB, by omega, ?_⟩
  intro v hv c hc
  exact hUW (Finset.mem_biUnion.mpr ⟨v, hv, hc⟩)

/-- If [n is at least one](hyp:hn), [there are at most n source vertices](hyp:hV),
and [B has at most n candidates](hyp:hB), then [the number of pairs consisting
of a source set of size u + 1 and a subset of B of size u is at most
n raised to 2(u + 1)](goal). -/
-- @node: degree_hall_pair_count
lemma degree_hall_pair_count {V C : Type} [Fintype V]
    (B : Finset C) (n u : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) (hB : B.card ≤ n) :
    ((Finset.univ : Finset V).powersetCard (u + 1)).card *
      (B.powersetCard u).card ≤ n ^ (2 * (u + 1)) := by
  rw [Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_univ]
  calc
    _ ≤ (Fintype.card V) ^ (u + 1) * B.card ^ u :=
      Nat.mul_le_mul (Nat.choose_le_pow _ _) (Nat.choose_le_pow _ _)
    _ ≤ n ^ (u + 1) * n ^ (u + 1) := by
      apply Nat.mul_le_mul (Nat.pow_le_pow_left hV _)
      exact (Nat.pow_le_pow_left hB _).trans (Nat.pow_le_pow_right hn (by omega))
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Suppose [0 < r < 1](hyp:hr), [n is at least two](hyp:hn), [there are at
most n source vertices](hyp:hV), [B has at most n candidates](hyp:hBn),
[each requirement has at most k coordinates](hyp:hsize), [each coordinate
occurs in at most Δ requirements](hyp:hload), [B has at least b more candidates
than sources](hyp:hB), and [b rᵏ/(1 + kΔ) is at least 5 log n](hyp:hexp).
Then [in an independent Bernoulli array with success probability r, the
probability that some source set U of size u + 1 and some subset W of B of
size u have no satisfied requirement from U outside W is at most
n raised to 2(u + 1) times exp(−5(u + 1) log n)](goal). -/
-- @node: degree_hall_size_failure_probability
lemma degree_hall_size_failure_probability {V X C : Type} [Fintype V]
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (r : ℝ) (hr : CompressionDensity r) (R : V → Finset X)
    (B : Finset C) (n k Δ b u : ℕ) (hn : 2 ≤ n)
    (hV : Fintype.card V ≤ n) (hBn : B.card ≤ n)
    (hsize : ∀ v, (R v).card ≤ k)
    (hload : ∀ x, (Finset.univ.filter (fun v => x ∈ R v)).card ≤ Δ)
    (hB : Fintype.card V + b ≤ B.card)
    (hexp : 5 * naturalLog n ≤ (b : ℝ) * r ^ k / (1 + (k : ℝ) * Δ)) :
    (productMeasure (X × C) r).Pr (fun z =>
      ∃ U ∈ (Finset.univ : Finset V).powersetCard (u + 1),
      ∃ W ∈ B.powersetCard u,
        ∀ v ∈ U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v, z (x, c) = true) ≤
      (n : ℝ) ^ (2 * (u + 1)) * Real.exp (-5 * (u + 1 : ℝ) * naturalLog n) := by
  classical
  let D := productMeasure (X × C) r
  let A := (Finset.univ : Finset V).powersetCard (u + 1)
  let F := B.powersetCard u
  let a := Real.exp (-5 * (u + 1 : ℝ) * naturalLog n)
  have hpair (U : Finset V) (hU : U ∈ A) (W : Finset C) (hW : W ∈ F) :
      D.Pr (fun z => ∀ v ∈ U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v, z (x, c) = true) ≤ a := by
    have hUc : U.card = u + 1 := (Finset.mem_powersetCard.mp hU).2
    obtain ⟨hWB, hWc⟩ := Finset.mem_powersetCard.mp hW
    have hbound := degree_hall_pair_probability r hr R B k Δ b hsize hload hB U W hWB
      (by omega)
    have hp : D.Pr (fun z => ∀ v ∈ U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v, z (x, c) = true) ≤
        Real.exp (-(b : ℝ) * U.card * r ^ k / (1 + (k : ℝ) * Δ)) := by
      convert hbound using 1
    refine hp.trans ?_
    rw [hUc]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg (u + 1) :
      (0 : ℝ) ≤ (u + 1 : ℕ))
    push_cast at hmul ⊢
    calc
      -(b : ℝ) * (u + 1) * r ^ k / (1 + (k : ℝ) * Δ) =
          -(u + 1 : ℝ) * ((b : ℝ) * r ^ k / (1 + (k : ℝ) * Δ)) := by ring
      _ ≤ -5 * (u + 1 : ℝ) * naturalLog n := by nlinarith
  have hcount : (A.card : ℝ) * F.card ≤ (n : ℝ) ^ (2 * (u + 1)) := by
    exact_mod_cast degree_hall_pair_count B n u (by omega) hV hBn
  calc
    _ = D.Pr (fun z => ∃ U ∈ A, ∃ W ∈ F,
        ∀ v ∈ U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v, z (x, c) = true) := by congr 1
    _ ≤ ∑ U ∈ A, D.Pr (fun z => ∃ W ∈ F,
        ∀ v ∈ U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v, z (x, c) = true) :=
      by
        convert transfer_finite_union_bound D A
          (fun U z => ∃ W ∈ F, ∀ v ∈ U, ∀ c ∈ B \ W,
            ¬ ∀ x ∈ R v, z (x, c) = true) using 1
    _ ≤ ∑ U ∈ A, ∑ _W ∈ F, a := by
      apply Finset.sum_le_sum
      intro U hU
      calc
        _ ≤ ∑ W ∈ F, D.Pr (fun z =>
            ∀ v ∈ U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v, z (x, c) = true) := by
          convert transfer_finite_union_bound D F
            (fun W z => ∀ v ∈ U, ∀ c ∈ B \ W,
              ¬ ∀ x ∈ R v, z (x, c) = true) using 1
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro W hW
          exact hpair U hU W hW
    _ = (A.card : ℝ) * F.card * a := by simp [mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _)

/-- If [0 < r < 1](hyp:hr), [n is at least two](hyp:hn), [there are at most
n source vertices](hyp:hV), [B has at most n candidates](hyp:hBn), [each
requirement has size at most k](hyp:hsize), [each coordinate occurs in at
most Δ requirements](hyp:hload), [B has at least b more candidates than
sources](hyp:hB), and [b rᵏ/(1 + kΔ) is at least 5 log n](hyp:hexp), then
[in an independent Bernoulli array with success probability r, the probability
that no injective assignment into B satisfies all source requirements is
at most 2/n³](goal). -/
-- @node: degree_layer_matching_failure_probability
lemma degree_layer_matching_failure_probability {V X C : Type} [Fintype V]
    [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    (r : ℝ) (hr : CompressionDensity r) (R : V → Finset X)
    (B : Finset C) (n k Δ b : ℕ) (hn : 2 ≤ n)
    (hV : Fintype.card V ≤ n) (hBn : B.card ≤ n)
    (hsize : ∀ v, (R v).card ≤ k)
    (hload : ∀ x, (Finset.univ.filter (fun v => x ∈ R v)).card ≤ Δ)
    (hB : Fintype.card V + b ≤ B.card)
    (hexp : 5 * naturalLog n ≤ (b : ℝ) * r ^ k / (1 + (k : ℝ) * Δ)) :
    (productMeasure (X × C) r).Pr (fun z =>
      ¬ ∃ f : V → C, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ x ∈ R v, z (x, f v) = true) ≤ 2 / (n : ℝ) ^ 3 := by
  classical
  let D := productMeasure (X × C) r
  let bad := fun (u : ℕ) (z : X × C → Bool) =>
    ∃ U ∈ (Finset.univ : Finset V).powersetCard (u + 1),
    ∃ W ∈ B.powersetCard u,
      ∀ v ∈ U, ∀ c ∈ B \ W, ¬ ∀ x ∈ R v, z (x, c) = true
  have hcover (z : X × C → Bool)
      (hz : ¬ ∃ f : V → C, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ x ∈ R v, z (x, f v) = true) :
      ∃ u ∈ Finset.range (Fintype.card V), bad u z := by
    let cand : V → Finset C := fun v => B.filter (fun c => ∀ x ∈ R v, z (x, c) = true)
    have hfail : ¬ ∃ f : V → C, Function.Injective f ∧ ∀ v, f v ∈ cand v := by
      rintro ⟨f, hf, hmem⟩
      exact hz ⟨f, hf, fun v => Finset.mem_filter.mp (hmem v)⟩
    obtain ⟨U, hUne, W, hWB, hWU, hUW⟩ := degree_hall_obstruction B cand (by omega)
      (fun v => Finset.filter_subset _ _) hfail
    have hUc : U.card ≤ Fintype.card V := Finset.card_le_univ _
    have hUp := hUne.card_pos
    refine ⟨U.card - 1, Finset.mem_range.mpr (by omega), U, ?_, W, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by omega⟩
    · exact Finset.mem_powersetCard.mpr ⟨hWB, by omega⟩
    · intro v hv c hc hs
      have hcW := hUW v hv (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hc).1, hs⟩)
      exact (Finset.mem_sdiff.mp hc).2 hcW
  calc
    _ = D.Pr (fun z => ¬ ∃ f : V → C, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ x ∈ R v, z (x, f v) = true) := by congr 1
    _ ≤ D.Pr (fun z => ∃ u ∈ Finset.range (Fintype.card V), bad u z) :=
      FiniteDesign.Pr_mono _ _ _ hcover
    _ ≤ ∑ u ∈ Finset.range (Fintype.card V), D.Pr (bad u) :=
      by
        convert transfer_finite_union_bound D (Finset.range (Fintype.card V)) bad using 1
        apply Finset.sum_congr rfl
        intro u hu
        congr 1
    _ ≤ ∑ u ∈ Finset.range (Fintype.card V),
        (n : ℝ) ^ (2 * (u + 1)) * Real.exp (-5 * (u + 1 : ℝ) * naturalLog n) := by
      apply Finset.sum_le_sum
      intro u hu
      convert degree_hall_size_failure_probability r hr R B n k Δ b u hn hV hBn
        hsize hload hB hexp using 1 <;> first | rfl | congr 1
    _ ≤ _ := degree_hall_union_bound n (Fintype.card V) hn

/-- Suppose [0 < r < 1](hyp:hr), [Y and B are disjoint host vertex sets](hyp:hYB),
[n is at least two](hyp:hn), [there are at most n source vertices](hyp:hV),
[each requirement on Y has at most k vertices](hyp:hsize), [each vertex of Y
occurs in at most Δ requirements](hyp:hload), [B has at least b more vertices
than sources](hyp:hB), and [b rᵏ/(1 + kΔ) is at least 5 log n](hyp:hexp).
Then [in the random host with edge probability r, the probability that no
injective assignment into B meets all required adjacencies to Y is at most
2/n³](goal). -/
-- @node: degree_host_layer_matching_failure_probability
lemma degree_host_layer_matching_failure_probability {V : Type} [Fintype V]
    (n : ℕ) (r : ℝ) (hr : CompressionDensity r) (Y B : Finset (Fin n))
    (hYB : Disjoint Y B) (R : V → Finset ↥Y) (k Δ b : ℕ) (hn : 2 ≤ n)
    (hV : Fintype.card V ≤ n) (hsize : ∀ v, (R v).card ≤ k)
    (hload : ∀ y, (Finset.univ.filter (fun v => y ∈ R v)).card ≤ Δ)
    (hB : Fintype.card V + b ≤ B.card)
    (hexp : 5 * naturalLog n ≤ (b : ℝ) * r ^ k / (1 + (k : ℝ) * Δ)) :
    (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z =>
      ¬ ∃ f : V → Fin n, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ y ∈ R v, (hostGraph z).Adj (f v) y.val) ≤
      2 / (n : ℝ) ^ 3 := by
  classical
  have hc (c : ↥B) : c.val ∉ Y := by
    intro hy
    exact Finset.disjoint_left.mp hYB hy c.property
  let e : ↥Y × ↥B → KEdge n := fun a => neighborhoodEdge Y a.2.val (hc a.2) a.1
  have hinj : Function.Injective e := by
    intro a b hab
    have he := congrArg Subtype.val hab
    simp only [e, neighborhoodEdge, Sym2.eq_iff] at he
    rcases he with he | he
    · exact Prod.ext (Subtype.ext he.2) (Subtype.ext he.1)
    · exact (hc a.2 (he.1 ▸ b.1.property)).elim
  have hadj (z : KEdge n → Bool) (c : ↥B) (y : ↥Y) :
      (hostGraph z).Adj c.val y.val ↔ z (e (y, c)) = true := by
    have hne : c.val ≠ y.val := fun h => hc c (h ▸ y.property)
    simp [hostGraph, SimpleGraph.fromEdgeSet_adj, e, neighborhoodEdge, hne]
  let P := fun z : (↥Y × ↥B) → Bool =>
    ¬ ∃ f : V → ↥B, Function.Injective f ∧
      ∀ v, f v ∈ (Finset.univ : Finset ↥B) ∧ ∀ y ∈ R v, z (y, f v) = true
  have hevent (z : KEdge n → Bool) :
      (¬ ∃ f : V → Fin n, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ y ∈ R v, (hostGraph z).Adj (f v) y.val) ↔
      P (fun a => z (e a)) := by
    apply not_congr
    constructor
    · rintro ⟨f, hf, hmem⟩
      refine ⟨fun v => ⟨f v, (hmem v).1⟩, ?_, ?_⟩
      · intro v w hvw
        exact hf (congrArg Subtype.val hvw)
      · intro v
        exact ⟨Finset.mem_univ _, fun y hy => (hadj z _ y).mp ((hmem v).2 y hy)⟩
    · rintro ⟨f, hf, hmem⟩
      refine ⟨fun v => (f v).val, ?_, ?_⟩
      · intro v w hvw
        exact hf (Subtype.ext hvw)
      · intro v
        exact ⟨(f v).property, fun y hy => (hadj z _ y).mpr ((hmem v).2 y hy)⟩
  have hprob : (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z =>
      ¬ ∃ f : V → Fin n, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ y ∈ R v, (hostGraph z).Adj (f v) y.val) =
      (productMeasure (↥Y × ↥B) r).Pr P := by
    rw [(randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr_congr _ _ hevent]
    exact productMeasure_E_comp_injective r e hinj (FiniteDesign.ind P)
  rw [hprob]
  have h := degree_layer_matching_failure_probability r hr R (Finset.univ : Finset ↥B)
    n k Δ b hn hV (by simpa using Finset.card_le_univ B) hsize hload
    (by simpa using hB) hexp
  convert h using 1

/-- If [0 < r < 1](hyp:hr), [Y and B are disjoint](hyp:hYB), and [event A
depends only on host adjacencies within Y](hyp:hA), then [the probability
of A and failure to assign distinct vertices in B satisfying all requirements
on Y equals the probability of A times the probability of that assignment
failure](goal). -/
-- @node: degree_fresh_layer_probability_factor
lemma degree_fresh_layer_probability_factor {V : Type} [Fintype V]
    (n : ℕ) (r : ℝ) (hr : CompressionDensity r) (Y B : Finset (Fin n))
    (hYB : Disjoint Y B) (R : V → Finset ↥Y)
    (A : (KEdge n → Bool) → Prop)
    (hA : ∀ z z', (∀ a ∈ Y, ∀ c ∈ Y,
      (hostGraph z).Adj a c ↔ (hostGraph z').Adj a c) → (A z ↔ A z')) :
    (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => A z ∧
      ¬ ∃ f : V → Fin n, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ y ∈ R v, (hostGraph z).Adj (f v) y.val) =
    (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr A * (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z =>
      ¬ ∃ f : V → Fin n, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ y ∈ R v, (hostGraph z).Adj (f v) y.val) := by
  classical
  let D := randomHost n r ⟨hr.1.le, hr.2.le⟩
  let F := fun z : KEdge n → Bool =>
    ¬ ∃ f : V → Fin n, Function.Injective f ∧
      ∀ v, f v ∈ B ∧ ∀ y ∈ R v, (hostGraph z).Adj (f v) y.val
  have hc (c : ↥B) : c.val ∉ Y := by
    intro hy
    exact Finset.disjoint_left.mp hYB hy c.property
  let e : ↥Y × ↥B → KEdge n := fun a => neighborhoodEdge Y a.2.val (hc a.2) a.1
  let block : Finset (KEdge n) := Finset.univ.image e
  have hadj (z : KEdge n → Bool) (c : ↥B) (y : ↥Y) :
      (hostGraph z).Adj c.val y.val ↔ z (e (y, c)) = true := by
    have hne : c.val ≠ y.val := fun h => hc c (h ▸ y.property)
    simp [hostGraph, SimpleGraph.fromEdgeSet_adj, e, neighborhoodEdge, hne]
  have hF : ∀ z z', (∀ d ∈ block, z d = z' d) → (F z ↔ F z') := by
    intro z z' hz
    apply not_congr
    apply exists_congr
    intro f
    apply and_congr_right
    intro hf
    apply forall_congr'
    intro v
    apply and_congr_right
    intro hv
    apply forall₂_congr
    intro y hy
    rw [hadj z ⟨f v, hv⟩ y, hadj z' ⟨f v, hv⟩ y,
      hz (e (y, ⟨f v, hv⟩)) (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)]
  have hcomp : ∀ z z', (∀ d ∉ block, z d = z' d) → (A z ↔ A z') := by
    intro z z' hz
    apply hA z z'
    intro a ha c hcY
    by_cases hac : a = c
    · subst c
      simp
    · let d : KEdge n := ⟨s(a, c), by simpa using hac⟩
      have hd : d ∉ block := by
        intro hd
        obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hd
        have he := congrArg Subtype.val hp
        simp only [e, neighborhoodEdge, d, Sym2.eq_iff] at he
        rcases he with he | he
        · exact hc p.2 (he.1.symm ▸ ha)
        · exact hc p.2 (he.1.symm ▸ hcY)
      have heq := hz d hd
      have hevent (w : KEdge n → Bool) :
          (hostGraph w).Adj a c ↔ w d = true := by
        simp [hostGraph, SimpleGraph.fromEdgeSet_adj, d, hac]
      rw [hevent z, hevent z', heq]
  have hfactor : D.E (fun z => FiniteDesign.ind F z * FiniteDesign.ind A z) =
      D.E (FiniteDesign.ind F) * D.E (FiniteDesign.ind A) := by
    dsimp [D, randomHost]
    rw [Toolkit.Foundations.Probability.bernoulliCube_eq r hr.1.le hr.2.le]
    apply FiniteDesign.E_prod_block_mul _ block
    · intro z z' hz
      simp only [FiniteDesign.ind, hF z z' hz]
    · intro z z' hz
      simp only [FiniteDesign.ind, hcomp z z' hz]
  have hpoint (z : KEdge n → Bool) :
      FiniteDesign.ind (fun z => A z ∧ F z) z = FiniteDesign.ind F z * FiniteDesign.ind A z := by
    by_cases ha : A z <;> by_cases hf : F z <;> simp [FiniteDesign.ind, ha, hf]
  change D.E (FiniteDesign.ind (fun z => A z ∧ F z)) =
    D.E (FiniteDesign.ind A) * D.E (FiniteDesign.ind F)
  rw [FiniteDesign.E_congr _ hpoint, hfactor, mul_comm]

/-- Suppose [0 < r < 1](hyp:hr), [Y and B are disjoint](hyp:hYB), [n is at
least two](hyp:hn), [there are at most n sources](hyp:hV), [each requirement
on Y has size at most k](hyp:hsize), [each vertex of Y occurs in at most Δ
requirements](hyp:hload), [B has at least b more vertices than sources](hyp:hB),
and [b rᵏ/(1 + kΔ) is at least 5 log n](hyp:hexp). If [A depends only on
host adjacencies within Y](hyp:hA), then [the probability of A and failure
to assign distinct vertices in B satisfying all required adjacencies is at
most the probability of A times 2/n³](goal). -/
-- @node: degree_fresh_layer_failure_bound
lemma degree_fresh_layer_failure_bound {V : Type} [Fintype V]
    (n : ℕ) (r : ℝ) (hr : CompressionDensity r) (Y B : Finset (Fin n))
    (hYB : Disjoint Y B) (R : V → Finset ↥Y) (k Δ b : ℕ) (hn : 2 ≤ n)
    (hV : Fintype.card V ≤ n) (hsize : ∀ v, (R v).card ≤ k)
    (hload : ∀ y, (Finset.univ.filter (fun v => y ∈ R v)).card ≤ Δ)
    (hB : Fintype.card V + b ≤ B.card)
    (hexp : 5 * naturalLog n ≤ (b : ℝ) * r ^ k / (1 + (k : ℝ) * Δ))
    (A : (KEdge n → Bool) → Prop)
    (hA : ∀ z z', (∀ a ∈ Y, ∀ c ∈ Y,
      (hostGraph z).Adj a c ↔ (hostGraph z').Adj a c) → (A z ↔ A z')) :
    (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => A z ∧
      ¬ ∃ f : V → Fin n, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ y ∈ R v, (hostGraph z).Adj (f v) y.val) ≤
      (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr A * (2 / (n : ℝ) ^ 3) := by
  rw [degree_fresh_layer_probability_factor n r hr Y B hYB R A hA]
  exact mul_le_mul_of_nonneg_left
    (degree_host_layer_matching_failure_probability n r hr Y B hYB R k Δ b hn hV
      hsize hload hB hexp) (FiniteDesign.Pr_nonneg _ A)

/-- Suppose [0 < r < 1](hyp:hr), [Y and B are disjoint](hyp:hYB), [n is at
least two](hyp:hn), [there are at most n sources](hyp:hV), [each requirement
on Y has at most k vertices](hyp:hsize), [each vertex of Y occurs in at most
Δ requirements](hyp:hload), [B has at least b more vertices than sources](hyp:hB),
and [b rᵏ/(1 + kΔ) is at least 5 log n](hyp:hexp). If [A depends only on
host adjacencies within Y](hyp:hA), then [the probability of A and a successful
injective assignment into B meeting every adjacency requirement is at least
(1 − 2/n³) times the probability of A](goal). -/
-- @node: degree_fresh_layer_success_bound
lemma degree_fresh_layer_success_bound {V : Type} [Fintype V]
    (n : ℕ) (r : ℝ) (hr : CompressionDensity r) (Y B : Finset (Fin n))
    (hYB : Disjoint Y B) (R : V → Finset ↥Y) (k Δ b : ℕ) (hn : 2 ≤ n)
    (hV : Fintype.card V ≤ n) (hsize : ∀ v, (R v).card ≤ k)
    (hload : ∀ y, (Finset.univ.filter (fun v => y ∈ R v)).card ≤ Δ)
    (hB : Fintype.card V + b ≤ B.card)
    (hexp : 5 * naturalLog n ≤ (b : ℝ) * r ^ k / (1 + (k : ℝ) * Δ))
    (A : (KEdge n → Bool) → Prop)
    (hA : ∀ z z', (∀ a ∈ Y, ∀ c ∈ Y,
      (hostGraph z).Adj a c ↔ (hostGraph z').Adj a c) → (A z ↔ A z')) :
    (1 - 2 / (n : ℝ) ^ 3) * (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr A ≤
    (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr (fun z => A z ∧
      ∃ f : V → Fin n, Function.Injective f ∧
        ∀ v, f v ∈ B ∧ ∀ y ∈ R v, (hostGraph z).Adj (f v) y.val) := by
  classical
  have hbound := degree_fresh_layer_failure_bound n r hr Y B hYB R k Δ b hn hV
    hsize hload hB hexp A hA
  have hsplit := (randomHost n r ⟨hr.1.le, hr.2.le⟩).Pr_split A (fun z =>
    ∃ f : V → Fin n, Function.Injective f ∧
      ∀ v, f v ∈ B ∧ ∀ y ∈ R v, (hostGraph z).Adj (f v) y.val)
  linarith

end Papers.OaiGraphDecompositionsIntegral
