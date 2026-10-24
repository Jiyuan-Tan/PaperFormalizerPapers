module

public import Papers.OaiLinearVarianceRandom.Helpers.RootExposure
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Counting clauses with specified root incidences

Coarse absolute constants suffice for the uniform moment estimates. We count
signed root subsets, so no independence between literals of a clause is used.
-/

public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

open Classical in
-- @node: card_clause_extensions_le
/-- For [a specified set t of signed literals](hyp:t) on n coordinates,
[the number of proper three-literal clauses containing t is at most the number of ways to choose 3 minus the size of t literals from the 2n signed literals](goal),
where subtraction of natural numbers is truncated at zero. -/
lemma card_clause_extensions_le {n : ℕ} (t : Finset (Fin n × Bool)) :
    Fintype.card {c : ProperClause n // t ⊆ c.val} ≤
      (2 * n).choose (3 - t.card) := by
  let f : {c : ProperClause n // t ⊆ c.val} →
      {s : Finset (Fin n × Bool) // s.card = 3 - t.card} :=
    fun c => ⟨c.val.val \ t, by
      rw [Finset.card_sdiff_of_subset c.property, c.val.property.1]⟩
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    apply Subtype.ext
    have hsd := congrArg Subtype.val h
    change c.val.val \ t = d.val.val \ t at hsd
    have hc := Finset.sdiff_union_of_subset c.property
    have hd := Finset.sdiff_union_of_subset d.property
    rw [← hc, ← hd, hsd]
  apply (Fintype.card_le_of_injective f hf).trans
  simp [Fintype.card_finset_len, Nat.mul_comm]

open Classical in
-- @node: card_root_incidence_le
/-- For [a reference proper three-literal clause](hyp:c0) on n coordinates and [a nonnegative incidence threshold k](hyp:k),
[the number of proper three-literal clauses with at least k literals on the reference clause's coordinates is at most the number of ways to choose k of the six signed root literals, times the number of ways to choose 3 minus k of all 2n signed literals](goal),
where subtraction of natural numbers is truncated at zero. -/
lemma card_root_incidence_le {n : ℕ} (c0 : ProperClause n) (k : ℕ) :
    Fintype.card {c : ProperClause n // k ≤ (rootLiterals c0 c).card} ≤
      Nat.choose 6 k * (2 * n).choose (3 - k) := by
  let R : Finset (Fin n × Bool) := (roots c0) ×ˢ Finset.univ
  have hR : R.card = 6 := by simp [R, roots_card]
  let E : Finset (ProperClause n) := Finset.univ.filter
    (fun c => k ≤ (rootLiterals c0 c).card)
  have hcover : E ⊆ (R.powersetCard k).biUnion
      (fun t => Finset.univ.filter (fun c : ProperClause n => t ⊆ c.val)) := by
    intro c hc
    have hk := (Finset.mem_filter.mp hc).2
    obtain ⟨t, ht, htk⟩ := Finset.exists_subset_card_eq hk
    apply Finset.mem_biUnion.mpr
    refine ⟨t, Finset.mem_powersetCard.mpr ⟨?_, htk⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    · intro l hl
      have hroot := (Finset.mem_filter.mp (ht hl)).2
      simp [R, hroot]
    · exact ht.trans (Finset.filter_subset _ _)
  calc
    _ = E.card := by simp [E, Fintype.card_subtype]
    _ ≤ _ := Finset.card_le_card hcover
    _ ≤ ∑ t ∈ R.powersetCard k,
        (Finset.univ.filter (fun c : ProperClause n => t ⊆ c.val)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ t ∈ R.powersetCard k, (2 * n).choose (3 - k) := by
      apply Finset.sum_le_sum
      intro t ht
      have htk := (Finset.mem_powersetCard.mp ht).2
      simpa [Fintype.card_subtype, htk] using card_clause_extensions_le t
    _ = _ := by simp [Finset.card_powersetCard, hR]

open Classical in
-- @node: uniformClauseMeasure_real_set
/-- For [a property P of proper three-literal clauses](hyp:P) on n coordinates,
[its probability under the uniform clause law equals the number of clauses satisfying P divided by eight times the number of ways to choose three coordinates from n](goal). -/
lemma uniformClauseMeasure_real_set {n : ℕ} (P : ProperClause n → Prop) :
    (uniformClauseMeasure n 3).real {c | P c} =
      (Fintype.card {c : ProperClause n // P c} : ℝ) /
        (8 * n.choose 3) := by
  calc
    _ = (Fintype.card {c : ProperClause n // P c} : ℝ) /
        Fintype.card (ProperClause n) := by
      simp [uniformClauseMeasure, measureReal_def, uniformOn_univ,
        Measure.count_apply_finite, Set.toFinite, Set.toFinset_card,
        ENNReal.toReal_div, Fintype.card_subtype]
    _ = _ := by rw [card_properClauseA]; norm_num

-- @node: choose_three_lower_bound
/-- If [n is at least six](hyp:hn), [the cube of n is at most twenty-four times the number of ways to choose three elements from n elements](goal). -/
lemma choose_three_lower_bound {n : ℕ} (hn : 6 ≤ n) :
    (n : ℝ) ^ 3 ≤ 24 * (n.choose 3 : ℝ) := by
  have hp := Nat.descFactorial_eq_factorial_mul_choose n 3
  simp [Nat.descFactorial_succ, Nat.factorial_succ] at hp
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]; norm_num
  have heq : (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) =
      6 * (n.choose 3 : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hn1, hn2, mul_comm, mul_left_comm, mul_assoc] using congrArg (fun x : ℕ => (x : ℝ)) hp
  have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [sq_nonneg ((n : ℝ) - 3),
    mul_nonneg (by linarith : (0 : ℝ) ≤ n) (sq_nonneg ((n : ℝ) - 3))]

open Classical in
-- @node: root_hit_probability_le
/-- If [the coordinate count n is at least six](hyp:hn), then for [any reference proper three-literal clause](hyp:c0),
[the probability that a uniformly sampled proper three-literal clause contains at least one literal on a coordinate of the reference clause is at most 72 divided by n](goal). -/
lemma root_hit_probability_le {n : ℕ} (hn : 6 ≤ n) (c0 : ProperClause n) :
    (uniformClauseMeasure n 3).real {c | 1 ≤ (rootLiterals c0 c).card} ≤
      72 / (n : ℝ) := by
  classical
  rw [uniformClauseMeasure_real_set]
  simp only [Fintype.card_eq_nat_card]
  have hc := card_root_incidence_le c0 1
  simp only [Fintype.card_eq_nat_card] at hc
  have hb := Nat.choose_le_pow (2 * n) 2
  simp only [Nat.choose_one_right, show 3 - 1 = 2 from rfl] at hc
  have hcard : (Fintype.card {c : ProperClause n //
      1 ≤ (rootLiterals c0 c).card} : ℝ) ≤ 24 * (n : ℝ) ^ 2 := by
    simp only [Fintype.card_eq_nat_card]
    have h := hc.trans (Nat.mul_le_mul_left 6 hb)
    have h' : (Nat.card {c : ProperClause n //
        1 ≤ (rootLiterals c0 c).card} : ℝ) ≤ 6 * (2 * (n : ℝ)) ^ 2 := by
      exact_mod_cast h
    nlinarith
  simp only [Fintype.card_eq_nat_card] at *
  have hd := choose_three_lower_bound hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hchoose : (0 : ℝ) < n.choose 3 := by nlinarith [pow_pos hn' 3]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (n.choose 3 : ℝ)) hn']
  calc
    _ ≤ (24 * (n : ℝ) ^ 2) * n := mul_le_mul_of_nonneg_right hcard hn'.le
    _ = 24 * (n : ℝ) ^ 3 := by ring
    _ ≤ 24 * (24 * (n.choose 3 : ℝ)) := mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = _ := by ring

open Classical in
-- @node: root_collision_probability_le
/-- If [the coordinate count n is at least six](hyp:hn), then for [any reference proper three-literal clause](hyp:c0),
[the probability that a uniformly sampled proper three-literal clause contains at least two literals on coordinates of the reference clause is at most 90 divided by n squared](goal). -/
lemma root_collision_probability_le {n : ℕ} (hn : 6 ≤ n) (c0 : ProperClause n) :
    (uniformClauseMeasure n 3).real {c | 2 ≤ (rootLiterals c0 c).card} ≤
      90 / (n : ℝ) ^ 2 := by
  classical
  rw [uniformClauseMeasure_real_set]
  simp only [Fintype.card_eq_nat_card]
  have hc := card_root_incidence_le c0 2
  simp only [Fintype.card_eq_nat_card] at hc
  simp only [show Nat.choose 6 2 = 15 by decide, show 3 - 2 = 1 from rfl,
    Nat.choose_one_right] at hc
  have hcard : (Fintype.card {c : ProperClause n //
      2 ≤ (rootLiterals c0 c).card} : ℝ) ≤ 30 * (n : ℝ) := by
    have h' : (Nat.card {c : ProperClause n //
        2 ≤ (rootLiterals c0 c).card} : ℝ) ≤ 15 * (2 * (n : ℝ)) := by
      exact_mod_cast hc
    simp only [Fintype.card_eq_nat_card] at *
    linarith
  simp only [Fintype.card_eq_nat_card] at *
  have hd := choose_three_lower_bound hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hchoose : (0 : ℝ) < n.choose 3 := by nlinarith [pow_pos hn' 3]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (n.choose 3 : ℝ))
    (sq_pos_of_pos hn')]
  calc
    _ ≤ (30 * (n : ℝ)) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = 30 * (n : ℝ) ^ 3 := by ring
    _ ≤ 30 * (24 * (n.choose 3 : ℝ)) := mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = _ := by ring

end Papers.OaiLinearVarianceRandom
