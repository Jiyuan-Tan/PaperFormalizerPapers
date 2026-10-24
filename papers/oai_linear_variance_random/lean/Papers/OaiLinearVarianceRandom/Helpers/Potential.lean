module

public import Papers.OaiLinearVarianceRandom.Helpers.AssignmentSets
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Independent-clause increments and the potential drift inequality -/

public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option linter.unusedVariables false
variable {u : ℕ}

open Classical in
-- @node: killProb_eq_expect
/-- [The probability that j independent uniform proper two-literal clauses eliminate every assignment in S equals the average indicator that their survivor set is empty](goal). -/
lemma killProb_eq_expect (j : ℕ) (S : Finset (Fin u → Bool)) :
    killProb j S = 𝔼 cs : Fin j → ProperClauseA u 2,
      (if familySurvivors j S cs = ∅ then (1 : ℝ) else 0) := by
  simp [killProb, Fintype.expect_eq_sum_div_card, Fintype.card_subtype]

open Classical in
-- @node: oneKillProb_eq_expect
/-- [The probability that a uniform proper a-literal clause eliminates every assignment in S equals the average indicator that no assignment in S satisfies that clause](goal). -/
lemma oneKillProb_eq_expect (a : ℕ) (S : Finset (Fin u → Bool)) :
    oneKillProb a S = 𝔼 C : ProperClauseA u a,
      (if survivors S C = ∅ then (1 : ℝ) else 0) := by
  simp [oneKillProb, Fintype.expect_eq_sum_div_card, Fintype.card_subtype]

open Classical in
-- @node: familySurvivors_cons
/-- [The assignments in S surviving a family with C prepended are exactly those that survive the remaining j clauses and also satisfy C](goal). -/
lemma familySurvivors_cons (j : ℕ) (S : Finset (Fin u → Bool))
    (C : ProperClauseA u 2) (cs : Fin j → ProperClauseA u 2) :
    familySurvivors (j + 1) S (Fin.cons C cs) =
      survivors (familySurvivors j S cs) C := by
  ext z
  simp [familySurvivors, survivors, Fin.forall_fin_succ, and_left_comm, and_comm]

open Classical in
-- @node: familySurvivors_survivors
/-- [Restricting S to assignments satisfying C before applying a family of j two-literal clauses gives the same survivors as applying the family first and then C](goal). -/
lemma familySurvivors_survivors (j a : ℕ) (S : Finset (Fin u → Bool))
    (C : ProperClauseA u a) (cs : Fin j → ProperClauseA u 2) :
    familySurvivors j (survivors S C) cs =
      survivors (familySurvivors j S cs) C := by
  ext z
  simp [familySurvivors, survivors, and_comm, and_assoc]

open Classical in
-- @node: killProb_succ_average
/-- [The probability that j + 1 independent uniform two-literal clauses eliminate S equals the average probability that one more such clause eliminates the survivors of the first j clauses](goal). -/
lemma killProb_succ_average (j : ℕ) (S : Finset (Fin u → Bool)) :
    killProb (j + 1) S =
      𝔼 cs : Fin j → ProperClauseA u 2, oneKillProb 2 (familySurvivors j S cs) := by
  rw [killProb_eq_expect]
  let e : (Fin (j + 1) → ProperClauseA u 2) ≃
      (ProperClauseA u 2 × (Fin j → ProperClauseA u 2)) :=
    { toFun := fun cs => (cs 0, fun k => cs k.succ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := fun cs => by funext k; refine Fin.cases ?_ (fun k => ?_) k <;> rfl
      right_inv := fun p => by cases p; rfl }
  have h := Fintype.expect_equiv e
    (fun cs => if familySurvivors (j + 1) S cs = ∅ then (1 : ℝ) else 0)
    (fun p => if survivors (familySurvivors j S p.2) p.1 = ∅ then (1 : ℝ) else 0)
    (fun cs => by
      rw [← familySurvivors_cons]
      change _ = if familySurvivors (j + 1) S (e.symm (e cs)) = ∅ then _ else _
      rw [e.symm_apply_apply])
  rw [h, ← Finset.univ_product_univ, Finset.expect_product]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro cs _
  simpa only using (oneKillProb_eq_expect (u := u) 2 (familySurvivors j S cs)).symm

open Classical in
-- @node: killProb_increment
/-- If [there are at least three assignment coordinates](hyp:hu), [the increase in the probability of eliminating S from adding a two-literal clause equals the average one-clause elimination probability of the surviving assignments, counted as zero when none remain](goal). -/
lemma killProb_increment (hu : OneU u) (j : ℕ) (S : Finset (Fin u → Bool)) :
    killProb (j + 1) S - killProb j S =
      𝔼 cs : Fin j → ProperClauseA u 2,
        (if (familySurvivors j S cs).Nonempty then
          oneKillProb 2 (familySurvivors j S cs) else 0) := by
  -- Subtract the already-killed families; only nonempty old survivor sets contribute.
  rw [killProb_succ_average, killProb_eq_expect, ← Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro cs _
  by_cases h : (familySurvivors j S cs).Nonempty
  · simp [h, h.ne_empty]
  · have he : familySurvivors j S cs = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have := properClauseA_nonempty u 2 (by unfold OneU at hu; omega)
    simp [he, oneKillProb, survivors]

open Classical in
-- @node: integral_uniformClause_eq_expect
/-- If [the clause length a does not exceed the number of coordinates](hyp:ha), [the integral of f under the uniform proper a-literal clause law equals its finite average over all such clauses](goal). -/
lemma integral_uniformClause_eq_expect (a : ℕ) (ha : a ≤ u)
    (f : ProperClauseA u a → ℝ) :
    (∫ C, f C ∂(uniformClauseMeasure u a)) = 𝔼 C, f C := by
  have := properClauseA_nonempty u a ha
  have : IsProbabilityMeasure (uniformClauseMeasure u a) := by
    unfold uniformClauseMeasure
    infer_instance
  rw [integral_fintype (Integrable.of_finite), Fintype.expect_eq_sum_div_card,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro C _
  simp [uniformClauseMeasure, measureReal_def, uniformOn_univ,
    div_eq_inv_mul]

open Classical in
-- @node: killProb_survivor_increment
/-- If [the clause length a does not exceed the number of coordinates](hyp:ha), [the average increase in the j-clause elimination probability after restricting S by a uniform a-literal clause equals the average probability that this clause eliminates the j-clause survivors, counted as zero when none remain](goal). -/
lemma killProb_survivor_increment (a : ℕ) (ha : a ≤ u)
    (j : ℕ) (S : Finset (Fin u → Bool)) :
    (𝔼 C : ProperClauseA u a, (killProb j (survivors S C) - killProb j S)) =
      𝔼 cs : Fin j → ProperClauseA u 2,
        (if (familySurvivors j S cs).Nonempty then
          oneKillProb a (familySurvivors j S cs) else 0) := by
  have := properClauseA_nonempty u a ha
  -- Exchange the independent finite averages, then add the final clause last.
  simp_rw [killProb_eq_expect, ← Finset.expect_sub_distrib]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro cs _
  simp_rw [familySurvivors_survivors]
  by_cases h : (familySurvivors j S cs).Nonempty
  · simp only [h, h.ne_empty, if_true, if_false, sub_zero]
    exact (oneKillProb_eq_expect a _).symm
  · have he : familySurvivors j S cs = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he, survivors]

open Classical in
-- @node: killProb_three_increment
/-- If [there are at least three assignment coordinates](hyp:hu), [the expected increase in the j-clause elimination probability after restricting S by a uniform three-literal clause equals the average probability that this clause eliminates the j-clause survivors, counted as zero when none remain](goal). -/
lemma killProb_three_increment (hu : OneU u) (j : ℕ) (S : Finset (Fin u → Bool)) :
    (∫ C, killProb j (survivors S C) - killProb j S ∂(uniformClauseMeasure u 3)) =
      𝔼 cs : Fin j → ProperClauseA u 2,
        (if (familySurvivors j S cs).Nonempty then
          oneKillProb 3 (familySurvivors j S cs) else 0) := by
  rw [integral_uniformClause_eq_expect 3 hu]
  exact killProb_survivor_increment 3 hu j S

-- @node: finite_average_rpow_le
/-- For a function on a nonempty finite population, if [every value is nonnegative](hyp:hf), [the three-halves power of its average is at most the average of its three-halves powers](goal). -/
lemma finite_average_rpow_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, f x) ^ beta ≤ 𝔼 x, (f x) ^ beta := by
  classical
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hj := (convexOn_rpow (show 1 ≤ beta by norm_num [beta])).map_sum_le
    (t := Finset.univ) (w := fun _ : α => (Fintype.card α : ℝ)⁻¹)
    (p := f) (by intro x _; positivity)
    (by simp [hc]) (by intro x _; exact hf x)
  simpa only [Fintype.expect_eq_sum_div_card, Finset.sum_div, smul_eq_mul,
    div_eq_inv_mul, ← Finset.mul_sum] using hj

open Classical in
-- @node: killProb_increment_nonneg
/-- If [there are at least three assignment coordinates](hyp:hu), [adding one independent uniform two-literal clause cannot decrease the probability of eliminating S](goal). -/
lemma killProb_increment_nonneg (hu : OneU u) (j : ℕ)
    (S : Finset (Fin u → Bool)) : 0 ≤ killProb (j + 1) S - killProb j S := by
  rw [killProb_increment hu]
  apply Finset.expect_nonneg
  intro cs _
  split_ifs <;> (try unfold oneKillProb) <;> positivity

open Classical in
-- @node: killProb_increment_rpow_le
/-- Suppose [there are at least three assignment coordinates](hyp:hu), [the two- and three-literal clause laws are uniform](hyp:hclause), and [the auxiliary two-literal families are sampled independently with replacement](hyp:hreplacement). Then [the three-halves power of the increase in elimination probability from the next two-literal clause is at most three times the expected increase in the j-clause elimination probability from restricting S by a three-literal clause, plus the inverse cube of the number of coordinates](goal). -/
lemma killProb_increment_rpow_le (hu : OneU u)
    (ν : (a : ℕ) → Measure (ProperClauseA u a))
    (hclause : ∀ a, a = 2 ∨ a = 3 → OneClauseLaw a (ν a))
    (νj : (j : ℕ) → Measure (Fin j → ProperClauseA u 2))
    (hreplacement : SampledWithReplacement (ν 2) νj)
    (j : ℕ) (S : Finset (Fin u → Bool)) :
    (killProb (j + 1) S - killProb j S) ^ beta ≤
      3 * (∫ C, killProb j (survivors S C) - killProb j S ∂(ν 3)) +
        (u : ℝ) ^ (-3 : ℝ) := by
  have := properClauseA_nonempty u 2 (by unfold OneU at hu; omega)
  have hν : ν 3 = uniformClauseMeasure u 3 := hclause 3 (Or.inr rfl)
  rw [hν, killProb_increment hu, killProb_three_increment hu]
  let f := fun cs : Fin j → ProperClauseA u 2 =>
    if (familySurvivors j S cs).Nonempty then
      oneKillProb 2 (familySurvivors j S cs) else 0
  let g := fun cs : Fin j → ProperClauseA u 2 =>
    if (familySurvivors j S cs).Nonempty then
      oneKillProb 3 (familySurvivors j S cs) else 0
  change (𝔼 cs, f cs) ^ beta ≤ 3 * (𝔼 cs, g cs) + _
  calc
    (𝔼 cs, f cs) ^ beta ≤ 𝔼 cs, (f cs) ^ beta :=
      finite_average_rpow_le f (by
        intro cs
        dsimp [f]
        split_ifs <;> (try unfold oneKillProb) <;> positivity)
    _ ≤ 𝔼 cs, (3 * g cs + (u : ℝ) ^ (-3 : ℝ)) := by
      apply Finset.expect_le_expect
      intro cs _
      by_cases h : (familySurvivors j S cs).Nonempty
      · simp only [f, g, h, if_true]
        exact oneKillProb_two_rpow_le hu ν hclause _ h νj hreplacement
      · simp only [f, g, h, if_false]
        rw [Real.zero_rpow (by norm_num [beta])]
        positivity
    _ = _ := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]

-- @node: potential_bounds
/-- [The potential of any assignment set at length d lies between zero and d](goal). -/
lemma potential_bounds (d : ℕ) (S : Finset (Fin u → Bool)) :
    0 ≤ potential d S ∧ potential d S ≤ d := by
  constructor
  · exact Finset.sum_nonneg fun j _ => (killProb_bounds j S).1
  · calc
      potential d S ≤ ∑ _j ∈ Finset.range d, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => (killProb_bounds j S).2
      _ = d := by simp

-- @node: potential_antitone
/-- If [S′ is a subset of S](hyp:h), [the length-d potential of S is at most that of S′](goal). -/
lemma potential_antitone (d : ℕ) {S S' : Finset (Fin u → Bool)} (h : S' ⊆ S) :
    potential d S ≤ potential d S' :=
  Finset.sum_le_sum fun j _ => killProb_antitone j h

open Classical in
-- @node: potential_expected_increment
/-- If [there are at least three assignment coordinates](hyp:hu), [the expected increase in the length-d potential after restricting S by a uniform three-literal clause equals the sum, over family lengths from zero through d − 1, of the corresponding expected increases in elimination probability](goal). -/
lemma potential_expected_increment (hu : OneU u) (d : ℕ)
    (S : Finset (Fin u → Bool)) :
    (∫ C, potential d (survivors S C) - potential d S ∂(uniformClauseMeasure u 3)) =
      ∑ j ∈ Finset.range d,
        ∫ C, killProb j (survivors S C) - killProb j S ∂(uniformClauseMeasure u 3) := by
  simp_rw [integral_uniformClause_eq_expect 3 hu, potential, ← Finset.sum_sub_distrib]
  exact Finset.expect_sum_comm _ _ _

open Classical in
-- @node: lem:potential
/-- Suppose [there are at least three assignment coordinates](hyp:hu), [the two- and three-literal clause laws are uniform](hyp:hclause), [d is positive](hyp:hd), [auxiliary two-literal families are sampled independently with replacement](hyp:hreplacement), and [the three-literal clause is uniform and independent of every auxiliary family under the joint laws](hyp:hC). Then [the length-d potential lies between zero and d and increases when S is reduced; moreover, the three-halves power of the d-clause elimination probability, multiplied by the indicator that S is nonempty, is at most the square root of d times the sum of three times the expected potential increase from a three-literal clause and d times the inverse cube of the number of coordinates](goal). -/
lemma potential_drift (hu : OneU u)
    (ν : (a : ℕ) → Measure (ProperClauseA u a))
    (hclause : ∀ a, a = 2 ∨ a = 3 → OneClauseLaw a (ν a))
    (d : ℕ) (hd : PotentialD d) (S : Finset (Fin u → Bool))
    (νj : (j : ℕ) → Measure (Fin j → ProperClauseA u 2))
    (hreplacement : SampledWithReplacement (ν 2) νj)
    (joint : (j : ℕ) → Measure ((Fin j → ProperClauseA u 2) × ProperClauseA u 3))
    (hC : PotentialClauseLaw (ν 3) νj joint) :
    (0 ≤ potential d S ∧ potential d S ≤ d) ∧
    (∀ S' : Finset (Fin u → Bool), S' ⊆ S → potential d S ≤ potential d S') ∧
    (if S.Nonempty then (1 : ℝ) else 0) * (killProb d S) ^ beta ≤
      (d : ℝ) ^ (beta - 1) *
        (3 * (∫ C, potential d (survivors S C) - potential d S ∂(ν 3)) +
          d * (u : ℝ) ^ (-3 : ℝ)) := by
  refine ⟨potential_bounds d S, (fun S' h => potential_antitone d h), ?_⟩
  have hν : ν 3 = uniformClauseMeasure u 3 := hclause 3 (Or.inr rfl)
  -- Jensen and the one-clause bound apply separately to every successive increment.
  have hsum :
      (∑ j ∈ Finset.range d, (killProb (j + 1) S - killProb j S) ^ beta) ≤
        3 * (∫ C, potential d (survivors S C) - potential d S ∂(ν 3)) +
          d * (u : ℝ) ^ (-3 : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range d,
          (3 * (∫ C, killProb j (survivors S C) - killProb j S ∂(ν 3)) +
            (u : ℝ) ^ (-3 : ℝ)) :=
        Finset.sum_le_sum fun j _ =>
          killProb_increment_rpow_le hu ν hclause νj hreplacement j S
      _ = _ := by
        rw [hν, potential_expected_increment hu]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
  by_cases hS : S.Nonempty
  · simp only [hS, if_true, one_mul]
    have htel : (∑ j ∈ Finset.range d, (killProb (j + 1) S - killProb j S)) =
        killProb d S := by
      rw [Finset.sum_range_sub (fun j => killProb j S)]
      rw [killProb_zero_of_nonempty hu S hS, sub_zero]
    -- The power-sum inequality turns the telescoping increments into q_d^beta.
    have hp := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (Finset.range d) (f := fun j => killProb (j + 1) S - killProb j S)
      (show 1 ≤ beta by norm_num [beta])
      (fun j _ => killProb_increment_nonneg hu j S)
    rw [htel, Finset.card_range] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left hsum
      (Real.rpow_nonneg (Nat.cast_nonneg d) _))
  · simp only [hS, if_false, zero_mul]
    have hz : 0 ≤ ∑ j ∈ Finset.range d,
        (killProb (j + 1) S - killProb j S) ^ beta :=
      Finset.sum_nonneg fun j _ =>
        Real.rpow_nonneg (killProb_increment_nonneg hu j S) _
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hz.trans hsum)


end Papers.OaiLinearVarianceRandom
