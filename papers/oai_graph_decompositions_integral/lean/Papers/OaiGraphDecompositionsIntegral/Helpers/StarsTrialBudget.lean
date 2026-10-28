module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsBinomial
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Field.GeomSum

/-! # Summing the trial costs in the star embedding

The two binomial regimes give a uniform bound for the sum of the mean
waiting-time budgets. Markov's inequality then turns the resulting trial
expectation into a probability of finishing within the original center bin.
These lemmas do not assume an embedding process exists: its construction
and the counting inequality remain separate proof obligations.
-/

public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

/-- If [every size in the finite set S is at least one](hyp:hS), [the sum of
one hundredth raised to those sizes is at most one ninety-ninth](goal). -/
-- @node: star_positive_geometric_sum
lemma star_positive_geometric_sum (S : Finset ℕ) (hS : ∀ ell ∈ S, 1 ≤ ell) :
    (∑ ell ∈ S, (1 / 100 : ℝ) ^ ell) ≤ 1 / 99 := by
  let N := S.sup id + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hsub : S ⊆ Finset.Ico 1 N := by
    intro ell hell
    have hu : ell ≤ S.sup id := Finset.le_sup (f := id) hell
    exact Finset.mem_Ico.mpr ⟨hS ell hell, by dsimp [N]; omega⟩
  calc
    _ ≤ ∑ ell ∈ Finset.Ico 1 N, (1 / 100 : ℝ) ^ ell :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (((1 / 100 : ℝ) ^ N) - 1 / 100) / (1 / 100 - 1) := by
      rw [geom_sum_Ico (by norm_num : (1 / 100 : ℝ) ≠ 1) hN, pow_one]
    _ ≤ 1 / 99 := by
      have hpow : 0 ≤ (1 / 100 : ℝ) ^ N := by positivity
      norm_num only [show (1 / 100 - 1 : ℝ) = -99 / 100 by norm_num] at *
      linarith

/-- Suppose [n is positive](hyp:hn), [ell is at least one](hyp:hell),
[q is nonnegative](hyp:hq), [A times q is less than one half](hyp:hp),
[ell is at most n divided by one hundred](hyp:hsize), and
[ell factorial divided by n raised to ell plus one, multiplied by m divided
by twice the exponential of one, is at most q raised to ell](hyp:hcount).
Then [m divided by the star trial success probability at parameter A times q
is at most six times m plus twice the exponential of one times n times
one hundredth raised to ell](goal). -/
-- @node: star_trial_cost_le
lemma star_trial_cost_le (n ell m : ℕ) (q : ℝ)
    (hn : 0 < n) (hell : 1 ≤ ell) (hq : 0 ≤ q)
    (hp : starConstA * q < 1 / 2)
    (hsize : (ell : ℝ) ≤ (n : ℝ) / 100)
    (hcount : (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
      ((m : ℝ) / (2 * Real.exp 1)) ≤ q ^ ell) :
    (m : ℝ) / starTrialSuccess n (starConstA * q) ell ≤
      6 * m + (2 * Real.exp 1 * n) * (1 / 100 : ℝ) ^ ell := by
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, zero_div, mul_zero, zero_add]
    positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hA : 0 < starConstA := by unfold starConstA; positivity
  by_cases hmean : 2 * (ell : ℝ) ≤ starBinomialMean n (starConstA * q)
  · have hu := star_trial_success_large_mean n ell (starConstA * q)
      (mul_nonneg hA.le hq) (by linarith) hell hmean
    have hupos : 0 < starTrialSuccess n (starConstA * q) ell := by linarith
    have hcost : (m : ℝ) / starTrialSuccess n (starConstA * q) ell ≤ 6 * m := by
      apply (div_le_iff₀ hupos).mpr
      nlinarith
    exact hcost.trans (le_add_of_nonneg_right (by positivity))
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsmall := star_trial_success_small_mean_of_count n ell m q hn hq hp
      hsize (lt_of_not_ge hmean) hcount
    have hden : 0 < 2 * Real.exp 1 * (n : ℝ) := by positivity
    have hpow : 0 < (100 : ℝ) ^ ell := by positivity
    have hupos : 0 < starTrialSuccess n (starConstA * q) ell :=
      lt_of_lt_of_le (by positivity) hsmall
    have hmul := (div_le_iff₀ hden).mp hsmall
    have hcost : (m : ℝ) / starTrialSuccess n (starConstA * q) ell ≤
        (2 * Real.exp 1 * n) / (100 : ℝ) ^ ell := by
      apply (div_le_iff₀ hupos).mpr
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hpow).mpr
      nlinarith
    have heq : (2 * Real.exp 1 * (n : ℝ)) / (100 : ℝ) ^ ell =
        (2 * Real.exp 1 * n) * (1 / 100 : ℝ) ^ ell := by rw [div_pow]; ring
    rw [heq] at hcost
    exact hcost.trans (le_add_of_nonneg_left (by positivity))

/-- Suppose [n is positive](hyp:hn), [q is nonnegative](hyp:hq),
[A times q is less than one half](hyp:hp), and every size ell in S
[is at least one](hyp:hell), [is at most n divided by one hundred](hyp:hsize),
and [satisfies the counting bound: ell factorial divided by n raised to ell
plus one, times its multiplicity divided by twice the exponential of one,
is at most q raised to ell](hyp:hcount). If [the total multiplicity is at most
n divided by two hundred](hyp:hcomponents), [the sum of multiplicities divided
by their star trial success probabilities at parameter A times q is at most
n times the sum of three hundredths and twice the exponential of one divided
by ninety-nine](goal). -/
-- @node: star_total_trial_budget_le
lemma star_total_trial_budget_le (n : ℕ) (S : Finset ℕ) (m : ℕ → ℕ) (q : ℝ)
    (hn : 0 < n) (hq : 0 ≤ q) (hp : starConstA * q < 1 / 2)
    (hell : ∀ ell ∈ S, 1 ≤ ell)
    (hsize : ∀ ell ∈ S, (ell : ℝ) ≤ (n : ℝ) / 100)
    (hcount : ∀ ell ∈ S, (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
      ((m ell : ℝ) / (2 * Real.exp 1)) ≤ q ^ ell)
    (hcomponents : (∑ ell ∈ S, (m ell : ℝ)) ≤ (n : ℝ) / 200) :
    (∑ ell ∈ S, (m ell : ℝ) / starTrialSuccess n (starConstA * q) ell) ≤
      (3 / 100 + 2 * Real.exp 1 / 99) * n := by
  calc
    _ ≤ ∑ ell ∈ S, (6 * (m ell : ℝ) +
        (2 * Real.exp 1 * n) * (1 / 100 : ℝ) ^ ell) := by
      apply Finset.sum_le_sum
      intro ell hmem
      exact star_trial_cost_le n ell (m ell) q hn (hell ell hmem) hq hp
        (hsize ell hmem) (hcount ell hmem)
    _ = 6 * (∑ ell ∈ S, (m ell : ℝ)) +
        (2 * Real.exp 1 * n) * (∑ ell ∈ S, (1 / 100 : ℝ) ^ ell) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 6 * ((n : ℝ) / 200) + (2 * Real.exp 1 * n) * (1 / 99) := by
      gcongr
      exact star_positive_geometric_sum S hell
    _ = _ := by ring

/-- [Three hundredths plus twice the exponential of one divided by ninety-nine
is strictly less than one eighth](goal). -/
-- @node: star_trial_budget_coefficient_lt
lemma star_trial_budget_coefficient_lt :
    (3 / 100 + 2 * Real.exp 1 / 99 : ℝ) < 1 / 8 := by
  have he := Real.exp_one_lt_three
  linarith

/-- Suppose [n is positive](hyp:hn), [q is nonnegative](hyp:hq),
[A times q is less than one half](hyp:hp), and every size ell in S
[is at least one](hyp:hell), [is at most n divided by one hundred](hyp:hsize),
and [has ell factorial divided by n raised to ell plus one, times its
multiplicity divided by twice the exponential of one, at most q raised to ell](hyp:hcount).
If [the total multiplicity is at most n divided by two hundred](hyp:hcomponents)
and [the expected trial count is at most the sum of multiplicities divided by
their star trial success probabilities at parameter A times q](hyp:hwaiting),
[the expected trial count is strictly less than n divided by eight](goal). -/
-- @node: star_expected_trials_lt
lemma star_expected_trials_lt {Ω : Type} [Fintype Ω] (D : FiniteDesign Ω)
    (T : Ω → ℕ) (n : ℕ) (S : Finset ℕ) (m : ℕ → ℕ) (q : ℝ)
    (hn : 0 < n) (hq : 0 ≤ q) (hp : starConstA * q < 1 / 2)
    (hell : ∀ ell ∈ S, 1 ≤ ell)
    (hsize : ∀ ell ∈ S, (ell : ℝ) ≤ (n : ℝ) / 100)
    (hcount : ∀ ell ∈ S, (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
      ((m ell : ℝ) / (2 * Real.exp 1)) ≤ q ^ ell)
    (hcomponents : (∑ ell ∈ S, (m ell : ℝ)) ≤ (n : ℝ) / 200)
    (hwaiting : D.E (fun z => (T z : ℝ)) ≤
      ∑ ell ∈ S, (m ell : ℝ) / starTrialSuccess n (starConstA * q) ell) :
    D.E (fun z => (T z : ℝ)) < (n : ℝ) / 8 := by
  have hbudget := star_total_trial_budget_le n S m q hn hq hp hell hsize hcount hcomponents
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (3 / 100 + 2 * Real.exp 1 / 99) * n := hwaiting.trans hbudget
    _ < (1 / 8 : ℝ) * n := mul_lt_mul_of_pos_right star_trial_budget_coefficient_lt hnpos
    _ = _ := by ring

/-- If [n is positive](hyp:hn) and [the expected natural-valued trial count T
under the finite probability design D is at most n divided by eight](hyp:hET),
[the probability that T is at most the integer part of n divided by two is
at least one half](goal). -/
-- @node: star_finish_probability_of_expected_trials
lemma star_finish_probability_of_expected_trials {Ω : Type} [Fintype Ω]
    (D : FiniteDesign Ω) (T : Ω → ℕ) (n : ℕ) (hn : 0 < n)
    (hET : D.E (fun z => (T z : ℝ)) ≤ (n : ℝ) / 8) :
    (1 / 2 : ℝ) ≤ D.Pr (fun z => T z ≤ n / 2) := by
  classical
  let c : ℝ := (n / 2 + 1 : ℕ)
  let A := fun z => T z ≤ n / 2
  have hc : (n : ℝ) / 4 ≤ c := by
    have hnat : n ≤ 2 * (n / 2 + 1) := by omega
    have hr : (n : ℝ) ≤ 2 * (n / 2 + 1 : ℕ) := by exact_mod_cast hnat
    dsimp [c]
    linarith [Nat.cast_nonneg (n / 2 + 1) (α := ℝ)]
  have hmarkov : c * D.Pr (fun z => ¬ A z) ≤ D.E (fun z => (T z : ℝ)) := by
    unfold FiniteDesign.Pr
    rw [← D.E_const_mul]
    apply Finset.sum_le_sum
    intro z _
    apply mul_le_mul_of_nonneg_left _ (D.p_nonneg z)
    by_cases hz : A z
    · simp [FiniteDesign.ind, hz]
    · have ht : n / 2 + 1 ≤ T z := by dsimp [A] at hz; omega
      simpa [FiniteDesign.ind, hz, c] using (show (n / 2 + 1 : ℕ) ≤ (T z : ℝ) by exact_mod_cast ht)
  have hsplit : D.Pr A + D.Pr (fun z => ¬ A z) = 1 := by
    unfold FiniteDesign.Pr
    rw [← D.E_add]
    calc
      _ = D.E (fun _ => (1 : ℝ)) := D.E_congr (fun z => by
        by_cases hz : A z <;> simp [FiniteDesign.ind, hz])
      _ = 1 := D.E_const 1
  have hprob := D.Pr_nonneg (fun z => ¬ A z)
  have hmul := mul_le_mul_of_nonneg_right hc hprob
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  change (1 / 2 : ℝ) ≤ D.Pr A
  nlinarith

end Papers.OaiGraphDecompositionsIntegral
