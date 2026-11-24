module

public import Papers.HawkesD75660b.Helpers.MeanRecurrence

/-! Closed solution of the reciprocal-mean recurrence. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

-- @node: meanCorrection_normalize
/-- If [i is smaller than n](hyp:hi), [the binomial coefficient choosing i from n times ((i + 1)/(n + 1)) to power i − 1 times ((n − i)/(n + 1)) to power n − i equals n − i times that binomial coefficient times (i + 1) to power i − 1 times (n − i) to power n − i − 1, divided by (n + 1) to power n − 1](goal). -/
lemma meanCorrection_normalize {n i : ℕ} (hi : i < n) :
    (Nat.choose n i : ℝ) * (((i + 1 : ℝ) / (n + 1 : ℝ)) ^ ((i : ℤ) - 1)) *
        (((n : ℝ) - i) / (n + 1 : ℝ)) ^ (n - i) =
      ((n : ℝ) - i) * ((Nat.choose n i : ℝ) *
        ((i + 1 : ℝ) ^ ((i : ℤ) - 1) / (n + 1 : ℝ) ^ ((n : ℤ) - 1)) *
        ((n : ℝ) - i) ^ ((n : ℤ) - i - 1)) := by
  have hb : (n + 1 : ℝ) ≠ 0 := by positivity
  have hc : (n : ℝ) - i ≠ 0 := by
    have : (i : ℝ) < n := by exact_mod_cast hi
    linarith
  have hexp : ((n - i : ℕ) : ℤ) = (n : ℤ) - i := by
    exact_mod_cast Nat.cast_sub (Nat.le_of_lt hi)
  rw [div_zpow, div_pow, ← zpow_natCast ((n : ℝ) - i),
    ← zpow_natCast (n + 1 : ℝ), hexp]
  have hden : (n + 1 : ℝ) ^ ((i : ℤ) - 1) *
      (n + 1 : ℝ) ^ ((n : ℤ) - i) = (n + 1 : ℝ) ^ ((n : ℤ) - 1) := by
    rw [← zpow_add₀ hb]
    congr 1
    ring
  have hnum : ((n : ℝ) - i) ^ ((n : ℤ) - i) =
      ((n : ℝ) - i) * ((n : ℝ) - i) ^ ((n : ℤ) - i - 1) := by
    rw [← zpow_one_add₀ hc]
    congr 1
    ring
  rw [hnum]
  calc
    _ = ((n : ℝ) - i) * ((Nat.choose n i : ℝ) *
        (i + 1 : ℝ) ^ ((i : ℤ) - 1) /
        ((n + 1 : ℝ) ^ ((i : ℤ) - 1) * (n + 1 : ℝ) ^ ((n : ℤ) - i)) *
        ((n : ℝ) - i) ^ ((n : ℤ) - i - 1)) := by ring
    _ = _ := by rw [hden]; ring

-- @env: S2
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (κ : Ω → CountVector n)

-- @node: thm:meanrecursolve1
/-- Suppose [the recurrence index conditions require n to be positive and m to be smaller than n](hyp:hindex), [the random count vector κ has the preference count distribution under P](hyp:hlaw), [both count domain conventions identify nonnegative integer counts with integers at least zero](hyp:hdomain,hzero), and [the solution index convention also requires n to be positive and m to be smaller than n](hyp:hrange). Then [the expected reciprocal of the cumulative count through m + 1 minus m equals (n + 1)/(n − m), less 1/(n − m) times the sum over i from zero through m of the binomial coefficient choosing i from n times ((i + 1)/(n + 1)) to power i − 1 times ((n − i)/(n + 1)) to power n − i](goal). -/
theorem meanRecurrenceSolution (m : ℕ)
    (hindex : meanRecurrenceSolutionIndex n m) (hlaw : meanRecurrenceSolutionLaw P κ)
    (hdomain : naturalCountDomainConvention) (hrange : solutionIndexConvention n m)
    (hzero : zeroCountConvention) :
    (∫ ω, 1 / ((prefixCount (κ ω) (m + 1) : ℝ) - m) ∂P) =
      (n + 1 : ℝ) / ((n : ℝ) - m) -
      (1 / ((n : ℝ) - m)) *
        ∑ i ∈ Finset.range (m + 1), -- @realizes i(correction index from zero through m)
          (Nat.choose n i : ℝ) * (((i + 1 : ℝ) / (n + 1 : ℝ)) ^ ((i : ℤ) - 1)) *
            (((n : ℝ) - i) / (n + 1 : ℝ)) ^ (n - i) := by
  let F : ℕ → ℝ := fun j =>
    ∫ ω, 1 / ((prefixCount (κ ω) j : ℝ) - j + 1) ∂P
  let A : ℕ → ℝ := fun i =>
    (Nat.choose n i : ℝ) * (((i + 1 : ℝ) / (n + 1 : ℝ)) ^ ((i : ℤ) - 1)) *
      (((n : ℝ) - i) / (n + 1 : ℝ)) ^ (n - i)
  have hFzero : F 0 = 1 := by simp [F, prefixCount]
  have hstep (j : ℕ) (hj : j < n) :
      F (j + 1) = (1 + 1 / ((n : ℝ) - j)) * F j -
        (Nat.choose n j : ℝ) *
          ((j + 1 : ℝ) ^ ((j : ℤ) - 1) / (n + 1 : ℝ) ^ ((n : ℤ) - 1)) *
          ((n : ℝ) - j) ^ ((n : ℤ) - j - 1) := by
    have h := meanRecurrence P κ hindex.1 hlaw hdomain hzero j hj
    have hF : F (j + 1) =
        ∫ ω, 1 / ((prefixCount (κ ω) (j + 1) : ℝ) - j) ∂P := by
      dsimp [F]
      congr 1
      funext ω
      congr 1
      push_cast
      ring
    rw [hF]
    exact h
  have htel : ∀ j : ℕ, j ≤ n →
      ((n : ℝ) - j + 1) * F j = (n + 1 : ℝ) - ∑ i ∈ Finset.range j, A i := by
    intro j
    induction j with
    | zero =>
      intro hj
      simp [hFzero]
    | succ j ih =>
      intro hj
      have hjn : j < n := by omega
      have hne : (n : ℝ) - j ≠ 0 := by
        have : (j : ℝ) < n := by exact_mod_cast hjn
        linarith
      have hprev := ih (by omega)
      have hrec := hstep j hjn
      have hterm := meanCorrection_normalize hjn
      change A j = _ at hterm
      rw [Finset.sum_range_succ]
      have hcoef : ((n : ℝ) - j) * (1 + 1 / ((n : ℝ) - j)) =
          (n : ℝ) - j + 1 := by
        field_simp [hne]
      calc
        _ = ((n : ℝ) - j) * F (j + 1) := by push_cast; ring
        _ = ((n : ℝ) - j + 1) * F j - A j := by
          rw [hrec, mul_sub, ← mul_assoc, hcoef, ← hterm]
        _ = _ := by rw [hprev]; ring
  have ht := htel (m + 1) (by have := hrange.2; omega)
  have hne : (n : ℝ) - m ≠ 0 := by
    have : (m : ℝ) < n := by exact_mod_cast hindex.2
    linarith
  have hF : F (m + 1) =
      ∫ ω, 1 / ((prefixCount (κ ω) (m + 1) : ℝ) - m) ∂P := by
    dsimp [F]
    congr 1
    funext ω
    congr 1
    push_cast
    ring
  rw [hF] at ht
  dsimp [A] at ht
  push_cast at ht
  field_simp [hne]
  nlinarith

end Papers.HawkesD75660b
