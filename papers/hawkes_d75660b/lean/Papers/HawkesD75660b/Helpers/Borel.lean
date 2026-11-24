module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Analysis.SpecificLimits.Normed
public import Papers.HawkesD75660b.Basic

/-! Normalization and elementary properties of the Borel law. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Papers.HawkesD75660b

-- @env: S3
variable (ρ : ℝ≥0)

-- @node: borelMass_nonneg
/-- For any nonnegative parameter ρ and nonnegative integer j, [the Borel mass at j
is nonnegative](goal). -/
lemma borelMass_nonneg (j : ℕ) : 0 ≤ borelMass ρ j := by
  unfold borelMass
  split_ifs <;> positivity

-- @node: borel_geometric_ratio_lt_one
/-- If [the nonnegative parameter ρ is less than one](hyp:hρ), then
[the geometric ratio ρ exp(1 − ρ) is less than one](goal). -/
lemma borel_geometric_ratio_lt_one (hρ : subcritical ρ) :
    (ρ : ℝ) * Real.exp (1 - (ρ : ℝ)) < 1 := by
  have hr : (ρ : ℝ) < 1 := by exact_mod_cast hρ
  have he := Real.add_one_lt_exp (show (ρ : ℝ) - 1 ≠ 0 by linarith)
  have hm := mul_lt_mul_of_pos_right he (Real.exp_pos (1 - (ρ : ℝ)))
  simpa only [sub_add_cancel, ← Real.exp_add, sub_add_sub_cancel, sub_self, Real.exp_zero] using hm

-- @node: borelMass_succ_geometric_bound
/-- For any nonnegative parameter ρ and nonnegative integer j, [the Borel mass at
j + 1 is at most exp(1 − ρ) times the j-th power of ρ exp(1 − ρ)](goal). -/
lemma borelMass_succ_geometric_bound (j : ℕ) :
    borelMass ρ (j + 1) ≤ Real.exp (1 - (ρ : ℝ)) *
      ((ρ : ℝ) * Real.exp (1 - (ρ : ℝ))) ^ j := by
  have hfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by positivity
  have hfac_le : (Nat.factorial j : ℝ) ≤ Nat.factorial (j + 1) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ j)
  have hb : ((j + 1 : ℕ) : ℝ) ^ j / Nat.factorial (j + 1) ≤
      Real.exp (j + 1 : ℕ) :=
    (div_le_div_of_nonneg_left (by positivity) hfac hfac_le).trans
      (Real.pow_div_factorial_le_exp _ (by positivity) j)
  calc
    borelMass ρ (j + 1) =
        (Real.exp (-(ρ : ℝ) * (j + 1)) * (ρ : ℝ) ^ j) *
          (((j + 1 : ℕ) : ℝ) ^ j / Nat.factorial (j + 1)) := by
      simp only [borelMass, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_pow]
      ring
    _ ≤ (Real.exp (-(ρ : ℝ) * (j + 1)) * (ρ : ℝ) ^ j) *
        Real.exp (j + 1 : ℕ) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Real.exp (1 - (ρ : ℝ)) *
        ((ρ : ℝ) * Real.exp (1 - (ρ : ℝ))) ^ j := by
      rw [mul_pow, ← Real.exp_nat_mul]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [mul_assoc, mul_comm ((ρ : ℝ) ^ j), ← mul_assoc, ← Real.exp_add]
      rw [mul_left_comm (Real.exp (1 - (ρ : ℝ))), ← Real.exp_add]
      rw [mul_comm (Real.exp _)]
      congr 2 <;> ring

-- @node: borelMass_polynomial_summable
/-- If [the nonnegative parameter ρ is less than one](hyp:hρ), then, for every
nonnegative integer k, [the series of Borel masses at j multiplied by j to the
power k converges](goal). -/
lemma borelMass_polynomial_summable (hρ : subcritical ρ) (k : ℕ) :
    Summable (fun j => borelMass ρ j * (j : ℝ) ^ k) := by
  let q : ℝ := (ρ : ℝ) * Real.exp (1 - (ρ : ℝ))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact borel_geometric_ratio_lt_one ρ hρ
  have hs : Summable (fun j : ℕ => (j + 1 : ℝ) ^ k * q ^ j) := by
    have ht := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hq).add
      (summable_geometric_of_norm_lt_one hq)
    apply Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity) (pow_nonneg hq0 _))
      (fun j => mul_le_mul_of_nonneg_right
        (add_pow_le (Nat.cast_nonneg j) (by positivity : (0 : ℝ) ≤ 1) k) (pow_nonneg hq0 _))
    simpa only [one_pow, add_mul, mul_assoc, one_mul] using ht.mul_left ((2 : ℝ) ^ (k - 1))
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (borelMass_nonneg ρ _) (by positivity))
    (fun j => mul_le_mul_of_nonneg_right (borelMass_succ_geometric_bound ρ j) (by positivity))
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm] using
    hs.mul_left (Real.exp (1 - (ρ : ℝ)))

-- @node: borelMass_summable
/-- If [the nonnegative parameter ρ is less than one](hyp:hρ), then [the series
of Borel masses over all nonnegative integers converges](goal). -/
lemma borelMass_summable (hρ : subcritical ρ) : Summable (borelMass ρ) := by
  simpa only [pow_zero, mul_one] using borelMass_polynomial_summable ρ hρ 0

-- @node: borelMeasure_singleton
/-- For any nonnegative parameter ρ and nonnegative integer j, [the real-valued
measure of the singleton containing j under the Borel measure equals the Borel
mass at j](goal). -/
lemma borelMeasure_singleton (j : ℕ) :
    (borelMeasure ρ).real {j} = borelMass ρ j := by
  unfold Measure.real borelMeasure
  rw [Measure.sum_smul_dirac_singleton, ENNReal.toReal_ofReal (borelMass_nonneg ρ j)]

-- @node: borelMeasure_positive_support
/-- If [the nonnegative parameter ρ is less than one](hyp:hρ), then [a count is
strictly positive almost everywhere under the Borel measure with parameter ρ](goal). -/
lemma borelMeasure_positive_support (hρ : subcritical ρ) :
    ∀ᵐ j ∂borelMeasure ρ, 0 < j := by
  rw [ae_iff]
  have hset : {j : ℕ | ¬0 < j} = {0} := by ext j; simp
  rw [hset]
  unfold borelMeasure
  rw [Measure.sum_smul_dirac_singleton]
  simp [borelMass]

-- @node: borelMeasure_zero_parameter
/-- [The Borel measure with parameter zero is the point mass at one](goal). -/
lemma borelMeasure_zero_parameter : borelMeasure 0 = Measure.dirac 1 := by
  have hmass (j : ℕ) : borelMass 0 j = if j = 1 then 1 else 0 := by
    by_cases h0 : j = 0
    · subst j; simp [borelMass]
    by_cases h1 : j = 1
    · subst j; simp [borelMass]
    have hexp : j - 1 ≠ 0 := by omega
    simp [borelMass, h0, h1, zero_pow hexp]
  apply Measure.ext_of_singleton
  intro j
  unfold borelMeasure
  rw [Measure.sum_smul_dirac_singleton, hmass]
  by_cases hj : j = 1
  · subst j; simp
  · simp [hj, Ne.symm hj]

end Papers.HawkesD75660b
