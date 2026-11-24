module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Papers.HawkesD75660b.Helpers.Borel

/-! Finite Borel moments before signed series and integrals are exchanged. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Papers.HawkesD75660b

variable (ρ : ℝ≥0) (hρ : subcritical ρ)

-- @node: harmonicNumber_nonneg
/-- For every nonnegative integer j, [the j-th harmonic number is nonnegative](goal). -/
lemma harmonicNumber_nonneg (j : ℕ) : 0 ≤ harmonicNumber j := by
  unfold harmonicNumber harmonic
  positivity

-- @node: harmonicNumber_le_nat
/-- For every nonnegative integer j, [the j-th harmonic number is at most j](goal). -/
lemma harmonicNumber_le_nat (j : ℕ) : harmonicNumber j ≤ j := by
  unfold harmonicNumber harmonic
  push_cast
  calc
    (∑ i ∈ Finset.range j, ((i : ℝ) + 1)⁻¹) ≤
        ∑ i ∈ Finset.range j, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply inv_le_one_of_one_le₀
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    _ = j := by simp

include hρ

-- @node: borel_second_moment_summable
/-- If the nonnegative parameter ρ is less than one, then [the series
of Borel masses at j multiplied by j squared converges](goal). -/
lemma borel_second_moment_summable :
    Summable (fun j => borelMass ρ j * (j : ℝ)^2) := by
  exact borelMass_polynomial_summable ρ hρ 2

-- @node: borel_first_moment_integrable
/-- If the nonnegative parameter ρ is less than one, then [the count
has a finite absolute first moment under the Borel measure with parameter ρ](goal). -/
lemma borel_first_moment_integrable :
    Integrable (fun j : ℕ => (j : ℝ)) (borelMeasure ρ) := by
  unfold borelMeasure
  apply integrable_sum_dirac (fun j => ENNReal.ofReal_ne_top)
  simp only [ENNReal.toReal_ofReal (borelMass_nonneg ρ _), Real.norm_natCast]
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (borelMass_nonneg ρ j) (by positivity))
    (fun j => ?_) (borel_second_moment_summable ρ hρ)
  apply mul_le_mul_of_nonneg_left _ (borelMass_nonneg ρ j)
  have hj : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
    cases j with
    | zero => norm_num
    | succ j => have : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
                nlinarith
  exact hj

-- @node: borel_harmonic_moment_summable
/-- If the nonnegative parameter ρ is less than one, then [the series
of Borel masses at j multiplied by j and by the j-th harmonic number converges](goal). -/
lemma borel_harmonic_moment_summable :
    Summable (fun j => borelMass ρ j * (j : ℝ) * harmonicNumber j) := by
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (mul_nonneg (borelMass_nonneg ρ j) (by positivity))
      (harmonicNumber_nonneg j)) (fun j => ?_) (borel_second_moment_summable ρ hρ)
  calc
    borelMass ρ j * (j : ℝ) * harmonicNumber j ≤ borelMass ρ j * j * j :=
      mul_le_mul_of_nonneg_left (harmonicNumber_le_nat j)
        (mul_nonneg (borelMass_nonneg ρ j) (by positivity))
    _ = borelMass ρ j * (j : ℝ)^2 := by ring

-- @node: borel_harmonic_moment_integrable
/-- If the nonnegative parameter ρ is less than one, then [the count
multiplied by its harmonic number is integrable under the Borel measure with
parameter ρ](goal). -/
lemma borel_harmonic_moment_integrable :
    Integrable (fun j : ℕ => (j : ℝ) * harmonicNumber j) (borelMeasure ρ) := by
  unfold borelMeasure
  apply integrable_sum_dirac (fun j => ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (borelMass_nonneg ρ _),
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (harmonicNumber_nonneg _)),
    ← mul_assoc] using borel_harmonic_moment_summable ρ hρ

-- @node: auxiliary_harmonic_integrable
/-- If the nonnegative parameter ρ is less than one and [the
nonnegative integer-valued random variable B has the Borel law with parameter ρ
under the measure Q](hyp:hB), then [B multiplied by its harmonic number is
integrable under Q](goal). -/
lemma auxiliary_harmonic_integrable {ΩB : Type*} [MeasurableSpace ΩB]
    (Q : Measure ΩB) (B : ΩB → ℕ) (hB : auxiliaryBorelLaw ρ Q B) :
    Integrable (fun ω => (B ω : ℝ) * harmonicNumber (B ω)) Q := by
  have hi := borel_harmonic_moment_integrable ρ hρ
  rw [← hB.map_eq] at hi
  exact hi.comp_aemeasurable hB.aemeasurable

end Papers.HawkesD75660b
