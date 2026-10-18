module
public import Papers.TbsNeuralCausalPi.Setup.Networks
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic
/-! # Polynomial comparisons for positive-temperature generator mixtures

On fixed exogenous inputs, the exponential noise factors are constants. Treating
the transformed mixture weights as extra parameters clears the common positive
denominator. A grid comparison then has polynomial degree at most one more than
the component outputs. Zero mixture weights are allowed throughout.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationMixtureAmplitude
/-- For [mixture weights p](hyp:p), [temperature tau](hyp:tau), and
[component i](hyp:i), the [transformed mixture amplitude](goal) is zero
when that component's weight is zero, and otherwise is the exponential of
its log weight divided by the temperature. -/
def simulationMixtureAmplitude {n : ℕ} (p : Fin n → ℝ) (tau : ℝ) (i : Fin n) : ℝ :=
  if p i = 0 then 0 else Real.exp (Real.log (p i) / tau)

-- @node: simulationMixtureAmplitude_nonneg
/-- [Every transformed mixture amplitude is nonnegative, for any real
weights and temperature](goal). -/
lemma simulationMixtureAmplitude_nonneg {n : ℕ} (p : Fin n → ℝ) (tau : ℝ)
    (i : Fin n) : 0 ≤ simulationMixtureAmplitude p tau i := by
  unfold simulationMixtureAmplitude
  split_ifs <;> positivity

-- @node: simulationMixture_exponential_factorization
/-- [The exponential of a component's log weight plus its noise, divided
by temperature, with zero assigned to a zero weight, equals its transformed
mixture amplitude times the exponential of noise divided by temperature](goal). -/
lemma simulationMixture_exponential_factorization {n : ℕ}
    (p : Fin n → ℝ) (tau : ℝ) (G : Fin n → ℝ) (i : Fin n) :
    (if p i = 0 then 0 else Real.exp ((Real.log (p i) + G i) / tau)) =
      simulationMixtureAmplitude p tau i * Real.exp (G i / tau) := by
  by_cases hi : p i = 0
  · simp [simulationMixtureAmplitude, hi]
  · simp [simulationMixtureAmplitude, hi, add_div, Real.exp_add]

-- @node: simulationMixture_denominator_pos
/-- If [the mixture weights sum to one](hyp:hsum), then [the sum of the
transformed amplitudes times their exponential noise factors is strictly
positive](goal). -/
lemma simulationMixture_denominator_pos {n : ℕ}
    (p : Fin n → ℝ) (hsum : ∑ i, p i = 1) (tau : ℝ) (G : Fin n → ℝ) :
    0 < ∑ i, simulationMixtureAmplitude p tau i * Real.exp (G i / tau) := by
  have hex : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∑ i, p i = 0 := Finset.sum_eq_zero (fun i _ => h i)
    linarith
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos' (fun j _ =>
    mul_nonneg (simulationMixtureAmplitude_nonneg p tau j) (Real.exp_pos _).le)
  exact ⟨i, Finset.mem_univ _, by
    simp only [simulationMixtureAmplitude, if_neg hi]
    positivity⟩

-- @node: gumbelSoftmaxMix_coordinate_quotient
/-- At [a nonzero temperature](hyp:htau), [each coordinate of the
Gumbel--softmax mixture equals the sum of the component coordinates weighted
by transformed amplitudes and exponential noise factors, divided by the sum
of those same weights](goal). -/
lemma gumbelSoftmaxMix_coordinate_quotient {n d : ℕ}
    (V : Fin n → L1Vec d) (p : Fin n → ℝ) {tau : ℝ} (htau : tau ≠ 0)
    (G : Fin n → ℝ) (j : Fin d) :
    (gumbelSoftmaxMix V p tau G).ofLp j =
      (∑ i, (V i).ofLp j *
        (simulationMixtureAmplitude p tau i * Real.exp (G i / tau))) /
      (∑ i, simulationMixtureAmplitude p tau i * Real.exp (G i / tau)) := by
  simp only [gumbelSoftmaxMix, if_neg htau, softmaxWeights, WithLp.ofLp_toLp]
  simp_rw [simulationMixture_exponential_factorization, ← mul_div_assoc]
  exact (Finset.sum_div _ _ _).symm

-- @node: simulationMixtureComparison
/-- Given [the parameter variable representing each component's transformed
weight](hyp:weightVar), [fixed component noise factors R](hyp:R),
[component output polynomials V](hyp:V), and [a comparison
threshold](hyp:threshold), the [mixture comparison polynomial](goal) sums,
over components, the noise factor times the weight variable times the
component output polynomial minus the threshold. -/
def simulationMixtureComparison {σ : Type*} {n : ℕ}
    (weightVar : Fin n → σ) (R : Fin n → ℝ)
    (V : Fin n → MvPolynomial σ ℝ) (threshold : ℝ) : MvPolynomial σ ℝ :=
  ∑ i, MvPolynomial.C (R i) * MvPolynomial.X (weightVar i) *
    (V i - MvPolynomial.C threshold)

-- @node: simulationMixtureComparison_degree
/-- If [each component output polynomial has total degree at most
d](hyp:hV), then [the mixture comparison polynomial has total degree at
most d plus one](goal). -/
lemma simulationMixtureComparison_degree {σ : Type*} {n d : ℕ}
    (weightVar : Fin n → σ) (R : Fin n → ℝ)
    (V : Fin n → MvPolynomial σ ℝ) (threshold : ℝ)
    (hV : ∀ i, (V i).totalDegree ≤ d) :
    (simulationMixtureComparison weightVar R V threshold).totalDegree ≤ d + 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  have hw := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (R i) : MvPolynomial σ ℝ) (MvPolynomial.X (weightVar i))
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] at hw
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by have hv := (MvPolynomial.totalDegree_sub_C_le (V i) threshold).trans (hV i)
        omega)

-- @node: simulationMixtureComparison_eval
/-- [Evaluating the mixture comparison polynomial at a parameter assignment
gives the sum of evaluated component outputs times their assigned weight
variables and fixed noise factors, minus the threshold times the sum of
those weight variables times noise factors](goal). -/
lemma simulationMixtureComparison_eval {σ : Type*} {n : ℕ}
    (weightVar : Fin n → σ) (R : Fin n → ℝ)
    (V : Fin n → MvPolynomial σ ℝ) (threshold : ℝ) (x : σ → ℝ) :
    MvPolynomial.eval x (simulationMixtureComparison weightVar R V threshold) =
      (∑ i, MvPolynomial.eval x (V i) * (x (weightVar i) * R i)) -
        threshold * ∑ i, x (weightVar i) * R i := by
  simp only [simulationMixtureComparison, map_sum, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

-- @node: gumbelSoftmaxMix_le_iff_polynomial
/-- If [the mixture weights sum to one](hyp:hsum), [the temperature is
nonzero](hyp:htau), [the assigned weight variables equal the transformed
mixture amplitudes](hyp:hx), and [the evaluated output polynomials equal the
chosen component coordinates](hyp:hV), then [the mixture coordinate is at
most the threshold exactly when the mixture comparison polynomial, using
the exponential noise factors, evaluates to a nonpositive number](goal). -/
lemma gumbelSoftmaxMix_le_iff_polynomial {σ : Type*} {n d : ℕ}
    (weightVar : Fin n → σ) (Vpoly : Fin n → MvPolynomial σ ℝ)
    (x : σ → ℝ) (V : Fin n → L1Vec d) (j : Fin d)
    (p : Fin n → ℝ) (hsum : ∑ i, p i = 1) {tau : ℝ} (htau : tau ≠ 0)
    (G : Fin n → ℝ) (threshold : ℝ)
    (hx : ∀ i, x (weightVar i) = simulationMixtureAmplitude p tau i)
    (hV : ∀ i, MvPolynomial.eval x (Vpoly i) = (V i).ofLp j) :
    (gumbelSoftmaxMix V p tau G).ofLp j ≤ threshold ↔
      MvPolynomial.eval x (simulationMixtureComparison weightVar
        (fun i => Real.exp (G i / tau)) Vpoly threshold) ≤ 0 := by
  rw [gumbelSoftmaxMix_coordinate_quotient V p htau G j,
    div_le_iff₀ (simulationMixture_denominator_pos p hsum tau G),
    simulationMixtureComparison_eval]
  simp_rw [hx, hV]
  exact sub_nonpos.symm

-- @node: gumbelSoftmaxMix_lt_iff_polynomial
/-- If [the mixture weights sum to one](hyp:hsum), [the temperature is
nonzero](hyp:htau), [the assigned weight variables equal the transformed
mixture amplitudes](hyp:hx), and [the evaluated output polynomials equal the
chosen component coordinates](hyp:hV), then [the mixture coordinate is
strictly below the threshold exactly when the mixture comparison polynomial,
using the exponential noise factors, evaluates to a negative number](goal). -/
lemma gumbelSoftmaxMix_lt_iff_polynomial {σ : Type*} {n d : ℕ}
    (weightVar : Fin n → σ) (Vpoly : Fin n → MvPolynomial σ ℝ)
    (x : σ → ℝ) (V : Fin n → L1Vec d) (j : Fin d)
    (p : Fin n → ℝ) (hsum : ∑ i, p i = 1) {tau : ℝ} (htau : tau ≠ 0)
    (G : Fin n → ℝ) (threshold : ℝ)
    (hx : ∀ i, x (weightVar i) = simulationMixtureAmplitude p tau i)
    (hV : ∀ i, MvPolynomial.eval x (Vpoly i) = (V i).ofLp j) :
    (gumbelSoftmaxMix V p tau G).ofLp j < threshold ↔
      MvPolynomial.eval x (simulationMixtureComparison weightVar
        (fun i => Real.exp (G i / tau)) Vpoly threshold) < 0 := by
  rw [gumbelSoftmaxMix_coordinate_quotient V p htau G j,
    div_lt_iff₀ (simulationMixture_denominator_pos p hsum tau G),
    simulationMixtureComparison_eval]
  simp_rw [hx, hV]
  exact sub_neg.symm

-- @node: truncated_gumbelSoftmaxMix_le_iff_polynomial
/-- If [the mixture weights sum to one](hyp:hsum), [the temperature is
nonzero](hyp:htau), [the assigned weight variables equal the transformed
mixture amplitudes](hyp:hx), and [the evaluated output polynomials equal the
chosen component coordinates](hyp:hV), then [the mixture coordinate capped
above at K and then floored at minus K is at most the threshold exactly when
the threshold is at least minus K and either it is at least K or the mixture
comparison polynomial with exponential noise factors evaluates to a
nonpositive number](goal). -/
lemma truncated_gumbelSoftmaxMix_le_iff_polynomial {σ : Type*} {n d : ℕ}
    (weightVar : Fin n → σ) (Vpoly : Fin n → MvPolynomial σ ℝ)
    (x : σ → ℝ) (V : Fin n → L1Vec d) (j : Fin d)
    (p : Fin n → ℝ) (hsum : ∑ i, p i = 1) {tau : ℝ} (htau : tau ≠ 0)
    (G : Fin n → ℝ) (K threshold : ℝ)
    (hx : ∀ i, x (weightVar i) = simulationMixtureAmplitude p tau i)
    (hV : ∀ i, MvPolynomial.eval x (Vpoly i) = (V i).ofLp j) :
    (truncK K (gumbelSoftmaxMix V p tau G)).ofLp j ≤ threshold ↔
      -K ≤ threshold ∧ (K ≤ threshold ∨
        MvPolynomial.eval x (simulationMixtureComparison weightVar
          (fun i => Real.exp (G i / tau)) Vpoly threshold) ≤ 0) := by
  change max (-K) (min ((gumbelSoftmaxMix V p tau G).ofLp j) K) ≤ threshold ↔ _
  rw [max_le_iff, min_le_iff,
    gumbelSoftmaxMix_le_iff_polynomial weightVar Vpoly x V j p hsum htau G threshold hx hV]
  tauto

-- @node: truncated_gumbelSoftmaxMix_lt_iff_polynomial
/-- If [the mixture weights sum to one](hyp:hsum), [the temperature is
nonzero](hyp:htau), [the assigned weight variables equal the transformed
mixture amplitudes](hyp:hx), and [the evaluated output polynomials equal the
chosen component coordinates](hyp:hV), then [the mixture coordinate capped
above at K and then floored at minus K is strictly below the threshold
exactly when the threshold is strictly above minus K and either it is
strictly above K or the mixture comparison polynomial with exponential
noise factors evaluates to a negative number](goal). -/
lemma truncated_gumbelSoftmaxMix_lt_iff_polynomial {σ : Type*} {n d : ℕ}
    (weightVar : Fin n → σ) (Vpoly : Fin n → MvPolynomial σ ℝ)
    (x : σ → ℝ) (V : Fin n → L1Vec d) (j : Fin d)
    (p : Fin n → ℝ) (hsum : ∑ i, p i = 1) {tau : ℝ} (htau : tau ≠ 0)
    (G : Fin n → ℝ) (K threshold : ℝ)
    (hx : ∀ i, x (weightVar i) = simulationMixtureAmplitude p tau i)
    (hV : ∀ i, MvPolynomial.eval x (Vpoly i) = (V i).ofLp j) :
    (truncK K (gumbelSoftmaxMix V p tau G)).ofLp j < threshold ↔
      -K < threshold ∧ (K < threshold ∨
        MvPolynomial.eval x (simulationMixtureComparison weightVar
          (fun i => Real.exp (G i / tau)) Vpoly threshold) < 0) := by
  change max (-K) (min ((gumbelSoftmaxMix V p tau G).ofLp j) K) < threshold ↔ _
  rw [max_lt_iff, min_lt_iff,
    gumbelSoftmaxMix_lt_iff_polynomial weightVar Vpoly x V j p hsum htau G threshold hx hV]
  tauto

end
end Papers.TbsNeuralCausalPi
