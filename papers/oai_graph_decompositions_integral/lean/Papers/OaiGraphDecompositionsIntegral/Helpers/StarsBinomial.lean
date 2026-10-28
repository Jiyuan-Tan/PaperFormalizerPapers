module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsQuantities
public import Toolkit.Foundations.Probability.BiasedCube
public import Causalean.Experimentation.DesignBased.ProductVariance
public import Causalean.Mathlib.Probability.BernoulliMeasure
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Binomial trial estimates for the star embedding

The count is the actual number of true coordinates in the finite product law.
The large-mean estimate follows from its first two moments and the
Paley--Zygmund argument, with no additional probabilistic hypotheses.
-/

public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

/-- [The number of true entries in the Boolean vector z equals the sum of
the indicators of its true entries](goal). -/
-- @node: star_binomial_count_eq_sum
lemma star_binomial_count_eq_sum (b : ℕ) (z : Fin b → Bool) :
    ((toFinset' z).card : ℝ) = ∑ i : Fin b, if z i then (1 : ℝ) else 0 := by
  classical
  rw [toFinset', Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  cases z i <;> rfl

/-- If [p is nonnegative](hyp:hp0) and [at most one](hyp:hp1), then [the
expected number of successes in b independent trials with success
probability p is b times p](goal). -/
-- @node: star_binomial_first_moment
lemma star_binomial_first_moment (b : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomialDesign b p).E (fun z => ((toFinset' z).card : ℝ)) = (b : ℝ) * p := by
  classical
  simp_rw [star_binomial_count_eq_sum]
  rw [FiniteDesign.E_sum]
  change (∑ i : Fin b, (Toolkit.Foundations.Probability.bernoulliCube (Fin b) p).E
    (fun z => if z i then (1 : ℝ) else 0)) = _
  rw [Toolkit.Foundations.Probability.bernoulliCube_eq p hp0 hp1]
  change (∑ i : Fin b, (prodDesign (fun _ : Fin b => coinDesign p hp0 hp1)).E
    (fun z => if z i then (1 : ℝ) else 0)) = _
  calc
    _ = ∑ _i : Fin b, p := by
      apply Finset.sum_congr rfl
      intro i _
      exact (FiniteDesign.E_prod_apply (fun _ : Fin b => coinDesign p hp0 hp1) i
        (fun c => if c then (1 : ℝ) else 0)).trans (coinDesign_E_treat p hp0 hp1)
    _ = _ := by simp

/-- If [p is nonnegative](hyp:hp0) and [at most one](hyp:hp1), then [the
variance of the success count in b independent trials with success
probability p is b times p times (1 − p)](goal). -/
-- @node: star_binomial_variance
lemma star_binomial_variance (b : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomialDesign b p).Var (fun z => ((toFinset' z).card : ℝ)) =
      (b : ℝ) * p * (1 - p) := by
  classical
  simp_rw [star_binomial_count_eq_sum]
  change (Toolkit.Foundations.Probability.bernoulliCube (Fin b) p).Var _ = _
  rw [Toolkit.Foundations.Probability.bernoulliCube_eq p hp0 hp1]
  change (prodDesign (fun _ : Fin b => coinDesign p hp0 hp1)).Var _ = _
  have h := FiniteDesign.Var_prod_linear_comb
    (fun _ : Fin b => coinDesign p hp0 hp1) (fun _ => (1 : ℝ))
    (fun _ b => if b then (1 : ℝ) else 0)
  simpa [coinDesign_Var_treat, mul_assoc] using h

/-- If [p is nonnegative](hyp:hp0) and [at most one](hyp:hp1), then [the
second moment of the success count in b independent trials is at most
the squared mean (bp)² plus the mean bp](goal). -/
-- @node: star_binomial_second_moment_le
lemma star_binomial_second_moment_le (b : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomialDesign b p).E (fun z => ((toFinset' z).card : ℝ) ^ 2) ≤
      ((b : ℝ) * p) ^ 2 + (b : ℝ) * p := by
  have hv := star_binomial_variance b p hp0 hp1
  rw [FiniteDesign.Var_eq, star_binomial_first_moment b p hp0 hp1] at hv
  nlinarith [mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) (sq_nonneg p)]

/-- If [X is nonnegative at every outcome](hyp:hX), then [one quarter of its
squared mean under the finite probability law D is at most its second moment
times the probability that X is at least half its mean](goal).

The multiplicative form also covers a zero second moment. -/
-- @node: star_half_mean_second_moment
lemma star_half_mean_second_moment {Ω : Type} [Fintype Ω]
    (D : FiniteDesign Ω) (X : Ω → ℝ) (hX : ∀ z, 0 ≤ X z) :
    (D.E X) ^ 2 / 4 ≤ D.E (fun z => X z ^ 2) * D.Pr (fun z => D.E X / 2 ≤ X z) := by
  classical
  let A := fun z => D.E X / 2 ≤ X z
  let Y := fun z => X z * FiniteDesign.ind A z
  have hm := D.E_nonneg hX
  have hy : 0 ≤ D.E Y := D.E_nonneg (fun z =>
    mul_nonneg (hX z) (FiniteDesign.ind_nonneg A z))
  have hcut : D.E X / 2 ≤ D.E Y := by
    have hpoint : ∀ z, X z ≤ D.E X / 2 + Y z := by
      intro z
      by_cases hz : A z
      · simp [Y, FiniteDesign.ind, hz]
        linarith
      · have hz' : X z < D.E X / 2 := lt_of_not_ge hz
        simp only [Y, FiniteDesign.ind, if_neg hz, mul_zero, add_zero]
        exact hz'.le
    have hbound : D.E X ≤ D.E (fun z => D.E X / 2 + Y z) :=
      Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hpoint z) (D.p_nonneg z))
    rw [D.E_add, D.E_const] at hbound
    linarith
  have hcs : (D.E Y) ^ 2 ≤ D.E (fun z => X z ^ 2) * D.Pr A := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun z => D.p z * Y z)
      (f := fun z => D.p z * X z ^ 2)
      (g := fun z => D.p z * FiniteDesign.ind A z)
    · intro z _
      exact mul_nonneg (D.p_nonneg z) (sq_nonneg _)
    · intro z _
      exact mul_nonneg (D.p_nonneg z) (FiniteDesign.ind_nonneg _ _)
    · intro z _
      by_cases hz : A z <;> simp [Y, FiniteDesign.ind, hz]; nlinarith
  have hsq : (D.E X) ^ 2 / 4 ≤ (D.E Y) ^ 2 := by nlinarith
  exact hsq.trans hcs

/-- If [p is nonnegative](hyp:hp0) and [at most one](hyp:hp1), [the target
ell is at least one](hyp:hell), and [the mean success count among floor(n/3)
trials is at least twice ell](hyp:hmean), then [the probability of at least
ell successes is at least one sixth](goal). -/
-- @node: star_trial_success_large_mean
lemma star_trial_success_large_mean (n ell : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hell : 1 ≤ ell)
    (hmean : 2 * (ell : ℝ) ≤ starBinomialMean n p) :
    (1 / 6 : ℝ) ≤ starTrialSuccess n p ell := by
  classical
  let D := binomialDesign (availableLeaves n) p
  let X := fun z : Fin (availableLeaves n) → Bool => ((toFinset' z).card : ℝ)
  let μ := starBinomialMean n p
  have hμ : 2 ≤ μ := by
    have : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    dsimp [μ]
    linarith
  have hfirst : D.E X = μ := star_binomial_first_moment _ p hp0 hp1
  have hsecond : D.E (fun z => X z ^ 2) ≤ μ ^ 2 + μ :=
    star_binomial_second_moment_le _ p hp0 hp1
  have hhalf := star_half_mean_second_moment D X (fun z => Nat.cast_nonneg _)
  rw [hfirst] at hhalf
  have hevent : D.Pr (fun z => μ / 2 ≤ X z) ≤ starTrialSuccess n p ell := by
    apply D.Pr_mono
    intro z hz
    have hcount : (ell : ℝ) ≤ (toFinset' z).card := by
      change μ / 2 ≤ (toFinset' z).card at hz
      dsimp [μ] at hz
      linarith
    exact_mod_cast hcount
  have hprob := D.Pr_nonneg (fun z => μ / 2 ≤ X z)
  have hupper := mul_le_mul_of_nonneg_right hsecond hprob
  have hpos : 0 < μ ^ 2 := by positivity
  have hratio : (1 / 6 : ℝ) ≤ D.Pr (fun z => μ / 2 ≤ X z) := by
    by_contra h
    have hlt : D.Pr (fun z => μ / 2 ≤ X z) < 1 / 6 := lt_of_not_ge h
    have hprod := mul_lt_mul_of_pos_left hlt (show 0 < μ ^ 2 + μ by positivity)
    nlinarith [sq_nonneg (μ - 2), mul_nonneg (sub_nonneg.mpr hμ) (show 0 ≤ μ by linarith)]
  exact hratio.trans hevent

/-- If [p is nonnegative](hyp:hp0) and [at most one](hyp:hp1), then [the
expectation of F applied to the success count in b independent trials equals
the sum, over counts from zero to b, of F at that count times its binomial
probability mass](goal). -/
-- @node: star_binomial_expectation_eq_sum
lemma star_binomial_expectation_eq_sum (b : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : ℕ → ℝ) :
    (binomialDesign b p).E (fun z => F (toFinset' z).card) =
      ∑ j ∈ Finset.range (b + 1),
        Causalean.Mathlib.Probability.binomialWeight b p j * F j := by
  classical
  change (Toolkit.Foundations.Probability.bernoulliCube (Fin b) p).E _ = _
  rw [Toolkit.Foundations.Probability.bernoulliCube_eq p hp0 hp1]
  simpa only [FiniteDesign.E, bernoulliDesign, prodDesign_p, coinDesign,
    Bool.cond_eq_ite, toFinset', Fintype.card_fin] using
    (Causalean.Mathlib.Probability.sum_bernoulli_eq_binomial (ι := Fin b) p F)

/-- If [p is nonnegative](hyp:hp0) and [at most one](hyp:hp1), and [ell is
at most b](hyp:hell), then [the probability of at least ell successes in b
independent trials is at least the binomial mass at ell, namely b choose ell
times p to the power ell times (1 − p) to the power b − ell](goal). -/
-- @node: star_binomial_tail_ge_mass
lemma star_binomial_tail_ge_mass (b ell : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hell : ell ≤ b) :
    (b.choose ell : ℝ) * p ^ ell * (1 - p) ^ (b - ell) ≤
      (binomialDesign b p).Pr (fun z => ell ≤ (toFinset' z).card) := by
  classical
  have heq : (binomialDesign b p).Pr (fun z => (toFinset' z).card = ell) =
      (b.choose ell : ℝ) * p ^ ell * (1 - p) ^ (b - ell) := by
    change (binomialDesign b p).E (fun z => if (toFinset' z).card = ell then 1 else 0) = _
    rw [star_binomial_expectation_eq_sum b p hp0 hp1 (fun j => if j = ell then 1 else 0)]
    simp [Finset.mem_range, Nat.lt_succ_of_le hell,
      Causalean.Mathlib.Probability.binomialWeight]
  rw [← heq]
  exact FiniteDesign.Pr_mono _ _ _ (fun _ h => h.ge)

/-- If [p is nonnegative](hyp:hp0) and [less than one half](hyp:hp1), then
[the natural logarithm of 1 − p is at least −2p](goal). -/
-- @node: star_log_one_sub_lower
lemma star_log_one_sub_lower (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1 / 2) :
    -2 * p ≤ Real.log (1 - p) := by
  have hpos : 0 < 1 - p := by linarith
  have hinv : (1 - p)⁻¹ ≤ 1 + 2 * p := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg hp0 (show 0 ≤ 1 - 2 * p by linarith)]
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  linarith

/-- If [p is nonnegative](hyp:hp0) and [less than one half](hyp:hp1), [ell
is at most b](hyp:hell), and [b times p is less than twice ell](hyp:hmean),
then [the failure factor (1 − p) to the power b − ell is at least exp(−4 ell)](goal). -/
-- @node: star_binomial_failure_factor_lower
lemma star_binomial_failure_factor_lower (b ell : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p < 1 / 2) (hell : ell ≤ b)
    (hmean : (b : ℝ) * p < 2 * ell) :
    Real.exp (-4 * (ell : ℝ)) ≤ (1 - p) ^ (b - ell) := by
  have hlog := star_log_one_sub_lower p hp0 hp1
  have hmul := mul_le_mul_of_nonneg_left hlog
    (Nat.cast_nonneg (b - ell) : (0 : ℝ) ≤ ((b - ell : ℕ) : ℝ))
  have hexp : -4 * (ell : ℝ) ≤ (b - ell : ℕ) * Real.log (1 - p) := by
    rw [Nat.cast_sub hell] at hmul ⊢
    nlinarith [mul_nonneg hp0 (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell)]
  calc
    _ ≤ Real.exp ((b - ell : ℕ) * Real.log (1 - p)) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < 1 - p)]

/-- If [x is nonnegative](hyp:hx) and [at most b + 1 minus ell, with this
subtraction truncated at zero](hyp:hbx), then [b choose ell is at least
x to the power ell divided by ell factorial](goal). -/
-- @node: star_choose_lower
lemma star_choose_lower (b ell : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hbx : x ≤ (b + 1 - ell : ℕ)) :
    x ^ ell / (ell.factorial : ℝ) ≤ (b.choose ell : ℝ) := by
  have hpow := Nat.pow_sub_le_descFactorial b ell
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hpow
  have hpow' : ((b + 1 - ell : ℕ) : ℝ) ^ ell ≤
      (ell.factorial : ℝ) * b.choose ell := by exact_mod_cast hpow
  apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos ell : (0 : ℝ) < ell.factorial)).mpr
  calc
    x ^ ell ≤ ((b + 1 - ell : ℕ) : ℝ) ^ ell := pow_le_pow_left₀ hx hbx ell
    _ ≤ _ := by nlinarith

/-- If [p is nonnegative](hyp:hp0) and [less than one half](hyp:hp1), [ell
is at most n/100](hyp:hell), and [the mean success count among floor(n/3)
trials is less than twice ell](hyp:hmean), then [the probability of at least
ell successes is at least (n/4) to the power ell times p to the power ell,
divided by ell factorial, times exp(−4 ell)](goal). -/
-- @node: star_trial_success_small_mean_mass
lemma star_trial_success_small_mean_mass (n ell : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p < 1 / 2)
    (hell : (ell : ℝ) ≤ (n : ℝ) / 100)
    (hmean : starBinomialMean n p < 2 * ell) :
    ((n : ℝ) / 4) ^ ell * p ^ ell / (ell.factorial : ℝ) *
      Real.exp (-4 * (ell : ℝ)) ≤ starTrialSuccess n p ell := by
  have hs : 100 * ell ≤ n := by
    have : (100 : ℝ) * ell ≤ n := by linarith
    exact_mod_cast this
  have hellb : ell ≤ availableLeaves n := by dsimp [availableLeaves]; omega
  have hbase : (n : ℝ) / 4 ≤ (availableLeaves n + 1 - ell : ℕ) := by
    have hnat : n ≤ 4 * (availableLeaves n + 1 - ell) := by
      dsimp [availableLeaves]
      omega
    have : (n : ℝ) ≤ 4 * (availableLeaves n + 1 - ell : ℕ) := by exact_mod_cast hnat
    linarith
  have hchoose := star_choose_lower (availableLeaves n) ell ((n : ℝ) / 4)
    (by positivity) hbase
  have hfactor := star_binomial_failure_factor_lower (availableLeaves n) ell p
    hp0 hp1 hellb hmean
  have hmass := star_binomial_tail_ge_mass (availableLeaves n) ell p hp0
    (by linarith) hellb
  calc
    _ = (((n : ℝ) / 4) ^ ell / (ell.factorial : ℝ) * p ^ ell) *
        Real.exp (-4 * (ell : ℝ)) := by ring
    _ ≤ ((availableLeaves n).choose ell : ℝ) * p ^ ell *
        (1 - p) ^ (availableLeaves n - ell) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hchoose (pow_nonneg hp0 _)
      · exact hfactor
      · exact (Real.exp_pos _).le
      · positivity
    _ ≤ _ := hmass

/-- [For A = 400 exp(4), the product of (A/4) to the power ell and
exp(−4 ell) equals 100 to the power ell](goal). -/
-- @node: star_small_mean_constant_identity
lemma star_small_mean_constant_identity (ell : ℕ) :
    (starConstA / 4) ^ ell * Real.exp (-4 * (ell : ℝ)) = (100 : ℝ) ^ ell := by
  have hA : starConstA / 4 = 100 * Real.exp 4 := by unfold starConstA; ring
  rw [hA, mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  have hz : (ell : ℝ) * 4 + -4 * (ell : ℝ) = 0 := by ring
  rw [hz, Real.exp_zero, mul_one]

/-- If [n is positive](hyp:hn), [q is nonnegative](hyp:hq), [Aq is less than
one half, where A = 400 exp(4)](hyp:hp), [ell is at most n/100](hyp:hell),
[the mean count among floor(n/3) trials with success probability Aq is less
than twice ell](hyp:hmean), and [ell factorial divided by n to the power
ell + 1, times m divided by 2 exp(1), is at most q to the power ell](hyp:hcount),
then [the probability of at least ell successes is at least 100 to the power
ell times m divided by 2 exp(1)n](goal).

The counting inequality is an explicit input to this local assembly lemma. -/
-- @node: star_trial_success_small_mean_of_count
lemma star_trial_success_small_mean_of_count (n ell m : ℕ) (q : ℝ)
    (hn : 0 < n) (hq : 0 ≤ q)
    (hp : starConstA * q < 1 / 2)
    (hell : (ell : ℝ) ≤ (n : ℝ) / 100)
    (hmean : starBinomialMean n (starConstA * q) < 2 * ell)
    (hcount : (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
      ((m : ℝ) / (2 * Real.exp 1)) ≤ q ^ ell) :
    (100 : ℝ) ^ ell * m / (2 * Real.exp 1 * n) ≤
      starTrialSuccess n (starConstA * q) ell := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < ell.factorial := by exact_mod_cast Nat.factorial_pos ell
  have hA : 0 < starConstA := by unfold starConstA; positivity
  have hmass := star_trial_success_small_mean_mass n ell (starConstA * q)
    (mul_nonneg hA.le hq) hp hell hmean
  have hcancel : ((n : ℝ) / 4) ^ ell * (starConstA * q) ^ ell /
      (ell.factorial : ℝ) * Real.exp (-4 * (ell : ℝ)) =
      (100 : ℝ) ^ ell * ((n : ℝ) ^ ell * q ^ ell / (ell.factorial : ℝ)) := by
    calc
      _ = ((n : ℝ) * q) ^ ell / (ell.factorial : ℝ) *
          ((starConstA / 4) ^ ell * Real.exp (-4 * (ell : ℝ))) := by
        rw [div_pow, div_pow, mul_pow, mul_pow]
        ring
      _ = _ := by rw [star_small_mean_constant_identity, mul_pow]; ring
  rw [hcancel] at hmass
  refine le_trans ?_ hmass
  have hmul := mul_le_mul_of_nonneg_left hcount
    (div_nonneg (pow_nonneg hnpos.le ell) hfac.le)
  have hcancel' : (n : ℝ) ^ ell / (ell.factorial : ℝ) *
      ((ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
        ((m : ℝ) / (2 * Real.exp 1))) = (m : ℝ) / (2 * Real.exp 1 * n) := by
    rw [pow_succ]
    field_simp
  rw [hcancel'] at hmul
  have hfinal := mul_le_mul_of_nonneg_left hmul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 100) ell)
  convert hfinal using 1 <;> ring

end Papers.OaiGraphDecompositionsIntegral
