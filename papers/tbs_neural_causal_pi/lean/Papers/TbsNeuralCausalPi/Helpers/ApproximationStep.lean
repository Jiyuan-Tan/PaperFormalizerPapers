module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Model
public import Causalean.Mathlib.Probability.FiniteMarkovOscillation
/-! # Local comparison and propagation of intervention errors

The categorical estimates use the midpoint oscillation bound, so their constants
are half the label diameter. The history recurrence uses a finite geometric sum
and remains valid when the mechanism Lipschitz constant is zero.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.style.whitespace false
open scoped ENNReal NNReal

-- @node: categorical_expectation_contrast_le
/-- If [p is a probability vector](hyp:hp), [q is a probability vector](hyp:hq),
and [any two values of g differ by at most D](hyp:hg), then [the absolute difference
of their expectations of g is at most D/2 times the sum of the absolute differences
between their probabilities](goal). -/
lemma categorical_expectation_contrast_le {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    {g : Fin k → ℝ} {D : ℝ} (hg : ∀ i j, |g i-g j| ≤ D) :
    |(∑ j, p j * g j) - ∑ j, q j * g j| ≤
      D / 2 * ∑ j, |p j-q j| := by
  let : Nonempty (Fin k) :=
    Causalean.Mathlib.Probability.FiniteMarkovOscillation.nonemptyOfProbabilityVector p hp
  have h := Causalean.Mathlib.Probability.FiniteMarkovOscillation.abs_sum_sub_mul_le_oscillation_halfL1
    hp hq hg
  simp_rw [sub_mul] at h
  rw [Finset.sum_sub_distrib] at h
  convert h using 1
  ring

-- @node: categorical_expectation_sup_error_le
/-- If [p and q are probability vectors](hyp:hp,hq), [the values of g differ by
at most k minus one](hyp:hg), and [each probability differs by at most e](hyp:he),
then [their expectations of g differ by at most k times k minus one, divided by
two, times e](goal), with subtraction truncated at zero. -/
lemma categorical_expectation_sup_error_le {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    {g : Fin k → ℝ} (hg : ∀ i j, |g i-g j| ≤ (k-1 : ℕ))
    {e : ℝ} (he : ∀ j, |p j-q j| ≤ e) :
    |(∑ j, p j * g j) - ∑ j, q j * g j| ≤
      (k : ℝ) * (k-1 : ℕ) / 2 * e := by
  calc
    _ ≤ ((k-1 : ℕ) : ℝ) / 2 * ∑ j, |p j-q j| :=
      categorical_expectation_contrast_le hp hq hg
    _ ≤ ((k-1 : ℕ) : ℝ) / 2 * ∑ _j : Fin k, e := by
      gcongr
      exact he _
    _ = _ := by simp; ring

-- @node: categorical_history_expectation_dist_le
/-- Suppose [p and q are probability vectors](hyp:hp,hq), [D is nonnegative](hyp:hD),
[their total absolute probability difference is at most L times the distance
between histories x and y](hyp:hprop), [g and h differ at each label by at most
that history distance](hyp:hhistory), and [h varies across labels by at most D](hyp:hlabels).
Then [the p-weighted expectation of g and the q-weighted expectation of h differ
by at most 1 + DL/2 times the distance between x and y](goal). -/
lemma categorical_history_expectation_dist_le
    {X : Type*} [PseudoMetricSpace X] {k : ℕ}
    {p q : Fin k → ℝ} (hp : p ∈ probabilitySimplex k)
    (hq : q ∈ probabilitySimplex k) {g h : Fin k → ℝ}
    {x y : X} {L D : ℝ} (hD : 0 ≤ D)
    (hprop : (∑ j, |p j-q j|) ≤ L * dist x y)
    (hhistory : ∀ j, |g j-h j| ≤ dist x y)
    (hlabels : ∀ i j, |h i-h j| ≤ D) :
    |(∑ j, p j * g j) - ∑ j, q j * h j| ≤
      (1 + D * L / 2) * dist x y := by
  have hfirst : |∑ j, p j * (g j-h j)| ≤ dist x y := by
    calc
      _ ≤ ∑ j, |p j * (g j-h j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, p j * |g j-h j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (hp.1 j)]
      _ ≤ ∑ j, p j * dist x y := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hhistory j) (hp.1 j)
      _ = dist x y := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hsecond := categorical_expectation_contrast_le hp hq hlabels
  have hsplit : (∑ j, p j * g j) - ∑ j, q j * h j =
      (∑ j, p j * (g j-h j)) + ((∑ j, p j * h j) - ∑ j, q j * h j) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc
    _ ≤ |∑ j, p j * (g j-h j)| + |(∑ j, p j * h j) - ∑ j, q j * h j| :=
      abs_add_le _ _
    _ ≤ dist x y + D / 2 * ∑ j, |p j-q j| := add_le_add hfirst hsecond
    _ ≤ dist x y + D / 2 * (L * dist x y) := by
      gcongr
    _ = _ := by ring

-- @node: categorical_history_expectation_lipschitzOn
/-- Suppose [p is probability-valued on S](hyp:hp), [p is L-Lipschitz there in
the sum metric](hyp:hLip), [g changes by at most the history distance when its
label is fixed](hyp:hhistory), and [g varies across labels by at most D at each
history in S](hyp:hlabels). Then [the p-weighted conditional expectation of g
is Lipschitz on S with constant 1 + DL/2](goal). -/
lemma categorical_history_expectation_lipschitzOn
    {X : Type*} [PseudoMetricSpace X] {k : ℕ} {S : Set X}
    {p : X → L1Vec k} {L D : ℝ≥0}
    (hp : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex k)
    (hLip : LipschitzOnWith L p S) (g : X → Fin k → ℝ)
    (hhistory : ∀ x ∈ S, ∀ y ∈ S, ∀ j, |g x j-g y j| ≤ dist x y)
    (hlabels : ∀ y ∈ S, ∀ i j, |g y i-g y j| ≤ D) :
    LipschitzOnWith (1 + D * L / 2)
      (fun x => ∑ j, (p x).ofLp j * g x j) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  have hprop : (∑ j, |(p x).ofLp j-(p y).ofLp j|) ≤ (L : ℝ) * dist x y := by
    simpa only [PiLp.dist_eq_of_L1, Real.dist_eq] using hLip.dist_le_mul x hx y hy
  simpa only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_ofNat] using
    categorical_history_expectation_dist_le (hp x hx) (hp y hy) D.coe_nonneg
      hprop (hhistory x hx y hy) (hlabels y hy)

-- @node: continuous_expectation_sup_error_le
/-- If [f is 1-Lipschitz in the sum metric](hyp:hf) and [each coordinate of v
and w differs by at most e](hyp:he), then [f evaluated at v and w differs by at
most d times e, where d is their dimension](goal). -/
lemma continuous_expectation_sup_error_le {d : ℕ} {f : L1Vec d → ℝ}
    (hf : LipschitzWith 1 f) (v w : L1Vec d) {e : ℝ}
    (he : ∀ j, |v.ofLp j-w.ofLp j| ≤ e) :
    |f v-f w| ≤ (d : ℝ) * e := by
  calc
    _ ≤ dist v w := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul v w
    _ = ∑ j, |v.ofLp j-w.ofLp j| := by rw [PiLp.dist_eq_of_L1]; rfl
    _ ≤ ∑ _j : Fin d, e := Finset.sum_le_sum fun j _ => he j
    _ = _ := by simp

-- @node: continuous_history_expectation_lipschitzOn
/-- If [f is L-Lipschitz on S](hyp:hf) and [the change in g between any two
histories in S and any two output vectors is bounded by the sum of their
distances](hyp:hg), then [evaluating g at a history and its output under f is
Lipschitz on S with constant 1 + L](goal). -/
lemma continuous_history_expectation_lipschitzOn
    {X : Type*} [PseudoMetricSpace X] {d : ℕ} {S : Set X}
    {f : X → L1Vec d} {L : ℝ≥0} (hf : LipschitzOnWith L f S)
    (g : X → L1Vec d → ℝ)
    (hg : ∀ x ∈ S, ∀ y ∈ S, ∀ v w,
      |g x v-g y w| ≤ dist x y + dist v w) :
    LipschitzOnWith (1+L) (fun x => g x (f x)) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  calc
    _ ≤ dist x y + dist (f x) (f y) := hg x hx y hy _ _
    _ ≤ dist x y + (L : ℝ) * dist x y :=
      add_le_add le_rfl (hf.dist_le_mul x hx y hy)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_one]; ring

-- @node: approximation_history_recurrence_le
/-- For [a nonnegative, possibly infinite error sequence E](hyp:E) and
[nonnegative, possibly infinite coefficients A and T](hyp:A,T), if [each next
error is at most A times the current error plus T](hyp:hstep), then [the error
at stage m is at most A to the power m times the initial error plus T times
the sum of powers of A from zero through m minus one](goal). -/
lemma approximation_history_recurrence_le (E : ℕ → ℝ≥0∞) (A T : ℝ≥0∞)
    (hstep : ∀ r, E (r+1) ≤ A * E r + T) (m : ℕ) :
    E m ≤ A^m * E 0 + T * ∑ r ∈ Finset.range m, A^r := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      E (m+1) ≤ A * E m + T := hstep m
      _ ≤ A * (A^m * E 0 + T * ∑ r ∈ Finset.range m, A^r) + T := by
        gcongr
      _ = A^(m+1) * E 0 + T * ∑ r ∈ Finset.range (m+1), A^r := by
        rw [Finset.sum_range_succ']
        simp_rw [pow_succ']
        rw [← Finset.mul_sum]
        simp only [pow_zero]
        ring

-- @node: approximationPropagationConstant
/-- For [nonnegative amplification and local-error coefficients A and B](hyp:A,B)
and [an update bound N](hyp:N), the [propagation constant](goal) is the maximum
of A to the power N and B times the sum of powers of A from zero through N minus one. -/
def approximationPropagationConstant (A B : ℝ≥0) (N : ℕ) : ℝ≥0 :=
  max (A^N) (B * ∑ r ∈ Finset.range N, A^r)

-- @node: approximation_history_uniform_bound
/-- For [a nonnegative, possibly infinite error sequence E](hyp:E),
[nonnegative coefficients A and B](hyp:A,B), and [a nonnegative, possibly infinite
structural error S](hyp:S), suppose [A is at least one](hyp:hA) and [each next
error is at most A times the current error plus B times S](hyp:hstep).
If [m is at most N](hyp:hm), then [the error at m is at most the propagation
constant for A, B, and N times the sum of S and the initial error](goal). -/
lemma approximation_history_uniform_bound (E : ℕ → ℝ≥0∞) (A B : ℝ≥0)
    (S : ℝ≥0∞) (hA : 1 ≤ A)
    (hstep : ∀ r, E (r+1) ≤ (A : ℝ≥0∞) * E r + (B : ℝ≥0∞) * S)
    {m N : ℕ} (hm : m ≤ N) :
    E m ≤ (approximationPropagationConstant A B N : ℝ≥0∞) * (S + E 0) := by
  have hpow : (A : ℝ≥0∞)^m ≤ (A : ℝ≥0∞)^N :=
    pow_le_pow_right₀ (by exact_mod_cast hA) hm
  have hsum : (∑ r ∈ Finset.range m, (A : ℝ≥0∞)^r) ≤
      ∑ r ∈ Finset.range N, (A : ℝ≥0∞)^r :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hm)
  have hfirst : (A : ℝ≥0∞)^N ≤ (approximationPropagationConstant A B N : ℝ≥0∞) := by
    exact_mod_cast (le_max_left (A^N) (B * ∑ r ∈ Finset.range N, A^r))
  have hsecond : (B : ℝ≥0∞) * (∑ r ∈ Finset.range N, (A : ℝ≥0∞)^r) ≤
      (approximationPropagationConstant A B N : ℝ≥0∞) := by
    exact_mod_cast (le_max_right (A^N) (B * ∑ r ∈ Finset.range N, A^r))
  calc
    E m ≤ (A : ℝ≥0∞)^m * E 0 + (B : ℝ≥0∞) * S *
        ∑ r ∈ Finset.range m, (A : ℝ≥0∞)^r :=
      approximation_history_recurrence_le E A ((B : ℝ≥0∞)*S) hstep m
    _ ≤ (A : ℝ≥0∞)^N * E 0 + ((B : ℝ≥0∞) *
        ∑ r ∈ Finset.range N, (A : ℝ≥0∞)^r) * S := by
      rw [mul_right_comm (B : ℝ≥0∞) S]
      gcongr
    _ ≤ (approximationPropagationConstant A B N : ℝ≥0∞) * E 0 +
        (approximationPropagationConstant A B N : ℝ≥0∞) * S := by
      gcongr
    _ = _ := by rw [mul_add, add_comm]

end Papers.TbsNeuralCausalPi
