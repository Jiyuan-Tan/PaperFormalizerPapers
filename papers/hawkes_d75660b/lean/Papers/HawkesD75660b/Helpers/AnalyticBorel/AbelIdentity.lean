module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Data.Nat.Choose.Sum
public import Papers.HawkesD75660b.Helpers.BorelMoments
public import Mathlib.Tactic.LinearCombination

/-! A finite Abel identity for the rooted-tree coefficient calculation.
The argument uses differentiation and induction, independently of Borel normalization. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Papers.HawkesD75660b.AnalyticBorel

/-- The [tree Abel polynomial](goal) is [one at degree zero](step:1) and,
[at degree n + 1, equals x times the nth power of x + n + 1](step:2). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbelPoly
def treeAbelPoly : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, x => x * (x + (n + 1 : ℕ)) ^ n

/-- [The degree-n tree Abel polynomial at zero is one if n is zero and zero otherwise](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbelPoly_zero
lemma treeAbelPoly_zero (n : ℕ) :
    treeAbelPoly n 0 = if n = 0 then 1 else 0 := by
  cases n <;> simp [treeAbelPoly]

/-- [The derivative of the degree-(n + 1) tree Abel polynomial at x is n + 1 times
the degree-n tree Abel polynomial at x + 1](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbelPoly_hasDerivAt
lemma treeAbelPoly_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (treeAbelPoly (n + 1))
      (((n + 1 : ℕ) : ℝ) * treeAbelPoly n (x + 1)) x := by
  cases n with
  | zero =>
    have hf : treeAbelPoly 1 = id := by
      funext y
      simp [treeAbelPoly]
    rw [hf]
    simpa [treeAbelPoly] using hasDerivAt_id x
  | succ n =>
    have h := (hasDerivAt_id x).mul
      (((hasDerivAt_id x).add_const ((n + 1 + 1 : ℕ) : ℝ)).pow (n + 1))
    convert h using 1 <;> try rfl
    dsimp [treeAbelPoly]
    push_cast
    rw [pow_succ]
    ring

/-- For [a nonnegative integer n](hyp:n) and [real numbers x and y](hyp:x,y),
the [finite Abel sum](goal) sums, over k from zero through n, the binomial
coefficient n choose k times the degree-k tree Abel polynomial at x times
the (n − k)th power of y − k. -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbelSum
def treeAbelSum (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℝ) * treeAbelPoly k x * (y - k) ^ (n - k)

/-- [The degree-(n + 1) Abel sum at x and y equals y to the power n + 1 plus
the sum over k from zero through n of n + 1 choose k + 1 times the degree-(k + 1)
tree Abel polynomial at x times the (n − k)th power of y − k − 1](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbelSum_succ
lemma treeAbelSum_succ (n : ℕ) (x y : ℝ) :
    treeAbelSum (n + 1) x y = y ^ (n + 1) +
      ∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose (k + 1) : ℝ) * treeAbelPoly (k + 1) x *
          (y - (k + 1 : ℕ)) ^ (n - k) := by
  rw [treeAbelSum, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, treeAbelPoly,
    one_mul, sub_zero, Nat.sub_zero, Nat.add_sub_add_right]
  rw [add_comm]

/-- [The derivative in the first argument of the degree-(n + 1) Abel sum at
x and y is n + 1 times the degree-n Abel sum at x + 1 and y − 1](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbelSum_hasDerivAt
lemma treeAbelSum_hasDerivAt (n : ℕ) (x y : ℝ) :
    HasDerivAt (fun t => treeAbelSum (n + 1) t y)
      (((n + 1 : ℕ) : ℝ) * treeAbelSum n (x + 1) (y - 1)) x := by
  have hf : (fun t => treeAbelSum (n + 1) t y) =
      (fun t => y ^ (n + 1) + ∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose (k + 1) : ℝ) * treeAbelPoly (k + 1) t *
          (y - (k + 1 : ℕ)) ^ (n - k)) := by
    funext t
    exact treeAbelSum_succ n t y
  rw [hf]
  have h := (HasDerivAt.fun_sum (u := Finset.range (n + 1))
    (fun k _ => ((treeAbelPoly_hasDerivAt k x).const_mul
      ((n + 1).choose (k + 1) : ℝ)).mul_const
        ((y - (k + 1 : ℕ)) ^ (n - k)))).const_add (y ^ (n + 1))
  convert h using 1 <;> try rfl
  rw [treeAbelSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hc : ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) =
      ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  push_cast at hc ⊢
  rw [show y - (k + 1 : ℝ) = y - 1 - k by ring]
  calc
    _ = ((n : ℝ) + 1) * (n.choose k : ℝ) *
        treeAbelPoly k (x + 1) * (y - 1 - k) ^ (n - k) := by ring
    _ = _ := by rw [hc]; ring

/-- [The degree-n Abel sum with first argument zero and second argument y equals y to the nth power](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbelSum_zero_left
lemma treeAbelSum_zero_left (n : ℕ) (y : ℝ) : treeAbelSum n 0 y = y ^ n := by
  rw [treeAbelSum]
  simp [treeAbelPoly_zero, Finset.sum_ite_eq', Finset.mem_range]

/-- [The degree-n finite Abel sum at x and y equals the nth power of x + y](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbelSum_eq_add_pow
lemma treeAbelSum_eq_add_pow (n : ℕ) (x y : ℝ) :
    treeAbelSum n x y = (x + y) ^ n := by
  induction n generalizing x y with
  | zero => simp [treeAbelSum, treeAbelPoly]
  | succ n ih =>
    have hd (t : ℝ) : HasDerivAt
        (fun t => treeAbelSum (n + 1) t y - (t + y) ^ (n + 1)) 0 t := by
      have h₁ := treeAbelSum_hasDerivAt n t y
      rw [ih] at h₁
      have h₂ := ((hasDerivAt_id t).add_const y).pow (n + 1)
      convert h₁.sub h₂ using 1 <;> try rfl
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one, id_eq]
      rw [show t + 1 + (y - 1) = t + y by ring]
      ring
    have hc := is_const_of_deriv_eq_zero
      (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) x 0
    rw [treeAbelSum_zero_left, zero_add, sub_self] at hc
    exact sub_eq_zero.mp hc

/-- [Multiplying the degree-k tree Abel polynomial at one by k + 1 gives
the kth power of k + 1](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbelPoly_one_mul
lemma treeAbelPoly_one_mul (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * treeAbelPoly k 1 = ((k + 1 : ℕ) : ℝ) ^ k := by
  cases k with
  | zero => norm_num [treeAbelPoly]
  | succ k =>
    simp only [treeAbelPoly, Nat.cast_add, Nat.cast_one, one_mul]
    rw [pow_succ]
    ring

/-- [Summing n + 1 choose k + 1 times the kth power of k + 1 times the
(n − k)th power of y − k − 1, for k from zero through n, gives n + 1 times
the nth power of y](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeAbel_rooted_coeff
lemma treeAbel_rooted_coeff (n : ℕ) (y : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ k *
        (y - (k + 1 : ℕ)) ^ (n - k)) = ((n + 1 : ℕ) : ℝ) * y ^ n := by
  calc
    _ = ((n + 1 : ℕ) : ℝ) * treeAbelSum n 1 (y - 1) := by
      rw [treeAbelSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← treeAbelPoly_one_mul]
      have hc : ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) =
          ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n k
      have hy : y - (k + 1 : ℕ) = y - 1 - k := by push_cast; ring
      rw [hy]
      calc
        _ = (((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
            treeAbelPoly k 1 * (y - 1 - k) ^ (n - k) := by ring
        _ = _ := by rw [← hc]; ring
    _ = _ := by rw [treeAbelSum_eq_add_pow]; congr 2; ring

/-- [Summing n + 1 choose k + 1 times the kth power of k + 1 times the
(n − k)th power of n − k, for k from zero to n − 1, gives n times the nth
power of n + 1](goal).

This is a finite rooted-tree convolution identity; its proof uses no normalization
or generating-function identity. -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTree_convolution_coeff
lemma rootedTree_convolution_coeff (n : ℕ) :
    (∑ k ∈ Finset.range n,
      ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ k *
        ((n - k : ℕ) : ℝ) ^ (n - k)) = (n : ℝ) * ((n + 1 : ℕ) : ℝ) ^ n := by
  have h := treeAbel_rooted_coeff n ((n + 1 : ℕ) : ℝ)
  rw [Finset.sum_range_succ] at h
  have hs : (∑ k ∈ Finset.range n,
      ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ k *
        (((n + 1 : ℕ) : ℝ) - (k + 1 : ℕ)) ^ (n - k)) =
      ∑ k ∈ Finset.range n,
        ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ k *
          ((n - k : ℕ) : ℝ) ^ (n - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := (Finset.mem_range.mp hk).le
    rw [Nat.cast_sub hk']
    push_cast
    congr 2; ring
  rw [hs] at h
  simp only [Nat.choose_self, Nat.cast_one, one_mul, sub_self, Nat.sub_self,
    pow_zero, mul_one] at h
  push_cast at h ⊢
  nlinarith [h]

end Papers.HawkesD75660b.AnalyticBorel
