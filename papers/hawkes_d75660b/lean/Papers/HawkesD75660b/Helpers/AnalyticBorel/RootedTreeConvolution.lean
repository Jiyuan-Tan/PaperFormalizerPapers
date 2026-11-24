module

public import Papers.HawkesD75660b.Helpers.AnalyticBorel.RootedTreeSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! The convergent rooted-tree convolution and its subcritical branch.
All identities here are independent of Borel normalization. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Papers.HawkesD75660b.AnalyticBorel

/-- For [a real series argument z](hyp:z) and [a nonnegative integer index n](hyp:n),
the [degree-weighted rooted-tree term](goal) is n times the rooted-tree term at z
and index n. -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeWeightedTerm
def rootedTreeWeightedTerm (z : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * rootedTreeTerm z n

/-- [The degree-weighted rooted-tree term at index n is zero when n=0 and is
n^n z^n/n! otherwise](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeWeightedTerm_eq
lemma rootedTreeWeightedTerm_eq (z : ℝ) (n : ℕ) :
    rootedTreeWeightedTerm z n =
      if n = 0 then 0 else (n : ℝ) ^ n * z ^ n / (n.factorial : ℝ) := by
  cases n with
  | zero => simp [rootedTreeWeightedTerm]
  | succ n =>
    simp only [rootedTreeWeightedTerm, rootedTreeTerm, Nat.succ_ne_zero,
      ↓reduceIte, Nat.add_sub_cancel]
    rw [pow_succ]
    ring

/-- If [z is nonnegative](hyp:hz), then [every degree-weighted rooted-tree term
at z is nonnegative](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeWeightedTerm_nonneg
lemma rootedTreeWeightedTerm_nonneg {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ rootedTreeWeightedTerm z n :=
  mul_nonneg (Nat.cast_nonneg _) (rootedTreeTerm_nonneg hz n)

/-- If [z is nonnegative](hyp:hz), then [the degree-weighted rooted-tree term
at index n is at most (z exp(1))^n](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeWeightedTerm_le_geometric
lemma rootedTreeWeightedTerm_le_geometric {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    rootedTreeWeightedTerm z n ≤ (z * Real.exp 1) ^ n := by
  rw [rootedTreeWeightedTerm_eq]
  split_ifs with hn
  · positivity
  · calc
      (n : ℝ) ^ n * z ^ n / (n.factorial : ℝ) =
          ((n : ℝ) ^ n / (n.factorial : ℝ)) * z ^ n := by ring
      _ ≤ Real.exp (n : ℝ) * z ^ n := by
        gcongr
        exact Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
      _ = (z * Real.exp 1) ^ n := by
        rw [mul_pow, ← Real.exp_nat_mul]
        simp [mul_comm]

/-- If [z is nonnegative](hyp:hz) and [z < exp(−1)](hyp:hzlt), then
[the degree-weighted rooted-tree terms at z have a convergent sum](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeWeightedTerm_summable
lemma rootedTreeWeightedTerm_summable {z : ℝ} (hz : 0 ≤ z)
    (hzlt : z < Real.exp (-1)) : Summable (rootedTreeWeightedTerm z) := by
  have hq : z * Real.exp 1 < 1 := by
    calc
      z * Real.exp 1 < Real.exp (-1) * Real.exp 1 :=
        mul_lt_mul_of_pos_right hzlt (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add]; norm_num
  exact Summable.of_nonneg_of_le (rootedTreeWeightedTerm_nonneg hz)
    (rootedTreeWeightedTerm_le_geometric hz)
    (summable_geometric_of_lt_one (mul_nonneg hz (Real.exp_pos _).le) hq)

/-- [The sum over k from zero to n of the rooted-tree term at k times the
degree-weighted rooted-tree term at n−k equals the degree-weighted term at n
minus the unweighted term at n, all evaluated at z](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeTerm_convolution
lemma rootedTreeTerm_convolution (z : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      rootedTreeTerm z k * rootedTreeWeightedTerm z (n - k)) =
        rootedTreeWeightedTerm z n - rootedTreeTerm z n := by
  cases n with
  | zero => simp [rootedTreeTerm, rootedTreeWeightedTerm]
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [show rootedTreeTerm z 0 = 0 by simp [rootedTreeTerm], zero_mul, add_zero]
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, show rootedTreeWeightedTerm z 0 = 0 by
      simp [rootedTreeWeightedTerm], mul_zero, add_zero]
    have hs : (∑ k ∈ Finset.range n,
        rootedTreeTerm z (k + 1) * rootedTreeWeightedTerm z (n + 1 - (k + 1))) =
        (z ^ (n + 1) / ((n + 1).factorial : ℝ)) *
          (∑ k ∈ Finset.range n,
            ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ k *
              ((n - k : ℕ) : ℝ) ^ (n - k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hkn : k + 1 ≤ n + 1 := by omega
      have hn : n - k ≠ 0 := by omega
      have hc : ((n + 1).choose (k + 1) : ℝ) *
          ((k + 1).factorial : ℝ) * ((n - k).factorial : ℝ) =
            ((n + 1).factorial : ℝ) := by
        have h := Nat.choose_mul_factorial_mul_factorial hkn
        rw [Nat.add_sub_add_right] at h
        exact_mod_cast h
      simp only [Nat.add_sub_add_right, rootedTreeTerm, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
        rootedTreeWeightedTerm_eq, hn] 
      have hp : z ^ (n + 1) = z ^ (k + 1) * z ^ (n - k) := by
        rw [← pow_add, show k + 1 + (n - k) = n + 1 by omega]
      rw [hp]
      field_simp
      linear_combination -(z ^ (k + 1) * z ^ (n - k)) * hc
    rw [hs, rootedTree_convolution_coeff]
    simp only [rootedTreeWeightedTerm, rootedTreeTerm, Nat.succ_ne_zero,
      ↓reduceIte, Nat.add_sub_cancel]
    push_cast
    ring

/-- For [a real series argument z](hyp:z), the [degree-weighted rooted-tree
series](goal) is the infinite sum of the degree-weighted rooted-tree terms at z. -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeWeightedSeries
def rootedTreeWeightedSeries (z : ℝ) : ℝ := ∑' n, rootedTreeWeightedTerm z n

/-- If [z is nonnegative](hyp:hz) and [z < exp(−1)](hyp:hzlt), then
[the rooted-tree series times its degree-weighted series equals the
degree-weighted series minus the rooted-tree series, all evaluated at z](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_convolution
lemma rootedTreeSeries_convolution {z : ℝ} (hz : 0 ≤ z)
    (hzlt : z < Real.exp (-1)) :
    rootedTreeSeries z * rootedTreeWeightedSeries z =
      rootedTreeWeightedSeries z - rootedTreeSeries z := by
  have ht := rootedTreeTerm_summable hz hzlt
  have hw := rootedTreeWeightedTerm_summable hz hzlt
  calc
    _ = ∑' n, ∑ k ∈ Finset.range (n + 1),
        rootedTreeTerm z k * rootedTreeWeightedTerm z (n - k) :=
      tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ht.norm hw.norm
    _ = ∑' n, (rootedTreeWeightedTerm z n - rootedTreeTerm z n) := by
      apply tsum_congr
      intro n
      exact rootedTreeTerm_convolution z n
    _ = _ := hw.tsum_sub ht

/-- If [z is positive](hyp:hz) and [z < exp(−1)](hyp:hzlt), then
[the rooted-tree series at z is positive](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_pos
lemma rootedTreeSeries_pos {z : ℝ} (hz : 0 < z)
    (hzlt : z < Real.exp (-1)) : 0 < rootedTreeSeries z := by
  have h := (rootedTreeTerm_summable hz.le hzlt).le_tsum 1
    (fun n _ => rootedTreeTerm_nonneg hz.le n)
  have h₁ : rootedTreeTerm z 1 = z := by simp [rootedTreeTerm]
  rw [h₁] at h
  exact hz.trans_le h

/-- If [z is positive](hyp:hz) and [z < exp(−1)](hyp:hzlt), then
[the degree-weighted rooted-tree series at z is positive](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeWeightedSeries_pos
lemma rootedTreeWeightedSeries_pos {z : ℝ} (hz : 0 < z)
    (hzlt : z < Real.exp (-1)) : 0 < rootedTreeWeightedSeries z := by
  have h := (rootedTreeWeightedTerm_summable hz.le hzlt).le_tsum 1
    (fun n _ => rootedTreeWeightedTerm_nonneg hz.le n)
  have h₁ : rootedTreeWeightedTerm z 1 = z := by
    simp [rootedTreeWeightedTerm, rootedTreeTerm]
  rw [h₁] at h
  exact hz.trans_le h

/-- If [z is nonnegative](hyp:hz) and [z < exp(−1)](hyp:hzlt), then
[the rooted-tree series at z is strictly less than one](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_lt_one
lemma rootedTreeSeries_lt_one {z : ℝ} (hz : 0 ≤ z)
    (hzlt : z < Real.exp (-1)) : rootedTreeSeries z < 1 := by
  rcases hz.eq_or_lt with hz0 | hzpos
  · rw [← hz0, rootedTreeSeries_zero]
    norm_num
  have hconv := rootedTreeSeries_convolution hz hzlt
  have ht := rootedTreeSeries_pos hzpos hzlt
  have hw := rootedTreeWeightedSeries_pos hzpos hzlt
  by_contra hn
  have hmul : rootedTreeWeightedSeries z ≤
      rootedTreeSeries z * rootedTreeWeightedSeries z := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_of_not_gt hn) hw.le
  linarith

end Papers.HawkesD75660b.AnalyticBorel
