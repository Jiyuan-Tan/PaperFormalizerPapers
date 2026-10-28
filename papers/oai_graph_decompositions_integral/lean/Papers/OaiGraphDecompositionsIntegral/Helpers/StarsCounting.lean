module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.QLower
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsQuantities

/-! # The numerical consequence of a uniform star-copy cover

At an expectation threshold below one, every cover has cost at least one half.
Applied to the uniform cover by equal-size star forests, this gives the
counting inequality without taking fractional powers.
-/

public section

open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

/-- If [the source graph has an edge](hyp:hedge), [its vertex count is at
most n](hyp:hsize), [its expectation threshold on n vertices is below
one](hyp:hq), and [a finite family covers all host edge sets containing a
copy of the source](hyp:hC), then [the family's cover polynomial evaluated
at that threshold is at least one half](goal). -/
-- @node: coverCost_at_expectationThreshold_ge
lemma coverCost_at_expectationThreshold_ge (J : SimpleGraph V) (n : ℕ)
    (hedge : J.edgeSet.Nonempty) (hsize : Fintype.card V ≤ n)
    (hq : expectationThreshold J n < 1) (C : Finset (Finset (KEdge n)))
    (hC : Covers C (containmentFamily J n)) :
    (1 / 2 : ℝ) ≤ coverPolynomial C (expectationThreshold J n) := by
  classical
  let q := expectationThreshold J n
  have hmax := expectationThresholdRaw_isGreatest J n hedge hsize
  have hne : J.edgeSet ≠ ∅ := Set.nonempty_iff_ne_empty.mp hedge
  have hqraw : q = expectationThresholdRaw J n := by
    simp [q, expectationThreshold, hne]
  have hqnonneg : 0 ≤ q := by rw [hqraw]; exact hmax.1.1.1
  by_contra hcost
  have hslack : 0 < 1 / 2 - coverPolynomial C q := by dsimp [q]; linarith
  have hcont : Continuous (coverPolynomial C) := by unfold coverPolynomial; fun_prop
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
    (1 / 2 - coverPolynomial C q) hslack
  let t := min (δ / 2) ((1 - q) / 2)
  have ht : 0 < t := lt_min (by linarith) (by dsimp [q]; linarith)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htq : q + t ≤ 1 := by
    have := min_le_right (δ / 2) ((1 - q) / 2)
    dsimp [t] at *
    linarith
  have hdist : dist (q + t) q < δ := by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
  have hc := hclose hdist
  rw [Real.dist_eq] at hc
  have hcp : coverPolynomial C (q + t) ≤ 1 / 2 := by
    have := (abs_lt.mp hc).2
    linarith
  have hle := hmax.2 ⟨⟨by linarith, htq⟩, C, hC, ⟨by linarith, htq⟩, hcp⟩
  rw [← hqraw] at hle
  linarith

/-- [For every nonnegative integer m, m factorial is at least the m-th power
of m divided by Euler's number](goal). -/
-- @node: star_factorial_lower
lemma star_factorial_lower (m : ℕ) :
    ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (m : ℝ) (by positivity) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have he : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    simpa using Real.exp_nat_mul 1 m
  rw [he] at h
  rw [div_pow]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < Real.exp 1 ^ m)).mpr
  have := (div_le_iff₀ hf).mp h
  nlinarith

/-- Suppose [the source graph has an edge](hyp:hedge), [its vertex count is
at most n](hyp:hsize), and [its expectation threshold on n vertices is below
one](hyp:hq). If [a finite family covers all copies of the source](hyp:hC),
[each member has k edges](hyp:hk), and [the family has at most b members](hyp:hcount),
then [b times the k-th power of the expectation threshold is at least one half](goal). -/
-- @node: uniform_cover_power_lower
lemma uniform_cover_power_lower (J : SimpleGraph V) (n k : ℕ)
    (hedge : J.edgeSet.Nonempty) (hsize : Fintype.card V ≤ n)
    (hq : expectationThreshold J n < 1) (C : Finset (Finset (KEdge n)))
    (hC : Covers C (containmentFamily J n)) (hk : ∀ E ∈ C, E.card = k)
    (b : ℝ) (hcount : (C.card : ℝ) ≤ b) :
    (1 / 2 : ℝ) ≤ b * expectationThreshold J n ^ k := by
  classical
  have hnonneg : 0 ≤ expectationThreshold J n := by
    have h := (expectationThresholdRaw_isGreatest J n hedge hsize).1.1.1
    simpa [expectationThreshold, Set.nonempty_iff_ne_empty.mp hedge] using h
  calc
    (1 / 2 : ℝ) ≤ coverPolynomial C (expectationThreshold J n) :=
      coverCost_at_expectationThreshold_ge J n hedge hsize hq C hC
    _ = (C.card : ℝ) * expectationThreshold J n ^ k := by
      unfold coverPolynomial
      simp_rw [Finset.sum_congr rfl (fun E hE =>
        congrArg (fun j => expectationThreshold J n ^ j) (hk E hE))]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (pow_nonneg hnonneg _)

/-- If [m is positive](hyp:hm), then [the m-th power of m divided by twice
Euler's number is at most one half of m factorial](goal). -/
-- @node: star_factorial_lower_half
lemma star_factorial_lower_half (m : ℕ) (hm : 0 < m) :
    ((m : ℝ) / (2 * Real.exp 1)) ^ m ≤ (m.factorial : ℝ) / 2 := by
  have htwo : (2 : ℝ) ≤ 2 ^ m := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm)
  calc
    ((m : ℝ) / (2 * Real.exp 1)) ^ m =
        (((m : ℝ) / Real.exp 1) ^ m) / 2 ^ m := by
      rw [← div_pow]
      congr 1
      ring
    _ ≤ (m.factorial : ℝ) / 2 ^ m :=
      div_le_div_of_nonneg_right (star_factorial_lower m) (by positivity)
    _ ≤ (m.factorial : ℝ) / 2 := by gcongr

/-- Suppose [the source graph has an edge](hyp:hedge), [its vertex count is
at most n](hyp:hsize), [n is positive](hyp:hn), [m is positive](hyp:hm), and
[its expectation threshold on n vertices is below one](hyp:hq). If [a finite
family covers all copies of the source](hyp:hC), [every member has m times
ell edges](hyp:hk), and [the number of members is at most the star copy-count
bound for n, ell, and m](hyp:hcount), then [the ell-th power of the expectation
threshold is at least ell factorial divided by n to the power ell plus one,
multiplied by m divided by twice Euler's number](goal). -/
-- @node: star_count_lower_of_cover
lemma star_count_lower_of_cover (J : SimpleGraph V) (n ell m : ℕ)
    (hedge : J.edgeSet.Nonempty) (hsize : Fintype.card V ≤ n)
    (hn : 0 < n) (hm : 0 < m) (hq : expectationThreshold J n < 1)
    (C : Finset (Finset (KEdge n)))
    (hC : Covers C (containmentFamily J n))
    (hk : ∀ E ∈ C, E.card = m * ell)
    (hcount : (C.card : ℝ) ≤ starCopyCountBound n ell m) :
    (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
        ((m : ℝ) / (2 * Real.exp 1)) ≤ expectationThreshold J n ^ ell := by
  have hpower := uniform_cover_power_lower J n (m * ell) hedge hsize hq C hC hk
    (starCopyCountBound n ell m) hcount
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < ell.factorial := by exact_mod_cast Nat.factorial_pos ell
  have hmf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hboundpos : 0 < starCopyCountBound n ell m := by
    unfold starCopyCountBound
    positivity
  have hnonneg : 0 ≤ expectationThreshold J n := by
    classical
    have h := (expectationThresholdRaw_isGreatest J n hedge hsize).1.1.1
    simpa [expectationThreshold, Set.nonempty_iff_ne_empty.mp hedge] using h
  apply le_of_pow_le_pow_left₀ (Nat.ne_of_gt hm) (pow_nonneg hnonneg ell)
  apply (mul_le_mul_iff_right₀ hboundpos).mp
  rw [← pow_mul, Nat.mul_comm ell m]
  calc
    starCopyCountBound n ell m *
        ((ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
          ((m : ℝ) / (2 * Real.exp 1))) ^ m =
        (((m : ℝ) / (2 * Real.exp 1)) ^ m) / m.factorial := by
      unfold starCopyCountBound
      rw [mul_pow, div_pow, ← pow_mul]
      rw [Nat.mul_comm (ell + 1) m]
      field_simp
    _ ≤ 1 / 2 := (div_le_iff₀ hmf).mpr (by
      have := star_factorial_lower_half m hm
      linarith)
    _ ≤ _ := hpower

end Papers.OaiGraphDecompositionsIntegral
