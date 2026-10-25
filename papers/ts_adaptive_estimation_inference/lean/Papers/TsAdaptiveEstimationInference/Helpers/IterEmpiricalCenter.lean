module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVFixedCenter
/-! Deterministic transport from fixed population centers to fitted centers.
The empirical identities use the original representatives and observations.
No concentration or measurability assertion is supplied by these lemmas. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld W X Z) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

-- @node: iter_empirical_norms_of_squared_comparisons
/-- Suppose [K is nonnegative](hyp:hK), [r is nonnegative](hyp:hr), [the candidate sequence starts at zero](hyp:hzero), and [at each positive stage through t the absolute discrepancy between empirical and population squared error is at most K times r times the error norm plus r squared](hyp:hcomparison). [At every stage through t, the empirical error norm is at most K+1 times the sum of the population error norm and r](goal). -/
lemma iter_empirical_norms_of_squared_comparisons (n t : ℕ) (ω : Ω)
    (K r lam : ℝ) (candidate : ℕ → V.Hbar.toSubmodule)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hzero : candidate 0 = 0)
    (hcomparison : ∀ k, 1 ≤ k → k ≤ t →
      |primalEmpDistanceSq V P sample split n ω (candidate k)
          (populationIterate V lam k) -
        ‖candidate k - populationIterate V lam k‖ ^ 2| ≤
        K * (r * ‖candidate k - populationIterate V lam k‖ + r ^ 2)) :
    ∀ k, k ≤ t →
      Real.sqrt (primalEmpDistanceSq V P sample split n ω (candidate k)
          (populationIterate V lam k)) ≤
        (K + 1) * (‖candidate k - populationIterate V lam k‖ + r) := by
  intro k hkt
  cases k with
  | zero =>
      simp only [hzero, populationIterate, sub_self, norm_zero, zero_add,
        primalEmpDistanceSq, sub_self, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, blockAverage, Finset.sum_const_zero,
        mul_zero, Real.sqrt_zero]
      positivity
  | succ k =>
      exact iter_rdiv_empirical_norm_of_comparison V P sample split n ω K r
        (candidate (k + 1)) (populationIterate V lam (k + 1)) hK hr
        (hcomparison (k + 1) (by omega) hkt)

-- @node: iter_empirical_center_change_abs_le
/-- For [a candidate h](hyp:h), a comparator a, and two centers, [the absolute change in the empirical squared-distance difference between a and h when the center changes is at most twice the empirical distance between h and a times the empirical distance between the centers](goal). -/
lemma iter_empirical_center_change_abs_le (n : ℕ) (ω : Ω)
    (h a previous center : V.Hbar.toSubmodule) :
    |(primalEmpDistanceSq V P sample split n ω a previous -
        primalEmpDistanceSq V P sample split n ω h previous) -
      (primalEmpDistanceSq V P sample split n ω a center -
        primalEmpDistanceSq V P sample split n ω h center)| ≤
      2 * Real.sqrt (primalEmpDistanceSq V P sample split n ω h a) *
        Real.sqrt (primalEmpDistanceSq V P sample split n ω previous center) := by
  have hid := iter_rdiv_empirical_center_identity V P sample split n ω h a center previous
  have hid' := iter_rdiv_empirical_center_identity V P sample split n ω a h center previous
  have hc := iter_rdiv_empirical_cross_le V P sample split n ω h a previous center
  have hc' := iter_rdiv_empirical_cross_le V P sample split n ω a h previous center
  have hsym : primalEmpDistanceSq V P sample split n ω a h =
      primalEmpDistanceSq V P sample split n ω h a := by
    unfold primalEmpDistanceSq
    congr 1
    funext w
    ring
  rw [hsym] at hc'
  apply abs_le.mpr
  constructor <;> nlinarith only [hid, hid', hc, hc']

-- @node: iter_empirical_center_comparison
/-- For [a candidate h](hyp:h), suppose [K is nonnegative](hyp:hK), [r is nonnegative](hyp:hr), [the fixed-center quadratic increment differs from its population counterpart by at most K times the sum of r times the current error norm and r squared](hyp:hfixed), [the current empirical error norm is at most K times its population norm plus r](hyp:hcurrent), and [the empirical center error norm has the same bound](hyp:hprevious). [The random-center quadratic increment differs from the fixed-center population increment by at most K+2K² times the sum of r times the two error norms, r squared, and their product](goal). -/
lemma iter_empirical_center_comparison (n : ℕ) (ω : Ω) (K r : ℝ)
    (h a previous center : V.Hbar.toSubmodule) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hfixed : |(primalEmpDistanceSq V P sample split n ω a center -
        primalEmpDistanceSq V P sample split n ω h center) -
      (‖a - center‖ ^ 2 - ‖h - center‖ ^ 2)| ≤ K * (r * ‖h - a‖ + r ^ 2))
    (hcurrent : Real.sqrt (primalEmpDistanceSq V P sample split n ω h a) ≤
      K * (‖h - a‖ + r))
    (hprevious : Real.sqrt (primalEmpDistanceSq V P sample split n ω previous center) ≤
      K * (‖previous - center‖ + r)) :
    |(primalEmpDistanceSq V P sample split n ω a previous -
        primalEmpDistanceSq V P sample split n ω h previous) -
      (‖a - center‖ ^ 2 - ‖h - center‖ ^ 2)| ≤
      (K + 2 * K ^ 2) * (r * (‖h - a‖ + ‖previous - center‖) + r ^ 2 +
        ‖h - a‖ * ‖previous - center‖) := by
  have hc := iter_empirical_center_change_abs_le V P sample split n ω h a previous center
  have hm := mul_le_mul hcurrent hprevious (Real.sqrt_nonneg _)
    (mul_nonneg hK (by positivity : 0 ≤ ‖h - a‖ + r))
  have htriangle := abs_add_le
    ((primalEmpDistanceSq V P sample split n ω a previous -
      primalEmpDistanceSq V P sample split n ω h previous) -
      (primalEmpDistanceSq V P sample split n ω a center -
        primalEmpDistanceSq V P sample split n ω h center))
    ((primalEmpDistanceSq V P sample split n ω a center -
      primalEmpDistanceSq V P sample split n ω h center) -
      (‖a - center‖ ^ 2 - ‖h - center‖ ^ 2))
  rw [sub_add_sub_cancel] at htriangle
  have hrest : 0 ≤ K * (r * ‖previous - center‖ +
      ‖h - a‖ * ‖previous - center‖) := by positivity
  nlinarith only [htriangle, hc, hm, hfixed, hrest]

-- @node: iter_empirical_center_comparison_of_squared_comparisons
/-- Suppose [K is nonnegative](hyp:hK), [r is nonnegative](hyp:hr), [j does not exceed the horizon t](hyp:hjt), [the candidate starts at zero](hyp:hzero), [every positive-stage empirical squared error through t differs from its population counterpart by at most K times the sum of r times the error norm and r squared](hyp:hcomparison), and [the fixed-center quadratic increment at stage j obeys the analogous comparison](hyp:hfixed). [Replacing the previous population center by the previous candidate gives a quadratic-increment comparison bounded by (K+1)+2(K+1)² times the sum of r times the current and previous error norms, r squared, and the product of those norms](goal). -/
lemma iter_empirical_center_comparison_of_squared_comparisons
    (n t j : ℕ) (ω : Ω) (K r lam : ℝ)
    (candidate : ℕ → V.Hbar.toSubmodule)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hjt : j ≤ t) (hzero : candidate 0 = 0)
    (hcomparison : ∀ k, 1 ≤ k → k ≤ t →
      |primalEmpDistanceSq V P sample split n ω (candidate k)
          (populationIterate V lam k) -
        ‖candidate k - populationIterate V lam k‖ ^ 2| ≤
        K * (r * ‖candidate k - populationIterate V lam k‖ + r ^ 2))
    (hfixed : |(primalEmpDistanceSq V P sample split n ω
          (populationIterate V lam j) (populationIterate V lam (j - 1)) -
        primalEmpDistanceSq V P sample split n ω (candidate j)
          (populationIterate V lam (j - 1))) -
      (‖populationIterate V lam j - populationIterate V lam (j - 1)‖ ^ 2 -
        ‖candidate j - populationIterate V lam (j - 1)‖ ^ 2)| ≤
        K * (r * ‖candidate j - populationIterate V lam j‖ + r ^ 2)) :
    |(primalEmpDistanceSq V P sample split n ω (populationIterate V lam j)
          (candidate (j - 1)) -
        primalEmpDistanceSq V P sample split n ω (candidate j) (candidate (j - 1))) -
      (‖populationIterate V lam j - populationIterate V lam (j - 1)‖ ^ 2 -
        ‖candidate j - populationIterate V lam (j - 1)‖ ^ 2)| ≤
      ((K + 1) + 2 * (K + 1) ^ 2) *
        (r * (‖candidate j - populationIterate V lam j‖ +
          ‖candidate (j - 1) - populationIterate V lam (j - 1)‖) + r ^ 2 +
          ‖candidate j - populationIterate V lam j‖ *
            ‖candidate (j - 1) - populationIterate V lam (j - 1)‖) := by
  have hnorms := iter_empirical_norms_of_squared_comparisons V P sample split
    n t ω K r lam candidate hK hr hzero hcomparison
  apply iter_empirical_center_comparison V P sample split n ω (K + 1) r
    (candidate j) (populationIterate V lam j) (candidate (j - 1))
    (populationIterate V lam (j - 1)) (by positivity) hr
    (hfixed.trans (mul_le_mul_of_nonneg_right
      (show K ≤ K + 1 by linarith) (by positivity)))
    (hnorms j hjt) (hnorms (j - 1) (by omega))

end Papers.TsAdaptiveEstimationInference
