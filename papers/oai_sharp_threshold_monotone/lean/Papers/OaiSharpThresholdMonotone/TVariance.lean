module
public import Papers.OaiSharpThresholdMonotone.Helpers.ConstantBounds

/-! # The explicit variance bound for every n ≥ 2 and every interior bias -/

public section

open scoped BigOperators

namespace Papers.OaiSharpThresholdMonotone

-- @node: thm:variance
/-- For graphs on [at least two vertices](hyp:hn), if [a Boolean function of the
graph is invariant under vertex relabeling](hyp:hf) and [the independent edge
probability p is strictly between zero and one](hyp:hp), then [the function's
variance is at most its total influence multiplied by 2¹⁷ divided by the square
of the natural logarithm of the vertex count](goal). -/
theorem variance_le_log_sq_inv_mul_totalInfluence (n : ℕ) (p : ℝ)
    (f : (GraphEdge n → Bool) → Bool) (hn : VarianceVertexCount n)
    (hf : VarianceSymmetric f) (hp : VarianceBias p) :
    graphVariance p f ≤ 2 ^ 17 / (Real.log n) ^ 2 * graphTotalInfluence p f := by
  classical
  have hI : 0 ≤ graphTotalInfluence p f := by
    rw [graphTotalInfluence_eq_totalCoordInfluence]
    exact totalCoordInfluence_nonneg p f
  by_cases ht : CaptureLogSize n
  · obtain ⟨hm, _⟩ := capture_block_parameters n ht
    have hm3 : 3 ≤ sqrtBlockSize n := hm.1
    have hk : 0 < lowCutoff p (sqrtBlockSize n) :=
      lowCutoff_pos p _ hp (by exact_mod_cast (show 2 ≤ sqrtBlockSize n by omega))
    have hL : 0 < lowCutoff p (sqrtBlockSize n) ^ 2 / 2 := by positivity
    have hsplit : graphVariance p f ≤
        (∑ S ∈ Finset.univ.filter (fun S : Finset (GraphEdge n) =>
          1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p (sqrtBlockSize n) ^ 2 / 2),
          graphFourierCoeff p f S ^ 2) +
        ∑ S ∈ Finset.univ.filter (fun S : Finset (GraphEdge n) =>
          lowCutoff p (sqrtBlockSize n) ^ 2 / 2 < (S.card : ℝ)),
          fourierCoeff p f S ^ 2 := by
      rw [graphVariance, variance_eq_sum_fourierCoeff_sq p hp]
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S = ∅
      · simp [hS, not_lt_of_ge hL.le]
      · have hc : 1 ≤ S.card := Finset.one_le_card.mpr
          (Finset.nonempty_iff_ne_empty.mpr hS)
        by_cases hcut : (S.card : ℝ) ≤ lowCutoff p (sqrtBlockSize n) ^ 2 / 2
        · simp [hS, hc, hcut, not_lt_of_ge hcut]
        · simp [hS, hc, hcut, lt_of_not_ge hcut]
    have hlo := captured_lowDegree_mass_le p f hp hf ht
    have hhi := spectral_tail_le p _ hp hL f
    rw [← graphTotalInfluence_eq_totalCoordInfluence] at hhi
    have hcoeff : biasScale p ^ 2 / (lowCutoff p (sqrtBlockSize n) ^ 2 / 2) =
        2 * biasScale p ^ 2 / lowCutoff p (sqrtBlockSize n) ^ 2 := by ring
    rw [hcoeff] at hhi
    calc
      graphVariance p f ≤ _ := hsplit.trans (add_le_add hlo hhi)
      _ = (4 * (sqrtBlockSize n : ℝ) ^ (-(1 / 4 : ℝ)) +
          2 * biasScale p ^ 2 / lowCutoff p (sqrtBlockSize n) ^ 2) *
          graphTotalInfluence p f := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (large_vertex_coefficient_bound n ht p hp) hI
  · have hsmall : Real.log (n : ℝ) < 16 := lt_of_not_ge ht
    have hv := variance_le_biasScale_sq_mul_influence p hp f
    rw [← graphTotalInfluence_eq_totalCoordInfluence] at hv
    exact hv.trans (mul_le_mul_of_nonneg_right
      (small_vertex_coefficient_bound n hn hsmall p hp) hI)

end Papers.OaiSharpThresholdMonotone
