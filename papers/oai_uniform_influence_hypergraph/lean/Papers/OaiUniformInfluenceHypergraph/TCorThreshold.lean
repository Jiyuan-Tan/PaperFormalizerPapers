module
public import Papers.OaiUniformInfluenceHypergraph.TMain
public import Papers.OaiUniformInfluenceHypergraph.Helpers.RussoMargulis

/-! # Threshold width with the same constant as the variance theorem -/

public section

namespace Papers.OaiUniformInfluenceHypergraph

-- @node: thm:cor-threshold
/-- [For every edge size r at least three and every nonnegative constant C
that bounds variance by C divided by log(n) raised to r/(r − 1) times total edge
influence for all n at least r, all interior biases, and all Boolean responses
invariant under vertex permutations, every increasing nonconstant such response
has threshold width at most 2C divided by log(n) raised to r/(r − 1), times
log((1 − ε)/ε), whenever 0 < ε < 1/2](goal). -/
theorem thresholdWidth_le :
    ∀ (r : ℕ), MainUniformity r →
      ∀ (C : ℝ), 0 ≤ C → -- @realizes C_r(nonnegative main-bound constant)
        (∀ (n : ℕ), MainVertexCount n r → ∀ (p : ℝ), MainBias p →
          ∀ (f : (Edge n r → Bool) → Bool), IsHypergraphProperty f →
            (biasedLaw (Edge n r) p).Var (boolValue f) ≤
              C / Real.log (n : ℝ) ^ captureExponent r * totalEdgeInfluence p f) →
        ∀ (n : ℕ), MainVertexCount n r → ∀ (f : (Edge n r → Bool) → Bool),
          IsHypergraphProperty f → IsIncreasingNontrivial f →
          ∀ (ε : ℝ), ThresholdEpsilon ε →
            thresholdWidth f ε ≤ 2 * C / Real.log (n : ℝ) ^ captureExponent r *
              Real.log ((1 - ε) / ε) := by
  intro r hr C hC hvariance n hn f hf hmono ε hε
  have hCpos : 0 < C := by
    by_contra h
    have hCzero : C = 0 := le_antisymm (not_lt.mp h) hC
    have hp : MainBias (1 / 2 : ℝ) := by constructor <;> norm_num
    have hq := probCurve_interior f hmono (1 / 2) hp
    have hvar := hvariance n hn (1 / 2) hp f hf
    rw [boolean_variance_eq_curve, hCzero] at hvar
    simp only [zero_div, zero_mul] at hvar
    exact (not_le_of_gt (mul_pos hq.1 (sub_pos.mpr hq.2))) hvar
  have hn1 : 1 < (n : ℝ) := by
    have hr3 : 3 ≤ r := hr
    have hrn : r ≤ n := hn
    exact_mod_cast (show 1 < n by omega)
  have hpow : 0 < Real.log (n : ℝ) ^ captureExponent r :=
    Real.rpow_pos_of_pos (Real.log_pos hn1) _
  have hbound := thresholdWidth_le_of_logOdds_derivative_bound f hmono ε hε
    (Real.log (n : ℝ) ^ captureExponent r / C) (div_pos hpow hCpos) (by
      intro p hp
      have hq := probCurve_interior f hmono p hp
      have hvar := hvariance n hn p hp f hf
      rw [boolean_variance_eq_curve] at hvar
      apply (div_le_div_iff₀ hCpos (mul_pos hq.1 (sub_pos.mpr hq.2))).mpr
      have hscaled := (le_div_iff₀ hpow).mp
        (show probCurve f p * (1 - probCurve f p) ≤
          C * totalCoordInfluence p f / Real.log (n : ℝ) ^ captureExponent r by
          simpa only [totalCoordInfluence, totalEdgeInfluence, edgeInfluence,
            div_mul_eq_mul_div] using hvar)
      simpa only [mul_comm] using hscaled)
  convert hbound using 1
  field_simp

end Papers.OaiUniformInfluenceHypergraph
