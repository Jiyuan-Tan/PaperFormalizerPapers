module
public import Papers.OaiSharpThresholdMonotone.Helpers.Capture

/-! # Captured Fourier mass at the literal cutoff k²/2 -/

public section

open scoped BigOperators

namespace Papers.OaiSharpThresholdMonotone

-- @node: lem:block-capture
/-- For [an edge probability strictly between zero and one](hyp:hp) and
[a graph function invariant under vertex relabeling](hyp:hf), suppose
[the natural logarithm of the vertex count is at least 16](hyp:hn). Then
[the Fourier mass on nonempty edge sets of size at most half the square of the
low-degree cutoff for blocks of size floor √n is at most four times that block size
to the power −1/4 times the total influence](goal). -/
lemma captured_lowDegree_mass_le {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (hp : BiasInterior p) (hf : GraphSymmetric f) (hn : CaptureLogSize n) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (GraphEdge n) =>
      1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p (sqrtBlockSize n) ^ 2 / 2),
      graphFourierCoeff p f S ^ 2 ≤
      4 * (sqrtBlockSize n : ℝ) ^ (-(1 / 4 : ℝ)) * graphTotalInfluence p f := by
  classical
  let m := sqrtBlockSize n
  let π := blockLaw n m (sqrtBlockSize_le n)
  let D := Finset.univ.filter (fun S : Finset (GraphEdge n) =>
    1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p m ^ 2 / 2)
  have hm := (capture_block_parameters n hn).1
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hm.1)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (hm.1.trans hm.2))
  have hmass : (m : ℝ) / (2 * n) * ∑ S ∈ D, graphFourierCoeff p f S ^ 2 ≤
      2 * (m : ℝ) / n * (m : ℝ) ^ (-(1 / 4 : ℝ)) * graphTotalInfluence p f := by
    calc
      _ = ∑ S ∈ D, (m : ℝ) / (2 * n) * graphFourierCoeff p f S ^ 2 :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ S ∈ D, π.Pr (fun B => 1 ≤ (S ∩ freeEdges B.val).card ∧
          ((S ∩ freeEdges B.val).card : ℝ) ≤ lowCutoff p m) *
            graphFourierCoeff p f S ^ 2 := by
        apply Finset.sum_le_sum
        intro S hS
        exact mul_le_mul_of_nonneg_right
          (block_capture_probability_ge n hn p hp S (Finset.mem_filter.mp hS).2)
          (sq_nonneg _)
      _ ≤ ∑ S : Finset (GraphEdge n), π.Pr
          (fun B => 1 ≤ (S ∩ freeEdges B.val).card ∧
            ((S ∩ freeEdges B.val).card : ℝ) ≤ lowCutoff p m) *
              graphFourierCoeff p f S ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro S _ _
        exact mul_nonneg (π.Pr_nonneg _) (sq_nonneg _)
      _ ≤ _ := block_average_lowDegree_mass_le p f π hp hf hm
        (blockLaw_uniform (sqrtBlockSize_le n))
  have hcancel : 2 * (m : ℝ) / n * (m : ℝ) ^ (-(1 / 4 : ℝ)) *
      graphTotalInfluence p f = (m : ℝ) / (2 * n) *
        (4 * (m : ℝ) ^ (-(1 / 4 : ℝ)) * graphTotalInfluence p f) := by ring
  rw [hcancel] at hmass
  exact (mul_le_mul_iff_right₀ (div_pos hmpos (by positivity))).mp hmass

end Papers.OaiSharpThresholdMonotone
