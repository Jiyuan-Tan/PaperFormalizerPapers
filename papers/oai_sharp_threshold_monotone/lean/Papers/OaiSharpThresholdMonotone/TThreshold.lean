module
public import Papers.OaiSharpThresholdMonotone.TVariance
public import Papers.OaiSharpThresholdMonotone.Helpers.RussoMargulis

/-! # The explicit threshold width for the full printed epsilon range -/

public section

namespace Papers.OaiSharpThresholdMonotone

-- @node: logOdds_derivative_lower_bound
/-- For graphs on [at least two vertices](hyp:hn), suppose [the graph property is
invariant under vertex relabeling, increasing under edge addition, and nonempty
and proper](hyp:hP), and [the independent edge probability p is strictly between
zero and one](hyp:hp). Then [the total influence of the property's indicator,
divided by the product of its probability and one minus that probability, is at
least the square of the natural logarithm of the vertex count divided by
2¹⁷](goal). -/
lemma logOdds_derivative_lower_bound (n : ℕ) (P : Set (GraphConfig n))
    (hn : ThresholdVertexCount n) (hP : ThresholdProperty P)
    (p : ℝ) (hp : BiasInterior p) :
    (Real.log n) ^ 2 / 2 ^ 17 ≤
      graphTotalInfluence p (propertyIndicator P) /
        (propertyProb p P * (1 - propertyProb p P)) := by
  have hμ := propertyProb_interior P hP p hp
  have hpos : 0 < propertyProb p P * (1 - propertyProb p P) :=
    mul_pos hμ.1 (sub_pos.mpr hμ.2)
  have hv := variance_le_log_sq_inv_mul_totalInfluence n p (propertyIndicator P)
    hn (propertyIndicator_symmetric P hP.1) hp
  rw [graphVariance_indicator_eq] at hv
  have ht := sq_pos_of_pos (log_vertex_count_pos n hn)
  apply (le_div_iff₀ hpos).mpr
  have hv' := (le_div_iff₀ ht).mp (show propertyProb p P * (1 - propertyProb p P) ≤
      (2 ^ 17 * graphTotalInfluence p (propertyIndicator P)) / (Real.log n) ^ 2 by
    simpa [div_mul_eq_mul_div] using hv)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 17)).mpr
  nlinarith


-- @node: thm:threshold
/-- For graphs on [at least two vertices](hyp:hn) and [a nonempty, proper graph
property invariant under vertex relabeling and increasing under edge
addition](hyp:hP), if [ε is strictly between zero and one half](hyp:hε), then
[the difference between the edge-probability quantiles at levels 1 − ε and ε is
at most 2¹⁹ divided by the square of the natural logarithm of the vertex count,
multiplied by the natural logarithm of 1/(2ε)](goal). -/
theorem propertyQuantile_width_le (n : ℕ) (P : Set (GraphEdge n → Bool)) (ε : ℝ)
    (hn : ThresholdVertexCount n) (hP : ThresholdProperty P) (hε : ThresholdEpsilon ε) :
    propertyQuantile (1 - ε) P - propertyQuantile ε P ≤
      2 ^ 19 / (Real.log n) ^ 2 * Real.log (1 / (2 * ε)) := by
  have ht : 0 < (Real.log (n : ℝ)) ^ 2 := sq_pos_of_pos (log_vertex_count_pos n hn)
  have hA : 0 < (Real.log (n : ℝ)) ^ 2 / 2 ^ 17 := by positivity
  have hw := quantile_width_le_of_logOdds_derivative_bound P hP ε hε
    ((Real.log n) ^ 2 / 2 ^ 17) hA
    (fun p hp => logOdds_derivative_lower_bound n P hn hP p hp)
  calc
    _ ≤ _ := hw
    _ ≤ 2 / ((Real.log n) ^ 2 / 2 ^ 17) *
        (2 * Real.log (1 / (2 * ε))) :=
      mul_le_mul_of_nonneg_left (threshold_logarithm_bound ε hε) (by positivity)
    _ = _ := by field_simp

end Papers.OaiSharpThresholdMonotone
