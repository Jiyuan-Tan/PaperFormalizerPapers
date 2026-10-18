module
public import Papers.TbsExtremeEffects.Helpers.Hill.VonMises

/-! Exponential-spacing representation of full-input order statistics. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

/-- [The ordered exponential coordinates decrease in the required way](hyp:hY), [the ordered radii admit the given quantile representation](hyp:hR), and [the quantile has the stated tail derivative envelope](hyp:hTail) imply [that every log-radius spacing has the displayed error bound](goal). -/
-- @node: hill_spacing_errors_of_quantile_derivative
lemma hill_spacing_errors_of_quantile_derivative (M : ExtremeModel q d)
    (E : NeteExperiment M) (n k : ℕ) (w : E.Om)
    (Y : ℕ → ℝ) (Q Q' eta : ℝ → ℝ) (g b : ℝ)
    (hY : ∀ j ∈ Finset.Icc 1 k,
      Y (j + 1) ≤ Y j ∧ Y (k + 1) ≤ Y (j + 1))
    (hR : ∀ j ∈ Finset.Icc 1 (k + 1),
      orderedRadius E n w j = Q (Real.exp (Y j)))
    (hTail : ∀ u ≥ Y (k + 1),
      0 < Q (Real.exp u) ∧ HasDerivAt Q (Q' (Real.exp u)) (Real.exp u) ∧
      Real.exp u * Q' (Real.exp u) / Q (Real.exp u) - g = eta (Real.exp u) ∧
      |eta (Real.exp u)| ≤ b) :
    ∀ j ∈ Finset.Icc 1 k,
      |Real.log (orderedRadius E n w j / orderedRadius E n w (j + 1)) -
        g * (Y j - Y (j + 1))| ≤ b * (Y j - Y (j + 1)) := by
  intro j hj
  obtain ⟨horder, hbase⟩ := hY j hj
  have hj' : j ∈ Finset.Icc 1 (k + 1) := by
    obtain ⟨hjl, hjk⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨hjl, by omega⟩
  have hjnext : j + 1 ∈ Finset.Icc 1 (k + 1) := by
    obtain ⟨hjl, hjk⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [hR j hj', hR (j + 1) hjnext,
    Real.log_div (hTail (Y j) (hbase.trans horder)).1.ne'
      (hTail (Y (j + 1)) hbase).1.ne']
  apply hill_log_quantile_increment Q Q' eta g b (Y (j + 1)) (Y j) horder
  · intro u hu
    exact (hTail u (hbase.trans hu)).2.1
  · intro u hu
    exact (hTail u (hbase.trans hu)).1
  · intro u hu
    exact (hTail u (hbase.trans hu)).2.2.1
  · intro u hu
    exact (hTail u (hbase.trans hu)).2.2.2

/-- [A componentwise bound on every increment error](hyp:herror) implies [the corresponding bound for their normalized sum](goal). -/
-- @node: hill_normalized_sum_bias
lemma hill_normalized_sum_bias (k : ℕ) (u v : ℕ → ℝ) (g b : ℝ)
    (herror : ∀ j ∈ Finset.Icc 1 k, |u j - g * v j| ≤ b * v j) :
    |(k : ℝ)⁻¹ * (∑ j ∈ Finset.Icc 1 k, u j) -
      g * ((k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k, v j)| ≤
      b * ((k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k, v j) := by
  have hinv : 0 ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
  calc
    _ = (k : ℝ)⁻¹ * |∑ j ∈ Finset.Icc 1 k, (u j - g * v j)| := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [show (k : ℝ)⁻¹ * (∑ j ∈ Finset.Icc 1 k, u j) -
          g * ((k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k, v j) =
          (k : ℝ)⁻¹ * ((∑ j ∈ Finset.Icc 1 k, u j) -
            g * ∑ j ∈ Finset.Icc 1 k, v j) by ring,
        abs_mul, abs_of_nonneg hinv]
    _ ≤ (k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k, |u j - g * v j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinv
    _ ≤ (k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k, b * v j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum herror) hinv
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- [At least one upper order statistic is used](hyp:hk), [the selected rank is below the sample size](hyp:hkn), [the next ordered radius is positive](hyp:hpos), and [every log-spacing has the stated increment error](hyp:herror) imply [the displayed Hill-statistic bias bound](goal). -/
-- @node: hillStat_bias_of_log_increment_control
lemma hillStat_bias_of_log_increment_control (M : ExtremeModel q d)
    (E : NeteExperiment M) (n k : ℕ) (w : E.Om) (Y : ℕ → ℝ) (g b : ℝ)
    (hk : 1 ≤ k) (hkn : k < n) (hpos : 0 < orderedRadius E n w (k + 1))
    (herror : ∀ j ∈ Finset.Icc 1 k,
      |Real.log (orderedRadius E n w j / orderedRadius E n w (j + 1)) -
        g * (Y j - Y (j + 1))| ≤ b * (Y j - Y (j + 1))) :
    |hillStat E n k w -
      g * ((k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (Y j - Y (j + 1)))| ≤
      b * ((k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (Y j - Y (j + 1))) := by
  rw [hillStat_eq_weighted_spacings E n k w hk hkn hpos]
  apply hill_normalized_sum_bias
  intro j hj
  have hjpos : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  calc
    _ = (j : ℝ) * |Real.log (orderedRadius E n w j / orderedRadius E n w (j + 1)) -
        g * (Y j - Y (j + 1))| := by
      rw [show (j : ℝ) * Real.log (orderedRadius E n w j / orderedRadius E n w (j + 1)) -
          g * ((j : ℝ) * (Y j - Y (j + 1))) =
          (j : ℝ) * (Real.log (orderedRadius E n w j / orderedRadius E n w (j + 1)) -
            g * (Y j - Y (j + 1))) by ring, abs_mul, abs_of_nonneg hjpos]
    _ ≤ (j : ℝ) * (b * (Y j - Y (j + 1))) :=
      mul_le_mul_of_nonneg_left (herror j hj) hjpos
    _ = _ := by ring

/-- [The oracle prefix begins at a positive rank](hyp:hL), [its endpoint lies below the sample size](hyp:hkn), [the endpoint's next radius is positive](hyp:hpos), [each supplied average equals the corresponding weighted sum of adjacent spacings](hyp:hA), and [each log-radius increment differs from its scaled spacing by at most the stated multiple of that spacing](hyp:herror) imply [the Hill statistic differs from the scaled average by at most that multiple at every prefix rank](goal). -/
-- @node: hill_prefix_bias_of_log_increment_control
lemma hill_prefix_bias_of_log_increment_control (M : ExtremeModel q d)
    (E : NeteExperiment M) (n L k : ℕ) (w : E.Om) (Y A : ℕ → ℝ) (g b : ℝ)
    (hL : 1 ≤ L) (hkn : k < n) (hpos : 0 < orderedRadius E n w (k + 1))
    (hA : ∀ i ∈ Finset.Icc L k,
      A i = (i : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 i, (j : ℝ) * (Y j - Y (j + 1)))
    (herror : ∀ j ∈ Finset.Icc 1 k,
      |Real.log (orderedRadius E n w j / orderedRadius E n w (j + 1)) -
        g * (Y j - Y (j + 1))| ≤ b * (Y j - Y (j + 1))) :
    ∀ i ∈ Finset.Icc L k, |hillStat E n i w - g * A i| ≤ b * A i := by
  intro i hi
  obtain ⟨hli, hik⟩ := Finset.mem_Icc.mp hi
  have hipos : 0 < orderedRadius E n w (i + 1) :=
    hpos.trans_le (orderedRadius_antitone_on_ranks E n w (by omega) (by omega) (by omega))
  rw [hA i hi]
  apply hillStat_bias_of_log_increment_control M E n i w Y g b
    (hL.trans hli) (hik.trans_lt hkn) hipos
  intro j hj
  exact herror j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
    (Finset.mem_Icc.mp hj).2.trans hik⟩)

end Papers.TbsExtremeEffects
