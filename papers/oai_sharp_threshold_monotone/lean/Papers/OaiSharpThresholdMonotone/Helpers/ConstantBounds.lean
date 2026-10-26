module
public import Papers.OaiSharpThresholdMonotone.Helpers.BlockCapture

/-! # Explicit bounds for the small- and large-vertex branches

All constants are numerical and all bias cancellation is proved locally.
-/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

-- @node: log_vertex_count_pos
/-- If [the vertex count is at least two](hyp:hn), then
[its natural logarithm is positive](goal). -/
lemma log_vertex_count_pos (n : ℕ) (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) := by
  apply Real.log_pos
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

-- @node: lowCutoff_pos
/-- If [the edge probability lies strictly between zero and one](hyp:hp) and
[the real block-size parameter m is at least two](hyp:hm), then
[the low-degree cutoff √(p(1−p)) log(m)/64 is positive](goal). -/
lemma lowCutoff_pos (p m : ℝ) (hp : BiasInterior p) (hm : 2 ≤ m) :
    0 < lowCutoff p m := by
  unfold lowCutoff
  exact div_pos (mul_pos (biasScale_pos_le_half p hp).1
    (Real.log_pos (by linarith))) (by norm_num)

-- @node: spectral_tail_le
/-- For [a Boolean-valued function h on a finite set of binary coordinates](hyp:h),
if [the coordinate probability p lies strictly between zero and one](hyp:hp) and
[the degree threshold L is positive](hyp:hL), then
[the sum of squared Fourier coefficients of degree greater than L is at most
p(1−p)/L times the total coordinate influence of h](goal). -/
lemma spectral_tail_le {J : Type*} [Fintype J] [DecidableEq J]
    (p L : ℝ) (hp : BiasInterior p) (hL : 0 < L) (h : (J → Bool) → Bool) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset J => L < (S.card : ℝ)),
      fourierCoeff p h S ^ 2 ≤ biasScale p ^ 2 / L * totalCoordInfluence p h := by
  classical
  calc
    _ ≤ weightedSpectralMass p h / L := by
      apply (le_div_iff₀ hL).mpr
      rw [Finset.sum_mul]
      calc
        _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset J => L < (S.card : ℝ)),
            (S.card : ℝ) * fourierCoeff p h S ^ 2 := by
          apply Finset.sum_le_sum
          intro S hS
          have hc := (Finset.mem_filter.mp hS).2.le
          simpa [mul_comm] using mul_le_mul_of_nonneg_right hc
            (sq_nonneg (fourierCoeff p h S))
        _ ≤ weightedSpectralMass p h := by
          unfold weightedSpectralMass
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro S _ _
          exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    _ = _ := by rw [weightedSpectralMass_eq p hp]; ring

-- @node: captured_coefficient_bound
/-- If [the natural logarithm of the vertex count n is at least 16](hyp:hn), then
[four times floor √n to the power −1/4 is at most 2 to the power 15 divided by
the square of log n](goal). -/
lemma captured_coefficient_bound (n : ℕ) (hn : CaptureLogSize n) :
    4 * (sqrtBlockSize n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      2 ^ 15 / (Real.log n) ^ 2 := by
  obtain ⟨hm, hlog⟩ := capture_block_parameters n hn
  have hmpos : (0 : ℝ) < sqrtBlockSize n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hm.1)
  have ht : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) hn
  have hpow := Real.log_le_rpow_div hmpos.le (by norm_num : (0 : ℝ) < 1 / 8)
  have hlog0 : 0 ≤ Real.log (sqrtBlockSize n : ℝ) :=
    le_trans (by positivity) hlog
  have hsq : (Real.log (n : ℝ)) ^ 2 ≤
      576 * ((sqrtBlockSize n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := by
    have hbound : Real.log (n : ℝ) ≤
        24 * (sqrtBlockSize n : ℝ) ^ (1 / 8 : ℝ) := by linarith
    nlinarith [Real.rpow_pos_of_pos hmpos (1 / 8 : ℝ)]
  have hcancel : ((sqrtBlockSize n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 *
      (sqrtBlockSize n : ℝ) ^ (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le, ← Real.rpow_add hmpos]
    norm_num
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  have hmul := mul_le_mul_of_nonneg_right hsq
    (Real.rpow_nonneg hmpos.le (-(1 / 4 : ℝ)))
  nlinarith [hcancel]

-- @node: bias_cancellation_eq
/-- If [the edge probability p lies strictly between zero and one](hyp:hp) and
[the real block-size parameter m is at least two](hyp:hm), then
[twice p(1−p) divided by the square of the low-degree cutoff at m equals
2 to the power 13 divided by the square of log m](goal). -/
lemma bias_cancellation_eq (p m : ℝ) (hp : BiasInterior p) (hm : 2 ≤ m) :
    2 * biasScale p ^ 2 / lowCutoff p m ^ 2 = 2 ^ 13 / (Real.log m) ^ 2 := by
  have hσ : biasScale p ≠ 0 := (biasScale_pos_le_half p hp).1.ne'
  have hlog : Real.log m ≠ 0 := (Real.log_pos (by linarith : 1 < m)).ne'
  unfold lowCutoff
  field_simp
  ring

-- @node: bias_cancellation_le
/-- If [the natural logarithm of the vertex count n is at least 16](hyp:hn) and
[the edge probability p lies strictly between zero and one](hyp:hp), then
[twice p(1−p) divided by the square of the low-degree cutoff for blocks of size
floor √n is at most nine times 2 to the power 13 divided by the square of log n](goal). -/
lemma bias_cancellation_le (n : ℕ) (hn : CaptureLogSize n) (p : ℝ) (hp : BiasInterior p) :
    2 * biasScale p ^ 2 / lowCutoff p (sqrtBlockSize n) ^ 2 ≤
      9 * 2 ^ 13 / (Real.log n) ^ 2 := by
  obtain ⟨hm, hlog⟩ := capture_block_parameters n hn
  have hm2 : (2 : ℝ) ≤ sqrtBlockSize n := by
    exact_mod_cast (le_trans (by norm_num : 2 ≤ 3) hm.1)
  rw [bias_cancellation_eq p (sqrtBlockSize n) hp hm2]
  have ht : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) hn
  have hmlog : 0 < Real.log (sqrtBlockSize n : ℝ) :=
    lt_of_lt_of_le (by positivity) hlog
  apply (div_le_div_iff₀ (sq_pos_of_pos hmlog) (sq_pos_of_pos ht)).mpr
  have : Real.log (n : ℝ) ^ 2 ≤ 9 * Real.log (sqrtBlockSize n : ℝ) ^ 2 := by
    nlinarith
  nlinarith

-- @node: large_vertex_coefficient_bound
/-- If [the natural logarithm of the vertex count n is at least 16](hyp:hn) and
[the edge probability p lies strictly between zero and one](hyp:hp), then
[the sum of four times floor √n to the power −1/4 and twice p(1−p) divided by the
squared low-degree cutoff for blocks of size floor √n is at most 2 to the power 17
divided by the square of log n](goal). -/
lemma large_vertex_coefficient_bound (n : ℕ) (hn : CaptureLogSize n)
    (p : ℝ) (hp : BiasInterior p) :
    4 * (sqrtBlockSize n : ℝ) ^ (-(1 / 4 : ℝ)) +
      2 * biasScale p ^ 2 / lowCutoff p (sqrtBlockSize n) ^ 2 ≤
      2 ^ 17 / (Real.log n) ^ 2 := by -- @realizes C_0(literal constant 2^17)
  calc
    _ ≤ 2 ^ 15 / (Real.log n) ^ 2 + 9 * 2 ^ 13 / (Real.log n) ^ 2 :=
      add_le_add (captured_coefficient_bound n hn) (bias_cancellation_le n hn p hp)
    _ = (2 ^ 15 + 9 * 2 ^ 13) / (Real.log n) ^ 2 := by ring
    _ ≤ 2 ^ 17 / (Real.log n) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      norm_num

-- @node: small_vertex_coefficient_bound
/-- If [the vertex count n is at least two](hyp:hn),
[its natural logarithm is less than 16](hyp:hlog), and
[the edge probability p lies strictly between zero and one](hyp:hp), then
[the Bernoulli variance p(1−p) is at most 2 to the power 17 divided by the square
of log n](goal). -/
lemma small_vertex_coefficient_bound (n : ℕ) (hn : 2 ≤ n)
    (hlog : Real.log (n : ℝ) < 16) (p : ℝ) (hp : BiasInterior p) :
    biasScale p ^ 2 ≤ 2 ^ 17 / (Real.log n) ^ 2 := by
  have hlog := log_vertex_count_pos n hn
  obtain ⟨hσ, hσle⟩ := biasScale_pos_le_half p hp
  have hs : biasScale p ^ 2 ≤ 1 / 4 := by nlinarith
  have ht : (Real.log n) ^ 2 ≤ 256 := by nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
  calc
    _ ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 :=
      mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ ≤ (1 / 4 : ℝ) * 256 := mul_le_mul_of_nonneg_left ht (by norm_num)
    _ ≤ 2 ^ 17 := by norm_num

end Papers.OaiSharpThresholdMonotone
