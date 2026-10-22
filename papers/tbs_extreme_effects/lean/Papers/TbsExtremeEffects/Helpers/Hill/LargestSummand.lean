module
public import Papers.TbsExtremeEffects.Helpers.Hill.Convolution

/-! Pointwise and integrability bounds for the largest-summand partition. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped BigOperators
open Classical

/-- If [all summands are nonnegative](hyp:hW) and [their sum excluding the selected term is at most half the residual](hyp:hnear), then [each remaining summand is no larger than that residual](goal).
-/
-- @node: hill_largest_summand_near
lemma hill_largest_summand_near {m : ℕ} (W : Fin m → ℝ) (i : Fin m)
    {r : ℝ} (hW : ∀ j, 0 ≤ W j)
    (hnear : (∑ j ∈ Finset.univ.erase i, W j) ≤ r / 2) :
    ∀ j ∈ Finset.univ.erase i, W j ≤ r - ∑ l ∈ Finset.univ.erase i, W l := by
  intro j hj
  have hsingle := Finset.single_le_sum (fun l _ => hW l) hj
  linarith

/-- If [every nonselected summand is no larger than the residual](hyp:hmax), then [the residual is at least the residual divided by the number of summands](goal).
-/
-- @node: hill_largest_summand_residual_ge
lemma hill_largest_summand_residual_ge {m : ℕ} (W : Fin m → ℝ) (i : Fin m)
    {r : ℝ}
    (hmax : ∀ j ∈ Finset.univ.erase i,
      W j ≤ r - ∑ l ∈ Finset.univ.erase i, W l) :
    r / m ≤ r - ∑ l ∈ Finset.univ.erase i, W l := by
  have hm : 0 < m := (Nat.zero_le i.val).trans_lt i.isLt
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsum := Finset.sum_le_sum hmax
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast] at hsum
  apply (div_le_iff₀ hmR).mpr
  nlinarith

/-- Given [the scale vector](hyp:a), [the tail exponent](hyp:beta), [the residual level](hyp:r), [the summand vector](hyp:W), and [the selected coordinate](hyp:i), [the largest-summand partition integrand](goal) first forms [the sum of all nonselected summands](step:1), then [uses the unshifted density term when the residual dominates all of them and zero otherwise](step:2).
-/
-- @node: hillLargestSummandIntegrand
noncomputable def hillLargestSummandIntegrand {m : ℕ} (a : Fin m → ℝ)
    (beta r : ℝ) (W : Fin m → ℝ) (i : Fin m) : ℝ :=
  let v := ∑ j ∈ Finset.univ.erase i, W j
  if ∀ j ∈ Finset.univ.erase i, W j ≤ r - v then
    beta * (a i) ^ beta * (a i + (r - v)) ^ (-beta - 1)
  else 0

/-- If [the tail exponent is positive](hyp:hb), [the selected scale is positive](hyp:ha), and [the residual level is positive](hyp:hr), then [the largest-summand integrand is nonnegative and bounded by the stated global envelope](goal).
-/
-- @node: hill_largest_summand_integrand_bound
lemma hill_largest_summand_integrand_bound {m : ℕ} (a W : Fin m → ℝ) (i : Fin m)
    {beta r : ℝ} (hb : 0 < beta) (ha : 0 < a i) (hr : 0 < r) :
    0 ≤ hillLargestSummandIntegrand a beta r W i ∧
      hillLargestSummandIntegrand a beta r W i ≤
        beta * (a i) ^ beta * (r / m) ^ (-beta - 1) := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast ((Nat.zero_le i.val).trans_lt i.isLt)
  unfold hillLargestSummandIntegrand
  dsimp only
  split_ifs with hmax
  · have hres := hill_largest_summand_residual_ge W i hmax
    have hp := Real.rpow_le_rpow_of_nonpos (div_pos hr hm)
      (by linarith : r / m ≤ a i + (r - ∑ j ∈ Finset.univ.erase i, W j))
      (by linarith : -beta - 1 ≤ 0)
    have hbase : 0 < a i + (r - ∑ j ∈ Finset.univ.erase i, W j) :=
      (div_pos hr hm).trans_le (by linarith)
    exact ⟨mul_nonneg (by positivity) (Real.rpow_nonneg hbase.le _),
      mul_le_mul_of_nonneg_left hp (by positivity)⟩
  · constructor <;> positivity

/-- If [all summands are nonnegative](hyp:hW) and [the nonselected sum is at most half the residual](hyp:hnear), then [the largest-summand integrand equals its unshifted density expression](goal).
-/
-- @node: hill_largest_summand_integrand_near
lemma hill_largest_summand_integrand_near {m : ℕ} (a W : Fin m → ℝ) (i : Fin m)
    {beta r : ℝ} (hW : ∀ j, 0 ≤ W j)
    (hnear : (∑ j ∈ Finset.univ.erase i, W j) ≤ r / 2) :
    hillLargestSummandIntegrand a beta r W i =
      beta * (a i) ^ beta *
        (a i + (r - ∑ j ∈ Finset.univ.erase i, W j)) ^ (-beta - 1) := by
  exact if_pos (hill_largest_summand_near W i hW hnear)

/-- If [the tail exponent is positive](hyp:hb), [the selected scale is positive](hyp:ha), and [the residual level is positive](hyp:hr), then [the difference between the partition integrand and the unshifted density is bounded by the global envelope](goal).
-/
-- @node: hill_largest_summand_integrand_error
lemma hill_largest_summand_integrand_error {m : ℕ} (a W : Fin m → ℝ) (i : Fin m)
    {beta r : ℝ} (hb : 0 < beta) (ha : 0 < a i) (hr : 0 < r) :
    |hillLargestSummandIntegrand a beta r W i -
      beta * (a i) ^ beta * (a i + r) ^ (-beta - 1)| ≤
        beta * (a i) ^ beta * (r / m) ^ (-beta - 1) := by
  obtain ⟨hHpos, hHle⟩ := hill_largest_summand_integrand_bound a W i hb ha hr
  have hm : 1 ≤ (m : ℝ) := by
    exact_mod_cast (show 1 ≤ m from (Nat.zero_le i.val).trans_lt i.isLt)
  have hbase : r / m ≤ a i + r := by
    apply (div_le_iff₀ (by linarith : 0 < (m : ℝ))).mpr
    nlinarith
  have hp := Real.rpow_le_rpow_of_nonpos (div_pos hr (by linarith)) hbase
    (by linarith : -beta - 1 ≤ 0)
  have hfle := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ beta * (a i) ^ beta by positivity)
  have hfpos : 0 ≤ beta * (a i) ^ beta * (a i + r) ^ (-beta - 1) := by positivity
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- If [the tail exponent is positive](hyp:hb), [the selected scale is positive](hyp:ha), [the residual level is positive](hyp:hr), and [each random summand is measurable](hyp:hW), then [the largest-summand partition integrand is integrable](goal).
-/
-- @node: hill_largest_summand_integrand_integrable
lemma hill_largest_summand_integrand_integrable {m : ℕ}
    (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (a : Fin m → ℝ) (W : Fin m → (Fin m → ℝ) → ℝ) (i : Fin m)
    {beta r : ℝ} (hb : 0 < beta) (ha : 0 < a i) (hr : 0 < r)
    (hW : ∀ j, Measurable (W j)) :
    Integrable (fun z => hillLargestSummandIntegrand a beta r (fun j => W j z) i) P := by
  have hV : Measurable (fun z => ∑ j ∈ Finset.univ.erase i, W j z) := by fun_prop
  have hH : Measurable
      (fun z => hillLargestSummandIntegrand a beta r (fun j => W j z) i) := by
    first | fun_prop | skip
    have hs : MeasurableSet {z | ∀ j ∈ Finset.univ.erase i,
        W j z ≤ r - ∑ l ∈ Finset.univ.erase i, W l z} := by
      simpa only [Set.iInter_setOf, Pi.sub_apply] using
        (Finset.univ.erase i).measurableSet_biInter
          (fun j _ => measurableSet_le (hW j) ((measurable_const : Measurable (fun _ : Fin m → ℝ => r)).sub hV))
    exact Measurable.ite hs (by fun_prop) measurable_const
  apply Integrable.mono'
    (integrable_const (beta * (a i) ^ beta * (r / m) ^ (-beta - 1)))
    hH.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨hpos, hbound⟩ :=
    hill_largest_summand_integrand_bound a (fun j => W j z) i hb ha hr
  rwa [Real.norm_eq_abs, abs_of_nonneg hpos]

/-- Given [the scale vector](hyp:a), [the tail exponent](hyp:beta), [the residual level](hyp:r), [the density normalizing constant](hyp:kappa), [the target density](hyp:density), and [the permitted error budget](hyp:budget), [the largest-summand data condition](goal) asserts the existence of [a probability law](step:1), [measurable summands](step:2), [nonnegative summands almost surely](step:3), [a partition formula for the target density](step:4), and [a truncated-moment and tail bound within the budget](step:5).
-/
-- @node: HillLargestSummandData
noncomputable def HillLargestSummandData {m : ℕ} (a : Fin m → ℝ)
    (beta r kappa density budget : ℝ) : Prop :=
  ∃ (P : Measure (Fin m → ℝ)) (W : Fin m → (Fin m → ℝ) → ℝ),
    IsProbabilityMeasure P ∧ (∀ i, Measurable (W i)) ∧
    (∀ᵐ z ∂P, ∀ i, 0 ≤ W i z) ∧
    density = kappa * ∑ i, ∫ z,
      hillLargestSummandIntegrand a beta r (fun j => W j z) i ∂P ∧
    kappa * (∑ i : Fin m,
      ((beta * (a i) ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2)) *
        (∫ z, if (∑ j ∈ Finset.univ.erase i, W j z) ≤ r / 2 then
          (∑ j ∈ Finset.univ.erase i, W j z) else 0 ∂P) +
        (beta * (a i) ^ beta * (r / m) ^ (-beta - 1)) *
          P.real {z | r / 2 < ∑ j ∈ Finset.univ.erase i, W j z})) ≤ budget

/-- If [the tail exponent is positive](hyp:hb), [the residual level is positive](hyp:hr), [every scale is positive](hyp:ha), and [the largest-summand data condition holds](hyp:h), then [the corresponding Hill convolution remainder data condition holds](goal).
-/
-- @node: hill_convolution_data_of_largest_summand
lemma hill_convolution_data_of_largest_summand {m : ℕ} (a : Fin m → ℝ)
    {beta r kappa density budget : ℝ} (hb : 0 < beta) (hr : 0 < r)
    (ha : ∀ i, 0 < a i)
    (h : HillLargestSummandData a beta r kappa density budget) :
    HillConvolutionRemainderData a beta r kappa density budget := by
  obtain ⟨P, W, hP, hW, hpos, hpartition, hbudget⟩ := h
  let := hP
  refine ⟨P, (fun i z => hillLargestSummandIntegrand a beta r (fun j => W j z) i),
    (fun i z => ∑ j ∈ Finset.univ.erase i, W j z),
    (fun i => beta * (a i) ^ beta * (r / m) ^ (-beta - 1)), hP, ?_, ?_, ?_,
    ?_, ?_, hpartition, hbudget⟩
  · intro i; fun_prop
  · intro i
    filter_upwards [hpos] with z hz
    exact Finset.sum_nonneg (fun j _ => hz j)
  · intro i
    exact hill_largest_summand_integrand_integrable P a W i hb (ha i) hr hW
  · intro i
    filter_upwards [hpos] with z hz
    exact hill_largest_summand_integrand_near a (fun j => W j z) i hz
  · intro i
    exact Filter.Eventually.of_forall (fun z _ =>
      hill_largest_summand_integrand_error a (fun j => W j z) i hb (ha i) hr)

end Papers.TbsExtremeEffects
