module
public import Papers.TbsExtremeEffects.Helpers.Hill.LargestSummand

/-! Componentwise tail and truncated-moment bounds for the convolution remainder. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped BigOperators
open Classical

/-- [A nonnegative cap](hyp:hR) and [nonnegative summands on the finite index set](hyp:hW) ensure [that capping their sum is no larger than the sum of their individual caps](goal). -/
-- @node: hill_min_sum_le_sum_min
lemma hill_min_sum_le_sum_min {ι : Type*} (s : Finset ι) (W : ι → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hW : ∀ j ∈ s, 0 ≤ W j) :
    min (∑ j ∈ s, W j) R ≤ ∑ j ∈ s, min (W j) R := by
  by_cases hlarge : ∃ j ∈ s, R ≤ W j
  · obtain ⟨j, hj, hlarge⟩ := hlarge
    calc
      _ ≤ R := min_le_right _ _
      _ = min (W j) R := (min_eq_right hlarge).symm
      _ ≤ _ := Finset.single_le_sum (fun l hl => le_min (hW l hl) hR) hj
  · have hsmall : ∀ j ∈ s, W j ≤ R := by
      intro j hj
      exact (lt_of_not_ge (fun h => hlarge ⟨j, hj, h⟩)).le
    rw [Finset.sum_congr rfl (fun j hj => min_eq_left (hsmall j hj))]
    exact min_le_left _ _

/-- [A nonnegative threshold](hyp:hx) ensures [the union upper bound on the probability that the remainder sum exceeds it](goal): some component must exceed the threshold divided by the sample dimension.
No independence is needed for this union bound. -/
-- @node: hill_remainder_tail_union_bound
lemma hill_remainder_tail_union_bound {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (W : Fin m → Ω → ℝ) (i : Fin m)
    {x : ℝ} (hx : 0 ≤ x) :
    P.real {z | x < ∑ j ∈ Finset.univ.erase i, W j z} ≤
      ∑ j ∈ Finset.univ.erase i, P.real {z | x / m < W j z} := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast ((Nat.zero_le i.val).trans_lt i.isLt)
  apply (measureReal_mono (h₂ := measure_ne_top P _) ?_).trans
    (measureReal_biUnion_finset_le (Finset.univ.erase i) (fun j => {z | x / m < W j z}))
  intro z hz
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  by_contra h
  have hsmall : ∀ j ∈ Finset.univ.erase i, W j z ≤ x / m := by
    intro j hj
    exact le_of_not_gt (fun hjlarge => h ⟨j, hj, hjlarge⟩)
  have hsum := Finset.sum_le_sum hsmall
  have hcard : ((Finset.univ.erase i).card : ℝ) ≤ (m : ℝ) := by
    have hc : (Finset.univ.erase i).card ≤ m := by
      simpa using Finset.card_le_card (Finset.erase_subset i Finset.univ)
    exact_mod_cast hc
  have hbound : (∑ j ∈ Finset.univ.erase i, W j z) ≤ x := by
    calc
      _ ≤ ((Finset.univ.erase i).card : ℝ) * (x / m) := by
        simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
      _ ≤ (m : ℝ) * (x / m) := mul_le_mul_of_nonneg_right hcard (div_nonneg hx hm.le)
      _ = x := by field_simp
  exact (not_lt.mpr hbound) hz

/-- [A positive threshold](hyp:hx) and [a bound on each component's probability of exceeding every positive level by its coefficient times that level to the negative tail exponent](hyp:hTail) imply [a polynomial upper bound for the remainder sum's tail probability](goal). -/
-- @node: hill_remainder_polynomial_tail
lemma hill_remainder_polynomial_tail {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (W : Fin m → Ω → ℝ) (i : Fin m)
    (C : Fin m → ℝ) {beta x : ℝ} (hx : 0 < x)
    (hTail : ∀ j, ∀ y > 0, P.real {z | y < W j z} ≤ C j * y ^ (-beta)) :
    P.real {z | x < ∑ j ∈ Finset.univ.erase i, W j z} ≤
      ((∑ j ∈ Finset.univ.erase i, C j) * (m : ℝ) ^ beta) * x ^ (-beta) := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast ((Nat.zero_le i.val).trans_lt i.isLt)
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, P.real {z | x / m < W j z} :=
      hill_remainder_tail_union_bound P W i hx.le
    _ ≤ ∑ j ∈ Finset.univ.erase i, C j * (x / m) ^ (-beta) :=
      Finset.sum_le_sum (fun j _ => hTail j (x / m) (div_pos hx hm))
    _ = _ := by
      rw [← Finset.sum_mul, Real.div_rpow hx.le hm.le, Real.rpow_neg hm.le,
        div_inv_eq_mul]
      ring

/-- [A nonnegative cap](hyp:hR), [a measurable component](hyp:hW), and [its almost-sure nonnegativity](hyp:hpos) imply [that the capped component has a finite integral](goal), even if the original component does not. -/
-- @node: hill_capped_component_integrable
lemma hill_capped_component_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hW : Measurable W) (hpos : ∀ᵐ z ∂P, 0 ≤ W z) :
    Integrable (fun z => min (W z) R) P := by
  apply Integrable.mono' (integrable_const R)
  · have hm : Measurable (fun z => min (W z) R) := by fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [hpos] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hz hR)]
    exact min_le_right _ _

/-- [A nonnegative truncation level](hyp:hr), [measurable components](hyp:hW), and [their simultaneous almost-sure nonnegativity](hyp:hpos) imply [the bound of the truncated remainder mean by the sum of component capped means](goal). -/
-- @node: hill_remainder_truncated_moment_bound
lemma hill_remainder_truncated_moment_bound {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Fin m → Ω → ℝ) (i : Fin m)
    {r : ℝ} (hr : 0 ≤ r) (hW : ∀ j, Measurable (W j))
    (hpos : ∀ᵐ z ∂P, ∀ j, 0 ≤ W j z) :
    (∫ z, if (∑ j ∈ Finset.univ.erase i, W j z) ≤ r / 2 then
      (∑ j ∈ Finset.univ.erase i, W j z) else 0 ∂P) ≤
      ∑ j ∈ Finset.univ.erase i, ∫ z, min (W j z) (r / 2) ∂P := by
  have hV : Measurable (fun z => ∑ j ∈ Finset.univ.erase i, W j z) := by fun_prop
  have hVpos : ∀ᵐ z ∂P, 0 ≤ ∑ j ∈ Finset.univ.erase i, W j z := by
    filter_upwards [hpos] with z hz
    exact Finset.sum_nonneg (fun j _ => hz j)
  have hInt : ∀ j, Integrable (fun z => min (W j z) (r / 2)) P := by
    intro j
    exact hill_capped_component_integrable P (W j) (by positivity) (hW j)
      (hpos.mono (fun z hz => hz j))
  rw [← integral_finsetSum _ (fun j _ => hInt j)]
  apply integral_mono_ae (hill_truncated_remainder_integrable P _ hr hV hVpos)
    (integrable_finsetSum _ (fun j _ => hInt j))
  filter_upwards [hpos] with z hz
  have hcap := hill_min_sum_le_sum_min (Finset.univ.erase i) (fun j => W j z)
    (show 0 ≤ r / 2 by positivity) (fun j _ => hz j)
  split_ifs with hsmall
  · exact (min_eq_left hsmall).symm.le.trans hcap
  · exact Finset.sum_nonneg (fun j _ => le_min (hz j) (by positivity))

/-- Given [component scales](hyp:a), [the tail exponent](hyp:beta), [the radial threshold](hyp:r), [the normalizing constant](hyp:kappa), [the target density](hyp:density), and [the error budget](hyp:budget), [the component-data condition](goal) asserts the existence of a probability law, nonnegative measurable components with polynomial tails, the partition formula, and the displayed componentwise budget inequality.
The remainder's tail and truncated mean are derived, not supplied as identities. -/
-- @node: HillLargestSummandComponentData
noncomputable def HillLargestSummandComponentData {m : ℕ} (a : Fin m → ℝ)
    (beta r kappa density budget : ℝ) : Prop :=
  ∃ (P : Measure (Fin m → ℝ)) (W : Fin m → (Fin m → ℝ) → ℝ) (C : Fin m → ℝ),
    IsProbabilityMeasure P ∧ (∀ i, Measurable (W i)) ∧
    (∀ᵐ z ∂P, ∀ i, 0 ≤ W i z) ∧
    (∀ j, ∀ x > 0, P.real {z | x < W j z} ≤ C j * x ^ (-beta)) ∧
    density = kappa * ∑ i, ∫ z,
      hillLargestSummandIntegrand a beta r (fun j => W j z) i ∂P ∧
    kappa * (∑ i : Fin m,
      ((beta * (a i) ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2)) *
        (∑ j ∈ Finset.univ.erase i, ∫ z, min (W j z) (r / 2) ∂P) +
        (beta * (a i) ^ beta * (r / m) ^ (-beta - 1)) *
          (((∑ j ∈ Finset.univ.erase i, C j) * (m : ℝ) ^ beta) * (r / 2) ^ (-beta)))) ≤ budget

/-- [A positive tail exponent](hyp:hb), [a positive threshold](hyp:hr), [positive component scales](hyp:ha), [a nonnegative normalizing constant](hyp:hkappa), and the component-data condition together imply [the corresponding largest-summand data condition](goal).
The component budget supplies exactly the near/far remainder budget used by the convolution estimate. -/
-- @node: hill_largest_summand_data_of_component_data
lemma hill_largest_summand_data_of_component_data {m : ℕ} (a : Fin m → ℝ)
    {beta r kappa density budget : ℝ} (hb : 0 < beta) (hr : 0 < r)
    (ha : ∀ i, 0 < a i) (hkappa : 0 ≤ kappa)
    (h : HillLargestSummandComponentData a beta r kappa density budget) :
    HillLargestSummandData a beta r kappa density budget := by
  obtain ⟨P, W, C, hP, hW, hpos, hTail, hpartition, hbudget⟩ := h
  let := hP
  refine ⟨P, W, hP, hW, hpos, hpartition, ?_⟩
  apply le_trans ?_ hbudget
  apply mul_le_mul_of_nonneg_left _ hkappa
  apply Finset.sum_le_sum
  intro i _
  have hai := ha i
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (hill_remainder_truncated_moment_bound P W i hr.le hW hpos) (by positivity)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hill_remainder_polynomial_tail P W i C (by positivity) hTail

end Papers.TbsExtremeEffects
