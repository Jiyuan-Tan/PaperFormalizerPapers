module
public import Papers.TbsExtremeEffects.Helpers.Hill.RemainderMoments
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Layer-cake estimates for the capped component moments in the Hill proof. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped ENNReal

/-- For [a probability distribution](hyp:P), [a measurable component](hyp:W), [a nonnegative cap](hyp:hR), [measurability of that component](hyp:hW), and [its almost-sure nonnegativity](hyp:hpos), [its capped expectation equals the integral of its survival function up to the cap](goal).
@node: hill_capped_moment_tail_integral -/
lemma hill_capped_moment_tail_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hW : Measurable W) (hpos : ∀ᵐ z ∂P, 0 ≤ W z) :
    (∫ z, min (W z) R ∂P) = ∫ x in Set.Ioc 0 R, P.real {z | x < W z} := by
  have hInt := hill_capped_component_integrable P W hR hW hpos
  rw [hInt.integral_eq_integral_Ioc_meas_le
    (hpos.mono (fun z hz => le_min hz hR))
    (Filter.Eventually.of_forall (fun z => min_le_right (W z) R))]
  calc
    _ = ∫ x in Set.Ioc 0 R, P.real {z | x ≤ W z} := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have heq : {z | x ≤ min (W z) R} = {z | x ≤ W z} := by
        ext z
        exact le_min_iff.trans (and_iff_left hx.2)
      exact congrArg P.real heq
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [meas_le_ae_eq_meas_lt P (volume.restrict (Set.Ioc 0 R)) W]
        with x hx
      exact congrArg ENNReal.toReal hx

/-- For [a probability distribution](hyp:P), [a component](hyp:W), and finite interval endpoints, [its survival function is integrable on that interval](goal).
@node: hill_component_survival_integrableOn -/
lemma hill_component_survival_integrableOn {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (a b : ℝ) :
    IntegrableOn (fun x => P.real {z | x < W z}) (Set.Ioc a b) := by
  have hmono : Antitone (fun x => P.real {z | x < W z}) := by
    intro x y hxy
    exact measureReal_mono (h₂ := measure_ne_top P _)
      (fun z hz => hxy.trans_lt hz)
  apply Integrable.mono' (integrable_const (1 : ℝ)) hmono.measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg : 0 ≤ P.real {z | x < W z})]
  exact measureReal_le_one

/-- For [a probability distribution](hyp:P), [a measurable component](hyp:W), [a cap at least one](hyp:hR), [measurability](hyp:hW), [almost-sure nonnegativity](hyp:hpos), and [a polynomial survival-tail bound above one](hyp:hTail), [the capped expectation is bounded by one plus the integrated polynomial tail](goal).
@node: hill_capped_moment_polynomial_integral_bound -/
lemma hill_capped_moment_polynomial_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    {R beta C : ℝ} (hR : 1 ≤ R) (hW : Measurable W)
    (hpos : ∀ᵐ z ∂P, 0 ≤ W z)
    (hTail : ∀ x ≥ 1, P.real {z | x < W z} ≤ C * x ^ (-beta)) :
    (∫ z, min (W z) R ∂P) ≤ 1 + C * (∫ x in Set.Ioc 1 R, x ^ (-beta)) := by
  have hpow : IntegrableOn (fun x : ℝ => x ^ (-beta)) (Set.Ioc 1 R) := by
    apply (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuousOn_id.rpow_const
      (fun x hx => Or.inl (ne_of_gt (show 0 < x by linarith [hx.1])))
  have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioc 1 R) :=
    Set.disjoint_left.mpr (fun x hx hy => (not_lt.mpr hx.2) hy.1)
  rw [hill_capped_moment_tail_integral P W (by linarith) hW hpos,
    ← Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1) hR,
    setIntegral_union hdisjoint measurableSet_Ioc
      (hill_component_survival_integrableOn P W 0 1)
      (hill_component_survival_integrableOn P W 1 R)]
  apply add_le_add
  · calc
      _ ≤ ∫ x : ℝ in Set.Ioc 0 1, (1 : ℝ) := by
        apply setIntegral_mono_on (hill_component_survival_integrableOn P W 0 1)
          (integrable_const _) measurableSet_Ioc
        intro x hx
        exact measureReal_le_one
      _ = 1 := by simp
  · rw [← integral_const_mul]
    apply setIntegral_mono_on (hill_component_survival_integrableOn P W 1 R)
      (hpow.const_mul C) measurableSet_Ioc
    intro x hx
    exact hTail x hx.1.le

/-- Given [a tail exponent](hyp:beta), [a tail constant](hyp:C), and [a cap](hyp:R), [the capped-moment envelope](goal) is [the power-law formula below index one](step:1), [the logarithmic formula at index one](step:2), or [the constant formula above index one](step:3).
@node: hillCappedMomentEnvelope -/
noncomputable def hillCappedMomentEnvelope (beta C R : ℝ) : ℝ :=
  if beta < 1 then 1 + C / (1 - beta) * R ^ (1 - beta)
  else if beta = 1 then 1 + C * Real.log R
  else 1 + C / (beta - 1)

/-- If [the tail constant is nonnegative](hyp:hC) and [the cap is at least one](hyp:hR), [the integrated polynomial survival envelope is bounded by the explicit capped-moment envelope](goal).
@node: hill_polynomial_tail_integral_bound -/
lemma hill_polynomial_tail_integral_bound {beta C R : ℝ}
    (hC : 0 ≤ C) (hR : 1 ≤ R) :
    1 + C * (∫ x in Set.Ioc 1 R, x ^ (-beta)) ≤ hillCappedMomentEnvelope beta C R := by
  rw [← intervalIntegral.integral_of_le hR]
  unfold hillCappedMomentEnvelope
  split_ifs with hb hb1
  · rw [integral_rpow (Or.inl (by linarith : -1 < -beta)), Real.one_rpow]
    have he : -beta + 1 = 1 - beta := by ring
    rw [he]
    calc
      _ ≤ 1 + C * (R ^ (1 - beta) / (1 - beta)) := by
        gcongr
        linarith
      _ = _ := by ring
  · subst beta
    simp only [Real.rpow_neg_one]
    rw [integral_inv_of_pos (by norm_num) (by linarith), div_one]
  · have hbgt : 1 < beta := lt_of_le_of_ne (not_lt.mp hb) (Ne.symm hb1)
    have hz : (0 : ℝ) ∉ Set.uIcc 1 R := by
      rw [Set.uIcc_of_le hR]
      simp
    rw [integral_rpow (Or.inr ⟨by linarith, hz⟩), Real.one_rpow]
    have hfrac : (R ^ (-beta + 1) - 1) / (-beta + 1) ≤ 1 / (beta - 1) := by
      rw [show -beta + 1 = -(beta - 1) by ring, div_neg,
        ← neg_div, neg_sub]
      exact div_le_div_of_nonneg_right
        (sub_le_self 1 (Real.rpow_nonneg (by linarith) _)) (by linarith)
    calc
      _ ≤ 1 + C * (1 / (beta - 1)) := by gcongr
      _ = _ := by ring

/-- For [a probability distribution](hyp:P), [a measurable component](hyp:W), [a nonnegative tail constant](hyp:hC), [a cap at least one](hyp:hR), [measurability](hyp:hW), [almost-sure nonnegativity](hyp:hpos), and [a polynomial survival-tail bound](hyp:hTail), [the capped expectation is bounded by the explicit envelope](goal).
@node: hill_capped_moment_polynomial_bound -/
lemma hill_capped_moment_polynomial_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    {R beta C : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R) (hW : Measurable W)
    (hpos : ∀ᵐ z ∂P, 0 ≤ W z)
    (hTail : ∀ x ≥ 1, P.real {z | x < W z} ≤ C * x ^ (-beta)) :
    (∫ z, min (W z) R ∂P) ≤ hillCappedMomentEnvelope beta C R := by
  exact (hill_capped_moment_polynomial_integral_bound P W hR hW hpos hTail).trans
    (hill_polynomial_tail_integral_bound hC hR)

/-- For [a probability distribution](hyp:P), [a measurable component](hyp:W), [a nonnegative cap](hyp:hR), [measurability](hyp:hW), [almost-sure nonnegativity](hyp:hpos), and [a polynomial survival-tail bound at every positive threshold](hyp:hTail), [the capped expectation is bounded by the envelope evaluated at the larger of one and the cap](goal).
@node: hill_capped_moment_polynomial_bound_all -/
lemma hill_capped_moment_polynomial_bound_all {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    {R beta C : ℝ} (hR : 0 ≤ R) (hW : Measurable W)
    (hpos : ∀ᵐ z ∂P, 0 ≤ W z)
    (hTail : ∀ x > 0, P.real {z | x < W z} ≤ C * x ^ (-beta)) :
    (∫ z, min (W z) R ∂P) ≤ hillCappedMomentEnvelope beta C (max 1 R) := by
  have hC : 0 ≤ C := by
    have h := (measureReal_nonneg : 0 ≤ P.real {z | 1 < W z}).trans
      (hTail 1 (by norm_num))
    simpa using h
  calc
    _ ≤ ∫ z, min (W z) (max 1 R) ∂P := by
      apply integral_mono (hill_capped_component_integrable P W hR hW hpos)
        (hill_capped_component_integrable P W (by positivity) hW hpos)
      intro z
      exact min_le_min_left (W z) (le_max_right 1 R)
    _ ≤ _ := hill_capped_moment_polynomial_bound P W hC (le_max_left 1 R) hW hpos
      (fun x hx => hTail x (zero_lt_one.trans_le hx))

/-- For [component scales](hyp:a), [a tail exponent](hyp:beta), [a radius](hyp:r), [a prefactor](hyp:kappa), [a density value](hyp:density), and [an error budget](hyp:budget), [the polynomial largest-summand data condition](goal) asserts [a probability measure](step:1), [measurable component functions](step:2), [their almost-sure nonnegativity](step:3), [their polynomial survival bounds](step:4), [the density partition](step:5), and [the numerical remainder bound](step:6).
@node: HillLargestSummandPolynomialData -/
noncomputable def HillLargestSummandPolynomialData {m : ℕ} (a : Fin m → ℝ)
    (beta r kappa density budget : ℝ) : Prop :=
  ∃ (P : Measure (Fin m → ℝ)) (W : Fin m → (Fin m → ℝ) → ℝ) (C : Fin m → ℝ),
    IsProbabilityMeasure P ∧ (∀ i, Measurable (W i)) ∧
    (∀ᵐ z ∂P, ∀ i, 0 ≤ W i z) ∧
    (∀ j, ∀ x > 0, P.real {z | x < W j z} ≤ C j * x ^ (-beta)) ∧
    density = kappa * ∑ i, ∫ z,
      hillLargestSummandIntegrand a beta r (fun j => W j z) i ∂P ∧
    kappa * (∑ i : Fin m,
      ((beta * (a i) ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2)) *
        (∑ j ∈ Finset.univ.erase i,
          hillCappedMomentEnvelope beta (C j) (max 1 (r / 2))) +
        (beta * (a i) ^ beta * (r / m) ^ (-beta - 1)) *
          (((∑ j ∈ Finset.univ.erase i, C j) * (m : ℝ) ^ beta) *
            (r / 2) ^ (-beta)))) ≤ budget

/-- Given [a positive tail exponent](hyp:hb), [a positive radius](hyp:hr), [positive component scales](hyp:ha), [a nonnegative prefactor](hyp:hkappa), and [polynomial largest-summand data](hyp:h), [the corresponding component-moment data condition holds](goal).
@node: hill_component_data_of_polynomial_data -/
lemma hill_component_data_of_polynomial_data {m : ℕ} (a : Fin m → ℝ)
    {beta r kappa density budget : ℝ} (hb : 0 < beta) (hr : 0 < r)
    (ha : ∀ i, 0 < a i) (hkappa : 0 ≤ kappa)
    (h : HillLargestSummandPolynomialData a beta r kappa density budget) :
    HillLargestSummandComponentData a beta r kappa density budget := by
  obtain ⟨P, W, C, hP, hW, hpos, hTail, hpartition, hbudget⟩ := h
  let := hP
  refine ⟨P, W, C, hP, hW, hpos, hTail, hpartition, ?_⟩
  apply le_trans ?_ hbudget
  apply mul_le_mul_of_nonneg_left _ hkappa
  apply Finset.sum_le_sum
  intro i _
  have hai := ha i
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  exact hill_capped_moment_polynomial_bound_all P (W j) (by positivity) (hW j)
    (hpos.mono (fun z hz => hz j)) (hTail j)

end Papers.TbsExtremeEffects
