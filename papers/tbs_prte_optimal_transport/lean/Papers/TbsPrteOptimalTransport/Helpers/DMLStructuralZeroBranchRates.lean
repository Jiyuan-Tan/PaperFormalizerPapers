module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryBranchRates
/-! Branch-error energy at the fixed zero boundary. The outcome margin replaces
policy spacing from zero, which need not have a uniform positive lower bound. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Classical Topology

-- @node: binary_structural_zero_branches_stable
/-- If [the margin is positive](hyp:hc), [the true upper boundary is at least the margin](hyp:hbc),
[its distance from the true policy argument is at least the margin](hyp:hbq), [the fitted
policy argument and upper boundary each have absolute error at most the error bound](hyp:hq,hb),
and [that bound is less than half the margin](hyp:he), then [with the lower argument
fixed at zero, the fitted and true activity, interior-boundary, and negative-boundary
indicators all agree](goal). -/
lemma binary_structural_zero_branches_stable {q b qh bh err c : ℝ}
    (hc : 0 < c) (hbc : c ≤ b) (hbq : c ≤ |b - q|)
    (hq : |qh - q| ≤ err) (hb : |bh - b| ≤ err) (he : err < c / 2) :
    indicator (qh > max 0 bh) = indicator (q > max 0 b) ∧
    indicator (0 < bh ∧ bh < qh) = indicator (0 < b ∧ b < q) ∧
    indicator (0 > bh) = indicator (0 > b) := by
  have hb0 : 0 < b := hc.trans_le hbc
  have hbh0 : 0 < bh := by
    have := (abs_le.mp hb).1
    linarith
  have hiff : bh < qh ↔ b < q := by
    by_cases hlt : b < q
    · have hsep : c ≤ q - b := by
        simpa only [abs_of_neg (sub_neg.mpr hlt), neg_sub] using hbq
      have := (abs_le.mp hq).1
      have := (abs_le.mp hb).2
      constructor
      · intro _; exact hlt
      · intro _; linarith
    · have hsep : c ≤ b - q := by
        simpa only [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hlt))] using hbq
      have := (abs_le.mp hq).2
      have := (abs_le.mp hb).1
      have hnot : ¬ bh < qh := by linarith
      exact iff_of_false hnot hlt
  rw [max_eq_right hbh0.le, max_eq_right hb0.le]
  have hi : indicator (bh < qh) = indicator (b < q) := by rw [hiff]
  refine ⟨hi, ?_, ?_⟩
  · simpa only [hbh0, hb0, true_and] using hi
  · simp only [indicator, if_neg (not_lt.mpr hbh0.le), if_neg (not_lt.mpr hb0.le)]

-- @node: binary_structural_zero_branch_sq_error_bound
/-- If [the margin is positive](hyp:hc), [the true upper boundary is at least the
margin](hyp:hbc), [its distance from the policy argument is at least the margin](hyp:hbq),
and [both the fitted policy argument and fitted upper boundary have absolute errors
at most the error bound](hyp:hq,hb), then [the sum of squared errors of the three binary
branch indicators, with lower argument fixed at zero, is at most twelve times the
squared error bound divided by the squared margin](goal). -/
lemma binary_structural_zero_branch_sq_error_bound {q b qh bh err c : ℝ}
    (hc : 0 < c) (hbc : c ≤ b) (hbq : c ≤ |b - q|)
    (hq : |qh - q| ≤ err) (hb : |bh - b| ≤ err) :
    binaryBranchSqError q 0 b qh 0 bh ≤ (12 / c ^ 2) * err ^ 2 := by
  have he0 : 0 ≤ err := (abs_nonneg _).trans hq
  by_cases he : err < c / 2
  · obtain ⟨hi, hd, he'⟩ := binary_structural_zero_branches_stable hc hbc hbq hq hb he
    simp only [binaryBranchSqError, hi, hd, he', sub_self, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add]
    positivity
  · have hlarge : c / 2 ≤ err := le_of_not_gt he
    have hbound : binaryBranchSqError q 0 b qh 0 bh ≤ 3 := by
      unfold binaryBranchSqError
      have := score_indicator_sub_sq_le_one (qh > max 0 bh) (q > max 0 b)
      have := score_indicator_sub_sq_le_one (0 < bh ∧ bh < qh) (0 < b ∧ b < q)
      have := score_indicator_sub_sq_le_one (0 > bh) (0 > b)
      linarith
    apply hbound.trans
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 2 * err - c by linarith)
      (show 0 ≤ 2 * err + c by positivity)]

-- @node: binary_structural_zero_branch_component_energy_bound
/-- Suppose [the margin is positive](hyp:hc), [the true policy argument and upper
boundary are measurable](hyp:hq,hb), [their fitted counterparts are measurable](hyp:hqh,hbh),
[both estimation errors have finite second moments](hyp:heq,heb), and [almost everywhere
the true upper boundary and its distance from the policy argument are at least the
margin](hyp:hgap). Then [the sum of squared binary branch errors at the fixed zero
lower argument is integrable, and its integral is at most thirty-six divided by the
squared margin times the sum of the two component squared-error integrals](goal). -/
lemma binary_structural_zero_branch_component_energy_bound
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (q b qh bh : X → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : Measurable q) (hb : Measurable b)
    (hqh : Measurable qh) (hbh : Measurable bh)
    (heq : MemLp (fun x => qh x - q x) 2 ν)
    (heb : MemLp (fun x => bh x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ b x ∧ c ≤ |b x - q x|) :
    Integrable (fun x => binaryBranchSqError (q x) 0 (b x) (qh x) 0 (bh x)) ν ∧
      (∫ x, binaryBranchSqError (q x) 0 (b x) (qh x) 0 (bh x) ∂ν) ≤
        (36 / c ^ 2) * ((∫ x, (qh x - q x) ^ 2 ∂ν) +
          ∫ x, (bh x - b x) ^ 2 ∂ν) := by
  obtain ⟨he, henergy⟩ := integral_sq_abs_sum_three_le ν
    (fun x => qh x - q x) (fun x => bh x - b x) (fun _ => 0)
    heq heb (MemLp.zero)
  simp only [abs_zero, add_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, integral_zero] at he henergy
  let R := fun x => binaryBranchSqError (q x) 0 (b x) (qh x) 0 (bh x)
  have hm : Measurable R := by
    dsimp only [R]
    fun_prop
  have hn : ∀ x, 0 ≤ R x := fun x =>
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hbound : ∀ᵐ x ∂ν, R x ≤
      (12 / c ^ 2) * (|qh x - q x| + |bh x - b x|) ^ 2 := by
    filter_upwards [hgap] with x hx
    apply binary_structural_zero_branch_sq_error_bound hc hx.1 hx.2
    · linarith [abs_nonneg (bh x - b x)]
    · linarith [abs_nonneg (qh x - q x)]
  have hdom := he.integrable_sq.const_mul (12 / c ^ 2)
  have hi : Integrable R ν := hdom.mono' hm.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, (12 / c ^ 2) * (|qh x - q x| + |bh x - b x|) ^ 2 ∂ν :=
      integral_mono_ae hi hdom hbound
    _ = (12 / c ^ 2) * ∫ x, (|qh x - q x| + |bh x - b x|) ^ 2 ∂ν :=
      integral_const_mul _ _
    _ ≤ (12 / c ^ 2) * (3 * ((∫ x, (qh x - q x) ^ 2 ∂ν) +
        ∫ x, (bh x - b x) ^ 2 ∂ν)) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

-- @node: binary_structural_zero_branch_component_energy_isLittleOp
/-- Suppose [the margin is positive](hyp:hc), [the true policy argument and upper
boundary are measurable](hyp:hq,hb), [all their fitted versions are measurable](hyp:hqh,hbh),
[both fitted component errors have finite second moments](hyp:heq,heb), and [the true
upper boundary and its distance from the policy argument are at least the margin almost
everywhere](hyp:hgap). If [the policy-argument root mean squared error is of smaller
order in probability than the inverse fourth root of twice the evaluation size](hyp:hrq)
and [the boundary root mean squared error has the same rate](hyp:hrb), then [the
integrated sum of squared binary branch errors at the fixed zero lower argument is
of smaller order in probability than the inverse square root of twice the evaluation
size](goal). -/
lemma binary_structural_zero_branch_component_energy_isLittleOp
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (μ : Measure A) (ν : Measure X) (q b : X → ℝ)
    (qh bh : ℕ → A → X → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : Measurable q) (hb : Measurable b)
    (hqh : ∀ n a, Measurable (qh n a)) (hbh : ∀ n a, Measurable (bh n a))
    (heq : ∀ n a, MemLp (fun x => qh n a x - q x) 2 ν)
    (heb : ∀ n a, MemLp (fun x => bh n a x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ b x ∧ c ≤ |b x - q x|)
    (hrq : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (qh n a x - q x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrb : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (bh n a x - b x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp (fun n a => ∫ x,
      binaryBranchSqError (q x) 0 (b x) (qh n a x) 0 (bh n a x) ∂ν)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ := by
  have hqs := dml_quarter_rate_product μ _ _ hrq hrq
  have hbs := dml_quarter_rate_product μ _ _ hrb hrb
  simp only [← sq, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)] at hqs hbs
  have hr : ∀ᶠ n in atTop,
      0 ≤ ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
    Eventually.of_forall (fun n => Real.rpow_nonneg (by positivity) _)
  have he := hqs.add_eventually_nonneg_rate hr hbs
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 36 / c ^ 2) he
  intro n a
  rw [abs_of_nonneg (integral_nonneg fun x =>
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
  exact (binary_structural_zero_branch_component_energy_bound ν q b (qh n a) (bh n a)
    c hc hq hb (hqh n a) (hbh n a) (heq n a) (heb n a) hgap).2.trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

-- @node: binary_structural_zero_branch_l2_tendsto_probability_zero
/-- Suppose [the margin is positive](hyp:hc), [the true policy argument and upper
boundary are measurable](hyp:hq,hb), [all fitted counterparts are measurable](hyp:hqh,hbh),
[both component errors have finite second moments](hyp:heq,heb), and [the true upper
boundary and its distance from the policy argument are bounded below by the margin
almost everywhere](hyp:hgap). If [both the policy-argument and boundary root mean
squared errors are of smaller order in probability than the inverse fourth root of
twice the evaluation size](hyp:hrq,hrb), then [the square root of
the integrated sum of squared binary branch errors at the fixed zero lower argument
converges to zero in probability](goal). -/
lemma binary_structural_zero_branch_l2_tendsto_probability_zero
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (μ : Measure A) (ν : Measure X) (q b : X → ℝ)
    (qh bh : ℕ → A → X → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : Measurable q) (hb : Measurable b)
    (hqh : ∀ n a, Measurable (qh n a)) (hbh : ∀ n a, Measurable (bh n a))
    (heq : ∀ n a, MemLp (fun x => qh n a x - q x) 2 ν)
    (heb : ∀ n a, MemLp (fun x => bh n a x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ b x ∧ c ≤ |b x - q x|)
    (hrq : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (qh n a x - q x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrb : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (bh n a x - b x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ x,
        binaryBranchSqError (q x) 0 (b x) (qh n a x) 0 (bh n a x) ∂ν))
      atTop (fun _ _ => 0) := by
  apply dml_half_rate_energy_l2_tendsto_probability_zero
  · intro n a
    exact integral_nonneg fun x =>
      add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  · exact binary_structural_zero_branch_component_energy_isLittleOp μ ν q b qh bh c hc
      hq hb hqh hbh heq heb hgap hrq hrb

end Papers.TbsPrteOptimalTransport
