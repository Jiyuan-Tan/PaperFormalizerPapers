module
public import Papers.TbsExtremeEffects.Helpers.Hill.Renyi

/-! Simultaneous deviations of Hill statistics on the dyadic grid. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

/-- Given a [positive index](hyp:hi) that [does not exceed the sample size](hyp:hin), there is a [dyadic block containing that index](goal).
-/
-- @node: hill_dyadic_block_cover
lemma hill_dyadic_block_cover {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    ∃ a < hillGridSize n, 2 ^ a ≤ i ∧ i < 2 ^ (a + 1) := by
  obtain ⟨a, ha, ha'⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ i by exact_mod_cast hi) (show (1 : ℝ) < 2 by norm_num)
  have hpow : (2 : ℝ) ^ a ≤ n := ha.trans (by exact_mod_cast hin)
  have hn : 0 < (n : ℝ) := by exact_mod_cast hi.trans hin
  have hlog : (a : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have hac : a ≤ ⌈Real.log n / Real.log 2⌉₊ := by
    exact_mod_cast ((le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
      hlog).trans (Nat.le_ceil _)
  refine ⟨a, by unfold hillGridSize; omega, ?_, ?_⟩
  · exact_mod_cast ha
  · exact_mod_cast ha'

/-- If [the block endpoint is at most twice the index](hyp:hm) and [the deviation budget is nonnegative](hyp:hx), then [the block threshold is bounded by twice the index-scale threshold](goal).
-/
-- @node: hill_dyadic_threshold_le
lemma hill_dyadic_threshold_le {i m : ℕ} {x : ℝ}
    (hm : m ≤ 2 * i) (hx : 0 ≤ x) :
    Real.sqrt (2 * (m : ℝ) * x) ≤ 2 * Real.sqrt x * Real.sqrt i := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hsx := Real.sq_sqrt hx
    have hsi := Real.sq_sqrt (Nat.cast_nonneg i : 0 ≤ (i : ℝ))
    have hm' : (m : ℝ) ≤ 2 * i := by exact_mod_cast hm
    nlinarith [mul_le_mul_of_nonneg_right hm' hx]

/-- If [the lower index is at least one](hyp:hL), [the deviation budget is nonnegative](hyp:hx), and [every dyadic block obeys its maximal bound](hyp:hblocks), then [every partial sum between the lower index and the sample size obeys the simultaneous normalized bound](goal).
-/
-- @node: hill_spacing_bound_of_dyadic_control
lemma hill_spacing_bound_of_dyadic_control (B : ℕ → ℝ) {n L : ℕ} {x : ℝ}
    (hL : 1 ≤ L) (hx : 0 ≤ x)
    (hblocks : ∀ a < hillGridSize n, ∀ i ≤ min n (2 ^ (a + 1)),
      |B i| ≤ Real.sqrt (2 * (min n (2 ^ (a + 1)) : ℕ) * x) + x) :
    ∀ i ∈ Finset.Icc L n,
      |B i| / Real.sqrt i ≤ 2 * Real.sqrt x + x / Real.sqrt L := by
  intro i hi
  obtain ⟨hli, hin⟩ := Finset.mem_Icc.mp hi
  obtain ⟨a, ha, hai, hia⟩ := hill_dyadic_block_cover (hL.trans hli) hin
  have him : i ≤ min n (2 ^ (a + 1)) := le_min hin hia.le
  have hmi : min n (2 ^ (a + 1)) ≤ 2 * i := by
    apply (min_le_right _ _).trans
    rw [pow_succ]
    omega
  have hsi : 0 < Real.sqrt (i : ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast hL.trans hli)
  have hsL : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hL)
  calc
    _ ≤ (Real.sqrt (2 * (min n (2 ^ (a + 1)) : ℕ) * x) + x) / Real.sqrt i :=
      div_le_div_of_nonneg_right (hblocks a ha i him) hsi.le
    _ ≤ (2 * Real.sqrt x * Real.sqrt i + x) / Real.sqrt i :=
      div_le_div_of_nonneg_right (by linarith [hill_dyadic_threshold_le hmi hx]) hsi.le
    _ = 2 * Real.sqrt x + x / Real.sqrt i := by field_simp
    _ ≤ _ := add_le_add le_rfl
      (div_le_div_of_nonneg_left hx hsL (Real.sqrt_le_sqrt
        (show (L : ℝ) ≤ i by exact_mod_cast hli)))

/-- For a confidence level [in the stated admissible domain](hyp:hd), [the logarithmic budget is nonnegative and allocates total failure probability one half of the confidence level across the dyadic grid](goal).
-/
-- @node: hill_logBudget_calibration
lemma hill_logBudget_calibration (n : ℕ) {delta : ℝ} (hd : ConfidenceDomain delta) :
    0 ≤ hillLogBudget n delta ∧
      (hillGridSize n : ℝ) * (2 * Real.exp (-hillLogBudget n delta)) = delta / 2 := by
  have hJ : 0 < (hillGridSize n : ℝ) := by
    unfold hillGridSize
    positivity
  have hr : 0 < 4 * (hillGridSize n : ℝ) / delta := div_pos (by positivity) hd.1
  have hrone : 1 ≤ 4 * (hillGridSize n : ℝ) / delta := by
    apply (le_div_iff₀ hd.1).mpr
    have hJone : (1 : ℝ) ≤ hillGridSize n := by
      exact_mod_cast (show 1 ≤ hillGridSize n by unfold hillGridSize; omega)
    linarith [hd.2]
  refine ⟨Real.log_nonneg hrone, ?_⟩
  unfold hillLogBudget
  rw [Real.exp_neg, Real.exp_log hr]
  field_simp
  <;> ring

/-- For a confidence level [in the stated admissible domain](hyp:hd), [the Hill deviation radius is nonnegative](goal).
-/
-- @node: hillDeviation_nonneg
lemma hillDeviation_nonneg (n : ℕ) {delta : ℝ} (hd : ConfidenceDomain delta) :
    0 ≤ hillDeviation n delta := by
  unfold hillDeviation
  exact add_nonneg (by positivity)
    (div_nonneg (hill_logBudget_calibration n hd).1 (Real.sqrt_nonneg _))

/-- If [the partial-sum process is measurable](hyp:hB), [the lower index is positive](hyp:hL), [the confidence level is admissible](hyp:hd), and [each dyadic block has its stated maximal failure bound](hyp:hmax), then [the simultaneous normalized spacing bound holds with probability at least one minus half the confidence level](goal).
-/
-- @node: hill_spacing_simultaneous_probability
lemma hill_spacing_simultaneous_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (hB : ∀ i, Measurable (B i)) {n L : ℕ} (hL : 1 ≤ L)
    {delta : ℝ} (hd : ConfidenceDomain delta)
    (hmax : ∀ a < hillGridSize n,
      P.real {w | ∃ i ≤ min n (2 ^ (a + 1)),
        Real.sqrt (2 * (min n (2 ^ (a + 1)) : ℕ) * hillLogBudget n delta) +
          hillLogBudget n delta < |B i w|} ≤
        2 * Real.exp (-hillLogBudget n delta)) :
    1 - delta / 2 ≤ P.real {w | ∀ i ∈ Finset.Icc L n,
      |B i w| / Real.sqrt i ≤
        2 * Real.sqrt (hillLogBudget n delta) + hillLogBudget n delta / Real.sqrt L} := by
  let bad : ℕ → Set Ω := fun a => {w | ∃ i ≤ min n (2 ^ (a + 1)),
    Real.sqrt (2 * (min n (2 ^ (a + 1)) : ℕ) * hillLogBudget n delta) +
      hillLogBudget n delta < |B i w|}
  have hbad : ∀ a, MeasurableSet (bad a) := by
    intro a
    simp only [bad, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : i ≤ min n (2 ^ (a + 1))
    · simp only [hi, true_and]
      have hAbs : Measurable (fun w => |B i w|) := by fun_prop
      exact measurableSet_lt measurable_const hAbs
    · simp only [hi, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  let failures := ⋃ a ∈ Finset.range (hillGridSize n), bad a
  have hf : MeasurableSet failures :=
    MeasurableSet.biUnion (Set.to_countable _) (fun a _ => hbad a)
  have hfailure : P.real failures ≤ delta / 2 := by
    calc
      _ ≤ ∑ a ∈ Finset.range (hillGridSize n), P.real (bad a) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _a ∈ Finset.range (hillGridSize n),
          2 * Real.exp (-hillLogBudget n delta) :=
        Finset.sum_le_sum fun a ha => hmax a (Finset.mem_range.mp ha)
      _ = delta / 2 := by
        simpa using (hill_logBudget_calibration n hd).2
  have hcontrol : failuresᶜ ⊆ {w | ∀ i ∈ Finset.Icc L n,
      |B i w| / Real.sqrt i ≤
        2 * Real.sqrt (hillLogBudget n delta) + hillLogBudget n delta / Real.sqrt L} := by
    intro w hw
    apply hill_spacing_bound_of_dyadic_control (fun i => B i w) hL
      (hill_logBudget_calibration n hd).1
    intro a ha i hi
    apply le_of_not_gt
    intro hlt
    apply hw
    exact Set.mem_iUnion₂.mpr ⟨a, Finset.mem_range.mpr ha, i, hi, hlt⟩
  calc
    1 - delta / 2 ≤ P.real failuresᶜ := by
      rw [measureReal_compl hf, probReal_univ]
      linarith
    _ ≤ _ := measureReal_mono hcontrol

/-- If [the lower index is positive](hyp:hL), [each centered partial sum equals its index times the centered average](hyp:hcenter), and [those partial sums obey the normalized bound](hyp:hbound), then [the corresponding centered averages obey the scaled bound](goal).
-/
-- @node: hill_spacing_average_bound
lemma hill_spacing_average_bound (A B : ℕ → ℝ) {n L : ℕ} {c : ℝ}
    (hL : 1 ≤ L)
    (hcenter : ∀ i ∈ Finset.Icc L n, B i = (i : ℝ) * (A i - 1))
    (hbound : ∀ i ∈ Finset.Icc L n, |B i| / Real.sqrt i ≤ c) :
    ∀ i ∈ Finset.Icc L n, |A i - 1| ≤ c / Real.sqrt i := by
  intro i hi
  have hiPos : 0 < (i : ℝ) := by exact_mod_cast hL.trans (Finset.mem_Icc.mp hi).1
  have hs : 0 < Real.sqrt (i : ℝ) := Real.sqrt_pos.mpr hiPos
  have hsq := Real.sq_sqrt hiPos.le
  have hb := hbound i hi
  rw [hcenter i hi, abs_mul, abs_of_pos hiPos] at hb
  have hb' := (div_le_iff₀ hs).mp hb
  apply (le_div_iff₀ hs).mpr
  apply (mul_le_mul_iff_right₀ hs).mp
  nth_rw 1 [← hsq] at hb'
  convert hb' using 1 <;> ring

/-- If [the partial-sum process is measurable](hyp:hB), [the Hill lower cutoff is positive](hyp:hL), [partial sums and averages are related by centering](hyp:hcenter), [the confidence level is admissible](hyp:hd), and [each dyadic block has its maximal failure bound](hyp:hmax), then [all Hill averages above the cutoff obey the calibrated deviation bound with probability at least one minus half the confidence level](goal).
-/
-- @node: hill_average_simultaneous_probability
lemma hill_average_simultaneous_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : ℕ → Ω → ℝ)
    (hB : ∀ i, Measurable (B i)) {n : ℕ} (hL : 1 ≤ hillLower n)
    (hcenter : ∀ w i, B i w = (i : ℝ) * (A i w - 1))
    {delta : ℝ} (hd : ConfidenceDomain delta)
    (hmax : ∀ a < hillGridSize n,
      P.real {w | ∃ i ≤ min n (2 ^ (a + 1)),
        Real.sqrt (2 * (min n (2 ^ (a + 1)) : ℕ) * hillLogBudget n delta) +
          hillLogBudget n delta < |B i w|} ≤
        2 * Real.exp (-hillLogBudget n delta)) :
    1 - delta / 2 ≤ P.real {w | ∀ i ∈ Finset.Icc (hillLower n) n,
      |A i w - 1| ≤ hillDeviation n delta / Real.sqrt i} := by
  apply (hill_spacing_simultaneous_probability P B hB hL hd hmax).trans
  apply measureReal_mono (h₂ := measure_ne_top P _)
  intro w hw
  exact hill_spacing_average_bound (fun i => A i w) (fun i => B i w) hL
    (fun i _ => hcenter w i) hw

end Papers.TbsExtremeEffects
