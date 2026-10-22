module
public import Papers.TbsExtremeEffects.Helpers.Hill.Deviation

/-! Adaptive selection from the full-input Hill candidate set. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

/-- [A nonnegative tail index](hyp:hg), [a nonnegative deviation level](hyp:hc), [a positive first prefix rank](hyp:hL), [a sufficiently small deviation at that rank](hyp:hsmall), [the spacing-average bounds](hyp:hspacing), and [the Hill-bias bounds](hyp:hbias) imply [the displayed accuracy and two-sided bounds for every prefix statistic](goal). -/
-- @node: hill_prefix_bounds_of_spacing_control
lemma hill_prefix_bounds_of_spacing_control (H A : ℕ → ℝ) (g c : ℝ) (L k : ℕ)
    (hg : 0 ≤ g) (hc : 0 ≤ c) (hL : 1 ≤ L)
    (hsmall : c / Real.sqrt L ≤ 1 / 6)
    (hspacing : ∀ i ∈ Finset.Icc L k, |A i - 1| ≤ c / Real.sqrt i)
    (hbias : ∀ i ∈ Finset.Icc L k,
      |H i - g * A i| ≤ (g * c / Real.sqrt k) * A i) :
    ∀ i ∈ Finset.Icc L k,
      |H i - g| ≤ 3 * g * c / Real.sqrt i ∧
        g / 2 ≤ H i ∧ H i ≤ 3 * g / 2 := by
  intro i hi
  obtain ⟨hli, hik⟩ := Finset.mem_Icc.mp hi
  have hsL : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hL)
  have hsi : 0 < Real.sqrt (i : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hL.trans hli)
  have hsLi : Real.sqrt (L : ℝ) ≤ Real.sqrt (i : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hli)
  have hsik : Real.sqrt (i : ℝ) ≤ Real.sqrt (k : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hik)
  let ci := c / Real.sqrt i
  let ck := c / Real.sqrt k
  have hci : 0 ≤ ci := div_nonneg hc hsi.le
  have hci_small : ci ≤ 1 / 6 :=
    (div_le_div_of_nonneg_left hc hsL hsLi).trans hsmall
  have hck_ci : ck ≤ ci := div_le_div_of_nonneg_left hc hsi hsik
  have hA := hspacing i hi
  change |A i - 1| ≤ ci at hA
  obtain ⟨hAlo, hAhi⟩ := abs_le.mp hA
  have hApos : 0 ≤ A i := by linarith
  have hAupper : A i ≤ 7 / 6 := by linarith
  have hgc : 0 ≤ g * ci := mul_nonneg hg hci
  have hbiased : |H i - g * A i| ≤ (g * ci) * (7 / 6) := by
    calc
      _ ≤ (g * ck) * A i := by simpa only [ck, mul_div_assoc] using hbias i hi
      _ ≤ (g * ci) * A i :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hck_ci hg) hApos
      _ ≤ (g * ci) * (7 / 6) := mul_le_mul_of_nonneg_left hAupper hgc
  have hcenter : |g * A i - g| ≤ g * ci := by
    calc
      _ = g * |A i - 1| := by
        rw [show g * A i - g = g * (A i - 1) by ring, abs_mul, abs_of_nonneg hg]
      _ ≤ _ := mul_le_mul_of_nonneg_left hA hg
  have herr : |H i - g| ≤ 3 * g * ci := by
    calc
      _ ≤ |H i - g * A i| + |g * A i - g| := abs_sub_le _ _ _
      _ ≤ (g * ci) * (7 / 6) + g * ci := add_le_add hbiased hcenter
      _ ≤ _ := by nlinarith
  have hhalf : 3 * g * ci ≤ g / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hci_small hg]
  have habs := abs_le.mp (herr.trans hhalf)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ci, mul_div_assoc] using herr
  · linarith [habs.1]
  · linarith [habs.2]

/-- [The proposed rank lies in the candidate range](hyp:hk) and [it passes every required prefix comparison](hyp:hqual) imply that [it is no larger than the adaptively selected rank](goal). -/
-- @node: hillIndex_ge_of_qualifies
lemma hillIndex_ge_of_qualifies (M : ExtremeModel q d) (E : NeteExperiment M)
    (n k : ℕ) (delta : ℝ) (w : E.Om)
    (hk : k ∈ Finset.Icc (hillLower n) (n - 1))
    (hqual : ∀ i ∈ Finset.Icc (hillLower n) k,
      |hillStat E n i w - hillStat E n k w| ≤
        hillStat E n i w * hillTol n delta / Real.sqrt i) :
    k ≤ hillIndex E n delta w := by
  classical
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hk, hqual⟩)

/-- [The proposed rank lies in the candidate range](hyp:hk) and [it passes every required prefix comparison](hyp:hqual) imply that [the selected rank is a candidate and satisfies all of its own prefix comparisons](goal). -/
-- @node: hillIndex_qualifies_of_candidate
lemma hillIndex_qualifies_of_candidate (M : ExtremeModel q d) (E : NeteExperiment M)
    (n k : ℕ) (delta : ℝ) (w : E.Om)
    (hk : k ∈ Finset.Icc (hillLower n) (n - 1))
    (hqual : ∀ i ∈ Finset.Icc (hillLower n) k,
      |hillStat E n i w - hillStat E n k w| ≤
        hillStat E n i w * hillTol n delta / Real.sqrt i) :
    hillIndex E n delta w ∈ Finset.Icc (hillLower n) (n - 1) ∧
      ∀ i ∈ Finset.Icc (hillLower n) (hillIndex E n delta w),
        |hillStat E n i w - hillAdaptive E n delta w| ≤
          hillStat E n i w * hillTol n delta / Real.sqrt i := by
  classical
  let candidates := (Finset.Icc (hillLower n) (n - 1)).filter (fun j =>
    ∀ i ∈ Finset.Icc (hillLower n) j,
      |hillStat E n i w - hillStat E n j w| ≤
        hillStat E n i w * hillTol n delta / Real.sqrt i)
  have hmem : k ∈ candidates := Finset.mem_filter.mpr ⟨hk, hqual⟩
  have hmax := Finset.sup_mem_of_nonempty (f := id) ⟨k, hmem⟩
  have hselected : hillIndex E n delta w ∈ candidates := by
    obtain ⟨j, hj, heq⟩ := hmax
    change j = hillIndex E n delta w at heq
    exact heq ▸ hj
  exact Finset.mem_filter.mp hselected

/-- [A nonnegative tail index](hyp:hg), [a nonnegative deviation level](hyp:hc), [a positive lower candidate rank](hyp:hL), [the oracle error bounds](hyp:herror), and [the oracle lower bounds](hyp:hlower) imply [that every oracle prefix passes the adaptive selection comparison](goal). -/
-- @node: hill_oracle_qualifies
lemma hill_oracle_qualifies (M : ExtremeModel q d) (E : NeteExperiment M)
    (n k : ℕ) (delta : ℝ) (w : E.Om)
    (hg : 0 ≤ gamma M) (hc : 0 ≤ hillDeviation n delta)
    (hL : 1 ≤ hillLower n)
    (herror : ∀ i ∈ Finset.Icc (hillLower n) k,
      |hillStat E n i w - gamma M| ≤
        3 * gamma M * hillDeviation n delta / Real.sqrt i)
    (hlower : ∀ i ∈ Finset.Icc (hillLower n) k,
      gamma M / 2 ≤ hillStat E n i w) :
    ∀ i ∈ Finset.Icc (hillLower n) k,
      |hillStat E n i w - hillStat E n k w| ≤
        hillStat E n i w * hillTol n delta / Real.sqrt i := by
  intro i hi
  obtain ⟨hli, hik⟩ := Finset.mem_Icc.mp hi
  have hk : k ∈ Finset.Icc (hillLower n) k := Finset.mem_Icc.mpr ⟨hli.trans hik, le_rfl⟩
  have hsi : 0 < Real.sqrt (i : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hL.trans hli)
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (hL.trans hli).trans hik)
  have hsik : Real.sqrt (i : ℝ) ≤ Real.sqrt (k : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hik)
  have hnum : 0 ≤ 3 * gamma M * hillDeviation n delta := by positivity
  have hdiv : 3 * gamma M * hillDeviation n delta / Real.sqrt k ≤
      3 * gamma M * hillDeviation n delta / Real.sqrt i :=
    div_le_div_of_nonneg_left hnum hsi hsik
  have htriangle := abs_sub_le (hillStat E n i w) (gamma M) (hillStat E n k w)
  rw [abs_sub_comm (gamma M) (hillStat E n k w)] at htriangle
  have hsum : |hillStat E n i w - hillStat E n k w| ≤
      6 * gamma M * hillDeviation n delta / Real.sqrt i := by
    calc
      _ ≤ |hillStat E n i w - gamma M| + |hillStat E n k w - gamma M| := htriangle
      _ ≤ 3 * gamma M * hillDeviation n delta / Real.sqrt i +
          3 * gamma M * hillDeviation n delta / Real.sqrt i :=
        add_le_add (herror i hi) ((herror k hk).trans hdiv)
      _ = _ := by ring
  apply hsum.trans
  rw [hillTol]
  apply (div_le_div_iff_of_pos_right hsi).mpr
  have hbase : 6 * gamma M ≤ hillStat E n i w * 16 := by
    have := hlower i hi
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hbase hc]

/-- [A nonnegative tail index](hyp:hg), [a nonnegative deviation level](hyp:hc), [a positive lower candidate rank](hyp:hL), [an oracle rank in the candidate range](hyp:hk), [the oracle error bounds](hyp:herror), [the oracle lower bounds](hyp:hlower), and [the oracle endpoint upper bound](hyp:hupper) imply [that the selected rank is at least the oracle rank and the adaptive estimate obeys the stated constant-27 error bound](goal). -/
-- @node: hill_adaptive_oracle_bound
lemma hill_adaptive_oracle_bound (M : ExtremeModel q d) (E : NeteExperiment M)
    (n k : ℕ) (delta : ℝ) (w : E.Om)
    (hg : 0 ≤ gamma M) (hc : 0 ≤ hillDeviation n delta)
    (hL : 1 ≤ hillLower n)
    (hk : k ∈ Finset.Icc (hillLower n) (n - 1))
    (herror : ∀ i ∈ Finset.Icc (hillLower n) k,
      |hillStat E n i w - gamma M| ≤
        3 * gamma M * hillDeviation n delta / Real.sqrt i)
    (hlower : ∀ i ∈ Finset.Icc (hillLower n) k,
      gamma M / 2 ≤ hillStat E n i w)
    (hupper : hillStat E n k w ≤ 3 * gamma M / 2) :
    k ≤ hillIndex E n delta w ∧
      |hillAdaptive E n delta w - gamma M| ≤
        27 * gamma M * hillDeviation n delta / Real.sqrt k := by
  have hqual := hill_oracle_qualifies M E n k delta w hg hc hL herror hlower
  have hge := hillIndex_ge_of_qualifies M E n k delta w hk hqual
  refine ⟨hge, ?_⟩
  have hselected := (hillIndex_qualifies_of_candidate M E n k delta w hk hqual).2
  have hk' : k ∈ Finset.Icc (hillLower n) k :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, le_rfl⟩
  have hcompare := hselected k (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, hge⟩)
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast hL.trans (Finset.mem_Icc.mp hk).1)
  have htolerance : hillStat E n k w * hillTol n delta / Real.sqrt k ≤
      24 * gamma M * hillDeviation n delta / Real.sqrt k := by
    rw [hillTol]
    apply (div_le_div_iff_of_pos_right hsk).mpr
    nlinarith [mul_le_mul_of_nonneg_right hupper hc]
  calc
    _ ≤ |hillAdaptive E n delta w - hillStat E n k w| +
        |hillStat E n k w - gamma M| := abs_sub_le _ _ _
    _ ≤ 24 * gamma M * hillDeviation n delta / Real.sqrt k +
        3 * gamma M * hillDeviation n delta / Real.sqrt k := by
      rw [abs_sub_comm (hillAdaptive E n delta w)]
      exact add_le_add (hcompare.trans htolerance) (herror k hk')
    _ = _ := by ring

/-- [A nonnegative tail index](hyp:hg), [a nonnegative deviation level](hyp:hc), [a positive lower candidate rank](hyp:hL), [an oracle rank in the candidate range](hyp:hk), [a small lower-rank deviation](hyp:hsmall), [the spacing event bounds](hyp:hspacing), and [the bias event bounds](hyp:hbias) imply [the oracle-rank and constant-27 adaptive error guarantees](goal). -/
-- @node: hill_adaptive_bound_of_spacing_control
lemma hill_adaptive_bound_of_spacing_control (M : ExtremeModel q d)
    (E : NeteExperiment M) (n k : ℕ) (delta : ℝ) (w : E.Om) (A : ℕ → ℝ)
    (hg : 0 ≤ gamma M) (hc : 0 ≤ hillDeviation n delta)
    (hL : 1 ≤ hillLower n)
    (hk : k ∈ Finset.Icc (hillLower n) (n - 1))
    (hsmall : hillDeviation n delta / Real.sqrt (hillLower n) ≤ 1 / 6)
    (hspacing : ∀ i ∈ Finset.Icc (hillLower n) k,
      |A i - 1| ≤ hillDeviation n delta / Real.sqrt i)
    (hbias : ∀ i ∈ Finset.Icc (hillLower n) k,
      |hillStat E n i w - gamma M * A i| ≤
        (gamma M * hillDeviation n delta / Real.sqrt k) * A i) :
    k ≤ hillIndex E n delta w ∧
      |hillAdaptive E n delta w - gamma M| ≤
        27 * gamma M * hillDeviation n delta / Real.sqrt k := by
  have hbounds := hill_prefix_bounds_of_spacing_control (fun i => hillStat E n i w) A
    (gamma M) (hillDeviation n delta) (hillLower n) k hg hc hL hsmall hspacing hbias
  have hk' : k ∈ Finset.Icc (hillLower n) k :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, le_rfl⟩
  exact hill_adaptive_oracle_bound M E n k delta w hg hc hL hk
    (fun i hi => (hbounds i hi).1) (fun i hi => (hbounds i hi).2.1) (hbounds k hk').2.2

/-- [Measurability of the tail event](hyp:hT), [the spacing-event probability bound](hyp:hSprob), [the tail-event probability bound](hyp:hTprob), [a nonnegative tail index](hyp:hg), [a nonnegative deviation level](hyp:hc), [a positive lower candidate rank](hyp:hL), [an oracle rank in the candidate range](hyp:hk), [a small lower-rank deviation](hyp:hsmall), [the spacing bounds on the spacing event](hyp:hspacing), [the bias bounds on the tail event](hyp:hbias), and [an error radius at least as large as the deterministic bound](hyp:hrate) imply [confidence at least one minus delta for the adaptive error bound](goal).
Their independence is not required. -/
-- @node: hill_adaptive_probability_of_oracle_events
lemma hill_adaptive_probability_of_oracle_events (M : ExtremeModel q d)
    (E : NeteExperiment M) (n k : ℕ) (delta r : ℝ) (A : ℕ → E.Om → ℝ)
    (S T : Set E.Om) (hT : MeasurableSet T)
    (hSprob : 1 - delta / 2 ≤ E.P.real S)
    (hTprob : 1 - delta / 2 ≤ E.P.real T)
    (hg : 0 ≤ gamma M) (hc : 0 ≤ hillDeviation n delta)
    (hL : 1 ≤ hillLower n)
    (hk : k ∈ Finset.Icc (hillLower n) (n - 1))
    (hsmall : hillDeviation n delta / Real.sqrt (hillLower n) ≤ 1 / 6)
    (hspacing : ∀ w ∈ S, ∀ i ∈ Finset.Icc (hillLower n) k,
      |A i w - 1| ≤ hillDeviation n delta / Real.sqrt i)
    (hbias : ∀ w ∈ T, ∀ i ∈ Finset.Icc (hillLower n) k,
      |hillStat E n i w - gamma M * A i w| ≤
        (gamma M * hillDeviation n delta / Real.sqrt k) * A i w)
    (hrate : 27 * gamma M * hillDeviation n delta / Real.sqrt k ≤ r) :
    1 - delta ≤ E.P.real {w | |gamma M - hillAdaptive E n delta w| ≤ r} := by
  have hinter : 1 - delta ≤ E.P.real (S ∩ T) := by
    have hunion : E.P.real (S ∪ T) ≤ 1 := by
      simpa using (measureReal_mono (μ := E.P) (Set.subset_univ (S ∪ T)))
    have hadd := measureReal_union_add_inter (μ := E.P) (s := S) hT
    linarith
  apply hinter.trans
  apply measureReal_mono (h₂ := measure_ne_top E.P _)
  intro w hw
  have hbound := (hill_adaptive_bound_of_spacing_control M E n k delta w
    (fun i => A i w) hg hc hL hk hsmall (hspacing w hw.1) (hbias w hw.2)).2
  change |gamma M - hillAdaptive E n delta w| ≤ r
  simpa only [abs_sub_comm] using hbound.trans hrate

end Papers.TbsExtremeEffects
