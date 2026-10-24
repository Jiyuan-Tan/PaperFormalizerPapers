module

public import Papers.OaiLinearVarianceRandom.Helpers.DelayTools
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # The tower estimate for the squared omission delay -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- If [there are at least six variables](hyp:hn), then [the duration bound times
the indicator of a nonempty nonroot solution set times the cube of the killing
probability is at most seven times the incidence parameter to the power three
halves times the occupation term](goal). -/
-- @node: durationBound_mul_cube_le
lemma durationBound_mul_cube_le (hn : OmissionN n) (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (ω : Ω) :
    durationBound c0 Cseq i m ω *
      ((if (nonrootSolutions c0 Cseq i m ω).Nonempty then 1 else 0) *
        killProcess c0 Cseq i m ω ^ 3) ≤
      occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
        occupationTerm c0 Cseq i m ω := by
  classical
  let p := killProcess c0 Cseq i m ω
  let a := occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta
  have hp := killProcess_bounds hn c0 Cseq i m ω
  by_cases hS : (nonrootSolutions c0 Cseq i m ω).Nonempty
  · simp only [if_pos hS, one_mul, occupationTerm]
    by_cases hpos : 0 < p
    · have hW : durationBound c0 Cseq i m ω ≤ a * p ^ (-beta) := by
        change (if 0 < p then min (capL n : ℝ) (a * p ^ (-beta)) else capL n) ≤ _
        rw [if_pos hpos]
        exact min_le_right _ _
      calc
        _ ≤ (a * p ^ (-beta)) * p ^ 3 :=
          mul_le_mul_of_nonneg_right hW (pow_nonneg hp.1 3)
        _ = a * p ^ beta := by
          rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hpos]
          norm_num [beta]
    · have hz : p = 0 := le_antisymm (le_of_not_gt hpos) hp.1
      change durationBound c0 Cseq i m ω * p ^ 3 ≤ a * p ^ beta
      simp [hz, beta]
  · simp [hS, occupationTerm]

/-- If [there are at least six variables](hyp:hn), then [the duration bound times
the indicator of a nonempty nonroot solution set times the squared killing
probability is at most seven times the incidence parameter to the power three
halves](goal). -/
-- @node: durationBound_mul_sq_le
lemma durationBound_mul_sq_le (hn : OmissionN n) (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (ω : Ω) :
    durationBound c0 Cseq i m ω *
      ((if (nonrootSolutions c0 Cseq i m ω).Nonempty then 1 else 0) *
        killProcess c0 Cseq i m ω ^ 2) ≤
      occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta := by
  classical
  let p := killProcess c0 Cseq i m ω
  let a := occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta
  have hp := killProcess_bounds hn c0 Cseq i m ω
  have ha : 0 ≤ a := by dsimp [a]; unfold occupationK; positivity
  by_cases hS : (nonrootSolutions c0 Cseq i m ω).Nonempty
  · simp only [if_pos hS, one_mul]
    by_cases hpos : 0 < p
    · have hW : durationBound c0 Cseq i m ω ≤ a * p ^ (-beta) := by
        change (if 0 < p then min (capL n : ℝ) (a * p ^ (-beta)) else capL n) ≤ _
        rw [if_pos hpos]
        exact min_le_right _ _
      calc
        _ ≤ (a * p ^ (-beta)) * p ^ 2 :=
          mul_le_mul_of_nonneg_right hW (pow_nonneg hp.1 2)
        _ = a * p ^ (2 - beta) := by
          rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hpos]
          congr 2
          ring
        _ ≤ a * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one hp.1 hp.2 (by norm_num [beta])) ha
        _ = a := mul_one _
    · have hz : p = 0 := le_antisymm (le_of_not_gt hpos) hp.1
      change durationBound c0 Cseq i m ω * p ^ 2 ≤ a
      simpa [hz] using ha
  · simpa [hS] using ha

/-- With [at least six variables](hyp:hn), [an independent uniform clause
process](hyp:hlaw), and [an omitted index between one and the cap](hyp:hi), [the
conditional second moment of the omission delay given the exposure information
is almost surely at most twice the conditional expectation, given that same
information, of the sum of duration bounds times pivotal probabilities
conditional on the ordinary information, from the omitted index up to, but
excluding, the cap, under the law fixing the omitted clause](goal). -/
-- @node: condExp_delay_sq_towers
lemma condExp_delay_sq_towers (hn : OmissionN n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : DelayIndex i (capL n)) (c0 : ProperClause n) :
    let ν := fixedClauseMeasure μ Cseq i c0
    ν[(fun ω => (delay (fun j => Cseq j ω) i : ℝ) ^ 2) | exposureSigma c0 Cseq i]
      ≤ᵐ[ν] fun ω => 2 * ν[(fun ω => ∑ m ∈ Finset.Ico i (capL n),
        durationBound c0 Cseq i m ω *
          ν[eventIndicator (pivotalEvent Cseq i m) | ordinaryFiltration c0 Cseq i m] ω) |
        exposureSigma c0 Cseq i] ω := by
  classical
  let ν := fixedClauseMeasure μ Cseq i c0
  haveI : IsProbabilityMeasure ν := fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi.1 c0
  let J := Finset.Ico i (capL n)
  let X (m : ℕ) := eventIndicator (pivotalEvent Cseq i m)
  let F (m : ℕ) : Ω → ℝ := fun ω => ∑ s ∈ Finset.Ico m (capL n), X s ω
  let W := durationBound c0 Cseq i
  let P (m : ℕ) := ν[X m | ordinaryFiltration c0 Cseq i m]
  have hX (m : ℕ) : Integrable (X m) ν :=
    eventIndicator_integrable ν _ (pivotalEvent_measurable Cseq hlaw.1 i m hi.1).setOf
  have hX01 (m : ℕ) (ω : Ω) : 0 ≤ X m ω ∧ X m ω ≤ 1 := by
    dsimp [X, eventIndicator]
    split_ifs <;> norm_num
  have hXb (m : ℕ) : ∀ᵐ ω ∂ν, ‖X m ω‖ ≤ 1 := Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hX01 m ω).1] using (hX01 m ω).2
  have hF (m : ℕ) : Integrable (F m) ν := by
    apply integrable_finset_sum
    intro s hs
    exact hX s
  have hXF (m : ℕ) : Integrable (X m * F m) ν :=
    (hF m).bdd_mul (hX m).aestronglyMeasurable (hXb m)
  have hT (m : ℕ) (hm : m ∈ J) : Integrable (W m * P m) ν := by
    have ht := Finset.mem_Ico.mp hm
    have hWG := durationBound_stronglyMeasurable c0 Cseq i m ⟨ht.1, ht.2.le⟩
    apply integrable_condExp.bdd_mul
      (hWG.mono (ordinaryFiltration_le c0 Cseq hlaw.1 i m)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (durationBound_range c0 Cseq i m ω).1]
        using (durationBound_range c0 Cseq i m ω).2
  have hD : Integrable (fun ω => (delay (fun j => Cseq j ω) i : ℝ) ^ 2) ν := by
    have hFb : ∀ᵐ ω ∂ν, ‖F i ω‖ ≤ (capL n : ℝ) := Filter.Eventually.of_forall fun ω => by
      simpa only [F, X, Real.norm_eq_abs, abs_of_nonneg (pivotal_tail_sum_bounds Cseq i i ω).1]
        using (pivotal_tail_sum_bounds Cseq i i ω).2
    convert (hF i).bdd_mul (hF i).aestronglyMeasurable hFb using 1
    funext ω
    rw [delay_real_eq_sum hn Cseq i hi ω, pow_two]
  have hpath : (fun ω => (delay (fun j => Cseq j ω) i : ℝ) ^ 2) ≤ᵐ[ν]
      (2 : ℝ) • (∑ m ∈ J, X m * F m) := by
    filter_upwards [] with ω
    rw [delay_real_eq_sum hn Cseq i hi ω]
    simpa only [J, F, X, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.mul_apply] using
      ordered_sum_square_le (fun m => X m ω) (fun m => (hX01 m ω).1) i (capL n)
  have hbound := condExp_mono (m := (exposureSigma c0 Cseq i)) hD
    (by
      convert (integrable_finset_sum J fun m hm => hXF m).const_mul 2 using 1
      ext ω
      simp) hpath
  have hsum := condExp_finsetSum (μ := ν) (s := J) (fun m hm => hXF m) (exposureSigma c0 Cseq i)
  have hscale := condExp_smul (μ := ν) (2 : ℝ) (∑ m ∈ J, X m * F m) (exposureSigma c0 Cseq i)
  have hterm (m : ℕ) (hm : m ∈ J) :
      ν[X m * F m | (exposureSigma c0 Cseq i)] ≤ᵐ[ν] ν[W m * P m | (exposureSigma c0 Cseq i)] := by
    have ht := Finset.mem_Ico.mp hm
    have hdur := condExp_pivotal_duration_le hn μ Cseq hlaw i hi c0 m ht
    apply condExp_weighted_duration_le ν (G := ordinaryFiltration c0 Cseq i m)
      (H := testFiltration c0 Cseq i m) le_sup_left le_sup_left
      (testFiltration_le c0 Cseq hlaw.1 i m) (hX m) (hF m)
      (pivotalIndicator_aestronglyMeasurable μ Cseq hlaw i hi.1 c0 m ht.2.le)
      hdur.2 (hX01 m) (capL n : ℝ) _ hdur.1
    intro ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (durationBound_range c0 Cseq i m ω).1]
      using (durationBound_range c0 Cseq i m ω).2
  have hterms : ∀ᵐ ω ∂ν, ∀ m ∈ J, ν[X m * F m | (exposureSigma c0 Cseq i)] ω ≤ ν[W m * P m | (exposureSigma c0 Cseq i)] ω := by
    exact (ae_all_iff.mpr fun m => ae_all_iff.mpr fun hm => hterm m hm)
  have hsumT := condExp_finsetSum (μ := ν) (s := J) hT (exposureSigma c0 Cseq i)
  filter_upwards [hbound, hsum, hscale, hterms, hsumT] with ω hb hs hc ht hsT
  change ν[(fun ω => (delay (fun j => Cseq j ω) i : ℝ) ^ 2) | (exposureSigma c0 Cseq i)] ω ≤
    2 * ν[(fun ω => ∑ m ∈ J, W m ω * P m ω) | (exposureSigma c0 Cseq i)] ω
  calc
    _ ≤ 2 * ∑ m ∈ J, ν[X m * F m | (exposureSigma c0 Cseq i)] ω := by
      simpa only [hc, hs, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using hb
    _ ≤ 2 * ∑ m ∈ J, ν[W m * P m | (exposureSigma c0 Cseq i)] ω := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm => ht m hm) (by norm_num)
    _ = _ := by
      have hy : (fun ω => ∑ m ∈ J, W m ω * P m ω) = ∑ m ∈ J, W m * P m := by
        ext ω
        simp
      rw [hy, hsT, Finset.sum_apply]

end Papers.OaiLinearVarianceRandom
