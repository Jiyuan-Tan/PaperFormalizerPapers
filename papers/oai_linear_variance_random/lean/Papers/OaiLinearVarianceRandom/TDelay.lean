module

public import Papers.OaiLinearVarianceRandom.Helpers.DelayTowers
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Conditional second moment of the omission delay -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option linter.unusedVariables false

/-- Suppose [there are at least six variables](hyp:hn), [the clauses are
measurable independent uniform draws](hyp:hlaw), and [the omitted index lies
between one and the cap](hyp:hi). Then [under the measure fixing the omitted
clause, the conditional second moment of the omission delay given the root
exposure is almost surely bounded by twice the squared occupation constant
times the cubed incidence parameter when there are no collisions, twice the
occupation constant times the cap times the incidence parameter to the power
three halves when there is one collision, and the squared cap when there are
at least two collisions](goal). -/
-- @node: prop:delay
theorem condExp_delay_sq_le {n : ℕ} (hn : OmissionN n)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : DelayIndex i (capL n)) (c0 : ProperClause n) :
    ((fixedClauseMeasure μ Cseq i c0)[
        (fun ω => (delay (fun j => Cseq j ω) i : ℝ) ^ 2) |
          exposureSigma c0 Cseq i])
    ≤ᵐ[fixedClauseMeasure μ Cseq i c0]
      (fun ω => 2 * occupationK ^ 2 * (incidenceParam c0 Cseq i ω : ℝ) ^ 3 *
          (if collisionCount c0 Cseq i ω = 0 then 1 else 0) +
        2 * occupationK * capL n * (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
          (if collisionCount c0 Cseq i ω = 1 then 1 else 0) +
        (capL n : ℝ) ^ 2 * (if 2 ≤ collisionCount c0 Cseq i ω then 1 else 0)) := by
  classical
  let ν := fixedClauseMeasure μ Cseq i c0
  haveI : IsProbabilityMeasure ν := fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi.1 c0
  let J := Finset.Ico i (capL n)
  let W := durationBound c0 Cseq i
  let P (m : ℕ) := ν[eventIndicator (pivotalEvent Cseq i m) | ordinaryFiltration c0 Cseq i m]
  let Y : Ω → ℝ := fun ω => ∑ m ∈ J, W m ω * P m ω
  let Q : Ω → ℝ := fun ω => ∑ m ∈ J, occupationTerm c0 Cseq i m ω
  let a : Ω → ℝ := fun ω => occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta
  have hE := exposureSigma_le c0 Cseq hlaw.1 i
  have haM : StronglyMeasurable[exposureSigma c0 Cseq i] a := by
    have hd := incidenceParam_measurable c0 Cseq i
    dsimp [a]
    fun_prop
  have ha : Integrable a ν := integrable_exposure_counts μ Cseq hlaw i hi.1 c0
    (fun d _ => occupationK * (d : ℝ) ^ beta)
  have ha0 (ω : Ω) : 0 ≤ a ω := by dsimp [a]; unfold occupationK; positivity
  have hQ : Integrable Q ν := by
    apply integrable_finset_sum
    intro m hm
    have ht := Finset.mem_Ico.mp hm
    exact occupationTerm_integrable hn ν c0 Cseq hlaw.1 i m ⟨ht.1, ht.2.le⟩
  have hQb : ∀ᵐ ω ∂ν, ‖Q ω‖ ≤ (capL n : ℝ) := by
    filter_upwards [] with ω
    have ht (m : ℕ) : 0 ≤ occupationTerm c0 Cseq i m ω ∧
        occupationTerm c0 Cseq i m ω ≤ 1 := by
      have hp := killProcess_bounds hn c0 Cseq i m ω
      have hb := Real.rpow_le_one (z := beta) hp.1 hp.2 (by norm_num [beta])
      have h0 := Real.rpow_nonneg hp.1 beta
      unfold occupationTerm
      split_ifs <;> simp [h0, hb]
    have h0 : 0 ≤ Q ω := Finset.sum_nonneg fun m hm => (ht m).1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    calc
      Q ω ≤ ∑ m ∈ J, (1 : ℝ) := Finset.sum_le_sum fun m hm => (ht m).2
      _ = ((capL n - i : ℕ) : ℝ) := by simp [J]
      _ ≤ capL n := by exact_mod_cast Nat.sub_le (capL n) i
  have haQ : Integrable (a * Q) ν := by
    convert ha.bdd_mul hQ.aestronglyMeasurable hQb using 1
    ext ω
    exact mul_comm _ _
  have hY : Integrable Y ν := by
    apply integrable_finset_sum
    intro m hm
    have ht := Finset.mem_Ico.mp hm
    have hM := durationBound_stronglyMeasurable c0 Cseq i m ⟨ht.1, ht.2.le⟩
    exact integrable_condExp.bdd_mul
      (hM.mono (ordinaryFiltration_le c0 Cseq hlaw.1 i m)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [W, Real.norm_eq_abs, abs_of_nonneg (durationBound_range c0 Cseq i m ω).1]
          using (durationBound_range c0 Cseq i m ω).2)
  have htests : ∀ᵐ ω ∂ν, ∀ m ∈ J,
      (collisionCount c0 Cseq i ω = 0 → W m ω * P m ω ≤ a ω * occupationTerm c0 Cseq i m ω) ∧
      (collisionCount c0 Cseq i ω = 1 → W m ω * P m ω ≤ a ω) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro hm
    have ht := Finset.mem_Ico.mp hm
    have hp := condProb_pivotal_le hn μ Cseq hlaw i hi c0 m ht
    filter_upwards [hp.1, hp.2] with ω h0 h1
    constructor
    · intro hv
      exact (mul_le_mul_of_nonneg_left (h0 hv) (durationBound_range c0 Cseq i m ω).1).trans
        (durationBound_mul_cube_le hn c0 Cseq i m ω)
    · intro hv
      exact (mul_le_mul_of_nonneg_left (h1 hv) (durationBound_range c0 Cseq i m ω).1).trans
        (durationBound_mul_sq_le hn c0 Cseq i m ω)
  have hV := collisionCount_measurable c0 Cseq i
  have h0 := condExp_le_on_event ν hE (hV (measurableSet_singleton 0)) hY haQ (by
    filter_upwards [htests] with ω ht hv
    change Y ω ≤ a ω * Q ω
    dsimp [Y, Q]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun m hm => (ht m hm).1 hv)
  have hLa : Integrable (fun ω => (capL n : ℝ) * a ω) ν := ha.const_mul _
  have h1 := condExp_le_on_event ν hE (hV (measurableSet_singleton 1)) hY hLa (by
    filter_upwards [htests] with ω ht hv
    calc
      Y ω ≤ ∑ m ∈ J, a ω := Finset.sum_le_sum fun m hm => (ht m hm).2 hv
      _ = ((capL n - i : ℕ) : ℝ) * a ω := by simp [J]
      _ ≤ (capL n : ℝ) * a ω := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.sub_le (capL n) i) (ha0 ω))
  have hocc : ν[Q | exposureSigma c0 Cseq i] ≤ᵐ[ν] a := by
    by_cases hiL : i < capL n
    · have ho := condExp_occupation_le hn μ Cseq hlaw i hi c0 i ⟨le_rfl, hiL⟩
      have hh := testFiltration_le c0 Cseq hlaw.1 i i
      have heh : exposureSigma c0 Cseq i ≤ testFiltration c0 Cseq i i := le_sup_left.trans le_sup_left
      have hb := condExp_mono (m := exposureSigma c0 Cseq i) integrable_condExp ha ho
      have haeq := condExp_of_stronglyMeasurable hE haM ha
      filter_upwards [hb, condExp_condExp_of_le (f := Q) heh hh] with ω hb ht
      change ν[ν[Q | testFiltration c0 Cseq i i] | exposureSigma c0 Cseq i] ω ≤
        ν[a | exposureSigma c0 Cseq i] ω at hb
      simpa only [ht, haeq] using hb
    · have hiEq : i = capL n := Nat.le_antisymm hi.2 (Nat.le_of_not_gt hiL)
      have hQ0 : Q = 0 := by ext ω; simp [Q, J, hiEq]
      rw [hQ0, condExp_zero]
      exact Filter.Eventually.of_forall ha0
  have hpull := condExp_mul_of_stronglyMeasurable_left haM haQ hQ
  have hLaeq := condExp_of_stronglyMeasurable hE (haM.const_mul (capL n : ℝ)) hLa
  have htowers := condExp_delay_sq_towers hn μ Cseq hlaw i hi c0
  have hD : Integrable (fun ω => (delay (fun j => Cseq j ω) i : ℝ) ^ 2) ν := by
    have hFi : Integrable (fun ω => ∑ m ∈ J, eventIndicator (pivotalEvent Cseq i m) ω) ν := by
      apply integrable_finset_sum
      intro m hm
      exact eventIndicator_integrable ν _ (pivotalEvent_measurable Cseq hlaw.1 i m hi.1).setOf
    convert hFi.bdd_mul hFi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [J, Real.norm_eq_abs, abs_of_nonneg (pivotal_tail_sum_bounds Cseq i i ω).1]
          using (pivotal_tail_sum_bounds Cseq i i ω).2) using 1
    funext ω
    rw [delay_real_eq_sum hn Cseq i hi ω, pow_two]
  have hcap := condExp_mono (m := exposureSigma c0 Cseq i) hD
    (integrable_const ((capL n : ℝ) ^ 2)) (Filter.Eventually.of_forall fun ω => by
      have hd := pivotal_tail_sum_bounds Cseq i i ω
      change (delay (fun j => Cseq j ω) i : ℝ) ^ 2 ≤ (capL n : ℝ) ^ 2
      rw [delay_real_eq_sum hn Cseq i hi ω]
      nlinarith)
  rw [condExp_const hE] at hcap
  filter_upwards [htowers, h0, h1, hpull, hocc, hcap] with ω ht hzero hone hp ho hc
  change ν[(fun ω => (delay (fun j => Cseq j ω) i : ℝ) ^ 2) | exposureSigma c0 Cseq i] ω ≤ _
  have haSq : a ω * a ω = occupationK ^ 2 * (incidenceParam c0 Cseq i ω : ℝ) ^ 3 := by
    dsimp [a]
    have hr : (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
        (incidenceParam c0 Cseq i ω : ℝ) ^ beta = (incidenceParam c0 Cseq i ω : ℝ) ^ 3 := by
      rw [← Real.rpow_add (by exact_mod_cast (exposure_counts_range c0 Cseq i hi ω).2.2 :
        0 < (incidenceParam c0 Cseq i ω : ℝ))]
      norm_num [beta]
    nlinarith [hr]
  by_cases hv0 : collisionCount c0 Cseq i ω = 0
  · have hb : ν[Y | exposureSigma c0 Cseq i] ω ≤ a ω * a ω := by
      calc
        _ ≤ ν[a * Q | exposureSigma c0 Cseq i] ω := hzero hv0
        _ = a ω * ν[Q | exposureSigma c0 Cseq i] ω := hp
        _ ≤ a ω * a ω := mul_le_mul_of_nonneg_left ho (ha0 ω)
    have hv1 : collisionCount c0 Cseq i ω ≠ 1 := by omega
    have hv2 : ¬ 2 ≤ collisionCount c0 Cseq i ω := by omega
    simp only [if_pos hv0, if_neg hv1, if_neg hv2, mul_one, mul_zero, add_zero]
    calc
      _ ≤ 2 * (a ω * a ω) := ht.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = _ := by rw [haSq]; ring
  · by_cases hv1 : collisionCount c0 Cseq i ω = 1
    · have hb : ν[Y | exposureSigma c0 Cseq i] ω ≤ (capL n : ℝ) * a ω := by
        simpa only [hLaeq] using hone hv1
      have hv2 : ¬ 2 ≤ collisionCount c0 Cseq i ω := by omega
      simp only [if_neg hv0, if_pos hv1, if_neg hv2, mul_zero, mul_one, zero_add, add_zero]
      have hh := ht.trans (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2))
      dsimp [a] at hh
      nlinarith
    · have hv2 : 2 ≤ collisionCount c0 Cseq i ω := by omega
      simpa only [if_neg hv0, if_neg hv1, if_pos hv2, mul_zero, mul_one, zero_add] using hc

end Papers.OaiLinearVarianceRandom
