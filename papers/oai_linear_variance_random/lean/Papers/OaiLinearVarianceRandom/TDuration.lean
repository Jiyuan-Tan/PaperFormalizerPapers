module

public import Papers.OaiLinearVarianceRandom.Helpers.Pivotality
public import Papers.OaiLinearVarianceRandom.Helpers.MomentLaws
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Conditional duration of pivotality -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option linter.unusedVariables false

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- If [the current time lies between the omitted index and the cap](hyp:hm),
then [the duration bound is strongly measurable with respect to the ordinary
information available at that time](goal). -/
@[fun_prop]
-- @node: durationBound_stronglyMeasurable
lemma durationBound_stronglyMeasurable (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : i ≤ m ∧ m ≤ capL n) :
    StronglyMeasurable[ordinaryFiltration c0 Cseq i m] (durationBound c0 Cseq i m) := by
  letI : MeasurableSpace Ω := ordinaryFiltration c0 Cseq i m
  have hp := killProcess_stronglyMeasurable c0 Cseq i m hm
  have hd : Measurable (incidenceParam c0 Cseq i) :=
    (incidenceParam_measurable c0 Cseq i).mono le_sup_left le_rfl
  unfold durationBound
  apply Measurable.stronglyMeasurable
  apply Measurable.ite (measurableSet_lt measurable_const hp.measurable)
  · fun_prop
  · fun_prop

/-- If [every positively indexed clause is measurable](hyp:hC) and [the omitted
index is positive](hyp:hi), then [whether that clause is pivotal at any given
prefix is a measurable event](goal). -/
@[fun_prop]
-- @node: pivotalEvent_measurable
lemma pivotalEvent_measurable (Cseq : ℕ → Ω → ProperClause n)
    (hC : ∀ j, 1 ≤ j → Measurable (Cseq j)) (i s : ℕ) (hi : 1 ≤ i) :
    Measurable (fun ω => ω ∈ pivotalEvent Cseq i s) := by
  classical
  have hc (j : ℕ) (hj : 1 ≤ j) (z : Fin n → Bool) :
      Measurable (fun ω => ClauseSat (Cseq j ω) z) :=
    (measurable_of_finite (fun c : ProperClause n => ClauseSat c z)).comp (hC j hj)
  have hprefix (z : Fin n → Bool) : Measurable (fun ω =>
      ∀ j : Finset.Icc 1 s, (j : ℕ) ≠ i → ClauseSat (Cseq j ω) z) := by
    exact Measurable.forall fun j => (measurable_const.imp
      (hc j (Finset.mem_Icc.mp j.property).1 z))
  have hsat : Measurable (fun ω => ∃ z, ∀ j : Finset.Icc 1 s,
      (j : ℕ) ≠ i → ClauseSat (Cseq j ω) z) := Measurable.exists hprefix
  have hfull : Measurable (fun ω => ∃ z,
      (∀ j : Finset.Icc 1 s, (j : ℕ) ≠ i → ClauseSat (Cseq j ω) z) ∧
        ClauseSat (Cseq i ω) z) :=
    Measurable.exists fun z => (hprefix z).and (hc i hi z)
  convert (hsat.and hfull.not) using 1 <;>
    simp [pivotalEvent, omittedPrefixSat, Subtype.forall]

/-- If [an event is measurable](hyp:hA), then [its real-valued indicator is
integrable under any finite measure on outcomes](goal). -/
-- @node: eventIndicator_integrable
lemma eventIndicator_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) : Integrable (eventIndicator A) μ := by
  classical
  have heq : eventIndicator A = A.indicator (fun _ => (1 : ℝ)) := by
    ext ω
    simp [eventIndicator, Set.indicator_apply]
  rw [heq]
  exact (integrable_const (1 : ℝ)).indicator hA

/-- Suppose [there are at least six variables](hyp:hn), [the clauses are
measurable independent uniform draws](hyp:hlaw), [the omitted index lies between
one and the cap](hyp:hi), and [the current time is at least that index and
strictly below the cap](hyp:hm). Then [under the measure fixing the omitted
clause, the conditional expected number of pivotal prefixes from the current
time up to but excluding the cap, given the test information, is almost surely
at most the duration bound, and this bound is strongly measurable with respect
to the ordinary information at the current time](goal). -/
-- @node: thm:duration
theorem condExp_pivotal_duration_le {n : ℕ} (hn : OmissionN n)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : DelayIndex i (capL n)) (c0 : ProperClause n)
    (m : ℕ) (hm : DurationTime i m (capL n)) :
    (((fixedClauseMeasure μ Cseq i c0)[
        (fun ω => ∑ s ∈ Finset.Ico m (capL n), eventIndicator (pivotalEvent Cseq i s) ω) |
        testFiltration c0 Cseq i m]) ≤ᵐ[fixedClauseMeasure μ Cseq i c0]
          durationBound c0 Cseq i m) ∧
    StronglyMeasurable[ordinaryFiltration c0 Cseq i m] (durationBound c0 Cseq i m) := by
  classical
  let ν := fixedClauseMeasure μ Cseq i c0
  let F : Ω → ℝ := fun ω =>
    ∑ s ∈ Finset.Ico m (capL n), eventIndicator (pivotalEvent Cseq i s) ω
  let Q : Ω → ℝ := fun ω =>
    ∑ s ∈ Finset.Ico m (capL n), occupationTerm c0 Cseq i s ω
  let a : Ω → ℝ := fun ω => (killProcess c0 Cseq i m ω) ^ beta
  haveI : IsProbabilityMeasure ν :=
    fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi.1 c0
  have hH : (testFiltration c0 Cseq i m) ≤ ‹MeasurableSpace Ω› := testFiltration_le c0 Cseq hlaw.1 i m
  have haG : StronglyMeasurable[ordinaryFiltration c0 Cseq i m] a := by
    have hp := killProcess_stronglyMeasurable c0 Cseq i m ⟨hm.1, hm.2.le⟩
    dsimp [a]
    fun_prop
  have haH : StronglyMeasurable[(testFiltration c0 Cseq i m)] a := haG.mono le_sup_left
  have ha0 (ω : Ω) : 0 ≤ a ω :=
    Real.rpow_nonneg (killProcess_bounds hn c0 Cseq i m ω).1 _
  have ha1 (ω : Ω) : a ω ≤ 1 :=
    Real.rpow_le_one (killProcess_bounds hn c0 Cseq i m ω).1
      (killProcess_bounds hn c0 Cseq i m ω).2 (by norm_num [beta])
  have hF : Integrable F ν := by
    apply integrable_finset_sum
    intro s hs
    exact eventIndicator_integrable ν _
      (pivotalEvent_measurable Cseq hlaw.1 i s hi.1).setOf
  have hQ : Integrable Q ν := by
    apply integrable_finset_sum
    intro s hs
    have hs' := Finset.mem_Ico.mp hs
    exact occupationTerm_integrable hn ν c0 Cseq hlaw.1 i s
      ⟨hm.1.trans hs'.1, hs'.2.le⟩
  have haF : Integrable (a * F) ν := by
    exact hF.bdd_mul (haH.mono hH).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (ha0 ω)] using ha1 ω)
  have hFcap : ∀ ω, F ω ≤ (capL n : ℝ) := by
    intro ω
    calc
      F ω ≤ ∑ s ∈ Finset.Ico m (capL n), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        simp only [eventIndicator]
        split_ifs <;> norm_num
      _ = ((capL n - m : ℕ) : ℝ) := by simp
      _ ≤ capL n := by exact_mod_cast Nat.sub_le (capL n) m
  have hweighted : a * F ≤ᵐ[ν] Q := by
    filter_upwards [fixedClauseMeasure_ae_eq μ Cseq hlaw i hi.1 c0] with ω hfixed
    change a ω * F ω ≤ Q ω
    dsimp [F, Q]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hs' := Finset.mem_Ico.mp hs
    have hpmono : a ω ≤ (killProcess c0 Cseq i s ω) ^ beta := by
      apply Real.rpow_le_rpow (killProcess_bounds hn c0 Cseq i m ω).1
        (killProcess_monotone hn c0 Cseq i ω hs'.1) (by norm_num [beta])
    by_cases hp : ω ∈ pivotalEvent Cseq i s
    · have hS := pivotal_nonrootSolutions_nonempty c0 Cseq i s ω hfixed hp
      simpa only [eventIndicator, if_pos hp, mul_one, occupationTerm,
        if_pos hS, one_mul] using hpmono
    · have hnonneg : 0 ≤ occupationTerm c0 Cseq i s ω := by
        unfold occupationTerm
        split_ifs
        · simpa using Real.rpow_nonneg (killProcess_bounds hn c0 Cseq i s ω).1 beta
        · simp
      simpa only [eventIndicator, if_neg hp, mul_zero] using hnonneg
  have hcap : ν[F | (testFiltration c0 Cseq i m)] ≤ᵐ[ν] fun _ => (capL n : ℝ) := by
    have h := condExp_mono (m := (testFiltration c0 Cseq i m)) hF (integrable_const (capL n : ℝ))
      (Filter.Eventually.of_forall hFcap)
    simpa only [condExp_const hH] using h
  have hweightCE := condExp_mono (m := (testFiltration c0 Cseq i m)) haF hQ hweighted
  have hpull := condExp_mul_of_stronglyMeasurable_left haH haF hF
  have hocc := condExp_occupation_le hn μ Cseq hlaw i hi c0 m hm
  refine ⟨?_, durationBound_stronglyMeasurable c0 Cseq i m ⟨hm.1, hm.2.le⟩⟩
  filter_upwards [hcap, hweightCE, hpull, hocc] with ω hcapω hwω hpullω hoccω
  change ν[F | (testFiltration c0 Cseq i m)] ω ≤ durationBound c0 Cseq i m ω
  have hw : a ω * ν[F | (testFiltration c0 Cseq i m)] ω ≤
      occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta := by
    calc
      a ω * ν[F | (testFiltration c0 Cseq i m)] ω = ν[a * F | (testFiltration c0 Cseq i m)] ω := hpullω.symm
      _ ≤ ν[Q | (testFiltration c0 Cseq i m)] ω := hwω
      _ ≤ _ := hoccω
  unfold durationBound
  split_ifs with hp
  · apply le_min hcapω
    have hap : 0 < a ω := Real.rpow_pos_of_pos hp beta
    have hdiv : ν[F | (testFiltration c0 Cseq i m)] ω ≤
        (occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta) / a ω :=
      (le_div_iff₀ hap).mpr (by simpa only [mul_comm] using hw)
    simpa only [a, Real.rpow_neg hp.le, div_eq_mul_inv] using hdiv
  · exact hcapω

end Papers.OaiLinearVarianceRandom
