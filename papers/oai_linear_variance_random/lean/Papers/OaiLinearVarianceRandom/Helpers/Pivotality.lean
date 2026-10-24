module

public import Papers.OaiLinearVarianceRandom.Helpers.HiddenClauses
public import Papers.OaiLinearVarianceRandom.Helpers.RefinedHiddenClauses
public import Papers.OaiLinearVarianceRandom.Helpers.OrdinaryHiddenClauses
public import Papers.OaiLinearVarianceRandom.Helpers.TestNecessity
public import Papers.OaiLinearVarianceRandom.Helpers.TestClauses
public import Papers.OaiLinearVarianceRandom.Helpers.TestFamilyConditioning
public import Papers.OaiLinearVarianceRandom.Helpers.PivotalVector
public import Papers.OaiLinearVarianceRandom.Helpers.OrdinaryDrift
public import Papers.OaiLinearVarianceRandom.Helpers.OccupationMeasure
public import Papers.OaiLinearVarianceRandom.Helpers.MomentLaws
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Toolkit.Foundations.Probability.Processes.DriftRecursion

/-! # Conditional pivotality and occupation estimates -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option linter.unusedVariables false

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- If [there are at least six variables](hyp:hn), [the clauses are independent
and uniform](hyp:hlaw), [the omitted index is positive and at most the cap](hyp:hi),
and [the prefix cutoff is at least the omitted index and strictly below the
cap](hyp:hm), then [under the law fixing the omitted clause, the conditional
probability of pivotality given the ordinary filtration is almost surely at
most the cube of the killing probability when there are no collisions and at
most its square when there is one collision, with both bounds multiplied by
the indicator that the nonroot solution set is nonempty](goal). -/
-- @node: lem:tests
lemma condProb_pivotal_le (hn : OmissionN n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : DelayIndex i (capL n)) (c0 : ProperClause n)
    (m : ℕ) (hm : TestsTime i m (capL n)) :
    (∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0), collisionCount c0 Cseq i ω = 0 →
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator (pivotalEvent Cseq i m) |
          ordinaryFiltration c0 Cseq i m]) ω ≤
      (if (nonrootSolutions c0 Cseq i m ω).Nonempty then 1 else 0) *
        (killProcess c0 Cseq i m ω) ^ 3) ∧
    (∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0), collisionCount c0 Cseq i ω = 1 →
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator (pivotalEvent Cseq i m) |
          ordinaryFiltration c0 Cseq i m]) ω ≤
      (if (nonrootSolutions c0 Cseq i m ω).Nonempty then 1 else 0) *
        (killProcess c0 Cseq i m ω) ^ 2) := by
  classical
  have hbound : ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      ((fixedClauseMeasure μ Cseq i c0)[eventIndicator (pivotalEvent Cseq i m) |
        ordinaryFiltration c0 Cseq i m]) ω ≤
      (if (nonrootSolutions c0 Cseq i m ω).Nonempty then 1 else 0) *
        (killProcess c0 Cseq i m ω) ^ (availableRoots c0 Cseq i ω).card := by
    filter_upwards [condProb_pivotal_eq_fiber_fraction μ Cseq hlaw i hi.1 c0 m hm.2.le]
      with ω hω
    rw [hω]
    have hb := pivotalVector_fiber_fraction_le hn c0 Cseq i m hm.2.le ω
    simp only [← Nat.card_eq_fintype_card] at hb ⊢
    exact hb
  constructor
  · filter_upwards [hbound] with ω hb
    intro hv
    rw [(availableRoots_killProcess_powers c0 Cseq i m ω).1 hv] at hb
    exact hb
  · filter_upwards [hbound] with ω hb
    intro hv
    exact hb.trans (mul_le_mul_of_nonneg_left
      ((availableRoots_killProcess_powers c0 Cseq i m ω).2 hv)
      (by split_ifs <;> norm_num))

/-- If [there are at least six variables](hyp:hn), [the clauses are independent
and uniform](hyp:hlaw), [the omitted index is positive and at most the cap](hyp:hi),
and [the starting time is at least the omitted index and strictly below the
cap](hyp:hm), then [under the law fixing the omitted clause, the conditional
expected sum of occupation terms from that time up to but excluding the cap,
given the test filtration at the starting time, is almost surely at most the
occupation constant times the incidence parameter raised to the occupation
exponent](goal). -/
-- @node: lem:occupation
lemma condExp_occupation_le (hn : OmissionN n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : DelayIndex i (capL n)) (c0 : ProperClause n)
    (m : ℕ) (hm : OccupationTime i m (capL n)) :
    ((fixedClauseMeasure μ Cseq i c0)[
        (fun ω => ∑ s ∈ Finset.Ico m (capL n), occupationTerm c0 Cseq i s ω) |
        testFiltration c0 Cseq i m]) ≤ᵐ[fixedClauseMeasure μ Cseq i c0]
      (fun ω => occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta) := by
  classical
  let ν := fixedClauseMeasure μ Cseq i c0
  let B : Ω → ℝ := fun ω => (incidenceParam c0 Cseq i ω : ℝ) ^ beta
  let O : Ω → ℝ := fun ω => ∑ s ∈ Finset.Ico m (capL n),
    if isOrdinary c0 (Cseq (s + 1) ω) then occupationTerm c0 Cseq i s ω else 0
  let N : Ω → ℝ := fun ω => ∑ s ∈ Finset.Ico m (capL n),
    if isOrdinary c0 (Cseq (s + 1) ω) then 0 else occupationTerm c0 Cseq i s ω
  haveI : IsProbabilityMeasure ν :=
    fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi.1 c0
  have hH : (testFiltration c0 Cseq i m) ≤ ‹MeasurableSpace Ω› := testFiltration_le c0 Cseq hlaw.1 i m
  have hBmeas : StronglyMeasurable[(testFiltration c0 Cseq i m)] B := by
    have hd : @Measurable Ω ℕ (testFiltration c0 Cseq i m) inferInstance (incidenceParam c0 Cseq i) :=
      (incidenceParam_measurable c0 Cseq i).mono (le_sup_left.trans le_sup_left) le_rfl
    dsimp [B]
    fun_prop
  have hBint : Integrable B ν := by
    apply Integrable.of_bound (hBmeas.mono hH).aestronglyMeasurable
      ((capL n : ℝ) ^ beta)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    apply Real.rpow_le_rpow (Nat.cast_nonneg _)
    · exact_mod_cast (show incidenceParam c0 Cseq i ω ≤ capL n by
        have hz := (exposure_counts_range c0 Cseq i hi ω).1
        have hL : 1 ≤ capL n := hi.1.trans hi.2
        exact max_le hL (hz.trans (Nat.sub_le _ _)))
    · norm_num [beta]
  have hterm (s : ℕ) (hs : s ∈ Finset.Ico m (capL n)) :
      Integrable (occupationTerm c0 Cseq i s) ν := by
    obtain ⟨hms, hsL⟩ := Finset.mem_Ico.mp hs
    exact occupationTerm_integrable hn ν c0 Cseq hlaw.1 i s
      ⟨hm.1.trans hms, hsL.le⟩
  have hOrd (s : ℕ) (hs : s ∈ Finset.Ico m (capL n)) :
      MeasurableSet {ω | isOrdinary c0 (Cseq (s + 1) ω)} := by
    have h : Measurable (fun ω => isOrdinary c0 (Cseq (s + 1) ω)) := by
      exact (measurable_of_finite (isOrdinary c0)).comp (hlaw.1 _ (by omega))
    exact h.setOf
  have hOint : Integrable O ν := by
    apply integrable_finsetSum
    intro s hs
    convert (hterm s hs).indicator (hOrd s hs) using 1
    ext ω
    simp [Set.indicator_apply]
  have hNint : Integrable N ν := by
    apply integrable_finsetSum
    intro s hs
    convert (hterm s hs).indicator (hOrd s hs).compl using 1
    ext ω
    simp only [Set.indicator, Set.mem_compl_iff, Set.mem_ofPred_eq]
    split_ifs <;> rfl
  have hNbound : N ≤ᵐ[ν] B := by
    filter_upwards [] with ω
    have hnon := occupation_nonordinary_sum_le hn c0 Cseq i m hm.1 ω
    have hz := incidenceCount_le_rpow_beta c0 Cseq i ω
    dsimp [N, B]
    simpa only [Finset.sum_filter, ite_not] using hnon.trans hz
  have hNce := condExp_mono (m := testFiltration c0 Cseq i m) hNint hBint hNbound
  have hBce : ν[B | (testFiltration c0 Cseq i m)] =ᵐ[ν] B :=
    Filter.Eventually.of_forall (congrFun (condExp_of_stronglyMeasurable hH hBmeas hBint))
  -- Extend the ordinary-step drift by nonnegativity to all potential increments,
  -- then condition down to H_m and telescope the full increment sum.
  have hordinary : ν[O | (testFiltration c0 Cseq i m)] ≤ᵐ[ν] fun ω =>
      3 * B ω + (capL n : ℝ) * B ω * (nonrootCount n : ℝ) ^ (-3 : ℝ) := by
    let J := Finset.Ico m (capL n)
    let A : Ω → ℝ := fun ω => 3 * (incidenceParam c0 Cseq i ω : ℝ) ^ (beta - 1)
    let P (s : ℕ) : Ω → ℝ := fun ω =>
      potential (incidenceParam c0 Cseq i ω) (nonrootSolutions c0 Cseq i s ω)
    let D (s : ℕ) : Ω → ℝ := P (s + 1) - P s
    let X (s : ℕ) : Ω → ℝ := fun ω =>
      if isOrdinary c0 (Cseq (s + 1) ω) then occupationTerm c0 Cseq i s ω else 0
    let E : Ω → ℝ := fun ω => B ω * (nonrootCount n : ℝ) ^ (-3 : ℝ)
    have hdle (ω : Ω) : (incidenceParam c0 Cseq i ω : ℝ) ≤ capL n := by
      exact_mod_cast (show incidenceParam c0 Cseq i ω ≤ capL n from
        max_le (hi.1.trans hi.2)
          ((exposure_counts_range c0 Cseq i hi ω).1.trans (Nat.sub_le _ _)))
    have hAmeas (s : ℕ) : StronglyMeasurable[testFiltration c0 Cseq i s] A := by
      have hd : @Measurable Ω ℕ (testFiltration c0 Cseq i s) inferInstance
          (incidenceParam c0 Cseq i) :=
        (incidenceParam_measurable c0 Cseq i).mono (le_sup_left.trans le_sup_left) le_rfl
      dsimp [A]
      fun_prop
    have hAbound : ∀ᵐ ω ∂ν, ‖A ω‖ ≤ 3 * (capL n : ℝ) ^ (beta - 1) := by
      filter_upwards [] with ω
      dsimp [A]
      rw [abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (hdle ω) (by norm_num [beta])
    have hPmeas (s : ℕ) (hs : i ≤ s ∧ s ≤ capL n) :
        StronglyMeasurable[testFiltration c0 Cseq i s] (P s) := by
      let : MeasurableSpace Ω := testFiltration c0 Cseq i s
      have hd : Measurable (incidenceParam c0 Cseq i) :=
        (incidenceParam_measurable c0 Cseq i).mono (le_sup_left.trans le_sup_left) le_rfl
      have hS : Measurable (nonrootSolutions c0 Cseq i s) :=
        (nonrootSolutions_measurable c0 Cseq i s hs).mono le_sup_left le_top
      have hp : Measurable (fun p : ℕ × Finset (Fin (nonrootCount n) → Bool) =>
          potential p.1 p.2) := by fun_prop
      exact (hp.comp (hd.prodMk hS)).stronglyMeasurable
    have hPint (s : ℕ) (hs : i ≤ s ∧ s ≤ capL n) : Integrable (P s) ν := by
      apply Integrable.of_bound
        ((hPmeas s hs).mono (testFiltration_le c0 Cseq hlaw.1 i s)).aestronglyMeasurable
        (capL n : ℝ)
      filter_upwards [] with ω
      have hb := potential_bounds (incidenceParam c0 Cseq i ω)
        (nonrootSolutions c0 Cseq i s ω)
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2.trans (hdle ω)
    have hDint (s : ℕ) (hs : s ∈ J) : Integrable (D s) ν := by
      obtain ⟨hms, hsL⟩ := Finset.mem_Ico.mp hs
      have him := hm.1
      exact (hPint (s + 1) ⟨by omega, hsL⟩).sub (hPint s ⟨by omega, hsL.le⟩)
    have hADint (s : ℕ) (hs : s ∈ J) : Integrable (A * D s) ν :=
      (hDint s hs).bdd_mul
        ((hAmeas m).mono hH).aestronglyMeasurable hAbound
    have hEint : Integrable E ν := hBint.mul_const _
    have hEmeas : StronglyMeasurable[testFiltration c0 Cseq i m] E := by
      dsimp [E]
      fun_prop
    have hEce : ν[E | testFiltration c0 Cseq i m] =ᵐ[ν] E :=
      Filter.Eventually.of_forall (congrFun
        (condExp_of_stronglyMeasurable hH hEmeas hEint))
    have hXint (s : ℕ) (hs : s ∈ J) : Integrable (X s) ν := by
      have heq : X s = {ω | isOrdinary c0 (Cseq (s + 1) ω)}.indicator
          (occupationTerm c0 Cseq i s) := by
        ext ω
        simp [X, Set.indicator_apply]
      rw [heq]
      exact (hterm s hs).indicator (hOrd s hs)
    have hfil (s : ℕ) (hms : m ≤ s) :
        testFiltration c0 Cseq i m ≤ testFiltration c0 Cseq i s := by
      have hprefix {T : Type} (M : MeasurableSpace T) (f : ℕ → Ω → T) :
          (⨆ j ∈ (Finset.Icc 1 m).erase i, MeasurableSpace.comap (f j) M) ≤
            ⨆ j ∈ (Finset.Icc 1 s).erase i, MeasurableSpace.comap (f j) M := by
        apply iSup_le
        intro j
        apply iSup_le
        intro hj
        obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
        have hj' := Finset.mem_Icc.mp hj
        exact le_iSup_of_le j (le_iSup_of_le
          (Finset.mem_erase.mpr ⟨hji, Finset.mem_Icc.mpr ⟨hj'.1, hj'.2.trans hms⟩⟩) le_rfl)
      exact sup_le_sup (sup_le_sup le_rfl (hprefix _ _)) (hprefix _ _)
    have hsingle (s : ℕ) (hs : s ∈ J) :
        ν[X s | testFiltration c0 Cseq i m] ≤ᵐ[ν]
          fun ω => ν[A * D s | testFiltration c0 Cseq i m] ω + E ω := by
      obtain ⟨hms, hsL⟩ := Finset.mem_Ico.mp hs
      have hHs := testFiltration_le c0 Cseq hlaw.1 i s
      have hD0 : 0 ≤ᵐ[ν] D s := by
        filter_upwards [] with ω
        exact sub_nonneg.mpr (occupation_potential_monotone c0 Cseq i ω (Nat.le_succ s))
      have hpre : X s ≤ᵐ[ν] ν[A * D s | testFiltration c0 Cseq i s] + E := by
        filter_upwards [occupation_ordinary_conditional_drift hn μ Cseq hlaw i hi c0 s
          ⟨hm.1.trans hms, hsL⟩,
          condExp_mul_of_stronglyMeasurable_left (hAmeas s) (hADint s hs) (hDint s hs),
          condExp_nonneg (m := testFiltration c0 Cseq i s) hD0] with ω hdr hpull hnonneg
        change X s ω ≤ ν[A * D s | testFiltration c0 Cseq i s] ω + E ω
        rw [hpull]
        change X s ω ≤ A ω * ν[D s | testFiltration c0 Cseq i s] ω + E ω
        by_cases ho : isOrdinary c0 (Cseq (s + 1) ω)
        · have hDfun : D s = (fun ω' =>
              potential (incidenceParam c0 Cseq i ω') (nonrootSolutions c0 Cseq i (s + 1) ω') -
                potential (incidenceParam c0 Cseq i ω') (nonrootSolutions c0 Cseq i s ω')) := by
            ext ω'
            rfl
          rw [hDfun]
          simpa only [X, if_pos ho, A, E, B, ν] using hdr ho
        · simp only [X, if_neg ho]
          exact add_nonneg (mul_nonneg (by dsimp [A]; positivity) hnonneg)
            (by dsimp [E, B]; positivity)
      have hmono := condExp_mono (m := testFiltration c0 Cseq i m)
        (hXint s hs) (integrable_condExp.add hEint) hpre
      filter_upwards [hmono,
        condExp_add (μ := ν) (f := ν[A * D s | testFiltration c0 Cseq i s])
          integrable_condExp hEint (testFiltration c0 Cseq i m),
        condExp_condExp_of_le (μ := ν) (f := A * D s) (hfil s hms) hHs,
        hEce] with ω hmono hadd htower he
      simpa only [hadd, Pi.add_apply, htower, he] using hmono
    have hYint : Integrable (fun ω => ∑ s ∈ J, (A * D s) ω) ν :=
      integrable_finsetSum J (fun s hs => hADint s hs)
    have hYbound : (fun ω => ∑ s ∈ J, (A * D s) ω) ≤ᵐ[ν] fun ω => 3 * B ω := by
      filter_upwards [] with ω
      have htel : (∑ s ∈ J, D s ω) = P (capL n) ω - P m ω := by
        exact Finset.sum_Ico_sub (fun s => P s ω) hm.2.le
      have hbound : P (capL n) ω - P m ω ≤ incidenceParam c0 Cseq i ω := by
        have hlast := (potential_bounds (incidenceParam c0 Cseq i ω)
          (nonrootSolutions c0 Cseq i (capL n) ω)).2
        have hfirst := (potential_bounds (incidenceParam c0 Cseq i ω)
          (nonrootSolutions c0 Cseq i m ω)).1
        dsimp [P]
        linarith
      have hd0 : 0 < (incidenceParam c0 Cseq i ω : ℝ) := by
        exact_mod_cast (show 0 < incidenceParam c0 Cseq i ω from
          lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
      have hpow : (incidenceParam c0 Cseq i ω : ℝ) ^ (beta - 1) *
          incidenceParam c0 Cseq i ω = (incidenceParam c0 Cseq i ω : ℝ) ^ beta := by
        rw [Real.rpow_sub hd0, Real.rpow_one, div_mul_cancel₀ _ hd0.ne']
      calc
        _ = A ω * (∑ s ∈ J, D s ω) := by simp only [Pi.mul_apply, Finset.mul_sum]
        _ ≤ A ω * incidenceParam c0 Cseq i ω := by
          rw [htel]
          exact mul_le_mul_of_nonneg_left hbound (by dsimp [A]; positivity)
        _ = 3 * B ω := by dsimp [A, B]; rw [mul_assoc, hpow]
    have hYce := condExp_mono (m := testFiltration c0 Cseq i m)
      hYint (hBint.const_mul 3) hYbound
    have h3Bce : ν[(fun ω => 3 * B ω) | testFiltration c0 Cseq i m] =ᵐ[ν]
        fun ω => 3 * B ω :=
      Filter.Eventually.of_forall (congrFun (condExp_of_stronglyMeasurable hH
        (hBmeas.const_mul 3) (hBint.const_mul 3)))
    have hsingles : ∀ᵐ ω ∂ν, ∀ s ∈ J,
        ν[X s | testFiltration c0 Cseq i m] ω ≤
          ν[A * D s | testFiltration c0 Cseq i m] ω + E ω :=
      (Finset.eventually_all J).mpr hsingle
    filter_upwards [hsingles,
      condExp_finsetSum (μ := ν) (fun s hs => hXint s hs) (testFiltration c0 Cseq i m),
      condExp_finsetSum (μ := ν) (fun s hs => hADint s hs) (testFiltration c0 Cseq i m),
      hYce, h3Bce] with ω hsingle hsumX hsumY hY h3B
    have hsum := Finset.sum_le_sum (fun s hs => hsingle s hs)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
    have hcard : (J.card : ℝ) ≤ capL n := by
      exact_mod_cast (show J.card ≤ capL n by simp [J, Nat.card_Ico])
    have hE0 : 0 ≤ E ω := by dsimp [E, B]; positivity
    have hErr := mul_le_mul_of_nonneg_right hcard hE0
    change ν[(fun ω => ∑ s ∈ J, X s ω) | testFiltration c0 Cseq i m] ω ≤ _
    simp only [← Finset.sum_apply] at hY ⊢
    rw [hsumX]
    simp only [Finset.sum_apply] at hsumX hsumY ⊢
    rw [hsumY] at hY
    rw [h3B] at hY
    dsimp [E] at hErr
    dsimp [E] at hsum
    nlinarith
  have hsplit : (fun ω => ∑ s ∈ Finset.Ico m (capL n),
      occupationTerm c0 Cseq i s ω) = O + N := by
    funext ω
    dsimp [O, N]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp
  change ν[(fun ω => ∑ s ∈ Finset.Ico m (capL n),
      occupationTerm c0 Cseq i s ω) | (testFiltration c0 Cseq i m)] ≤ᵐ[ν] fun ω => occupationK * B ω
  rw [hsplit]
  filter_upwards [condExp_add hOint hNint (testFiltration c0 Cseq i m), hordinary, hNce, hBce] with ω hsum ho hnce hb
  rw [hsum]
  have hb0 : 0 ≤ B ω := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have herror := mul_le_mul_of_nonneg_right (occupation_cap_error_le hn) hb0
  rw [hb] at hnce
  dsimp only [Pi.add_apply]
  unfold occupationK
  nlinarith

end Papers.OaiLinearVarianceRandom
