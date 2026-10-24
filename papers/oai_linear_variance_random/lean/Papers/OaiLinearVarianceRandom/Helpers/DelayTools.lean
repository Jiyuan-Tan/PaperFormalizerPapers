module

public import Papers.OaiLinearVarianceRandom.TDuration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! # Measurability and ordered sums for the delay estimate -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]

open Classical in
/-- [A clause is uniquely determined by its exposure, ordinary contents, and test
contents relative to a fixed reference clause](goal). -/
-- @node: clause_observations_injective
lemma clause_observations_injective (c0 : ProperClause n) :
    Function.Injective (fun c : ProperClause n =>
      (expose c0 c, ordinaryContents c0 c, testContents c0 c)) := by
  intro c c' h
  have he := congrArg (fun p => p.1) h
  have ho := congrArg (fun p => p.2.1) h
  have ht := congrArg (fun p => p.2.2) h
  by_cases hc : isOrdinary c0 c
  · have hc' : isOrdinary c0 c' := by
      have hr : rootLiterals c0 c = rootLiterals c0 c' := congrArg Prod.fst he
      simpa only [isOrdinary, ← hr] using hc
    simpa [ordinaryContents, hc, hc'] using ho
  · by_cases htest : isTest c0 c
    · have hr : rootLiterals c0 c = rootLiterals c0 c' := congrArg Prod.fst he
      have htest' : isTest c0 c' := by
        simpa only [isTest, ← hr] using htest
      have hnr : c.val.filter (fun l => l.1 ∉ roots c0) =
          c'.val.filter (fun l => l.1 ∉ roots c0) := by
        simpa [testContents, htest, htest'] using ht
      apply Subtype.ext
      apply Finset.ext
      intro l
      by_cases hl : l.1 ∈ roots c0
      · have := Finset.ext_iff.mp hr l
        simpa [rootLiterals, hl] using this
      · have := Finset.ext_iff.mp hnr l
        simpa [hl] using this
    · have hex := congrArg Prod.snd he
      have hc' : ¬ isOrdinary c0 c' := by
        have hr : rootLiterals c0 c = rootLiterals c0 c' := congrArg Prod.fst he
        simpa only [isOrdinary, ← hr] using hc
      have ht' : ¬ isTest c0 c' := by
        have hr : rootLiterals c0 c = rootLiterals c0 c' := congrArg Prod.fst he
        simpa only [isTest, ← hr] using htest
      simpa [expose, hc, htest, hc', ht'] using hex

open Classical in
/-- If [the prefix length does not exceed the cap](hyp:hm) and [the index lies
between one and that length and differs from the omitted index](hyp:hj), then
[the clause at that index is measurable with respect to the test information
at that prefix](goal). -/
-- @node: clause_testFiltration_measurable
lemma clause_testFiltration_measurable (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m j : ℕ) (hm : m ≤ capL n)
    (hj : j ∈ (Finset.Icc 1 m).erase i) :
    @Measurable Ω (ProperClause n) (testFiltration c0 Cseq i m) inferInstance (Cseq j) := by
  letI : MeasurableSpace Ω := testFiltration c0 Cseq i m
  let E := Finset (Fin n × Bool) × Option (ProperClause n)
  let O := Option (ProperClause n)
  let T := Option (Finset (Fin n × Bool))
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSpace O := ⊤
  letI : MeasurableSpace T := ⊤
  let obs : ProperClause n → E × O × T := fun c =>
    (expose c0 c, ordinaryContents c0 c, testContents c0 c)
  have hobs : Function.Injective obs := clause_observations_injective c0
  have hjL : j ∈ (Finset.Icc 1 (capL n)).erase i := by
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩⟩
  have he : Measurable (fun ω => expose c0 (Cseq j ω)) := by
    apply Measurable.of_comap_le
    apply le_trans (b := exposureSigma c0 Cseq i)
    · exact le_iSup_of_le j (le_iSup_of_le hjL le_rfl)
    · exact le_sup_left.trans le_sup_left
  have ho : Measurable (fun ω => ordinaryContents c0 (Cseq j ω)) := by
    apply Measurable.of_comap_le
    apply le_trans (b := ordinaryFiltration c0 Cseq i m)
    · exact le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
    · exact le_sup_left
  have ht : Measurable (fun ω => testContents c0 (Cseq j ω)) := by
    apply Measurable.of_comap_le
    exact le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  haveI : Nonempty (ProperClause n) := ⟨c0⟩
  have h := (measurable_of_finite (Function.invFun obs)).comp (he.prodMk (ho.prodMk ht))
  convert h using 1
  funext ω
  exact (Function.leftInverse_invFun hobs (Cseq j ω)).symm

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw), [a positive omitted
index](hyp:hi), and [a prefix length no greater than the cap](hyp:hm), [the pivotal
event indicator is almost surely strongly measurable with respect to the test
information, under the law fixing the omitted clause to the reference clause](goal). -/
@[fun_prop]
-- @node: pivotalIndicator_aestronglyMeasurable
lemma pivotalIndicator_aestronglyMeasurable (μ : Measure Ω)
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : 1 ≤ i) (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    AEStronglyMeasurable[testFiltration c0 Cseq i m]
      (eventIndicator (pivotalEvent Cseq i m)) (fixedClauseMeasure μ Cseq i c0) := by
  have hsm : StronglyMeasurable[testFiltration c0 Cseq i m] (eventIndicator
      {ω | (∃ z, ∀ j : (Finset.Icc 1 m).erase i, ClauseSat (Cseq j ω) z) ∧
        ¬ ∃ z, (∀ j : (Finset.Icc 1 m).erase i, ClauseSat (Cseq j ω) z) ∧ ClauseSat c0 z}) := by
    letI : MeasurableSpace Ω := testFiltration c0 Cseq i m
    have hs (z : Fin n → Bool) : Measurable (fun ω =>
        ∀ j : (Finset.Icc 1 m).erase i, ClauseSat (Cseq j ω) z) := by
      apply Measurable.forall
      intro j
      exact (measurable_of_finite (fun c : ProperClause n => ClauseSat c z)).comp
        (clause_testFiltration_measurable c0 Cseq i m j hm j.property)
    let A : Set Ω := {ω | (∃ z, ∀ j : (Finset.Icc 1 m).erase i,
        ClauseSat (Cseq j ω) z) ∧ ¬ ∃ z, (∀ j : (Finset.Icc 1 m).erase i,
        ClauseSat (Cseq j ω) z) ∧ ClauseSat c0 z}
    have hA : MeasurableSet A := by
      exact ((Measurable.exists hs).and (Measurable.exists fun z =>
        (hs z).and measurable_const).not).setOf
    unfold eventIndicator
    exact (Measurable.ite hA measurable_const measurable_const).stronglyMeasurable
  apply hsm.aestronglyMeasurable.congr
  filter_upwards [fixedClauseMeasure_ae_eq μ Cseq hlaw i hi c0] with ω hfixed
  simp only [eventIndicator]
  congr 1
  simp only [pivotalEvent, Set.mem_setOf_eq, omittedPrefixSat, Subtype.forall,
    Finset.mem_erase, Finset.mem_Icc, and_imp, hfixed]
  congr 2 <;> aesop

open Classical in
/-- [The number of clauses sharing at least two root literals with the reference
clause is measurable with respect to the exposure information](goal). -/
@[fun_prop]
-- @node: collisionCount_measurable
lemma collisionCount_measurable (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) :
    @Measurable Ω ℕ (exposureSigma c0 Cseq i) inferInstance (collisionCount c0 Cseq i) := by
  letI : MeasurableSpace Ω := exposureSigma c0 Cseq i
  have he (j : ℕ) (hj : j ∈ (Finset.Icc 1 (capL n)).erase i) :
      @Measurable Ω _ _ ⊤ (fun ω => expose c0 (Cseq j ω)) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
  have hs : Measurable (fun ω => ∑ j ∈ (Finset.Icc 1 (capL n)).erase i,
      if 2 ≤ (rootLiterals c0 (Cseq j ω)).card then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro j hj
    exact Measurable.ite (he j hj (t := {e | 2 ≤ e.1.card}) (by trivial))
      measurable_const measurable_const
  change Measurable (fun ω => (((Finset.Icc 1 (capL n)).erase i).filter
    (fun j => 2 ≤ (rootLiterals c0 (Cseq j ω)).card)).card)
  simpa only [Finset.sum_boole, Nat.cast_id] using hs

/-- If [the conditioning information is contained in the ambient information](hyp:hE),
[the event is measurable with respect to the conditioning information](hyp:hA),
[both real functions are integrable](hyp:hf,hg), and [the first is at most the
second almost surely on that event](hyp:hfg), then [their conditional expectations
have the same ordering almost surely on the event](goal). -/
-- @node: condExp_le_on_event
lemma condExp_le_on_event (μ : Measure Ω) [IsFiniteMeasure μ]
    {E : MeasurableSpace Ω} (hE : E ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[E] A) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ ω ∂μ, ω ∈ A → f ω ≤ g ω) :
    ∀ᵐ ω ∂μ, ω ∈ A → μ[f | E] ω ≤ μ[g | E] ω := by
  have h := condExp_mono (m := E) (hf.indicator (hE _ hA))
    (hg.indicator (hE _ hA)) (by
      filter_upwards [hfg] with ω hω
      by_cases ha : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ha, hω])
  filter_upwards [h, condExp_indicator hf hA, condExp_indicator hg hA] with ω hω hfω hgω
  intro ha
  simpa only [hfω, hgω, Set.indicator_of_mem ha] using hω

/-- For [a nonnegative real sequence](hyp:hf), [the square of its sum from the
lower endpoint up to, but excluding, the upper endpoint is at most twice the sum
of each term times the tail sum starting at that term](goal). -/
-- @node: ordered_sum_square_le
lemma ordered_sum_square_le (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) (a b : ℕ) :
    (∑ k ∈ Finset.Ico a b, f k) ^ 2 ≤
      2 * ∑ k ∈ Finset.Ico a b, f k * ∑ j ∈ Finset.Ico k b, f j := by
  by_cases hab : a ≤ b
  · induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab]
      have hsum : (∑ k ∈ Finset.Ico a (b + 1), f k * ∑ j ∈ Finset.Ico k (b + 1), f j) =
          (∑ k ∈ Finset.Ico a b, f k * ∑ j ∈ Finset.Ico k b, f j) +
          (∑ k ∈ Finset.Ico a b, f k) * f b + f b ^ 2 := by
        rw [Finset.sum_Ico_succ_top hab]
        have heq : (∑ k ∈ Finset.Ico a b, f k * ∑ j ∈ Finset.Ico k (b + 1), f j) =
            (∑ k ∈ Finset.Ico a b, f k * ∑ j ∈ Finset.Ico k b, f j) +
            (∑ k ∈ Finset.Ico a b, f k) * f b := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_Ico_succ_top (Finset.mem_Ico.mp hk).2.le, mul_add]
        rw [heq]
        simp [pow_two]
      rw [hsum]
      nlinarith [sq_nonneg (f b)]
  · simp [Finset.Ico_eq_empty_of_le (by omega : b ≤ a)]

/-- Suppose [the first information set is contained in the second](hyp:hEG),
[the second is contained in the third](hyp:hGH), and [the third is contained in
the ambient information](hyp:hH). If [the two factors are integrable](hyp:hf,hg),
[the first factor is almost surely strongly measurable with respect to the third
information set](hyp:hfH), [the weight is strongly measurable with respect to the
second](hyp:hWG), [the first factor takes values between zero and one](hyp:hf01),
[the weight is uniformly bounded in absolute value by B](hyp:hWB), and [the
conditional expectation of the second factor given the third information set is
almost surely at most the weight](hyp:hW), then [the conditional expectation of
the product given the first information set is at most that of the weight times
the conditional expectation of the first factor given the second](goal). -/
-- @node: condExp_weighted_duration_le
lemma condExp_weighted_duration_le (μ : Measure Ω) [IsFiniteMeasure μ]
    {E G H : MeasurableSpace Ω} (hEG : E ≤ G) (hGH : G ≤ H) (hH : H ≤ mΩ)
    {f g W : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfH : AEStronglyMeasurable[H] f μ) (hWG : StronglyMeasurable[G] W)
    (hf01 : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) (B : ℝ)
    (hWB : ∀ ω, ‖W ω‖ ≤ B) (hW : μ[g | H] ≤ᵐ[μ] W) :
    μ[f * g | E] ≤ᵐ[μ] μ[W * μ[f | G] | E] := by
  have hfa : AEStronglyMeasurable[mΩ] f μ := hf.aestronglyMeasurable
  have hWa : AEStronglyMeasurable[mΩ] W μ := (hWG.mono (hGH.trans hH)).aestronglyMeasurable
  have hfb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1 := Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf01 ω).1] using (hf01 ω).2
  have hfg := hg.bdd_mul hfa hfb
  have hWf := hf.bdd_mul hWa (Filter.Eventually.of_forall hWB)
  have hfW : Integrable (f * W) μ := by
    convert hWf using 1
    ext ω
    exact mul_comm _ _
  have hfCE : Integrable (f * μ[g | H]) μ := integrable_condExp.bdd_mul hfa hfb
  have hWCE : Integrable (W * μ[f | G]) μ :=
    integrable_condExp.bdd_mul hWa (Filter.Eventually.of_forall hWB)
  have hpH := condExp_mul_of_aestronglyMeasurable_left hfH hfg hg
  have hinner : μ[f * g | H] ≤ᵐ[μ] f * W := by
    filter_upwards [hpH, hW] with ω hp hw
    rw [hp]
    exact mul_le_mul_of_nonneg_left hw (hf01 ω).1
  have hfirst := condExp_mono (m := E) integrable_condExp hfW hinner
  have hpG := condExp_mul_of_stronglyMeasurable_left hWG hWf hf
  have heq : μ[f * W | E] =ᵐ[μ] μ[W * μ[f | G] | E] := by
    have hcomm : f * W = W * f := mul_comm _ _
    rw [hcomm]
    exact (condExp_condExp_of_le hEG (hGH.trans hH)).symm.trans
      (condExp_congr_ae hpG)
  exact (condExp_condExp_of_le (hEG.trans hGH) hH).symm.trans_le
    (hfirst.trans_eq heq)

/-- If [there are at least six variables](hyp:hn) and [the omitted index lies
between one and the cap](hyp:hi), then [the omission delay, viewed as a real
number, equals the sum of pivotal event indicators from that index up to, but
excluding, the cap](goal). -/
-- @node: delay_real_eq_sum
lemma delay_real_eq_sum (hn : OmissionN n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (hi : DelayIndex i (capL n)) (ω : Ω) :
    (delay (fun j => Cseq j ω) i : ℝ) =
      ∑ m ∈ Finset.Ico i (capL n), eventIndicator (pivotalEvent Cseq i m) ω := by
  classical
  rw [delay_eq_delayIndicatorSum hn Cseq i hi ω]
  simp [delayIndicatorSum, eventIndicator, Finset.sum_boole]

/-- [The sum of pivotal event indicators from any starting time up to, but
excluding, the cap lies between zero and the cap](goal). -/
-- @node: pivotal_tail_sum_bounds
lemma pivotal_tail_sum_bounds (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (ω : Ω) :
    0 ≤ (∑ s ∈ Finset.Ico m (capL n), eventIndicator (pivotalEvent Cseq i s) ω) ∧
      (∑ s ∈ Finset.Ico m (capL n), eventIndicator (pivotalEvent Cseq i s) ω) ≤ capL n := by
  classical
  constructor
  · exact Finset.sum_nonneg fun s hs => by unfold eventIndicator; split_ifs <;> norm_num
  · calc
      _ ≤ ∑ s ∈ Finset.Ico m (capL n), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        unfold eventIndicator
        split_ifs <;> norm_num
      _ = ((capL n - m : ℕ) : ℝ) := by simp
      _ ≤ capL n := by exact_mod_cast Nat.sub_le (capL n) m

/-- For [an independent uniform clause process](hyp:hlaw) and [a positive omitted
index](hyp:hi), [every real function of the incidence parameter and collision
count is integrable under the law fixing the omitted clause to the reference
clause](goal). -/
-- @node: integrable_exposure_counts
lemma integrable_exposure_counts (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : 1 ≤ i) (c0 : ProperClause n) (f : ℕ → ℕ → ℝ) :
    Integrable (fun ω => f (incidenceParam c0 Cseq i ω)
      (collisionCount c0 Cseq i ω)) (fixedClauseMeasure μ Cseq i c0) := by
  classical
  let J := (Finset.Icc 1 (capL n)).erase i
  have hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i := by
    intro j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    exact ⟨(Finset.mem_Icc.mp hj).1, hne⟩
  convert fixedClauseMeasure_integrable_vector μ Cseq hlaw i hi c0 J hJ
    (fun cs => f (max 1 ((Finset.univ.filter
      (fun j : J => 1 ≤ (rootLiterals c0 (cs j)).card)).card))
      ((Finset.univ.filter (fun j : J => 2 ≤ (rootLiterals c0 (cs j)).card)).card)) using 1
  funext ω
  dsimp only
  unfold incidenceParam incidenceCount collisionCount
  simp only [Finset.card_filter]
  apply congrArg₂ f
  · apply congrArg (max 1)
    exact (Finset.sum_coe_sort J (fun j =>
      if 1 ≤ (rootLiterals c0 (Cseq j ω)).card then (1 : ℕ) else 0)).symm
  · exact (Finset.sum_coe_sort J (fun j =>
      if 2 ≤ (rootLiterals c0 (Cseq j ω)).card then (1 : ℕ) else 0)).symm


end Papers.OaiLinearVarianceRandom
