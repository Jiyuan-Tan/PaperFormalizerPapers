module
public import Papers.TbsExtremeEffects.Helpers.DRAssembly
public import Papers.TbsExtremeEffects.Helpers.Count

/-! Six-event confidence assembly for adaptive thresholds. Sampling failures are
controlled only on the nuisance event, where their conditional moments hold. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- If [the target event is contained in the nuisance event](hyp:hJG), [the retained event is measurable](hyp:hS), and [failure within the nuisance event has probability at most the budget](hyp:hBad), then [intersecting the target event with the retained event loses at most that budget in probability](goal).

@node: measureReal_inter_ge_sub_of_local_failure -/
lemma measureReal_inter_ge_sub_of_local_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {J G S : Set Ω} {b : ℝ}
    (hJG : J ⊆ G) (hS : MeasurableSet S) (hBad : P.real (G \ S) ≤ b) :
    P.real J - b ≤ P.real (J ∩ S) := by
  have hsmall : P.real (J \ S) ≤ b :=
    (measureReal_mono (h₂ := measure_ne_top P _)
      (Set.sdiff_subset_sdiff_left hJG)).trans hBad
  have hsplit := measureReal_inter_add_sdiff (μ := P) (s := J) hS
  linarith

/-- If [the nuisance event is measurable](hyp:hG), [each of four auxiliary events is measurable](hyp:hS), [the nuisance event has its probability guarantee](hyp:hGp), [the Hill event has its guarantee](hyp:hHp), [the two count events have their guarantees](hyp:hNp), and [each maximal-process failure is locally budgeted on the nuisance event](hyp:hAp,hCp), then [the intersection of all six events has probability at least one minus the confidence level](goal).

@node: adaptive_six_events_probability -/
lemma adaptive_six_events_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G H : Set Ω)
    (S : Fin 4 → Set Ω) (hG : MeasurableSet G)
    (hS : ∀ i, MeasurableSet (S i)) {delta : ℝ}
    (hGp : 1 - delta / 6 ≤ P.real G) (hHp : 1 - delta / 6 ≤ P.real H)
    (hNp : ∀ i : Fin 2, 1 - delta / 6 ≤ P.real (S i.castSucc.castSucc))
    (hAp : P.real (G \ S 2) ≤ delta / 6)
    (hCp : P.real (G \ S 3) ≤ delta / 6) :
    1 - delta ≤ P.real (((((H ∩ G) ∩ S 0) ∩ S 1) ∩ S 2) ∩ S 3) := by
  have hHG := probability_intersection_lower P H G hG hHp hGp
  have hN0 := probability_intersection_lower P (H ∩ G) (S 0) (hS 0) hHG (hNp 0)
  have hN1 := probability_intersection_lower P ((H ∩ G) ∩ S 0) (S 1)
    (hS 1) hN0 (hNp 1)
  have hA := measureReal_inter_ge_sub_of_local_failure P
    (J := ((H ∩ G) ∩ S 0) ∩ S 1) (fun _ hw => hw.1.1.2) (hS 2) hAp
  have hC := measureReal_inter_ge_sub_of_local_failure P
    (J := (((H ∩ G) ∩ S 0) ∩ S 1) ∩ S 2) (fun _ hw => hw.1.1.1.2) (hS 3) hCp
  linarith

/-- If [the nuisance event is measurable](hyp:hG), [all four auxiliary events are measurable](hyp:hS), [the nuisance guarantee holds](hyp:hGp), [the Hill guarantee holds](hyp:hHp), [the count guarantees hold](hyp:hNp), [the first local failure is budgeted](hyp:hAp), [the second local failure is budgeted](hyp:hCp), and [membership in all six events implies the target event](hyp:himp), then [the target event has probability at least one minus the confidence level](goal).

@node: adaptive_six_events_imp -/
lemma adaptive_six_events_imp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G H : Set Ω)
    (S : Fin 4 → Set Ω) (hG : MeasurableSet G)
    (hS : ∀ i, MeasurableSet (S i)) {delta : ℝ}
    (hGp : 1 - delta / 6 ≤ P.real G) (hHp : 1 - delta / 6 ≤ P.real H)
    (hNp : ∀ i : Fin 2, 1 - delta / 6 ≤ P.real (S i.castSucc.castSucc))
    (hAp : P.real (G \ S 2) ≤ delta / 6)
    (hCp : P.real (G \ S 3) ≤ delta / 6)
    (T : Set Ω) (himp : ∀ w ∈ G, w ∈ H → (∀ i, w ∈ S i) → w ∈ T) :
    1 - delta ≤ P.real T := by
  apply (adaptive_six_events_probability P G H S hG hS hGp hHp hNp hAp hCp).trans
  apply measureReal_mono (h₂ := measure_ne_top P _)
  intro w hw
  apply himp w hw.1.1.1.1.2 hw.1.1.1.1.1
  intro i
  fin_cases i
  · exact hw.1.1.1.2
  · exact hw.1.1.2
  · exact hw.1.2
  · exact hw.2

variable {q d : ℕ} {M : ExtremeModel q d}

/-- For [an even sample size](hyp:hn), [an iid sample](hyp:hiid), and [an index set containing one half of the observations](hyp:hI), [the probability that its tail-indicator sum falls below one quarter of its expected full-sample count has the stated exponential bound](goal).

@node: split_tail_indicator_lower_tail -/
lemma split_tail_indicator_lower_tail (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    (I : Finset (Fin n)) (hI : I.card = n / 2) :
    E.P.real {w | (∑ i ∈ I, if t < l1Norm (sampleU E n w i) then (1 : ℝ) else 0) <
      (n : ℝ) * tailProb M t / 4} ≤
      Real.exp (-((n : ℝ) * tailProb M t) / 16) := by
  classical
  let f : Obs q d → ℝ := fun z => if t < l1Norm z.2.2.2 then 1 else 0
  have hf : Measurable f := by
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      measurable_const measurable_const
  let X : Fin n → E.Om → ℝ := fun i w => f (obs E n w i)
  have hX : ∀ i, Measurable (X i) := by
    intro i
    exact hf.comp ((measurable_pi_apply i).comp (measurable_obs_tuple M E n))
  obtain ⟨hind, hlaw⟩ := relabelled_iid M E n hn hiid
  have hindX : iIndepFun X E.P := hind.comp (fun _ => f) (fun _ => hf)
  have hmean : ∀ i ∈ I, ∫ w, X i w ∂E.P = tailProb M t := by
    intro i _
    have hmap : (∫ w, X i w ∂E.P) =
        ∫ z, f z ∂E.P.map (fun w => obs E n w i) :=
      (integral_map ((measurable_pi_apply i).comp
        (measurable_obs_tuple M E n)).aemeasurable hf.aestronglyMeasurable).symm
    have hobs : Measurable (observation M) :=
      M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
    rw [hmap, hlaw i, integral_map hobs.aemeasurable hf.aestronglyMeasurable]
    change (∫ w, {w | t < radius M w}.indicator (fun _ => (1 : ℝ)) w ∂M.mu) = _
    rw [integral_indicator_const _ (measurableSet_lt measurable_const (measurable_radius M))]
    simp [tailProb, measureReal_def]
  have hbound := finite_bounded_count_lower_tail E.P X hX hindX
    (fun i w => by dsimp [X, f]; split_ifs <;> norm_num)
    I (tailProb_nonneg M t) hmean
  have hhalf : ((n / 2 : ℕ) : ℝ) = (n : ℝ) / 2 := by
    obtain ⟨k, hk⟩ := hn.2
    have hdiv : n / 2 = k := by omega
    rw [hdiv, hk]
    norm_num
  rw [hI, hhalf] at hbound
  have hsub : {w | (∑ i ∈ I, X i w) < (n : ℝ) * tailProb M t / 4} ⊆
      {w | (∑ i ∈ I, X i w) ≤ (n : ℝ) / 2 * tailProb M t / 2} := by
    intro w hw
    change (∑ i ∈ I, X i w) ≤ _
    change (∑ i ∈ I, X i w) < _ at hw
    linarith
  have hexponent : -((n : ℝ) / 2 * tailProb M t) / 8 =
      -((n : ℝ) * tailProb M t) / 16 := by ring
  rw [hexponent] at hbound
  exact (measureReal_mono hsub).trans hbound

/-- [The training exceedance count equals the sum of tail indicators over the training half](goal).

@node: trainCount_eq_sum_tail_indicators -/
lemma trainCount_eq_sum_tail_indicators (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (w : E.Om) :
    (trainCount E n t w : ℝ) = ∑ i ∈ trainIndices n,
      if t < l1Norm (sampleU E n w i) then (1 : ℝ) else 0 := by
  classical
  simp [trainCount, Finset.sum_boole]

/-- [An even iid sample](hyp:hn,hiid) has [a training exceedance count below one quarter of its expected tail count with probability at most the displayed exponential](goal).

@node: trainCount_lower_tail -/
lemma trainCount_lower_tail (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n) :
    E.P.real {w | (trainCount E n t w : ℝ) < (n : ℝ) * tailProb M t / 4} ≤
      Real.exp (-((n : ℝ) * tailProb M t) / 16) := by
  simpa only [trainCount_eq_sum_tail_indicators] using
    split_tail_indicator_lower_tail E n t hn hiid (trainIndices n)
      (equalSplit_cardinality n hn).1

/-- [The real-valued training exceedance count is a measurable function of the sample](goal).

@node: measurable_trainCount_real -/
@[fun_prop] lemma measurable_trainCount_real (E : NeteExperiment M) (n : ℕ) (t : ℝ) :
    Measurable (fun w => (trainCount E n t w : ℝ)) := by
  simp_rw [trainCount_eq_sum_tail_indicators]
  apply Finset.measurable_fun_sum
  intro i _
  apply Measurable.ite (measurableSet_lt measurable_const ?_) measurable_const measurable_const
  exact measurable_l1Norm.comp (((measurable_pi_apply i).comp
    (measurable_obs_tuple M E n)).snd.snd.snd)

/-- If [the count is measurable](hyp:hN), [the confidence level is positive](hyp:hd), [its lower-tail failure has the stated exponential bound](hyp:hTail), and [the expected count meets the logarithmic budget](hyp:hBudget), then [the count-success event is measurable and has probability at least one minus one sixth of the confidence level](goal).

@node: count_event_probability_of_exponential_failure -/
lemma count_event_probability_of_exponential_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : Ω → ℝ) (hN : Measurable N)
    {mu delta : ℝ} (hd : 0 < delta)
    (hTail : P.real {w | N w < mu / 4} ≤ Real.exp (-mu / 16))
    (hBudget : 16 * Real.log (6 / delta) ≤ mu) :
    MeasurableSet {w | mu / 4 ≤ N w} ∧
      1 - delta / 6 ≤ P.real {w | mu / 4 ≤ N w} := by
  have hmeas : MeasurableSet {w | mu / 4 ≤ N w} :=
    measurableSet_le measurable_const hN
  have hfailure : P.real {w | N w < mu / 4} ≤ delta / 6 := by
    apply hTail.trans
    calc
      _ ≤ Real.exp (-Real.log (6 / delta)) := Real.exp_le_exp.mpr (by linarith)
      _ = delta / 6 := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  have hcompl : {w | N w < mu / 4} = {w | mu / 4 ≤ N w}ᶜ := by
    ext w
    simp
  rw [hcompl, measureReal_compl hmeas, probReal_univ] at hfailure
  exact ⟨hmeas, by linarith⟩

/-- For [an even iid sample](hyp:hn,hiid), [a positive confidence level](hyp:hd), and [a sufficient endpoint expected-count budget](hyp:hBudget), [both training and evaluation endpoint count events are measurable and each has its one-sixth confidence guarantee](goal).

@node: adaptive_endpoint_count_events -/
lemma adaptive_endpoint_count_events (E : NeteExperiment M) (n : ℕ) (u : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    {delta : ℝ} (hd : 0 < delta)
    (hBudget : 16 * Real.log (6 / delta) ≤ (n : ℝ) * tailProb M u) :
    (MeasurableSet {w | (n : ℝ) * tailProb M u / 4 ≤ (trainCount E n u w : ℝ)} ∧
      1 - delta / 6 ≤ E.P.real {w | (n : ℝ) * tailProb M u / 4 ≤
        (trainCount E n u w : ℝ)}) ∧
    (MeasurableSet {w | (n : ℝ) * tailProb M u / 4 ≤ (evalCount E n u w : ℝ)} ∧
      1 - delta / 6 ≤ E.P.real {w | (n : ℝ) * tailProb M u / 4 ≤
        (evalCount E n u w : ℝ)}) := by
  exact ⟨count_event_probability_of_exponential_failure E.P
    (fun w => (trainCount E n u w : ℝ)) (measurable_trainCount_real E n u)
    hd (trainCount_lower_tail E n u hn hiid) hBudget,
    count_event_probability_of_exponential_failure E.P
    (fun w => (evalCount E n u w : ℝ)) (measurable_evalCount_real E n u)
    hd (evalCount_lower_tail E n u hn hiid) hBudget⟩

end Papers.TbsExtremeEffects
