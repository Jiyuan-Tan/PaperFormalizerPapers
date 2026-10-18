module
public import Papers.TbsExtremeEffects.Helpers.TrainingThresholdGhost
public import Papers.TbsExtremeEffects.Helpers.ThresholdSampling

/-! Localized squared envelopes for evaluation scores. The nuisance event is
training measurable; clipping to it preserves independence from evaluation data. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {q d : ℕ} {M : ExtremeModel q d}

/-- [The sum over reindexed evaluation observations equals the sum over the original evaluation index set](goal).

@node: evaluation_reindex_sum -/
lemma evaluation_reindex_sum (n : ℕ) (f : Fin n → ℝ) :
    (∑ j : Fin (evalIndices n).card, f (((evalIndices n).equivFin).symm j)) =
      ∑ i ∈ evalIndices n, f i := by
  rw [Finset.sum_subtype (evalIndices n) (fun _ => Iff.rfl) f]
  exact Fintype.sum_equiv ((evalIndices n).equivFin).symm _ _ (fun _ => rfl)

/-- If [the radial variable is measurable](hyp:hR), [the mark is measurable](hyp:hf), [the new threshold is no lower than the original one](hyp:ht), and [the mark restricted above the original threshold is integrable](hyp:hInt), then [the mark restricted above the new strict threshold is integrable](goal). This does not require integrability below the original endpoint.

@node: integrable_strict_threshold_of_lower -/
lemma integrable_strict_threshold_of_lower {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (R f : Z → ℝ) (hR : Measurable R) (hf : Measurable f)
    {ell t : ℝ} (ht : ell ≤ t)
    (hInt : Integrable (fun z => if ell < R z then f z else 0) μ) :
    Integrable (fun z => if t < R z then f z else 0) μ := by
  have hMeas : Measurable (fun z => if t < R z then f z else 0) := by
    first | fun_prop | skip
    exact hf.ite (measurableSet_lt measurable_const hR) measurable_const
  apply hInt.mono hMeas.aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : t < R z
  · simp only [hz, ht.trans_lt hz, if_true, le_refl]
  · simp only [hz, if_false, norm_zero]
    exact norm_nonneg _

/-- If [the sample size is even](hyp:hn), [sampling is independent and identically distributed](hyp:hiid), [the fitted mark is jointly measurable with respect to training information and an observation](hyp:hf), [the training event is measurable](hyp:hG), [each mark clipped above the baseline threshold is integrable on that event](hyp:hMark), and [the clipped evaluation-square sum is integrable](hyp:hEnergy), then [there is a nonnegative integrable envelope that uniformly bounds squared threshold-centered evaluation sums on the training event and has the stated energy budget](goal).

@node: evaluation_localized_threshold_square_envelope -/
lemma evaluation_localized_threshold_square_envelope (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    (f : E.Om → Obs q d → ℝ)
    (hf : @Measurable (E.Om × Obs q d) ℝ
      ((trainSigma E n).prod inferInstance) inferInstance (Function.uncurry f))
    (G : Set E.Om) (hG : MeasurableSet[trainSigma E n] G) (ell : ℝ)
    (hMark : ∀ w ∈ G, Integrable
      (fun z => if ell < l1Norm z.2.2.2 then f w z else 0)
      (M.mu.map (observation M)))
    (hEnergy : Integrable (fun w => ∑ i : Fin n,
      if ell < l1Norm (sampleU E n w i) then
        (if w ∈ G ∧ i ∈ evalIndices n then f w (obs E n w i) else 0) ^ 2
      else 0) E.P) :
    ∃ H : E.Om → ℝ, Measurable H ∧ Integrable H E.P ∧ (∀ w, 0 ≤ H w) ∧
      (∫ w, H w ∂E.P) ≤ 16 * ∫ w, (∑ i : Fin n,
        if ell < l1Norm (sampleU E n w i) then
          (if w ∈ G ∧ i ∈ evalIndices n then f w (obs E n w i) else 0) ^ 2
        else 0) ∂E.P ∧
      ∀ᵐ w ∂E.P, w ∈ G → ∀ t ≥ ell,
        ((∑ i ∈ evalIndices n,
          if t < l1Norm (sampleU E n w i) then f w (obs E n w i) else 0) -
          (n / 2 : ℕ) * ∫ z, (if t < l1Norm z.2.2.2 then f w z else 0)
            ∂M.mu.map (observation M)) ^ 2 ≤ H w := by
  let g : E.Om × Obs q d → ℝ := fun p => if p.1 ∈ G then f p.1 p.2 else 0
  have hg : @Measurable (E.Om × Obs q d) ℝ
      ((trainSigma E n).prod inferInstance) inferInstance g := by
    letI : MeasurableSpace E.Om := trainSigma E n
    exact hf.ite (measurable_fst hG) measurable_const
  have hInt (w : E.Om) (t : ℝ) (ht : ell ≤ t) : Integrable
      (fun z => if t < l1Norm z.2.2.2 then g (w, z) else 0)
      (M.mu.map (observation M)) := by
    by_cases hw : w ∈ G
    · simp only [g, hw, if_true]
      apply integrable_strict_threshold_of_lower _ _ _ (by fun_prop)
        (hf.comp (measurable_const.prodMk measurable_id)) ht (hMark w hw)
    · simp only [g, hw, if_false, ite_self]
      exact integrable_const 0
  have hEq (w : E.Om) :
      (∑ j : Fin (evalIndices n).card,
        if ell < l1Norm (obs E n w (((evalIndices n).equivFin).symm j)).2.2.2 then
          g (w, obs E n w (((evalIndices n).equivFin).symm j)) ^ 2 else 0) =
      ∑ i : Fin n, if ell < l1Norm (sampleU E n w i) then
        (if w ∈ G ∧ i ∈ evalIndices n then f w (obs E n w i) else 0) ^ 2 else 0 := by
    rw [evaluation_reindex_sum n (fun i =>
      if ell < l1Norm (obs E n w i).2.2.2 then g (w, obs E n w i) ^ 2 else 0)]
    calc
      _ = ∑ i : Fin n, if i ∈ evalIndices n then
          (if ell < l1Norm (sampleU E n w i) then g (w, obs E n w i) ^ 2 else 0)
          else 0 := by
        have h := Finset.sum_filter (s := Finset.univ)
          (fun i : Fin n => i ∈ evalIndices n)
          (fun i => if ell < l1Norm (sampleU E n w i) then
            g (w, obs E n w i) ^ 2 else 0)
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at h
        convert h using 1 <;> rfl
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ evalIndices n <;> by_cases hw : w ∈ G <;>
          by_cases hr : ell < l1Norm (sampleU E n w i) <;> simp [g, hi, hw, hr]
  have hEnergy' : Integrable (fun w => ∑ j : Fin (evalIndices n).card,
      if ell < l1Norm (obs E n w (((evalIndices n).equivFin).symm j)).2.2.2 then
        g (w, obs E n w (((evalIndices n).equivFin).symm j)) ^ 2 else 0) E.P := by
    simpa only [hEq] using hEnergy
  obtain ⟨H, hH, hHint, hH0, hBudget, hDom⟩ :=
    @evaluation_training_threshold_square_envelope q d M E n hn hiid
      E.Om (trainSigma E n) id measurable_id g hg ell hInt hEnergy'
  refine ⟨H, hH, hHint, hH0, ?_, ?_⟩
  · simpa only [id_eq, hEq] using hBudget
  · filter_upwards [hDom] with w hw
    intro hwG t ht
    have h := hw t ht
    dsimp only [id_eq, g] at h
    simp only [hwG, if_true] at h
    rw [evaluation_reindex_sum n (fun i =>
      if t < l1Norm (obs E n w i).2.2.2 then f w (obs E n w i) else 0)] at h
    rw [(equalSplit_cardinality n hn).2] at h
    convert h using 1 <;> rfl

/-- If [the sample size is even](hyp:hn), [sampling is independent and identically distributed](hyp:hiid), [the exponent is trained from the training sample](hyp:hTraining), [the noise is regularly varying](hyp:hRV), [the training event is measurable](hyp:hG), [the baseline threshold belongs to the threshold set](hyp:hEll), [it is no greater than every threshold considered](hyp:hLower), [the proposed moment budget is nonnegative](hyp:hV0), [all conditional score laws have finite second moment](hyp:hLp), and [the baseline score second moment is at most that budget](hyp:hV), then [there is a nonnegative integrable envelope for all squared threshold-centered scores on the event, with the stated 8n tail-probability budget](goal).

@node: evaluation_localized_score_square_envelope -/
lemma evaluation_localized_score_square_envelope (E : NeteExperiment M)
    (kind : EstimatorKind) (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    (hTraining : ExponentTraining E n) (hRV : NoiseRegularlyVarying M)
    (G : Set E.Om) (hG : MeasurableSet[trainSigma E n] G)
    (T : Set ℝ) (ell : ℝ) (hEll : ell ∈ T) (hLower : ∀ t ∈ T, ell ≤ t)
    {V : ℝ} (hV0 : 0 ≤ V)
    (hLp : ∀ w ∈ G, ∀ t ∈ T, MemLp (score E kind n w) 2 (obsTailLaw M t))
    (hV : ∀ w ∈ G, scoreSecondMoment E kind n ell w ≤ V) :
    ∃ H : E.Om → ℝ, Measurable H ∧ Integrable H E.P ∧ (∀ w, 0 ≤ H w) ∧
      (∫ w, H w ∂E.P) ≤ 8 * (n : ℝ) * V * tailProb M ell ∧
      ∀ᵐ w ∂E.P, w ∈ G → ∀ t ∈ T,
        thresholdCenteredScore E kind n t w ^ 2 ≤ H w := by
  letI := obsTailLaw_probability M hRV ell
  obtain ⟨hEnergy, hMean⟩ := evaluation_score_square_energy E kind n ell hn hiid
    hTraining hRV G hG hV0 (fun w hw => hLp w hw ell hEll) hV
  obtain ⟨H, hH, hInt, h0, hBudget, hDom⟩ :=
    evaluation_localized_threshold_square_envelope E n hn hiid (score E kind n)
      (measurable_score_training_joint E kind hTraining) G hG ell
      (fun w hw => (observation_tail_energy_unnormalize M hRV ell _
        ((hLp w hw ell hEll).integrable (by norm_num))).1) hEnergy
  refine ⟨H, hH, hInt, h0, ?_, ?_⟩
  · calc
      _ ≤ 16 * ((n : ℝ) / 2 * V * tailProb M ell) :=
        hBudget.trans (mul_le_mul_of_nonneg_left hMean (by norm_num))
      _ = _ := by ring
  · filter_upwards [hDom] with w hw
    intro hwG t ht
    have h := hw hwG t (hLower t ht)
    letI := obsTailLaw_probability M hRV t
    have hMeanEq := (observation_tail_energy_unnormalize M hRV t _
      ((hLp w hwG t ht).integrable (by norm_num))).2
    rw [hMeanEq] at h
    simpa only [thresholdCenteredScore, thresholdScoreSum_eq_indicator_sum,
      thresholdScoreMean, mul_assoc] using h

/-- [The population mean of the strict tail indicator equals the tail probability](goal).

@node: population_strict_tail_indicator_mean -/
lemma population_strict_tail_indicator_mean (M : ExtremeModel q d) (t : ℝ) :
    (∫ z : Obs q d, (if t < l1Norm z.2.2.2 then (1 : ℝ) else 0)
      ∂M.mu.map (observation M)) = tailProb M t := by
  have hobs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk (M.measurable_D.prodMk
      (M.measurable_Y.prodMk M.measurable_U))
  have hf : Measurable (fun z : Obs q d =>
      if t < l1Norm z.2.2.2 then (1 : ℝ) else 0) := by
    first | fun_prop | skip
    exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      measurable_const measurable_const
  rw [integral_map hobs.aemeasurable hf.aestronglyMeasurable]
  change (∫ w, {w | t < radius M w}.indicator (fun _ => (1 : ℝ)) w ∂M.mu) = _
  rw [integral_indicator_const _ (measurableSet_lt measurable_const (measurable_radius M))]
  simp [tailProb, measureReal_def]

/-- If [the sample size is even](hyp:hn), [sampling is independent and identically distributed](hyp:hiid), and [the training event is measurable](hyp:hG), then [there is a nonnegative integrable envelope for all squared threshold-centered counts on that event, with the stated 8n tail-probability budget](goal). Count-process symmetrization needs no score-moment premise.

@node: evaluation_localized_count_square_envelope -/
lemma evaluation_localized_count_square_envelope (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    (G : Set E.Om) (hG : MeasurableSet[trainSigma E n] G) (ell : ℝ) :
    ∃ H : E.Om → ℝ, Measurable H ∧ Integrable H E.P ∧ (∀ w, 0 ≤ H w) ∧
      (∫ w, H w ∂E.P) ≤ 8 * (n : ℝ) * tailProb M ell ∧
      ∀ᵐ w ∂E.P, w ∈ G → ∀ t ≥ ell,
        thresholdCenteredCount E n t w ^ 2 ≤ H w := by
  obtain ⟨hEnergy, hMean⟩ := evaluation_count_square_energy E n ell hn hiid G
    ((trainSigma_le E n) _ hG)
  have hMark (w : E.Om) (_hw : w ∈ G) : Integrable
      (fun z : Obs q d => if ell < l1Norm z.2.2.2 then (1 : ℝ) else 0)
      (M.mu.map (observation M)) := by
    exact (integrable_const (1 : ℝ)).indicator
      (measurableSet_lt measurable_const
        (show Measurable (fun z : Obs q d => l1Norm z.2.2.2) by fun_prop))
  obtain ⟨H, hH, hInt, h0, hBudget, hDom⟩ :=
    evaluation_localized_threshold_square_envelope E n hn hiid (fun _ _ => 1)
      (by fun_prop) G hG ell hMark hEnergy
  refine ⟨H, hH, hInt, h0, ?_, ?_⟩
  · calc
      _ ≤ 16 * ((n : ℝ) / 2 * tailProb M ell) :=
        hBudget.trans (mul_le_mul_of_nonneg_left hMean (by norm_num))
      _ = _ := by ring
  · filter_upwards [hDom] with w hw
    intro hwG t ht
    have h := hw hwG t ht
    rw [population_strict_tail_indicator_mean] at h
    simpa only [thresholdCenteredCount, evalCount_eq_sum_tail_indicators] using h

end Papers.TbsExtremeEffects
