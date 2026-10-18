module
public import Papers.TbsExtremeEffects.Helpers.ThresholdLocalization
public import Papers.TbsExtremeEffects.Helpers.ScoreSampling

/-! Deterministic conversion of bandwise score and count process bounds into
sampling error. The fitted score is held fixed across all thresholds. -/

@[expose] public section
noncomputable section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
variable {q d : ℕ} {M : ExtremeModel q d}

-- @node: thresholdScoreSum
/-- For a [specified model](hyp:M), [experiment](hyp:E), [estimator](hyp:kind), [sample size](hyp:n), [threshold](hyp:t), and [data realization](hyp:w), [the threshold score sum](goal) adds fitted scores over evaluation observations exceeding the threshold. -/
def thresholdScoreSum (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) : ℝ :=
  ∑ i ∈ evalSet E n t w, score E kind n w (obs E n w i)

-- @node: thresholdScoreMean
/-- For a [specified model](hyp:M), [experiment](hyp:E), [estimator](hyp:kind), [sample size](hyp:n), [threshold](hyp:t), and [data realization](hyp:w), [the threshold score mean](goal) is the fitted score's mean under the tail observation law. -/
def thresholdScoreMean (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) : ℝ :=
  ∫ z, score E kind n w z ∂obsTailLaw M t

-- @node: thresholdCenteredScore
/-- For a [specified model](hyp:M), [experiment](hyp:E), [estimator](hyp:kind), [sample size](hyp:n), [threshold](hyp:t), and [data realization](hyp:w), [the centered threshold score](goal) subtracts its split-size-and-tail-probability expectation. -/
def thresholdCenteredScore (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) : ℝ :=
  thresholdScoreSum E kind n t w -
    (n / 2 : ℕ) * tailProb M t * thresholdScoreMean E kind n t w

-- @node: thresholdCenteredCount
/-- For a [specified model](hyp:M), [experiment](hyp:E), [sample size](hyp:n), [threshold](hyp:t), and [data realization](hyp:w), [the centered threshold count](goal) is the evaluation count less its split-size-and-tail-probability expectation. -/
def thresholdCenteredCount (E : NeteExperiment M)
    (n : ℕ) (t : ℝ) (w : E.Om) : ℝ :=
  (evalCount E n t w : ℝ) - (n / 2 : ℕ) * tailProb M t

/-- [The evaluation count is nonincreasing as the threshold rises](goal). -/
-- @node: evalCount_antitone_threshold
lemma evalCount_antitone_threshold (E : NeteExperiment M) (n : ℕ) (w : E.Om) :
    Antitone (fun t => evalCount E n t w) := by
  classical
  intro t u htu
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi, hri⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, htu.trans_lt hri⟩

/-- [The training count is nonincreasing as the threshold rises](goal). -/
-- @node: trainCount_antitone_threshold
lemma trainCount_antitone_threshold (E : NeteExperiment M) (n : ℕ) (w : E.Om) :
    Antitone (fun t => trainCount E n t w) := by
  classical
  intro t u htu
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi, hri⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, htu.trans_lt hri⟩

/-- If the evaluation count at the upper endpoint is [at least the stated lower bound](hyp:hEval) and the training count there is [also at least that bound](hyp:hTrain), then throughout the band [both counts stay at least that bound](goal). -/
-- @node: threshold_band_counts_lower
lemma threshold_band_counts_lower (E : NeteExperiment M) (n : ℕ) (w : E.Om)
    {ell u N : ℝ} (hEval : N ≤ (evalCount E n u w : ℝ))
    (hTrain : N ≤ (trainCount E n u w : ℝ)) :
    ∀ t ∈ Set.Icc ell u,
      N ≤ (evalCount E n t w : ℝ) ∧ N ≤ (trainCount E n t w : ℝ) := by
  intro t ht
  exact ⟨hEval.trans (by exact_mod_cast evalCount_antitone_threshold E n w ht.2),
    hTrain.trans (by exact_mod_cast trainCount_antitone_threshold E n w ht.2)⟩

/-- [The threshold score sum equals the full evaluation-index sum with an indicator for exceeding the threshold](goal). -/
-- @node: thresholdScoreSum_eq_indicator_sum
lemma thresholdScoreSum_eq_indicator_sum (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) :
    thresholdScoreSum E kind n t w = ∑ i ∈ evalIndices n,
      if t < l1Norm (sampleU E n w i) then score E kind n w (obs E n w i) else 0 := by
  classical
  exact Finset.sum_filter _ _

/-- [Subtracting the score mean times the evaluation count equals the centered score minus the score mean times the centered count](goal). -/
-- @node: threshold_centered_score_identity
lemma threshold_centered_score_identity (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) :
    thresholdScoreSum E kind n t w -
        (evalCount E n t w : ℝ) * thresholdScoreMean E kind n t w =
      thresholdCenteredScore E kind n t w -
        thresholdScoreMean E kind n t w * thresholdCenteredCount E n t w := by
  unfold thresholdCenteredScore thresholdCenteredCount
  ring

/-- If the evaluation count is [positive](hyp:hN), then [the implemented estimate is the threshold score sum divided by that count](goal). -/
-- @node: etaEstimate_eq_thresholdScoreSum_div
lemma etaEstimate_eq_thresholdScoreSum_div (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) (hN : 0 < evalCount E n t w) :
    etaEstimate E kind n t w = thresholdScoreSum E kind n t w / evalCount E n t w := by
  cases kind <;>
    simp [etaEstimate, etaDR, etaIPW, Nat.ne_of_gt hN, thresholdScoreSum, score,
      div_eq_mul_inv, mul_comm]

/-- Under [regularly varying noise](hyp:hRV), a [square-integrable frozen score](hyp:hLp) whose [second moment is at most the stated bound](hyp:hV) has [absolute tail mean at most that bound's square root](goal). -/
-- @node: thresholdScoreMean_le_sqrt
lemma thresholdScoreMean_le_sqrt (E : NeteExperiment M) (kind : EstimatorKind)
    (hRV : NoiseRegularlyVarying M) (n : ℕ) (t : ℝ) (w : E.Om) {V : ℝ}
    (hLp : MemLp (score E kind n w) 2 (obsTailLaw M t))
    (hV : scoreSecondMoment E kind n t w ≤ V) :
    |thresholdScoreMean E kind n t w| ≤ Real.sqrt V := by
  let := obsTailLaw_probability M hRV t
  have hvar := variance_nonneg (X := score E kind n w) (μ := obsTailLaw M t)
  rw [variance_eq_sub hLp] at hvar
  have hsq : thresholdScoreMean E kind n t w ^ 2 ≤ V := by
    dsimp [thresholdScoreMean, scoreSecondMoment] at *
    simpa only [Pi.pow_apply] using (sub_nonneg.mp hvar).trans hV
  have hV0 : 0 ≤ V := (sq_nonneg _).trans hsq
  apply (Real.le_sqrt (abs_nonneg _) hV0).mpr
  simpa only [sq_abs] using hsq

/-- If the count lower bound is [positive](hyp:hN), the evaluation count is [at least that bound](hyp:hCount), the centered score is [bounded](hyp:hA), the centered count is [bounded](hyp:hB), and the score mean is [bounded](hyp:hU), then [the estimation error from that mean is bounded by the resulting ratio](goal). -/
-- @node: threshold_sampling_error_bound
lemma threshold_sampling_error_bound (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) {N A B U : ℝ}
    (hN : 0 < N) (hCount : N ≤ (evalCount E n t w : ℝ))
    (hA : |thresholdCenteredScore E kind n t w| ≤ A)
    (hB : |thresholdCenteredCount E n t w| ≤ B)
    (hU : |thresholdScoreMean E kind n t w| ≤ U) :
    |etaEstimate E kind n t w - thresholdScoreMean E kind n t w| ≤
      (A + U * B) / N := by
  have hCountPos : 0 < (evalCount E n t w : ℝ) := hN.trans_le hCount
  have hNatPos : 0 < evalCount E n t w := by exact_mod_cast hCountPos
  have hU0 : 0 ≤ U := (abs_nonneg _).trans hU
  have hNumerator : |thresholdScoreSum E kind n t w -
      (evalCount E n t w : ℝ) * thresholdScoreMean E kind n t w| ≤ A + U * B := by
    rw [threshold_centered_score_identity]
    calc
      _ ≤ |thresholdCenteredScore E kind n t w| +
          |thresholdScoreMean E kind n t w * thresholdCenteredCount E n t w| :=
        by simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (thresholdCenteredScore E kind n t w)
            (-(thresholdScoreMean E kind n t w * thresholdCenteredCount E n t w)))
      _ ≤ A + U * B := by
        rw [abs_mul]
        exact add_le_add hA (mul_le_mul hU hB (abs_nonneg _) hU0)
  rw [etaEstimate_eq_thresholdScoreSum_div E kind n t w hNatPos,
    div_sub' hCountPos.ne', abs_div, abs_of_pos hCountPos]
  exact (div_le_div_of_nonneg_right hNumerator hCountPos.le).trans
    (div_le_div_of_nonneg_left ((abs_nonneg _).trans hNumerator) hN hCount)

/-- For a [threshold selected inside the band](hyp:ht), with a [positive count lower bound](hyp:hN), an upper-endpoint count [at least that bound](hyp:hCount), and [uniform centered-process and bias bounds across the band](hyp:hProcesses), [the selected estimate is close to the target by the displayed bound](goal). -/
-- @node: selected_threshold_first_factor_bound
lemma selected_threshold_first_factor_bound (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (w : E.Om) {ell u t N A B U e : ℝ}
    (ht : t ∈ Set.Icc ell u) (hN : 0 < N)
    (hCount : N ≤ (evalCount E n u w : ℝ))
    (hProcesses : ∀ v ∈ Set.Icc ell u,
      |thresholdCenteredScore E kind n v w| ≤ A ∧
      |thresholdCenteredCount E n v w| ≤ B ∧
      |thresholdScoreMean E kind n v w| ≤ U ∧
      |thresholdScoreMean E kind n v w - etaTarget M| ≤ e) :
    |etaEstimate E kind n t w - etaTarget M| ≤ (A + U * B) / N + e := by
  obtain ⟨hA, hB, hU, he⟩ := hProcesses t ht
  have hCountT : N ≤ (evalCount E n t w : ℝ) :=
    hCount.trans (by exact_mod_cast evalCount_antitone_threshold E n w ht.2)
  exact (abs_sub_le (etaEstimate E kind n t w) (thresholdScoreMean E kind n t w)
    (etaTarget M)).trans (add_le_add
      (threshold_sampling_error_bound E kind n t w hN hCountT hA hB hU) he)

end Papers.TbsExtremeEffects
