module
public import Papers.TbsExtremeEffects.Helpers.ScoreMeasurability
public import Papers.TbsExtremeEffects.Helpers.EvaluationPatternBounds

/-! Training-information measurability of fitted scores and their sampling failures. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {q d : ℕ} {M : ExtremeModel q d}

-- @node: measurable_score_training_joint
/-- If the fitted exponent uses [only training information](hyp:hTraining), then [the fitted score is jointly measurable in the training data and an observation](goal). -/
@[fun_prop] lemma measurable_score_training_joint (E : NeteExperiment M)
    (kind : EstimatorKind) {n : ℕ} (hTraining : ExponentTraining E n) :
    @Measurable (E.Om × Obs q d) ℝ
      ((trainSigma E n).prod inferInstance) inferInstance
      (fun z => score E kind n z.1 z.2) := by
  let : MeasurableSpace E.Om := trainSigma E n
  have halpha : Measurable (E.alphaHat n) := hTraining
  have hpTrain := E.pHat_training n
  have hgSigma : MeasurableSpace.comap
      (fun w => (trainingMap E.Zraw E.trainSet E.aux n w, E.alphaHat n w))
        inferInstance ≤ trainSigma E n := by
    apply Measurable.comap_le
    exact (Measurable.of_comap_le le_rfl).prodMk halpha
  have hgTrain := (E.gHat_training n).mono
    (sup_le_sup (MeasurableSpace.comap_mono hgSigma) le_rfl) le_rfl
  have hdir : Measurable (fun z : E.Om × Obs q d => obsDirection z.2) := by
    unfold obsDirection
    fun_prop
  have hp : Measurable (fun z : E.Om × Obs q d => E.pHat n z.1 z.2.1) :=
    hpTrain.comp (measurable_fst.prodMk measurable_snd.fst)
  have hg (a : E.Om × Obs q d → Bool) (ha : Measurable a) :
      Measurable (fun z => E.gHat n z.1 z.2.1 (a z) (obsDirection z.2)) :=
    hgTrain.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk (ha.prodMk hdir)))
  have hY : Measurable (fun z : E.Om × Obs q d => pseudoOutcome E n z.1 z.2) := by
    unfold pseudoOutcome
    fun_prop
  have hD1 : Measurable (fun z : E.Om × Obs q d => if z.2.2.1 then (1 : ℝ) else 0) :=
    (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      measurable_snd.snd.fst
  have hD0 : Measurable (fun z : E.Om × Obs q d => if z.2.2.1 then (0 : ℝ) else 1) :=
    (measurable_of_finite (fun b : Bool => if b then (0 : ℝ) else 1)).comp
      measurable_snd.snd.fst
  cases kind
  · exact hY.mul ((hD1.div hp).sub (hD0.div (measurable_const.sub hp)))
  · exact ((hg (fun _ => true) measurable_const).sub (hg (fun _ => false) measurable_const)).add
      (((hD1.sub hp).div (hp.mul (measurable_const.sub hp))).mul
        (hY.sub (hg (fun z => z.2.2.1) measurable_snd.snd.fst)))

-- @node: score_evaluation_average_eq
/-- If the evaluation count is [nonzero](hyp:hw), then [the estimate equals the average fitted score over thresholded evaluation observations](goal). -/
lemma score_evaluation_average_eq (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) (hw : evalCount E n t w ≠ 0) :
    etaEstimate E kind n t w = (evalCount E n t w : ℝ)⁻¹ *
      ∑ i ∈ evalSet E n t w, score E kind n w (obs E n w i) := by
  cases kind <;> simp [etaEstimate, etaIPW, etaDR, hw, score]

/-- For an [even sample size](hyp:hn), [independent sampling](hyp:hIID), [regularly varying noise](hyp:hRV), and a [training-measurable fitted exponent](hyp:hTraining), with a [training-measurable nuisance event](hyp:hG), a [measurable count event](hyp:hN), a [training-measurable truncation bound](hyp:hB) that is [nonnegative](hyp:hBpos), a [positive failure level](hyp:hd), [nonzero evaluation counts on the count event](hyp:hcount), and [integrable frozen scores on the nuisance event](hyp:hf), [the truncated sampling failure within their intersection has probability at most half the failure level](goal). -/
-- @node: score_evaluation_localized_truncated_failure
lemma score_evaluation_localized_truncated_failure (E : NeteExperiment M)
    (kind : EstimatorKind) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (hTraining : ExponentTraining E n)
    (t : ℝ) (G N : Set E.Om) (hG : MeasurableSet[trainSigma E n] G)
    (hN : MeasurableSet N) (B : E.Om → ℝ) (hB : Measurable[trainSigma E n] B)
    (hBpos : ∀ w, 0 ≤ B w) {delta : ℝ} (hd : 0 < delta)
    (hcount : ∀ w ∈ N, evalCount E n t w ≠ 0)
    (hf : ∀ᵐ w ∂E.P, w ∈ G → Integrable (score E kind n w) (obsTailLaw M t)) :
    E.P.real ((G ∩ N) \ {w |
      |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
        scoreSamplingRadius (obsTailLaw M t) (score E kind n w)
          (evalCount E n t w) (B w) delta}) ≤ delta / 2 := by
  classical
  let R := {w | |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
    scoreSamplingRadius (obsTailLaw M t) (score E kind n w)
      (evalCount E n t w) (B w) delta}
  have hR : MeasurableSet R := measurableSet_score_truncation_event E kind hRV hTraining
    t delta B (hB.mono (trainSigma_le E n) le_rfl)
  have hGm : MeasurableSet G := (trainSigma_le E n) _ hG
  refine @evaluation_localized_truncated_failure q d M E n hn hIID hRV t
    E.Om (trainSigma E n) id measurable_id G hG (score E kind n) B delta hd
    ?_ ?_ (measurable_score_training_joint E kind hTraining) hB
    ((G ∩ N) \ R) ((hGm.inter hN).diff hR) ?_
  · filter_upwards [hf] with w hw hg
    exact ⟨measurable_score_frozen E kind n w, hw hg⟩
  · exact Filter.Eventually.of_forall (fun w _ => hBpos w)
  · intro w hw
    refine ⟨hw.1.1, hcount w hw.1.2, ?_⟩
    have herr : scoreSamplingRadius (obsTailLaw M t) (score E kind n w)
        (evalCount E n t w) (B w) delta <
        |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| :=
      lt_of_not_ge hw.2
    change scoreSamplingRadius _ _ _ _ _ < |etaEstimate E kind n t w - _| at herr
    rwa [score_evaluation_average_eq E kind n t w (hcount w hw.1.2)] at herr

/-- For an [even sample size](hyp:hn), [independent sampling](hyp:hIID), [regularly varying noise](hyp:hRV), and a [training-measurable fitted exponent](hyp:hTraining), with a [training-measurable nuisance event](hyp:hG), a [measurable count event](hyp:hN), a [positive failure level](hyp:hd), [nonzero evaluation counts on the count event](hyp:hcount), and [square-integrable frozen scores on the nuisance event](hyp:hf), [the variance-based sampling failure within their intersection has probability at most one quarter of the failure level](goal). -/
-- @node: score_evaluation_localized_variance_failure
lemma score_evaluation_localized_variance_failure (E : NeteExperiment M)
    (kind : EstimatorKind) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (hTraining : ExponentTraining E n)
    (t : ℝ) (G N : Set E.Om) (hG : MeasurableSet[trainSigma E n] G)
    (hN : MeasurableSet N) {delta : ℝ} (hd : 0 < delta)
    (hcount : ∀ w ∈ N, evalCount E n t w ≠ 0)
    (hf : ∀ᵐ w ∂E.P, w ∈ G → MemLp (score E kind n w) 2 (obsTailLaw M t)) :
    E.P.real ((G ∩ N) \ {w |
      |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
        Real.sqrt (4 * (scoreVariance E kind n t w).toReal /
          (delta * evalCount E n t w))}) ≤ delta / 4 := by
  classical
  let R := {w | |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
    Real.sqrt (4 * (scoreVariance E kind n t w).toReal / (delta * evalCount E n t w))}
  have hR : MeasurableSet R := measurableSet_score_variance_event E kind hRV hTraining t delta
  have hGm : MeasurableSet G := (trainSigma_le E n) _ hG
  apply @evaluation_localized_variance_failure q d M E n hn hIID hRV t
    E.Om (trainSigma E n) id measurable_id G hG (score E kind n) delta hd
    hf (measurable_score_training_joint E kind hTraining)
    ((G ∩ N) \ R) ((hGm.inter hN).diff hR)
  intro w hw
  refine ⟨hw.1.1, hcount w hw.1.2, ?_⟩
  have herr : Real.sqrt (4 * (scoreVariance E kind n t w).toReal /
      (delta * evalCount E n t w)) <
      |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| :=
    lt_of_not_ge hw.2
  change Real.sqrt (4 * (scoreVariance E kind n t w).toReal / (delta * evalCount E n t w)) <
    |etaEstimate E kind n t w - _| at herr
  rwa [score_evaluation_average_eq E kind n t w (hcount w hw.1.2)] at herr

-- @node: score_evaluation_truncated_sampling
/-- For an [even sample size](hyp:hn), [independent sampling](hyp:hIID), [regularly varying noise](hyp:hRV), a [training-measurable fitted exponent](hyp:hTraining), a [training-measurable nuisance event](hyp:hG), a [measurable count event](hyp:hN), a [training-measurable nonnegative truncation bound](hyp:hB,hBpos), a [positive failure level](hyp:hd), [the nuisance event having probability at least one minus one quarter of the failure level](hyp:hGprob), [the count event having that same probability bound](hyp:hNprob), [nonzero counts on the count event](hyp:hcount), and [integrable frozen scores on the nuisance event](hyp:hf), [the joint good event has probability at least one minus the failure level](goal). -/
lemma score_evaluation_truncated_sampling (E : NeteExperiment M)
    (kind : EstimatorKind) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (hTraining : ExponentTraining E n)
    (t : ℝ) (G N : Set E.Om) (hG : MeasurableSet[trainSigma E n] G)
    (hN : MeasurableSet N) (B : E.Om → ℝ) (hB : Measurable[trainSigma E n] B)
    (hBpos : ∀ w, 0 ≤ B w) {delta : ℝ} (hd : 0 < delta)
    (hGprob : 1 - delta / 4 ≤ E.P.real G) (hNprob : 1 - delta / 4 ≤ E.P.real N)
    (hcount : ∀ w ∈ N, evalCount E n t w ≠ 0)
    (hf : ∀ᵐ w ∂E.P, w ∈ G → Integrable (score E kind n w) (obsTailLaw M t)) :
    1 - delta ≤ E.P.real ((G ∩ N) ∩ {w |
      |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
        scoreSamplingRadius (obsTailLaw M t) (score E kind n w)
          (evalCount E n t w) (B w) delta}) := by
  classical
  let R := {w | |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
    scoreSamplingRadius (obsTailLaw M t) (score E kind n w)
      (evalCount E n t w) (B w) delta}
  have hR : MeasurableSet R := measurableSet_score_truncation_event E kind hRV hTraining
    t delta B (hB.mono (trainSigma_le E n) le_rfl)
  have hGm : MeasurableSet G := (trainSigma_le E n) _ hG
  have hbad := score_evaluation_localized_truncated_failure E kind n hn hIID hRV
    hTraining t G N hG hN B hB hBpos hd hcount hf
  have hGN := probability_intersection_lower E.P G N hN hGprob hNprob
  have hsplit := measureReal_inter_add_sdiff (μ := E.P) (s := G ∩ N) hR
  change 1 - delta ≤ E.P.real ((G ∩ N) ∩ R)
  linarith

-- @node: score_evaluation_variance_sampling
/-- For an [even sample size](hyp:hn), [independent sampling](hyp:hIID), [regularly varying noise](hyp:hRV), a [training-measurable fitted exponent](hyp:hTraining), a [training-measurable nuisance event](hyp:hG), a [measurable count event](hyp:hN), a [positive failure level](hyp:hd), [the nuisance event having probability at least one minus one quarter of the failure level](hyp:hGprob), [the count event having that same probability bound](hyp:hNprob), [nonzero counts on the count event](hyp:hcount), and [square-integrable frozen scores on the nuisance event](hyp:hf), [the joint variance-controlled event has probability at least one minus the failure level](goal). -/
lemma score_evaluation_variance_sampling (E : NeteExperiment M)
    (kind : EstimatorKind) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (hTraining : ExponentTraining E n)
    (t : ℝ) (G N : Set E.Om) (hG : MeasurableSet[trainSigma E n] G)
    (hN : MeasurableSet N) {delta : ℝ} (hd : 0 < delta)
    (hGprob : 1 - delta / 4 ≤ E.P.real G) (hNprob : 1 - delta / 4 ≤ E.P.real N)
    (hcount : ∀ w ∈ N, evalCount E n t w ≠ 0)
    (hf : ∀ᵐ w ∂E.P, w ∈ G → MemLp (score E kind n w) 2 (obsTailLaw M t)) :
    1 - delta ≤ E.P.real ((G ∩ N) ∩ {w |
      |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
        Real.sqrt (4 * (scoreVariance E kind n t w).toReal / (delta * evalCount E n t w))}) := by
  classical
  let R := {w | |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| ≤
    Real.sqrt (4 * (scoreVariance E kind n t w).toReal / (delta * evalCount E n t w))}
  have hR : MeasurableSet R := measurableSet_score_variance_event E kind hRV hTraining t delta
  have hGm : MeasurableSet G := (trainSigma_le E n) _ hG
  have hbad := score_evaluation_localized_variance_failure E kind n hn hIID hRV
    hTraining t G N hG hN hd hcount hf
  have hGN := probability_intersection_lower E.P G N hN hGprob hNprob
  have hsplit := measureReal_inter_add_sdiff (μ := E.P) (s := G ∩ N) hR
  change 1 - delta ≤ E.P.real ((G ∩ N) ∩ R)
  linarith

end Papers.TbsExtremeEffects
