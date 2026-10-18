module
public import Papers.TbsExtremeEffects.Helpers.EvaluationTrainingLaw
public import Causalean.Mathlib.Probability.FinitePartitionConditional

/-! Sampling bounds localized to a training event, and aggregation over evaluation patterns.
Moment assumptions are used only on the training event, as in the split-sample proof. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

-- @node: measurableSet_trained_truncated_failure
/-- Given [a probability law](hyp:mu), [a jointly measurable trained score](hyp:hf), [a truncation rule](hyp:B), [a measurable truncation rule](hyp:hB), [an evaluation sample size](hyp:m), and [a confidence level](hyp:delta), [the set where its truncated sampling radius is exceeded is measurable](goal). -/
lemma measurableSet_trained_truncated_failure
    {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (mu : Measure Z) [IsProbabilityMeasure mu] (f : A → Z → ℝ)
    (hf : Measurable (fun az : A × Z => f az.1 az.2))
    (B : A → ℝ) (hB : Measurable B) (m : ℕ) (delta : ℝ) :
    MeasurableSet {az : A × (Fin m → Z) |
      scoreSamplingRadius mu (f az.1) m (B az.1) delta <
        |(m : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂mu|} := by
  have hmean : Measurable (fun a => ∫ z, f a z ∂mu) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have habs : Measurable (fun az : A × Z => |f az.1 az.2|) := by fun_prop
  have hsmall : Measurable (fun a => ∫ z, if |f a z| ≤ B a then (f a z)^2 else 0 ∂mu) := by
    have hjoint : Measurable (fun az : A × Z =>
        if |f az.1 az.2| ≤ B az.1 then (f az.1 az.2)^2 else 0) := by
      exact (hf.pow_const 2).ite (measurableSet_le habs (hB.comp measurable_fst))
        measurable_const
    exact hjoint.stronglyMeasurable.integral_prod_right'.measurable
  have hlarge : Measurable (fun a => ∫ z, if B a < |f a z| then |f a z| else 0 ∂mu) := by
    have hjoint : Measurable (fun az : A × Z =>
        if B az.1 < |f az.1 az.2| then |f az.1 az.2| else 0) := by
      exact habs.ite (measurableSet_lt (hB.comp measurable_fst) habs) measurable_const
    exact hjoint.stronglyMeasurable.integral_prod_right'.measurable
  have havg : Measurable (fun az : A × (Fin m → Z) => ∑ j, f az.1 (az.2 j)) := by
    apply Finset.measurable_sum
    intro j _
    exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have herror : Measurable (fun az : A × (Fin m → Z) =>
      |(m : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂mu|) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.comp_def] using
      (((measurable_const : Measurable (fun _ : A × (Fin m → Z) => (m : ℝ)⁻¹)).mul havg).sub
        (hmean.comp measurable_fst)).norm
  unfold scoreSamplingRadius
  exact measurableSet_lt
    ((((measurable_const.mul (hsmall.comp measurable_fst)).div measurable_const).sqrt).add
      (measurable_const.mul (hlarge.comp measurable_fst)))
    herror

-- @node: measurableSet_trained_variance_failure
/-- Given [a probability law](hyp:mu), [a jointly measurable trained score](hyp:hf), [an evaluation sample size](hyp:m), and [a confidence level](hyp:delta), [the set where its variance sampling radius is exceeded is measurable](goal). -/
lemma measurableSet_trained_variance_failure
    {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (mu : Measure Z) [IsProbabilityMeasure mu] (f : A → Z → ℝ)
    (hf : Measurable (fun az : A × Z => f az.1 az.2)) (m : ℕ) (delta : ℝ) :
    MeasurableSet {az : A × (Fin m → Z) |
      Real.sqrt (4 * variance (f az.1) mu / (delta * m)) <
        |(m : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂mu|} := by
  have hmean : Measurable (fun a => ∫ z, f a z ∂mu) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hv : Measurable (fun a => evariance (f a) mu) := by
    simp_rw [evariance_eq_lintegral_ofReal]
    exact ((hf.sub (hmean.comp measurable_fst)).pow_const 2).ennreal_ofReal.lintegral_prod_right'
  have havg : Measurable (fun az : A × (Fin m → Z) => ∑ j, f az.1 (az.2 j)) := by
    apply Finset.measurable_sum
    intro j _
    exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have herror : Measurable (fun az : A × (Fin m → Z) =>
      |(m : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂mu|) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.comp_def] using
      (((measurable_const : Measurable (fun _ : A × (Fin m → Z) => (m : ℝ)⁻¹)).mul havg).sub
        (hmean.comp measurable_fst)).norm
  exact measurableSet_lt
    (((measurable_const.mul (hv.ennreal_toReal.comp measurable_fst)).div measurable_const).sqrt)
    herror

-- @node: evaluation_pattern_localized_truncated_failure
/-- If [the sample size is even](hyp:hn), [the observations are iid](hyp:hIID), [noise is regularly varying](hyp:hRV), [the error level is positive](hyp:hd), [the selected pattern is an evaluation pattern](hyp:hS), [that pattern has positive probability](hyp:hpos), [it contains observations](hyp:hcard), [the training statistic is training-measurable](hyp:hF), [the permitted training values form a measurable set](hyp:hg), [the frozen scores are measurable and integrable on that set](hyp:hf), [the truncation levels are nonnegative there](hyp:hB), and [the joint failure set is measurable](hyp:hV), then [conditional on the pattern, the localized truncated failure event has probability at most `delta / 2`](goal). -/
lemma evaluation_pattern_localized_truncated_failure {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    (hcard : 0 < S.card) {A : Type*} [MeasurableSpace A]
    (F : E.Om → A) (hF : Measurable[trainSigma E n] F)
    (g : Set A) (hg : MeasurableSet g)
    (f : A → Obs q d → ℝ) (B : A → ℝ) {delta : ℝ} (hd : 0 < delta)
    (hf : ∀ᵐ w ∂E.P, F w ∈ g →
      Measurable (f (F w)) ∧ Integrable (f (F w)) (obsTailLaw M t))
    (hB : ∀ᵐ w ∂E.P, F w ∈ g → 0 ≤ B (F w))
    (hV : MeasurableSet {az : A × (Fin S.card → Obs q d) |
      scoreSamplingRadius (obsTailLaw M t) (f az.1) S.card (B az.1) delta <
        |(S.card : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂obsTailLaw M t|}) :
    (cond E.P {w | evalSet E n t w = S}).real {w | F w ∈ g ∧
      scoreSamplingRadius (obsTailLaw M t) (f (F w)) S.card (B (F w)) delta <
        |(S.card : ℝ)⁻¹ * ∑ i ∈ S, f (F w) (obs E n w i) -
          ∫ z, f (F w) z ∂obsTailLaw M t|} ≤ delta / 2 := by
  let := obsTailLaw_probability M hRV t
  have hsum (w : E.Om) :
      ∑ j : Fin S.card, f (F w) (obs E n w ((S.equivFin).symm j)) =
        ∑ i ∈ S, f (F w) (obs E n w i) := by
    rw [(S.equivFin).symm.sum_comp (fun i : S => f (F w) (obs E n w i))]
    exact Finset.sum_attach S (fun i => f (F w) (obs E n w i))
  have h := evaluation_pattern_training_event_integral E n hn hIID hRV t S hS hpos F hF
    {az | az.1 ∈ g ∧
      scoreSamplingRadius (obsTailLaw M t) (f az.1) S.card (B az.1) delta <
        |(S.card : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂obsTailLaw M t|}
    ((hg.preimage measurable_fst).inter hV)
  have hsec (w : E.Om) :
      (Measure.pi (fun _ : Fin S.card => obsTailLaw M t)).real {z | F w ∈ g ∧
        scoreSamplingRadius (obsTailLaw M t) (f (F w)) S.card (B (F w)) delta <
          |(S.card : ℝ)⁻¹ * ∑ j, f (F w) (z j) - ∫ z, f (F w) z ∂obsTailLaw M t|} =
      if F w ∈ g then scoreIidFailure (obsTailLaw M t) (f (F w)) S.card (B (F w)) delta
        else 0 := by
    by_cases hw : F w ∈ g <;> simp [hw, scoreIidFailure]
  simp only [Set.mem_ofPred_eq, hsum, hsec] at h
  rw [h]
  have hb : ∀ᵐ w ∂E.P,
      ‖if F w ∈ g then scoreIidFailure (obsTailLaw M t) (f (F w)) S.card (B (F w)) delta
        else 0‖ ≤ delta / 2 := by
    filter_upwards [hf, hB] with w hfw hBw
    by_cases hw : F w ∈ g
    · simp only [hw, ↓reduceIte, Real.norm_eq_abs]
      rw [abs_of_nonneg (show 0 ≤ scoreIidFailure (obsTailLaw M t) (f (F w)) S.card (B (F w)) delta from ENNReal.toReal_nonneg)]
      exact score_iid_truncated_failure (obsTailLaw M t) hcard (hfw hw).1 (hfw hw).2
        (hBw hw) hd
    · simp only [hw, ↓reduceIte, norm_zero]; positivity
  have hb' := norm_integral_le_of_norm_le_const hb
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using (le_abs_self _).trans hb'

-- @node: evaluation_pattern_localized_variance_failure
/-- If [the sample size is even](hyp:hn), [the observations are iid](hyp:hIID), [noise is regularly varying](hyp:hRV), [the error level is positive](hyp:hd), [the selected pattern is an evaluation pattern](hyp:hS), [that pattern has positive probability](hyp:hpos), [it contains observations](hyp:hcard), [the training statistic is training-measurable](hyp:hF), [the permitted training values form a measurable set](hyp:hg), [the frozen scores have finite second moment there](hyp:hf), and [the joint failure set is measurable](hyp:hV), then [conditional on the pattern, the localized variance failure event has probability at most `delta / 4`](goal). -/
lemma evaluation_pattern_localized_variance_failure {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    (hcard : 0 < S.card) {A : Type*} [MeasurableSpace A]
    (F : E.Om → A) (hF : Measurable[trainSigma E n] F)
    (g : Set A) (hg : MeasurableSet g)
    (f : A → Obs q d → ℝ) {delta : ℝ} (hd : 0 < delta)
    (hf : ∀ᵐ w ∂E.P, F w ∈ g → MemLp (f (F w)) 2 (obsTailLaw M t))
    (hV : MeasurableSet {az : A × (Fin S.card → Obs q d) |
      Real.sqrt (4 * variance (f az.1) (obsTailLaw M t) / (delta * S.card)) <
        |(S.card : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂obsTailLaw M t|}) :
    (cond E.P {w | evalSet E n t w = S}).real {w | F w ∈ g ∧
      Real.sqrt (4 * variance (f (F w)) (obsTailLaw M t) / (delta * S.card)) <
        |(S.card : ℝ)⁻¹ * ∑ i ∈ S, f (F w) (obs E n w i) -
          ∫ z, f (F w) z ∂obsTailLaw M t|} ≤ delta / 4 := by
  let := obsTailLaw_probability M hRV t
  have hsum (w : E.Om) :
      ∑ j : Fin S.card, f (F w) (obs E n w ((S.equivFin).symm j)) =
        ∑ i ∈ S, f (F w) (obs E n w i) := by
    rw [(S.equivFin).symm.sum_comp (fun i : S => f (F w) (obs E n w i))]
    exact Finset.sum_attach S (fun i => f (F w) (obs E n w i))
  have h := evaluation_pattern_training_event_integral E n hn hIID hRV t S hS hpos F hF
    {az | az.1 ∈ g ∧
      Real.sqrt (4 * variance (f az.1) (obsTailLaw M t) / (delta * S.card)) <
        |(S.card : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂obsTailLaw M t|}
    ((hg.preimage measurable_fst).inter hV)
  have hsec (w : E.Om) :
      (Measure.pi (fun _ : Fin S.card => obsTailLaw M t)).real {z | F w ∈ g ∧
        Real.sqrt (4 * variance (f (F w)) (obsTailLaw M t) / (delta * S.card)) <
          |(S.card : ℝ)⁻¹ * ∑ j, f (F w) (z j) - ∫ z, f (F w) z ∂obsTailLaw M t|} =
      if F w ∈ g then scoreIidVarianceFailure (obsTailLaw M t) (f (F w)) S.card delta
        else 0 := by
    by_cases hw : F w ∈ g <;> simp [hw, scoreIidVarianceFailure]
  simp only [Set.mem_ofPred_eq, hsum, hsec] at h
  rw [h]
  have hb : ∀ᵐ w ∂E.P,
      ‖if F w ∈ g then scoreIidVarianceFailure (obsTailLaw M t) (f (F w)) S.card delta
        else 0‖ ≤ delta / 4 := by
    filter_upwards [hf] with w hfw
    by_cases hw : F w ∈ g
    · simp only [hw, ↓reduceIte, Real.norm_eq_abs]
      rw [abs_of_nonneg (show 0 ≤ scoreIidVarianceFailure (obsTailLaw M t) (f (F w)) S.card delta from ENNReal.toReal_nonneg)]
      exact score_iid_variance_failure (obsTailLaw M t) hcard (hfw hw) hd
    · simp only [hw, ↓reduceIte, norm_zero]; positivity
  have hb' := norm_integral_le_of_norm_le_const hb
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using (le_abs_self _).trans hb'

-- @node: evaluation_failure_of_pattern_bounds
/-- If [the failure event is measurable](hyp:hR), [the proposed bound is nonnegative](hyp:hb), and [every positive-probability evaluation pattern gives that conditional bound](hyp:hcond), then [the unconditional failure probability satisfies the same bound](goal). -/
lemma evaluation_failure_of_pattern_bounds {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (t : ℝ) (R : Set E.Om)
    (hR : MeasurableSet R) {b : ℝ} (hb : 0 ≤ b)
    (hcond : ∀ S : Finset (Fin n), E.P {w | evalSet E n t w = S} ≠ 0 →
      (cond E.P {w | evalSet E n t w = S}).real R ≤ b) :
    E.P.real R ≤ b := by
  have hm : Measurable (fun w (i : Fin n) =>
      if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0)) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : n / 2 ≤ i.val
    · simpa only [hi, ↓reduceIte, Function.comp_def] using (measurable_pi_apply i).comp
        (measurable_obs_tuple M E n)
    · simp only [hi, ↓reduceIte]; fun_prop
  have hC (S : Finset (Fin n)) : MeasurableSet {w | evalSet E n t w = S} :=
    hm.comap_le _ (evaluation_pattern_measurable_mask E n t S)
  have hbound := Causalean.Mathlib.Probability.measure_le_of_cond_le_on_finite_partition E.P
    (fun S : Finset (Fin n) => {w | evalSet E n t w = S}) hC
    (fun S T hST => by
      apply Set.disjoint_left.mpr
      intro w hwS hwT
      exact hST (hwS.symm.trans hwT))
    (by ext w; simp) R hR (ENNReal.ofReal b) (by
      intro S hpos
      let := cond_isProbabilityMeasure hpos
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hb).mpr (hcond S hpos))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hb)

-- @node: evaluation_positive_pattern_failure_bound
/-- If [the failure event is measurable](hyp:hR), [it never has a zero evaluation count](hyp:hcount), [the proposed bound is nonnegative](hyp:hb), and [every nonempty positive-probability evaluation pattern gives that conditional bound](hyp:hcond), then [the unconditional failure probability satisfies the same bound](goal). -/
lemma evaluation_positive_pattern_failure_bound {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (t : ℝ) (R : Set E.Om)
    (hR : MeasurableSet R) (hcount : ∀ w ∈ R, evalCount E n t w ≠ 0)
    {b : ℝ} (hb : 0 ≤ b)
    (hcond : ∀ S : Finset (Fin n), S ⊆ evalIndices n →
      E.P {w | evalSet E n t w = S} ≠ 0 → 0 < S.card →
      (cond E.P {w | evalSet E n t w = S}).real R ≤ b) :
    E.P.real R ≤ b := by
  apply evaluation_failure_of_pattern_bounds E n t R hR hb
  intro S hpos
  let := cond_isProbabilityMeasure hpos
  have hm : Measurable (fun w (i : Fin n) =>
      if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0)) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : n / 2 ≤ i.val
    · simpa only [hi, ↓reduceIte, Function.comp_def] using (measurable_pi_apply i).comp
        (measurable_obs_tuple M E n)
    · simp only [hi, ↓reduceIte]; fun_prop
  have hcell : MeasurableSet {w | evalSet E n t w = S} :=
    hm.comap_le _ (evaluation_pattern_measurable_mask E n t S)
  obtain ⟨w, hw⟩ := nonempty_of_measure_ne_zero hpos
  have hS : S ⊆ evalIndices n := by
    rw [← hw]
    exact Finset.filter_subset _ _
  by_cases hcard : 0 < S.card
  · exact hcond S hS hpos hcard
  · have hzero : S.card = 0 := by omega
    have hnull : (cond E.P {w | evalSet E n t w = S}) R = 0 := by
      apply measure_mono_null_ae (t := ∅) ?_ (measure_empty)
      filter_upwards [ae_cond_mem hcell] with w hw
      intro hwR
      exact (hcount w hwR) (by simp only [evalCount, hw, hzero])
    simp only [measureReal_def, hnull, ENNReal.toReal_zero]
    exact hb

-- @node: evaluation_localized_truncated_failure
/-- If [the sample size is even](hyp:hn), [the observations are iid](hyp:hIID), [noise is regularly varying](hyp:hRV), [the error level is positive](hyp:hd), [the training statistic is training-measurable](hyp:hF), [the permitted training values form a measurable set](hyp:hg), [the frozen scores are measurable and integrable there](hyp:hf), [the truncation levels are nonnegative there](hyp:hB), [the score is jointly measurable](hyp:hfJoint), [the truncation rule is measurable](hyp:hBmeas), [the failure event is measurable](hyp:hR), and [every point of it has the stated localized failure properties](hyp:hpoint), then [its probability is at most `delta / 2`](goal). -/
lemma evaluation_localized_truncated_failure {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A)
    (hF : Measurable[trainSigma E n] F) (g : Set A) (hg : MeasurableSet g)
    (f : A → Obs q d → ℝ) (B : A → ℝ) {delta : ℝ} (hd : 0 < delta)
    (hf : ∀ᵐ w ∂E.P, F w ∈ g →
      Measurable (f (F w)) ∧ Integrable (f (F w)) (obsTailLaw M t))
    (hB : ∀ᵐ w ∂E.P, F w ∈ g → 0 ≤ B (F w))
    (hfJoint : Measurable (fun az : A × Obs q d => f az.1 az.2))
    (hBmeas : Measurable B)
    (R : Set E.Om) (hR : MeasurableSet R)
    (hpoint : ∀ w ∈ R, F w ∈ g ∧ evalCount E n t w ≠ 0 ∧
      scoreSamplingRadius (obsTailLaw M t) (f (F w)) (evalCount E n t w) (B (F w)) delta <
        |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w, f (F w) (obs E n w i) -
          ∫ z, f (F w) z ∂obsTailLaw M t|) :
    E.P.real R ≤ delta / 2 := by
  let := obsTailLaw_probability M hRV t
  apply evaluation_positive_pattern_failure_bound E n t R hR
    (fun w hw => (hpoint w hw).2.1) (by positivity)
  intro S hS hpos hcard
  let := cond_isProbabilityMeasure hpos
  have hbound := evaluation_pattern_localized_truncated_failure E n hn hIID hRV t S
    hS hpos hcard F hF g hg f B hd hf hB
    (measurableSet_trained_truncated_failure (obsTailLaw M t) f hfJoint B hBmeas S.card delta)
  apply le_trans _ hbound
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  have hm : Measurable (fun w (i : Fin n) =>
      if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0)) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : n / 2 ≤ i.val
    · simpa only [hi, ↓reduceIte, Function.comp_def] using (measurable_pi_apply i).comp
        (measurable_obs_tuple M E n)
    · simp only [hi, ↓reduceIte]; fun_prop
  have hcell : MeasurableSet {w | evalSet E n t w = S} :=
    hm.comap_le _ (evaluation_pattern_measurable_mask E n t S)
  filter_upwards [ae_cond_mem hcell] with w hwcell
  intro hw
  obtain ⟨hwg, hwcount, hwbad⟩ := hpoint w hw
  refine ⟨hwg, ?_⟩
  simpa only [evalCount, hwcell] using hwbad

-- @node: evaluation_localized_variance_failure
/-- If [the sample size is even](hyp:hn), [the observations are iid](hyp:hIID), [noise is regularly varying](hyp:hRV), [the error level is positive](hyp:hd), [the training statistic is training-measurable](hyp:hF), [the permitted training values form a measurable set](hyp:hg), [the frozen scores have finite second moment there](hyp:hf), [the score is jointly measurable](hyp:hfJoint), [the failure event is measurable](hyp:hR), and [every point of it has the stated localized failure properties](hyp:hpoint), then [its probability is at most `delta / 4`](goal). -/
lemma evaluation_localized_variance_failure {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A)
    (hF : Measurable[trainSigma E n] F) (g : Set A) (hg : MeasurableSet g)
    (f : A → Obs q d → ℝ) {delta : ℝ} (hd : 0 < delta)
    (hf : ∀ᵐ w ∂E.P, F w ∈ g →
      MemLp (f (F w)) 2 (obsTailLaw M t))
    (hfJoint : Measurable (fun az : A × Obs q d => f az.1 az.2))
    (R : Set E.Om) (hR : MeasurableSet R)
    (hpoint : ∀ w ∈ R, F w ∈ g ∧ evalCount E n t w ≠ 0 ∧
      Real.sqrt (4 * variance (f (F w)) (obsTailLaw M t) / (delta * evalCount E n t w)) <
        |(evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w, f (F w) (obs E n w i) -
          ∫ z, f (F w) z ∂obsTailLaw M t|) :
    E.P.real R ≤ delta / 4 := by
  let := obsTailLaw_probability M hRV t
  apply evaluation_positive_pattern_failure_bound E n t R hR
    (fun w hw => (hpoint w hw).2.1) (by positivity)
  intro S hS hpos hcard
  let := cond_isProbabilityMeasure hpos
  have hbound := evaluation_pattern_localized_variance_failure E n hn hIID hRV t S
    hS hpos hcard F hF g hg f hd hf
    (measurableSet_trained_variance_failure (obsTailLaw M t) f hfJoint S.card delta)
  apply le_trans _ hbound
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  have hm : Measurable (fun w (i : Fin n) =>
      if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0)) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : n / 2 ≤ i.val
    · simpa only [hi, ↓reduceIte, Function.comp_def] using (measurable_pi_apply i).comp
        (measurable_obs_tuple M E n)
    · simp only [hi, ↓reduceIte]; fun_prop
  have hcell : MeasurableSet {w | evalSet E n t w = S} :=
    hm.comap_le _ (evaluation_pattern_measurable_mask E n t S)
  filter_upwards [ae_cond_mem hcell] with w hwcell
  intro hw
  obtain ⟨hwg, hwcount, hwbad⟩ := hpoint w hw
  refine ⟨hwg, ?_⟩
  simpa only [evalCount, hwcell] using hwbad

end Papers.TbsExtremeEffects
