module
public import Papers.TbsExtremeEffects.Helpers.EvaluationTailLaw
public import Papers.TbsExtremeEffects.Helpers.ScoreMeasurability

/-! Training laws and independence after conditioning on evaluation exceedance patterns.
The proofs use event factorization, without a disintegration assumption. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/-- If [the training sigma-algebra is contained in the ambient sigma-algebra](hyp:hG), [the event sigma-algebra is contained in it](hyp:hH), [the two sigma-algebras are independent under the original probability law](hyp:hind), [the conditioning event is measurable for the event sigma-algebra](hyp:hs), [that event has positive probability](hyp:hpos), and [the queried set is training-measurable](hyp:hA), then [conditioning on the event leaves the probability of the queried training set unchanged](goal).

@node: training_measure_cond_event -/
lemma training_measure_cond_event {W : Type*} [mW : MeasurableSpace W]
    (P : Measure W) [IsProbabilityMeasure P] {G H : MeasurableSpace W}
    (hG : G ≤ mW) (hH : H ≤ mW) (hind : Indep G H P)
    {s A : Set W} (hs : MeasurableSet[H] s) (hpos : P s ≠ 0)
    (hA : MeasurableSet[G] A) : cond P s A = P A := by
  rw [cond_apply (hH _ hs), Set.inter_comm,
    (Indep_iff G H P).mp hind A s hA hs, ← mul_assoc,
    mul_comm (P s)⁻¹ (P A), mul_assoc, ENNReal.inv_mul_cancel hpos (measure_ne_top P s),
    mul_one]

/-- If [both sigma-algebras are contained in the ambient sigma-algebra](hyp:hG,hH), [they are independent under the original law](hyp:hind), and [the conditioning event is event-measurable and has positive probability](hyp:hs,hpos), then [the same two sigma-algebras remain independent after conditioning on that event](goal).

@node: training_indep_cond_event -/
lemma training_indep_cond_event {W : Type*} [mW : MeasurableSpace W]
    (P : Measure W) [IsProbabilityMeasure P] {G H : MeasurableSpace W}
    (hG : G ≤ mW) (hH : H ≤ mW) (hind : Indep G H P)
    {s : Set W} (hs : MeasurableSet[H] s) (hpos : P s ≠ 0) :
    Indep G H (cond P s) := by
  let : MeasurableSpace W := mW
  apply (Indep_iff G H (cond P s)).mpr
  intro A B hA hB
  rw [training_measure_cond_event P hG hH hind hs hpos hA,
    cond_apply (hH _ hs), cond_apply (hH _ hs)]
  rw [show s ∩ (A ∩ B) = A ∩ (s ∩ B) from by ext w; simp [and_left_comm],
    (Indep_iff G H P).mp hind A (s ∩ B) hA (hs.inter hB)]
  ac_rfl

/-- If [the training and event sigma-algebras lie within the ambient sigma-algebra](hyp:hG,hH), [they are independent](hyp:hind), [the conditioning event is event-measurable and non-null](hyp:hs,hpos), and [the reported quantity is training-measurable](hyp:hF), then [its distribution is unchanged by conditioning on the event](goal).

@node: training_map_cond_event -/
lemma training_map_cond_event {W A : Type*} [mW : MeasurableSpace W]
    [MeasurableSpace A] (P : Measure W) [IsProbabilityMeasure P]
    {G H : MeasurableSpace W} (hG : G ≤ mW) (hH : H ≤ mW) (hind : Indep G H P)
    {s : Set W} (hs : MeasurableSet[H] s) (hpos : P s ≠ 0)
    (F : W → A) (hF : Measurable[G] F) :
    @Measure.map W A mW _ F (cond P s) = @Measure.map W A mW _ F P := by
  let : MeasurableSpace W := mW
  ext B hB
  rw [Measure.map_apply (hF.mono hG le_rfl) hB,
    Measure.map_apply (hF.mono hG le_rfl) hB]
  exact training_measure_cond_event P hG hH hind hs hpos (hF hB)

/-- [The event that the evaluation exceedance pattern equals the chosen finite index set is measurable using only the masked evaluation observations](goal).

@node: evaluation_pattern_measurable_mask -/
lemma evaluation_pattern_measurable_mask {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (t : ℝ) (S : Finset (Fin n)) :
    MeasurableSet[MeasurableSpace.comap
      (fun w (i : Fin n) => if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0))
      inferInstance] {w | evalSet E n t w = S} := by
  let F : (Fin n → Obs q d) → Finset (Fin n) := fun z =>
    (evalIndices n).filter (fun i => t < l1Norm (z i).2.2.2)
  have hF : Measurable F := by
    apply measurable_finset_iff.mpr
    intro i
    apply measurableSet_setOfPred.mp
    simp only [F, Finset.mem_filter]
    by_cases hi : i ∈ evalIndices n
    · simp only [hi, true_and]
      exact measurableSet_lt measurable_const (by unfold l1Norm; fun_prop)
    · simp only [hi, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  have hmask : Measurable[MeasurableSpace.comap
      (fun w (i : Fin n) => if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0))
      inferInstance]
      (fun w (i : Fin n) => if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0)) :=
    Measurable.of_comap_le le_rfl
  have heq : (fun w => F (fun i => if n / 2 ≤ i.val then obs E n w i
      else (0, false, 0, 0))) = evalSet E n t := by
    funext w
    apply Finset.ext
    intro i
    change (i ∈ (evalIndices n).filter (fun j => t < l1Norm
      (if n / 2 ≤ j.val then obs E n w j else (0, false, 0, 0)).2.2.2)) ↔
      i ∈ (evalIndices n).filter (fun j => t < l1Norm (obs E n w j).2.2.2)
    simp only [Finset.mem_filter, evalIndices, Finset.mem_univ, true_and]
    by_cases hi : n / 2 ≤ i.val <;> simp [hi]
  rw [← heq]
  exact (hF.comp hmask) (measurableSet_singleton S)

/-- If [the sample size is even](hyp:hn), [the observations are IID](hyp:hIID), [the specified evaluation pattern has positive probability](hyp:hpos), and [the fitted training statistic is training-measurable](hyp:hF), then [conditioning on that pattern does not change the statistic’s distribution](goal).

@node: evaluation_pattern_training_map -/
lemma evaluation_pattern_training_map {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (t : ℝ) (S : Finset (Fin n)) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A) (hF : Measurable[trainSigma E n] F) :
    (cond E.P {w | evalSet E n t w = S}).map F = E.P.map F := by
  apply training_map_cond_event E.P (trainSigma_le E n)
    (measurable_pi_lambda _ fun i => by
      by_cases hi : n / 2 ≤ i.val
      · simpa only [hi, ↓reduceIte, Function.comp_def] using (measurable_pi_apply i).comp
          (measurable_obs_tuple M E n)
      · simp only [hi, ↓reduceIte]; fun_prop).comap_le
    (evaluation_independent_training M E n hn hIID)
    (evaluation_pattern_measurable_mask E n t S) hpos F hF

/-- If [every selected index belongs to the evaluation half](hyp:hS), then [the selected observations are measurable from the masked evaluation observations](goal).

@node: evaluation_selected_measurable_mask -/
lemma evaluation_selected_measurable_mask {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (S : Finset (Fin n)) (hS : S ⊆ evalIndices n) :
    Measurable[MeasurableSpace.comap
      (fun w (i : Fin n) => if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0))
      inferInstance] (fun w (i : S) => obs E n w i) := by
  let : MeasurableSpace E.Om := MeasurableSpace.comap
    (fun w (i : Fin n) => if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0))
    inferInstance
  have hm : Measurable[MeasurableSpace.comap
      (fun w (i : Fin n) => if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0))
      inferInstance]
      (fun w (i : Fin n) => if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0)) :=
    Measurable.of_comap_le le_rfl
  apply measurable_pi_lambda
  intro i
  have hi : n / 2 ≤ i.val.val := (Finset.mem_filter.mp (hS i.property)).2
  simpa only [Function.comp_def, hi, ↓reduceIte] using
    (measurable_pi_apply (i : Fin n)).comp hm

/-- If [the sample size is even](hyp:hn), [sampling is IID](hyp:hIID), [the selected indices are all evaluation indices](hyp:hS), [the specified evaluation pattern is non-null](hyp:hpos), and [the fitted statistic is training-measurable](hyp:hF), then [that statistic and the selected evaluation observations are independent after conditioning on the pattern](goal).

@node: evaluation_pattern_training_selected_indep -/
lemma evaluation_pattern_training_selected_indep {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (t : ℝ) (S : Finset (Fin n)) (hS : S ⊆ evalIndices n)
    (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A) (hF : Measurable[trainSigma E n] F) :
    IndepFun F (fun w (i : S) => obs E n w i)
      (cond E.P {w | evalSet E n t w = S}) := by
  have hm : Measurable (fun w (i : Fin n) =>
      if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0)) := by
    apply measurable_pi_lambda
    intro i
    split_ifs
    · exact (measurable_pi_apply i).comp (measurable_obs_tuple M E n)
    · exact measurable_const
  have h := training_indep_cond_event E.P (trainSigma_le E n) hm.comap_le
    (evaluation_independent_training M E n hn hIID)
    (evaluation_pattern_measurable_mask E n t S) hpos
  apply (IndepFun_iff_Indep _ _ _).mpr
  exact indep_of_indep_of_le h hF.comap_le
    (evaluation_selected_measurable_mask E n S hS).comap_le

/-- If [the sample size is even](hyp:hn), [sampling is IID](hyp:hIID), [all selected indices are evaluation indices](hyp:hS), [the evaluation pattern has positive probability](hyp:hpos), and [the fitted statistic is training-measurable](hyp:hF), then [its joint conditional law with the selected observations factors into its training law and independent tail laws](goal).

@node: evaluation_pattern_training_selected_law -/
lemma evaluation_pattern_training_selected_law {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (t : ℝ) (S : Finset (Fin n)) (hS : S ⊆ evalIndices n)
    (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A) (hF : Measurable[trainSigma E n] F) :
    (cond E.P {w | evalSet E n t w = S}).map
      (fun w => (F w, fun i : S => obs E n w i)) =
      (E.P.map F).prod (Measure.pi (fun _ : S => obsTailLaw M t)) := by
  have hX : Measurable (fun w (i : S) => obs E n w i) := by
    exact measurable_pi_lambda _ fun i => (measurable_pi_apply (i : Fin n)).comp
      (measurable_obs_tuple M E n)
  have h := evaluation_pattern_training_selected_indep E n hn hIID t S hS hpos F hF
  rw [h.map_prod_eq_prod_map_map (hF.mono (trainSigma_le E n) le_rfl).aemeasurable
      hX.aemeasurable,
    evaluation_pattern_training_map E n hn hIID t S hpos F hF,
    evaluation_selected_tail_law E n hn hIID t S hS hpos]

/-- If [the sample size is even](hyp:hn), [sampling is IID](hyp:hIID), [the noise is regularly varying](hyp:hRV), [all selected indices are evaluation indices](hyp:hS), [the evaluation pattern is non-null](hyp:hpos), and [the fitted statistic is training-measurable](hyp:hF), then [the conditional joint law of that statistic and the enumerated selected observations is the product of its training law and identical tail laws](goal).

@node: evaluation_pattern_training_enumerated_law -/
lemma evaluation_pattern_training_enumerated_law {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A) (hF : Measurable[trainSigma E n] F) :
    (cond E.P {w | evalSet E n t w = S}).map
      (fun w => (F w, fun j : Fin S.card => obs E n w ((S.equivFin).symm j))) =
      (E.P.map F).prod (Measure.pi (fun _ : Fin S.card => obsTailLaw M t)) := by
  letI := obsTailLaw_probability M hRV t
  have hInd := evaluation_pattern_training_selected_indep E n hn hIID t S hS hpos F hF
  have hEnum : Measurable (fun z : S → Obs q d =>
      fun j : Fin S.card => z ((S.equivFin).symm j)) := by fun_prop
  have h := hInd.comp measurable_id hEnum
  have hm : Measurable (fun w (j : Fin S.card) => obs E n w ((S.equivFin).symm j)) := by
    exact measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp
      (measurable_obs_tuple M E n)
  change IndepFun F (fun w (j : Fin S.card) => obs E n w ((S.equivFin).symm j))
    (cond E.P {w | evalSet E n t w = S}) at h
  rw [h.map_prod_eq_prod_map_map (hF.mono (trainSigma_le E n) le_rfl).aemeasurable
      hm.aemeasurable,
    evaluation_pattern_training_map E n hn hIID t S hpos F hF,
    evaluation_enumerated_tail_law E n hn hIID hRV t S hS hpos]

/-- If [the sample size is even](hyp:hn), [sampling is IID](hyp:hIID), [the noise is regularly varying](hyp:hRV), [the selected indices are evaluation indices](hyp:hS), [the evaluation pattern has positive probability](hyp:hpos), [the fitted statistic is training-measurable](hyp:hF), and [the joint event is measurable](hyp:hV), then [the conditional probability of that joint event equals its average over the original training law of the corresponding independent-tail probability](goal).

@node: evaluation_pattern_training_event_integral -/
lemma evaluation_pattern_training_event_integral {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A) (hF : Measurable[trainSigma E n] F)
    (V : Set (A × (Fin S.card → Obs q d))) (hV : MeasurableSet V) :
    (cond E.P {w | evalSet E n t w = S}).real {w |
      (F w, fun j : Fin S.card => obs E n w ((S.equivFin).symm j)) ∈ V} =
      ∫ w, (Measure.pi (fun _ : Fin S.card => obsTailLaw M t)).real
        {z | (F w, z) ∈ V} ∂E.P := by
  letI := obsTailLaw_probability M hRV t
  have hFm := hF.mono (trainSigma_le E n) le_rfl
  have hX : Measurable (fun w (j : Fin S.card) => obs E n w ((S.equivFin).symm j)) := by
    exact measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp
      (measurable_obs_tuple M E n)
  letI : IsProbabilityMeasure (E.P.map F) := Measure.isProbabilityMeasure_map hFm.aemeasurable
  have hsec : Measurable (fun a =>
      (Measure.pi (fun _ : Fin S.card => obsTailLaw M t)) (Prod.mk a ⁻¹' V)) :=
    measurable_measure_prodMk_left hV
  have h := congrArg (fun μ : Measure (A × (Fin S.card → Obs q d)) => (μ V).toReal)
    (evaluation_pattern_training_enumerated_law E n hn hIID hRV t S hS hpos F hF)
  rw [Measure.map_apply (hFm.prodMk hX) hV, Measure.prod_apply hV] at h
  change ((cond E.P {w | evalSet E n t w = S})
    ((fun w => (F w, fun j : Fin S.card => obs E n w ((S.equivFin).symm j))) ⁻¹' V)).toReal = _
  rw [h, ← integral_toReal hsec.aemeasurable
      (Filter.Eventually.of_forall fun a => measure_lt_top _ _),
    integral_map hFm.aemeasurable hsec.ennreal_toReal.aestronglyMeasurable]
  rfl

/-- If [the sample size is even](hyp:hn), [sampling is IID](hyp:hIID), [the noise is regularly varying](hyp:hRV), [the selected indices are evaluation indices](hyp:hS), [the evaluation pattern has positive probability](hyp:hpos), [the fit is training-measurable](hyp:hF), and [the event that the empirical fitted-score mean exceeds its truncation radius is measurable](hyp:hV), then [the conditional failure probability equals the original-training-law average of the IID score failure probability](goal).

@node: evaluation_pattern_trained_truncated_transfer -/
lemma evaluation_pattern_trained_truncated_transfer {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A) (hF : Measurable[trainSigma E n] F)
    (f : A → Obs q d → ℝ) (B : A → ℝ) (delta : ℝ)
    (hV : MeasurableSet {az : A × (Fin S.card → Obs q d) |
      scoreSamplingRadius (obsTailLaw M t) (f az.1) S.card (B az.1) delta <
        |(S.card : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂obsTailLaw M t|}) :
    (cond E.P {w | evalSet E n t w = S}).real {w |
      scoreSamplingRadius (obsTailLaw M t) (f (F w)) S.card (B (F w)) delta <
        |(S.card : ℝ)⁻¹ * ∑ i ∈ S, f (F w) (obs E n w i) -
          ∫ z, f (F w) z ∂obsTailLaw M t|} =
      ∫ w, scoreIidFailure (obsTailLaw M t) (f (F w)) S.card (B (F w)) delta ∂E.P := by
  have hsum (w : E.Om) :
      ∑ j : Fin S.card, f (F w) (obs E n w ((S.equivFin).symm j)) =
        ∑ i ∈ S, f (F w) (obs E n w i) := by
    rw [(S.equivFin).symm.sum_comp (fun i : S => f (F w) (obs E n w i))]
    exact Finset.sum_attach S (fun i => f (F w) (obs E n w i))
  have h := evaluation_pattern_training_event_integral E n hn hIID hRV t S hS hpos F hF _ hV
  simpa only [Set.mem_setOf_eq, hsum, scoreIidFailure] using h

/-- If [the sample size is even](hyp:hn), [sampling is IID](hyp:hIID), [the noise is regularly varying](hyp:hRV), [the selected indices are evaluation indices](hyp:hS), [the evaluation pattern has positive probability](hyp:hpos), [the fit is training-measurable](hyp:hF), and [the event that the empirical fitted-score mean exceeds its variance radius is measurable](hyp:hV), then [the conditional failure probability equals the original-training-law average of the IID variance failure probability](goal).

@node: evaluation_pattern_trained_variance_transfer -/
lemma evaluation_pattern_trained_variance_transfer {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A) (hF : Measurable[trainSigma E n] F)
    (f : A → Obs q d → ℝ) (delta : ℝ)
    (hV : MeasurableSet {az : A × (Fin S.card → Obs q d) |
      Real.sqrt (4 * variance (f az.1) (obsTailLaw M t) / (delta * S.card)) <
        |(S.card : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂obsTailLaw M t|}) :
    (cond E.P {w | evalSet E n t w = S}).real {w |
      Real.sqrt (4 * variance (f (F w)) (obsTailLaw M t) / (delta * S.card)) <
        |(S.card : ℝ)⁻¹ * ∑ i ∈ S, f (F w) (obs E n w i) -
          ∫ z, f (F w) z ∂obsTailLaw M t|} =
      ∫ w, scoreIidVarianceFailure (obsTailLaw M t) (f (F w)) S.card delta ∂E.P := by
  have hsum (w : E.Om) :
      ∑ j : Fin S.card, f (F w) (obs E n w ((S.equivFin).symm j)) =
        ∑ i ∈ S, f (F w) (obs E n w i) := by
    rw [(S.equivFin).symm.sum_comp (fun i : S => f (F w) (obs E n w i))]
    exact Finset.sum_attach S (fun i => f (F w) (obs E n w i))
  have h := evaluation_pattern_training_event_integral E n hn hIID hRV t S hS hpos F hF _ hV
  simpa only [Set.mem_setOf_eq, hsum, scoreIidVarianceFailure] using h

/-- If [the sample size is even](hyp:hn), [sampling is IID](hyp:hIID), [the noise is regularly varying](hyp:hRV), [the selected indices are evaluation indices](hyp:hS), [the evaluation pattern is non-null](hyp:hpos), [at least one index is selected](hyp:hcard), [the fit is training-measurable](hyp:hF), [its score functions are measurable and integrable almost surely](hyp:hf), [its truncation bound is nonnegative almost surely](hyp:hB), [the empirical-score failure event is measurable](hyp:hV), and [the tolerance is positive](hyp:hd), then [the conditional truncated-score failure probability is at most one half of the tolerance](goal).

@node: evaluation_pattern_trained_truncated_failure -/
lemma evaluation_pattern_trained_truncated_failure {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    (hcard : 0 < S.card) {A : Type*} [MeasurableSpace A]
    (F : E.Om → A) (hF : Measurable[trainSigma E n] F)
    (f : A → Obs q d → ℝ) (B : A → ℝ) {delta : ℝ} (hd : 0 < delta)
    (hf : ∀ᵐ w ∂E.P, Measurable (f (F w)) ∧ Integrable (f (F w)) (obsTailLaw M t))
    (hB : ∀ᵐ w ∂E.P, 0 ≤ B (F w))
    (hV : MeasurableSet {az : A × (Fin S.card → Obs q d) |
      scoreSamplingRadius (obsTailLaw M t) (f az.1) S.card (B az.1) delta <
        |(S.card : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂obsTailLaw M t|}) :
    (cond E.P {w | evalSet E n t w = S}).real {w |
      scoreSamplingRadius (obsTailLaw M t) (f (F w)) S.card (B (F w)) delta <
        |(S.card : ℝ)⁻¹ * ∑ i ∈ S, f (F w) (obs E n w i) -
          ∫ z, f (F w) z ∂obsTailLaw M t|} ≤ delta / 2 := by
  letI := obsTailLaw_probability M hRV t
  rw [evaluation_pattern_trained_truncated_transfer E n hn hIID hRV t S hS hpos F hF f B delta hV]
  have hb : ∀ᵐ w ∂E.P,
      ‖scoreIidFailure (obsTailLaw M t) (f (F w)) S.card (B (F w)) delta‖ ≤ delta / 2 := by
    filter_upwards [hf, hB] with w hfw hBw
    have hnonneg : 0 ≤ scoreIidFailure (obsTailLaw M t) (f (F w)) S.card
        (B (F w)) delta := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact score_iid_truncated_failure (obsTailLaw M t) hcard hfw.1 hfw.2 hBw hd
  have h := norm_integral_le_of_norm_le_const hb
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using (le_abs_self _).trans h

/-- If [the sample size is even](hyp:hn), [sampling is IID](hyp:hIID), [the noise is regularly varying](hyp:hRV), [the selected indices are evaluation indices](hyp:hS), [the evaluation pattern is non-null](hyp:hpos), [at least one index is selected](hyp:hcard), [the fit is training-measurable](hyp:hF), [its score function has a finite second moment almost surely](hyp:hf), [the empirical-score variance failure event is measurable](hyp:hV), and [the tolerance is positive](hyp:hd), then [the conditional variance-based failure probability is at most one quarter of the tolerance](goal).

@node: evaluation_pattern_trained_variance_failure -/
lemma evaluation_pattern_trained_variance_failure {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    (hcard : 0 < S.card) {A : Type*} [MeasurableSpace A]
    (F : E.Om → A) (hF : Measurable[trainSigma E n] F)
    (f : A → Obs q d → ℝ) {delta : ℝ} (hd : 0 < delta)
    (hf : ∀ᵐ w ∂E.P, MemLp (f (F w)) 2 (obsTailLaw M t))
    (hV : MeasurableSet {az : A × (Fin S.card → Obs q d) |
      Real.sqrt (4 * variance (f az.1) (obsTailLaw M t) / (delta * S.card)) <
        |(S.card : ℝ)⁻¹ * ∑ j, f az.1 (az.2 j) - ∫ z, f az.1 z ∂obsTailLaw M t|}) :
    (cond E.P {w | evalSet E n t w = S}).real {w |
      Real.sqrt (4 * variance (f (F w)) (obsTailLaw M t) / (delta * S.card)) <
        |(S.card : ℝ)⁻¹ * ∑ i ∈ S, f (F w) (obs E n w i) -
          ∫ z, f (F w) z ∂obsTailLaw M t|} ≤ delta / 4 := by
  letI := obsTailLaw_probability M hRV t
  rw [evaluation_pattern_trained_variance_transfer E n hn hIID hRV t S hS hpos F hF f delta hV]
  have hb : ∀ᵐ w ∂E.P,
      ‖scoreIidVarianceFailure (obsTailLaw M t) (f (F w)) S.card delta‖ ≤ delta / 4 := by
    filter_upwards [hf] with w hfw
    have hnonneg : 0 ≤ scoreIidVarianceFailure (obsTailLaw M t) (f (F w)) S.card
        delta := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact score_iid_variance_failure (obsTailLaw M t) hcard hfw hd
  have h := norm_integral_le_of_norm_le_const hb
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using (le_abs_self _).trans h

end Papers.TbsExtremeEffects
