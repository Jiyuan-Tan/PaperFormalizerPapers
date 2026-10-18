module
public import Papers.TbsExtremeEffects.Helpers.TrainingScore
public import Papers.TbsExtremeEffects.Helpers.Count

/-! Integration of nonnegative evaluation energies with the training fit held fixed. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/-- If [the energy is measurable](hyp:hf), [nonnegative at every pair of inputs](hyp:hpos), [the proposed bound is nonnegative](hyp:hB), [every fixed first-coordinate energy is integrable](hyp:hInt), and [each such energy has expectation at most that bound](hyp:hMean), then [the energy is integrable under the product distribution and its product expectation is at most the bound](goal). -/
-- @node: nonnegative_product_energy_bound
lemma nonnegative_product_energy_bound {A Z : Type*}
    [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure A) (Q : Measure Z) [IsProbabilityMeasure P] [SFinite Q]
    (f : A × Z → ℝ) (hf : Measurable f) (hpos : ∀ a z, 0 ≤ f (a, z))
    {B : ℝ} (hB : 0 ≤ B)
    (hInt : ∀ a, Integrable (fun z => f (a, z)) Q)
    (hMean : ∀ a, (∫ z, f (a, z) ∂Q) ≤ B) :
    Integrable f (P.prod Q) ∧ (∫ az, f az ∂P.prod Q) ≤ B := by
  have hnorm : (fun a => ∫ z, ‖f (a, z)‖ ∂Q) =
      (fun a => ∫ z, f (a, z) ∂Q) := by
    funext a
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => Real.norm_of_nonneg (hpos a z)
  have houter : Integrable (fun a => ∫ z, f (a, z) ∂Q) P := by
    apply Integrable.of_bound
      hf.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable B
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_of_nonneg (integral_nonneg (hpos a))]
      exact hMean a
  have hprod : Integrable f (P.prod Q) :=
    (integrable_prod_iff hf.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hInt, by rwa [hnorm]⟩
  refine ⟨hprod, ?_⟩
  rw [integral_prod f hprod]
  exact (integral_mono houter (integrable_const B) hMean).trans_eq (by simp)

/-- If [the first random quantity is measurable](hyp:hF), [the second is measurable](hyp:hX), [they are independent](hyp:hind), [the energy is measurable](hyp:hf), [nonnegative](hyp:hpos), [the proposed bound is nonnegative](hyp:hB), [every energy conditional on the first quantity is integrable](hyp:hInt), and [each conditional expectation is at most the bound](hyp:hMean), then [the composed energy is integrable and has expectation at most the bound](goal). -/
-- @node: independent_nonnegative_energy_bound
lemma independent_nonnegative_energy_bound {W A Z : Type*}
    [MeasurableSpace W] [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure W) [IsProbabilityMeasure P]
    (F : W → A) (X : W → Z) (hF : Measurable F) (hX : Measurable X)
    (hind : IndepFun F X P) (f : A × Z → ℝ) (hf : Measurable f)
    (hpos : ∀ a z, 0 ≤ f (a, z)) {B : ℝ} (hB : 0 ≤ B)
    (hInt : ∀ a, Integrable (fun z => f (a, z)) (P.map X))
    (hMean : ∀ a, (∫ z, f (a, z) ∂P.map X) ≤ B) :
    Integrable (fun w => f (F w, X w)) P ∧
      (∫ w, f (F w, X w) ∂P) ≤ B := by
  letI : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hlaw := hind.map_prod_eq_prod_map_map hF.aemeasurable hX.aemeasurable
  obtain ⟨hprod, hbound⟩ := nonnegative_product_energy_bound
    (P.map F) (P.map X) f hf hpos hB hInt hMean
  have hmap : Integrable f (P.map (fun w => (F w, X w))) := by
    rwa [hlaw]
  refine ⟨hmap.comp_aemeasurable (hF.prodMk hX).aemeasurable, ?_⟩
  rw [← integral_map (hF.prodMk hX).aemeasurable hf.aestronglyMeasurable, hlaw]
  exact hbound

variable {q d : ℕ} {M : ExtremeModel q d}

/-- If [the sample size is even](hyp:hn), [the sample is independent and identically distributed](hyp:hiid), [the map depends measurably only on the training sample](hyp:hF), and [the selected index is an evaluation index](hyp:hi), then [that map is independent of the selected relabelled evaluation record](goal). -/
-- @node: evaluation_record_indep_training_map
lemma evaluation_record_indep_training_map (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A)
    (hF : Measurable[trainSigma E n] F) (i : Fin n) (hi : i ∈ evalIndices n) :
    IndepFun F (fun w => obs E n w i) E.P := by
  let mask := fun w (j : Fin n) =>
    if n / 2 ≤ j.val then obs E n w j else (0, false, 0, 0)
  let H := MeasurableSpace.comap mask inferInstance
  have hmask : Measurable[H] mask := Measurable.of_comap_le le_rfl
  have heval : Measurable[H] (fun w => obs E n w i) := by
    have hi' : n / 2 ≤ i.val := by simpa [evalIndices] using hi
    simpa only [mask, hi', if_true, Function.comp_def] using
      (measurable_pi_apply i).comp hmask
  apply (IndepFun_iff _ _ _).mpr
  intro S T hS hT
  exact (Indep_iff _ _ _).mp (evaluation_independent_training M E n hn hiid)
    _ _ (hF.comap_le _ hS) (heval.comap_le _ hT)

/-- If [the sample size is even](hyp:hn), [the sample is independent and identically distributed](hyp:hiid), [the fitted quantity is training-measurable](hyp:hF), [the chosen index is an evaluation index](hyp:hi), [the energy is measurable](hyp:hf), [nonnegative](hyp:hpos), [the bound is nonnegative](hyp:hB), [each population energy is integrable](hyp:hInt), and [each population expectation is at most the bound](hyp:hMean), then [the energy evaluated at that record is integrable and has expectation at most the bound](goal). -/
-- @node: evaluation_record_nonnegative_energy_bound
lemma evaluation_record_nonnegative_energy_bound (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A)
    (hF : Measurable[trainSigma E n] F) (i : Fin n) (hi : i ∈ evalIndices n)
    (f : A × Obs q d → ℝ) (hf : Measurable f)
    (hpos : ∀ a z, 0 ≤ f (a, z)) {B : ℝ} (hB : 0 ≤ B)
    (hInt : ∀ a, Integrable (fun z => f (a, z)) (M.mu.map (observation M)))
    (hMean : ∀ a, (∫ z, f (a, z) ∂M.mu.map (observation M)) ≤ B) :
    Integrable (fun w => f (F w, obs E n w i)) E.P ∧
      (∫ w, f (F w, obs E n w i) ∂E.P) ≤ B := by
  have hX : Measurable (fun w => obs E n w i) := by
    fun_prop
  have hlaw := (relabelled_iid M E n hn hiid).2 i
  exact independent_nonnegative_energy_bound E.P F (fun w => obs E n w i)
    (hF.mono (trainSigma_le E n) le_rfl) hX
    (evaluation_record_indep_training_map E n hn hiid F hF i hi)
    f hf hpos hB (by simpa only [hlaw] using hInt) (by simpa only [hlaw] using hMean)

/-- If [the noise is regularly varying](hyp:hRV) and [the function of an observation is integrable under the tail law at the threshold](hyp:hInt), then [its value restricted to observations beyond the threshold is integrable under the original observation law, with expectation equal to the tail probability times its tail-law expectation](goal). -/
-- @node: observation_tail_energy_unnormalize
lemma observation_tail_energy_unnormalize (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (f : Obs q d → ℝ)
    (hInt : Integrable f (obsTailLaw M t)) :
    Integrable (fun z => if t < l1Norm z.2.2.2 then f z else 0)
      (M.mu.map (observation M)) ∧
    (∫ z, (if t < l1Norm z.2.2.2 then f z else 0) ∂M.mu.map (observation M)) =
      tailProb M t * ∫ z, f z ∂obsTailLaw M t := by
  let Q := M.mu.map (observation M)
  let S := {z : Obs q d | t < l1Norm z.2.2.2}
  have hS : MeasurableSet S := by
    first | fun_prop | skip
    exact measurableSet_lt measurable_const (by fun_prop)
  have hobs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk (M.measurable_D.prodMk
      (M.measurable_Y.prodMk M.measurable_U))
  have hmass : Q S = M.mu {w | t < radius M w} :=
    Measure.map_apply hobs hS
  have hreal : (Q S).toReal = tailProb M t := by
    rw [hmass]
    rfl
  have hne : Q S ≠ 0 := by
    intro hz
    have := tailProb_pos_of_regularVariation M hRV t
    rw [← hreal, hz, ENNReal.toReal_zero] at this
    exact (lt_irrefl 0) this
  have hfinite : Q S ≠ ∞ := by
    letI : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hobs.aemeasurable
    exact measure_ne_top Q S
  have hRestrict : Integrable f (Q.restrict S) :=
    (integrable_inv_smul_measure hne hfinite).mp hInt
  have hcond : (∫ z, f z ∂obsTailLaw M t) =
      (Q S).toReal⁻¹ * ∫ z in S, f z ∂Q := by
    rw [obsTailLaw, ProbabilityTheory.cond, integral_smul_measure,
      ENNReal.toReal_inv, smul_eq_mul]
  change Integrable (S.indicator f) Q ∧ (∫ z, S.indicator f z ∂Q) = _
  refine ⟨(integrable_indicator_iff hS).mpr hRestrict, ?_⟩
  rw [integral_indicator hS, hcond, ← hreal, ← mul_assoc,
    mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hne, hfinite⟩), one_mul]

/-- If [the sample size is even](hyp:hn), [the sample is independent and identically distributed](hyp:hiid), [the fitted exponent is training-measurable](hyp:hTraining), [the noise is regularly varying](hyp:hRV), [the training event is measurable](hyp:hG), [the proposed moment bound is nonnegative](hyp:hV0), [each score on that event has a finite tail-law second moment](hyp:hLp), [that second moment is bounded by the proposed value](hyp:hV), and [the index is an evaluation index](hyp:hi), then [the thresholded squared score for that record is integrable and has expectation at most the bound times the tail probability](goal). -/
-- @node: evaluation_score_square_energy_record
lemma evaluation_score_square_energy_record (E : NeteExperiment M)
    (kind : EstimatorKind) (n : ℕ) (t : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    (hTraining : ExponentTraining E n) (hRV : NoiseRegularlyVarying M)
    (G : Set E.Om) (hG : MeasurableSet[trainSigma E n] G)
    {V : ℝ} (hV0 : 0 ≤ V)
    (hLp : ∀ w ∈ G, MemLp (score E kind n w) 2 (obsTailLaw M t))
    (hV : ∀ w ∈ G, scoreSecondMoment E kind n t w ≤ V)
    (i : Fin n) (hi : i ∈ evalIndices n) :
    Integrable (fun w => if t < l1Norm (sampleU E n w i) then
      (if w ∈ G then score E kind n w (obs E n w i) else 0) ^ 2 else 0) E.P ∧
    (∫ w, (if t < l1Norm (sampleU E n w i) then
      (if w ∈ G then score E kind n w (obs E n w i) else 0) ^ 2 else 0) ∂E.P) ≤
      V * tailProb M t := by
  classical
  let f : E.Om × Obs q d → ℝ := fun az =>
    if az.1 ∈ G then
      if t < l1Norm az.2.2.2.2 then score E kind n az.1 az.2 ^ 2 else 0 else 0
  have hf : @Measurable (E.Om × Obs q d) ℝ
      ((trainSigma E n).prod inferInstance) inferInstance f := by
    letI : MeasurableSpace E.Om := trainSigma E n
    have hs := measurable_score_training_joint E kind hTraining
    have hr : Measurable (fun az : E.Om × Obs q d => l1Norm az.2.2.2.2) := by
      fun_prop
    exact ((hs.pow_const 2).ite (measurableSet_lt measurable_const hr)
      measurable_const).ite (measurable_fst hG) measurable_const
  have hInt (w : E.Om) : Integrable (fun z => f (w, z))
      (M.mu.map (observation M)) := by
    by_cases hw : w ∈ G
    · simpa only [f, hw, if_true] using
        (observation_tail_energy_unnormalize M hRV t _ (hLp w hw).integrable_sq).1
    · simp only [f, hw, if_false]
      exact integrable_const 0
  have hMean (w : E.Om) : (∫ z, f (w, z) ∂M.mu.map (observation M)) ≤
      V * tailProb M t := by
    by_cases hw : w ∈ G
    · have h := (observation_tail_energy_unnormalize M hRV t _
        (hLp w hw).integrable_sq).2
      simp only [f, hw, if_true]
      rw [h, mul_comm V]
      exact mul_le_mul_of_nonneg_left (hV w hw) (tailProb_nonneg M t)
    · simp only [f, hw, if_false, integral_zero]
      exact mul_nonneg hV0 (tailProb_nonneg M t)
  have h := @evaluation_record_nonnegative_energy_bound q d M E n hn hiid
    E.Om (trainSigma E n) id measurable_id i hi f hf
    (fun w z => by dsimp [f]; split_ifs <;> positivity)
    (V * tailProb M t) (mul_nonneg hV0 (tailProb_nonneg M t)) hInt hMean
  have heq : (fun w => f (id w, obs E n w i)) =
      (fun w => if t < l1Norm (sampleU E n w i) then
        (if w ∈ G then score E kind n w (obs E n w i) else 0) ^ 2 else 0) := by
    funext w
    by_cases hw : w ∈ G <;> by_cases ht : t < l1Norm (sampleU E n w i) <;>
      simp [f, hw, ht, sampleU]
  rwa [heq] at h

/-- If [the sample size is even](hyp:hn), [the sample is independent and identically distributed](hyp:hiid), [the fitted exponent is training-measurable](hyp:hTraining), [the noise is regularly varying](hyp:hRV), [the training event is measurable](hyp:hG), [the proposed moment bound is nonnegative](hyp:hV0), [each score on that event has a finite tail-law second moment](hyp:hLp), and [that second moment is bounded by the proposed value](hyp:hV), then [the sum of thresholded squared evaluation scores is integrable and its expectation is at most the half-sample moment budget](goal). -/
-- @node: evaluation_score_square_energy
lemma evaluation_score_square_energy (E : NeteExperiment M)
    (kind : EstimatorKind) (n : ℕ) (t : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    (hTraining : ExponentTraining E n) (hRV : NoiseRegularlyVarying M)
    (G : Set E.Om) (hG : MeasurableSet[trainSigma E n] G)
    {V : ℝ} (hV0 : 0 ≤ V)
    (hLp : ∀ w ∈ G, MemLp (score E kind n w) 2 (obsTailLaw M t))
    (hV : ∀ w ∈ G, scoreSecondMoment E kind n t w ≤ V) :
    Integrable (fun w => ∑ i : Fin n, if t < l1Norm (sampleU E n w i) then
      (if w ∈ G ∧ i ∈ evalIndices n then score E kind n w (obs E n w i) else 0) ^ 2
      else 0) E.P ∧
    (∫ w, (∑ i : Fin n, if t < l1Norm (sampleU E n w i) then
      (if w ∈ G ∧ i ∈ evalIndices n then score E kind n w (obs E n w i) else 0) ^ 2
      else 0) ∂E.P) ≤ (n : ℝ) / 2 * V * tailProb M t := by
  classical
  let f := fun (i : Fin n) w => if t < l1Norm (sampleU E n w i) then
    (if w ∈ G then score E kind n w (obs E n w i) else 0) ^ 2 else 0
  have hRecord (i : Fin n) (hi : i ∈ evalIndices n) :
      Integrable (f i) E.P ∧ (∫ w, f i w ∂E.P) ≤ V * tailProb M t :=
    evaluation_score_square_energy_record E kind n t hn hiid hTraining hRV
      G hG hV0 hLp hV i hi
  have heq : (fun w => ∑ i : Fin n, if t < l1Norm (sampleU E n w i) then
      (if w ∈ G ∧ i ∈ evalIndices n then score E kind n w (obs E n w i) else 0) ^ 2
      else 0) = (fun w => ∑ i ∈ evalIndices n, f i w) := by
    funext w
    calc
      _ = ∑ i : Fin n, if i ∈ evalIndices n then f i w else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ evalIndices n <;> by_cases hw : w ∈ G <;>
          by_cases ht : t < l1Norm (sampleU E n w i) <;> simp [f, hi, hw, ht]
      _ = _ := by rw [← Finset.sum_filter]; simp
  rw [heq]
  refine ⟨integrable_finset_sum _ (fun i hi => (hRecord i hi).1), ?_⟩
  rw [integral_finset_sum _ (fun i hi => (hRecord i hi).1)]
  calc
    _ ≤ ∑ _i ∈ evalIndices n, V * tailProb M t :=
      Finset.sum_le_sum (fun i hi => (hRecord i hi).2)
    _ = (n : ℝ) / 2 * V * tailProb M t := by
      rw [Finset.sum_const, (equalSplit_cardinality n hn).2, nsmul_eq_mul]
      obtain ⟨k, hk⟩ := hn.2
      have hdiv : n / 2 = k := by omega
      rw [hdiv, hk]
      push_cast
      ring

end Papers.TbsExtremeEffects
