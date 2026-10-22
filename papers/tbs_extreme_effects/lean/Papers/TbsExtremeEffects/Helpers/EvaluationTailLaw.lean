module
public import Papers.TbsExtremeEffects.Helpers.ScoreSampling
public import Papers.TbsExtremeEffects.Helpers.Split
public import Toolkit.Foundations.Probability.Independence.ProductConditioning

/-! Product laws after conditioning on a fixed evaluation exceedance pattern.
This uses finite rectangles and requires no disintegration of the training law. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

-- @node: sample_map_cond
/-- Given [a measurable sample map](hyp:hX) and [a measurable conditioning set](hyp:hs), [mapping the sample conditioned on that set equals conditioning its mapped law on the same set](goal). -/
lemma sample_map_cond {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (P : Measure W) (X : W → Z) (hX : Measurable X)
    (s : Set Z) (hs : MeasurableSet s) :
    (cond P (X ⁻¹' s)).map X = cond (P.map X) s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul, ← Measure.restrict_map hX hs,
    Measure.map_apply hX hs]

-- @node: sample_conditioned_rectangle_law
/-- Given [a measurable sample vector](hyp:hX), [its product-law representation](hyp:hlaw), [measurable coordinate conditioning sets](hyp:hs), and [positive probability for every coordinate condition](hyp:hpos), [conditioning the original sample on the rectangle and then mapping it gives the product of coordinatewise conditional laws](goal). -/
lemma sample_conditioned_rectangle_law {W I Z : Type*} [MeasurableSpace W]
    [Fintype I] [MeasurableSpace Z] (P : Measure W) (X : W → I → Z)
    (hX : Measurable X) (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)]
    (hlaw : P.map X = Measure.pi μ) (s : I → Set Z)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : ∀ i, μ i (s i) ≠ 0) :
    (cond P {w | ∀ i, X w i ∈ s i}).map X =
      Measure.pi (fun i => cond (μ i) (s i)) := by
  have hevent : {w | ∀ i, X w i ∈ s i} = X ⁻¹' (Set.univ.pi s) := by
    ext w
    simp
  rw [hevent, sample_map_cond P X hX _ (MeasurableSet.univ_pi hs), hlaw]
  exact Toolkit.Foundations.Probability.Independence.cond_pi_univ_pi μ s hs hpos

-- @node: sample_rectangle_factors_nonzero
/-- Given [a measurable sample vector](hyp:hX), [its product-law representation](hyp:hlaw), [measurable coordinate conditioning sets](hyp:hs), and [a positive-probability conditioning rectangle](hyp:hpos), [every coordinate conditioning set has positive probability](goal). -/
lemma sample_rectangle_factors_nonzero {W I Z : Type*} [MeasurableSpace W]
    [Fintype I] [MeasurableSpace Z] (P : Measure W) (X : W → I → Z)
    (hX : Measurable X) (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)]
    (hlaw : P.map X = Measure.pi μ) (s : I → Set Z)
    (hs : ∀ i, MeasurableSet (s i))
    (hpos : P {w | ∀ i, X w i ∈ s i} ≠ 0) : ∀ i, μ i (s i) ≠ 0 := by
  have hevent : {w | ∀ i, X w i ∈ s i} = X ⁻¹' (Set.univ.pi s) := by
    ext w
    simp
  rw [hevent, ← Measure.map_apply hX (MeasurableSet.univ_pi hs), hlaw,
    Measure.pi_pi] at hpos
  exact fun i => Finset.prod_ne_zero_iff.mp hpos i (Finset.mem_univ i)

-- @node: sample_pi_subtype_law
/-- [Selecting the coordinates indexed by the finite set](hyp:S) from [a product law](hyp:μ) yields [the product of exactly those coordinate laws](goal). -/
lemma sample_pi_subtype_law {I Z : Type*} [Fintype I] [MeasurableSpace Z]
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)] (S : Finset I) :
    (Measure.pi μ).map (fun z (i : S) => z i) = Measure.pi (fun i : S => μ i) := by
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ (fun i => i ∈ S)
  have h := measurePreserving_fst.comp hsplit
  convert h.map_eq using 1
  · congr 1
  · congr 1
    exact Subsingleton.elim _ _

-- @node: sample_conditioned_selected_law
/-- Given [a measurable sample vector](hyp:hX), [its product-law representation](hyp:hlaw), [measurable coordinate conditioning sets](hyp:hs), [a positive-probability conditioning rectangle](hyp:hpos), and [a finite selection of coordinates](hyp:S), [the selected coordinates under the conditioned sample have the product of their coordinatewise conditional laws](goal). -/
lemma sample_conditioned_selected_law {W I Z : Type*} [MeasurableSpace W]
    [Fintype I] [MeasurableSpace Z] (P : Measure W) (X : W → I → Z)
    (hX : Measurable X) (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)]
    (hlaw : P.map X = Measure.pi μ) (s : I → Set Z)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : P {w | ∀ i, X w i ∈ s i} ≠ 0)
    (S : Finset I) :
    (cond P {w | ∀ i, X w i ∈ s i}).map (fun w (i : S) => X w i) =
      Measure.pi (fun i : S => cond (μ i) (s i)) := by
  have hfactors := sample_rectangle_factors_nonzero P X hX μ hlaw s hs hpos
  letI (i : I) : IsProbabilityMeasure (cond (μ i) (s i)) :=
    cond_isProbabilityMeasure (hfactors i)
  change (cond P {w | ∀ i, X w i ∈ s i}).map
    ((fun z (i : S) => z i) ∘ X) = _
  rw [← Measure.map_map (by fun_prop : Measurable (fun z (i : S) => z i)) hX,
    sample_conditioned_rectangle_law P X hX μ hlaw s hs hfactors]
  exact sample_pi_subtype_law _ S

-- @node: evaluation_pattern_rectangle
/-- If [the proposed pattern uses only evaluation indices](hyp:hS), then [having exactly that evaluation pattern is equivalent to each observation lying in its corresponding exceedance, non-exceedance, or unrestricted coordinate set](goal). -/
lemma evaluation_pattern_rectangle {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) :
    {w | evalSet E n t w = S} =
      {w | ∀ i : Fin n, obs E n w i ∈
        if i ∈ S then {z : Obs q d | t < l1Norm z.2.2.2}
        else if i ∈ evalIndices n then {z : Obs q d | t < l1Norm z.2.2.2}ᶜ
        else Set.univ} := by
  ext w
  constructor
  · intro hw i
    by_cases hi : i ∈ S
    · have hmem : i ∈ evalSet E n t w := hw.symm ▸ hi
      simpa [hi, evalSet, sampleU] using (Finset.mem_filter.mp hmem).2
    · by_cases he : i ∈ evalIndices n
      · have hnot : ¬ t < l1Norm (sampleU E n w i) := by
          intro hr
          exact hi (hw ▸ Finset.mem_filter.mpr ⟨he, hr⟩)
        simpa [hi, he, sampleU] using hnot
      · simp [hi, he]
  · intro hw
    apply Finset.ext
    intro i
    constructor
    · intro hi
      obtain ⟨he, hr⟩ := Finset.mem_filter.mp hi
      by_contra hn
      have hh := hw i
      simp only [hn, he, ↓reduceIte, Set.mem_compl_iff, Set.mem_setOf_eq] at hh
      exact hh hr
    · intro hi
      have hh := hw i
      simp only [hi, ↓reduceIte, Set.mem_setOf_eq] at hh
      exact Finset.mem_filter.mpr ⟨hS hi, hh⟩

-- @node: evaluation_pattern_conditional_law
/-- If [the sample size is even](hyp:hn), [the observations are iid](hyp:hIID), [the proposed pattern uses only evaluation indices](hyp:hS), and [every coordinate condition has positive probability](hyp:hpos), then [the full observation vector conditioned on that pattern has the product of the corresponding coordinatewise conditional laws](goal). -/
lemma evaluation_pattern_conditional_law {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (t : ℝ) (S : Finset (Fin n)) (hS : S ⊆ evalIndices n)
    (hpos : ∀ i : Fin n, (M.mu.map (observation M))
      (if i ∈ S then {z : Obs q d | t < l1Norm z.2.2.2}
       else if i ∈ evalIndices n then {z : Obs q d | t < l1Norm z.2.2.2}ᶜ
       else Set.univ) ≠ 0) :
    (cond E.P {w | evalSet E n t w = S}).map (fun w => obs E n w) =
      Measure.pi (fun i : Fin n => cond (M.mu.map (observation M))
        (if i ∈ S then {z : Obs q d | t < l1Norm z.2.2.2}
         else if i ∈ evalIndices n then {z : Obs q d | t < l1Norm z.2.2.2}ᶜ
         else Set.univ)) := by
  have hobs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  letI : IsProbabilityMeasure (M.mu.map (observation M)) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  rw [evaluation_pattern_rectangle E n t S hS]
  apply sample_conditioned_rectangle_law E.P (fun w => obs E n w)
    (measurable_obs_tuple M E n) (fun _ => M.mu.map (observation M))
    (relabelled_joint_law M E n hn hIID) _ _ hpos
  intro i
  split_ifs
  · first | fun_prop | skip
    exact measurableSet_lt measurable_const ((by unfold l1Norm; fun_prop))
  · exact (measurableSet_lt measurable_const ((by unfold l1Norm; fun_prop))).compl
  · exact MeasurableSet.univ

-- @node: evaluation_selected_tail_law
/-- If [the sample size is even](hyp:hn), [the observations are iid](hyp:hIID), [the proposed pattern uses only evaluation indices](hyp:hS), and [the pattern has positive probability](hyp:hpos), then [the selected observations conditioned on that pattern are independent draws from the tail law](goal). -/
lemma evaluation_selected_tail_law {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (t : ℝ) (S : Finset (Fin n)) (hS : S ⊆ evalIndices n)
    (hpos : E.P {w | evalSet E n t w = S} ≠ 0) :
    (cond E.P {w | evalSet E n t w = S}).map (fun w (i : S) => obs E n w i) =
      Measure.pi (fun _ : S => obsTailLaw M t) := by
  have hobs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  letI : IsProbabilityMeasure (M.mu.map (observation M)) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  rw [evaluation_pattern_rectangle E n t S hS] at hpos ⊢
  have h := sample_conditioned_selected_law E.P (fun w => obs E n w)
    (measurable_obs_tuple M E n) (fun _ => M.mu.map (observation M))
    (relabelled_joint_law M E n hn hIID)
    (fun i => if i ∈ S then {z : Obs q d | t < l1Norm z.2.2.2}
      else if i ∈ evalIndices n then {z : Obs q d | t < l1Norm z.2.2.2}ᶜ
      else Set.univ) (by
        intro i
        split_ifs
        · exact measurableSet_lt measurable_const (by unfold l1Norm; fun_prop)
        · exact (measurableSet_lt measurable_const (by unfold l1Norm; fun_prop)).compl
        · exact MeasurableSet.univ) hpos S
  convert h using 1
  congr 1
  funext i
  simp only [i.property, ↓reduceIte, obsTailLaw]

-- @node: evaluation_enumerated_tail_law
/-- If [the sample size is even](hyp:hn), [the observations are iid](hyp:hIID), [noise is regularly varying](hyp:hRV), [the proposed pattern uses only evaluation indices](hyp:hS), and [the pattern has positive probability](hyp:hpos), then [the enumerated selected observations conditioned on that pattern have the product tail law](goal). -/
lemma evaluation_enumerated_tail_law {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0) :
    (cond E.P {w | evalSet E n t w = S}).map
      (fun w (j : Fin S.card) => obs E n w ((S.equivFin).symm j)) =
      Measure.pi (fun _ : Fin S.card => obsTailLaw M t) := by
  letI := obsTailLaw_probability M hRV t
  have h := (measurePreserving_piCongrLeft
    (fun _ : Fin S.card => obsTailLaw M t) S.equivFin).map_eq
  have hm : Measurable (fun w (i : S) => obs E n w i) := by
    exact measurable_pi_lambda _ (fun i => (measurable_pi_apply (i : Fin n)).comp
      (measurable_obs_tuple M E n))
  rw [← evaluation_selected_tail_law E n hn hIID t S hS hpos,
    Measure.map_map (MeasurableEquiv.measurable _) hm] at h
  convert h using 1
  congr 1
  funext w j
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

-- @node: evaluation_pattern_truncated_failure
/-- If [the sample size is even](hyp:hn), [the observations are iid](hyp:hIID), [noise is regularly varying](hyp:hRV), [the proposed pattern uses only evaluation indices](hyp:hS), [the pattern has positive probability](hyp:hpos), [it contains observations](hyp:hcard), [the score is measurable](hyp:hf), [the score is integrable under the tail law](hyp:hInt), [the truncation level is nonnegative](hyp:hB), and [the confidence level is positive](hyp:hd), then [conditional on that pattern, exceeding the truncated sampling radius has probability at most `delta / 2`](goal). -/
lemma evaluation_pattern_truncated_failure {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    (hcard : 0 < S.card) (f : Obs q d → ℝ) (hf : Measurable f)
    (hInt : Integrable f (obsTailLaw M t)) {B delta : ℝ} (hB : 0 ≤ B) (hd : 0 < delta) :
    (cond E.P {w | evalSet E n t w = S}).real {w |
      scoreSamplingRadius (obsTailLaw M t) f S.card B delta <
        |(S.card : ℝ)⁻¹ * ∑ i ∈ S, f (obs E n w i) - ∫ z, f z ∂obsTailLaw M t|}
      ≤ delta / 2 := by
  letI := obsTailLaw_probability M hRV t
  let X := fun w (j : Fin S.card) => obs E n w ((S.equivFin).symm j)
  have hX : Measurable X := by
    exact measurable_pi_lambda _ (fun j => (measurable_pi_apply _).comp
      (measurable_obs_tuple M E n))
  have hlaw := evaluation_enumerated_tail_law E n hn hIID hRV t S hS hpos
  have hsum (w : E.Om) : ∑ j, f (X w j) = ∑ i ∈ S, f (obs E n w i) := by
    rw [show (∑ j, f (X w j)) = ∑ i : S, f (obs E n w i) from
      (S.equivFin).symm.sum_comp (fun i : S => f (obs E n w i))]
    exact Finset.sum_attach S (fun i => f (obs E n w i))
  have hmeas : MeasurableSet {z : Fin S.card → Obs q d |
      scoreSamplingRadius (obsTailLaw M t) f S.card B delta <
        |(S.card : ℝ)⁻¹ * ∑ i, f (z i) - ∫ z, f z ∂obsTailLaw M t|} := by
    first | fun_prop | skip
    exact measurableSet_lt measurable_const (by fun_prop)
  have hprob := score_iid_truncated_failure (obsTailLaw M t) hcard hf hInt hB hd
  change (Measure.pi (fun _ : Fin S.card => obsTailLaw M t)).real {z |
    scoreSamplingRadius (obsTailLaw M t) f S.card B delta <
      |(S.card : ℝ)⁻¹ * ∑ i, f (z i) - ∫ z, f z ∂obsTailLaw M t|} ≤ _ at hprob
  rw [← hlaw, Measure.real, Measure.map_apply hX hmeas] at hprob
  simpa only [Measure.real, Set.preimage_setOf_eq, hsum] using hprob

-- @node: evaluation_pattern_variance_failure
/-- If [the sample size is even](hyp:hn), [the observations are iid](hyp:hIID), [noise is regularly varying](hyp:hRV), [the proposed pattern uses only evaluation indices](hyp:hS), [the pattern has positive probability](hyp:hpos), [it contains observations](hyp:hcard), [the score is measurable](hyp:hf), [the score has finite second moment under the tail law](hyp:hInt), and [the confidence level is positive](hyp:hd), then [conditional on that pattern, exceeding the variance sampling radius has probability at most `delta / 4`](goal). -/
lemma evaluation_pattern_variance_failure {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (S : Finset (Fin n))
    (hS : S ⊆ evalIndices n) (hpos : E.P {w | evalSet E n t w = S} ≠ 0)
    (hcard : 0 < S.card) (f : Obs q d → ℝ) (hf : Measurable f)
    (hInt : MemLp f 2 (obsTailLaw M t)) {delta : ℝ} (hd : 0 < delta) :
    (cond E.P {w | evalSet E n t w = S}).real {w |
      Real.sqrt (4 * variance f (obsTailLaw M t) / (delta * S.card)) <
        |(S.card : ℝ)⁻¹ * ∑ i ∈ S, f (obs E n w i) - ∫ z, f z ∂obsTailLaw M t|}
      ≤ delta / 4 := by
  letI := obsTailLaw_probability M hRV t
  let X := fun w (j : Fin S.card) => obs E n w ((S.equivFin).symm j)
  have hX : Measurable X := by
    exact measurable_pi_lambda _ (fun j => (measurable_pi_apply _).comp
      (measurable_obs_tuple M E n))
  have hlaw := evaluation_enumerated_tail_law E n hn hIID hRV t S hS hpos
  have hsum (w : E.Om) : ∑ j, f (X w j) = ∑ i ∈ S, f (obs E n w i) := by
    rw [show (∑ j, f (X w j)) = ∑ i : S, f (obs E n w i) from
      (S.equivFin).symm.sum_comp (fun i : S => f (obs E n w i))]
    exact Finset.sum_attach S (fun i => f (obs E n w i))
  have hmeas : MeasurableSet {z : Fin S.card → Obs q d |
      Real.sqrt (4 * variance f (obsTailLaw M t) / (delta * S.card)) <
        |(S.card : ℝ)⁻¹ * ∑ i, f (z i) - ∫ z, f z ∂obsTailLaw M t|} := by
    first | fun_prop | skip
    exact measurableSet_lt measurable_const (by fun_prop)
  have hprob := score_iid_variance_failure (obsTailLaw M t) hcard hInt hd
  rw [← hlaw, Measure.real, Measure.map_apply hX hmeas] at hprob
  simpa only [Measure.real, Set.preimage_setOf_eq, hsum] using hprob

end Papers.TbsExtremeEffects
