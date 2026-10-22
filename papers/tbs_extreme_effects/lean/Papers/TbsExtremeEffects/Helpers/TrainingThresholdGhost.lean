module
public import Papers.TbsExtremeEffects.Helpers.ThresholdGhost
public import Papers.TbsExtremeEffects.Helpers.ScoreEnergy

/-! Squared threshold symmetrization with a measurable training parameter.
The training law is integrated only after the frozen-score comparison; no
conditional distribution or disintegration of the training information is used. -/

@[expose] public section
noncomputable section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped BigOperators
open Causalean.Stat.EmpiricalProcess.Countable


-- @node: measurable_training_thresholdGhostSquareMax
/-- If [the threshold score is measurable](hyp:hR) and [the parameter-dependent score is measurable](hyp:hf), then [the squared ghost maximum, evaluated with a common training parameter, is measurable](goal). -/
@[fun_prop]
lemma measurable_training_thresholdGhostSquareMax {A Z : Type*}
    [MeasurableSpace A] [MeasurableSpace Z] {n : ℕ}
    (R : Z → ℝ) (f : A × Z → ℝ) (ell : ℝ)
    (hR : Measurable R) (hf : Measurable f) :
    Measurable (fun p : A × ((Fin n → Z) × (Fin n → Z)) =>
      thresholdGhostSquareMax R (fun z => f (p.1, z)) ell p.2) := by
  let T : A × ((Fin n → Z) × (Fin n → Z)) →
      (Fin n → A × Z) × (Fin n → A × Z) :=
    fun p => ((fun i => (p.1, p.2.1 i)), (fun i => (p.1, p.2.2 i)))
  have hT : Measurable T := by fun_prop
  have hr : Measurable (R ∘ Prod.snd : A × Z → ℝ) := by fun_prop
  have h := (measurable_thresholdGhostSquareMax (n := n) (R ∘ Prod.snd) f ell hr hf).comp hT
  exact h

-- @node: trainingThresholdGhostEnvelope
/-- [The training threshold ghost envelope](goal) averages the squared ghost maximum over an independent sample from [the observation law](hyp:μ), using [the threshold score](hyp:R), [the parameter-dependent score](hyp:f), [the lower threshold endpoint](hyp:ell), and [the training parameter together with its sample](hyp:p). -/
def trainingThresholdGhostEnvelope {A Z : Type*} [MeasurableSpace Z]
    {n : ℕ} (μ : Measure Z) (R : Z → ℝ) (f : A × Z → ℝ) (ell : ℝ)
    (p : A × (Fin n → Z)) : ℝ :=
  ∫ y : Fin n → Z,
    thresholdGhostSquareMax R (fun z => f (p.1, z)) ell (p.2, y)
    ∂Measure.pi (fun _ : Fin n => μ)

-- @node: measurable_trainingThresholdGhostEnvelope
/-- If [the threshold score is measurable](hyp:hR) and [the parameter-dependent score is measurable](hyp:hf), then [the training threshold ghost envelope is measurable](goal). -/
@[fun_prop]
lemma measurable_trainingThresholdGhostEnvelope {A Z : Type*}
    [MeasurableSpace A] [MeasurableSpace Z] {n : ℕ}
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (R : Z → ℝ) (f : A × Z → ℝ) (ell : ℝ)
    (hR : Measurable R) (hf : Measurable f) :
    Measurable (trainingThresholdGhostEnvelope (n := n) μ R f ell) := by
  have hG : Measurable (fun p : (A × (Fin n → Z)) × (Fin n → Z) =>
      thresholdGhostSquareMax R (fun z => f (p.1.1, z)) ell (p.1.2, p.2)) := by
    have hT : Measurable (fun p : (A × (Fin n → Z)) × (Fin n → Z) =>
        (p.1.1, (p.1.2, p.2))) := by fun_prop
    have h := (measurable_training_thresholdGhostSquareMax (n := n) R f ell hR hf).comp hT
    exact h
  exact hG.stronglyMeasurable.integral_prod_right'.measurable

-- @node: trainingThresholdGhostEnvelope_nonneg
/-- [The training threshold ghost envelope](goal) is nonnegative for every [observation law](hyp:μ), [threshold score](hyp:R), [parameter-dependent score](hyp:f), [lower endpoint](hyp:ell), and [training parameter and sample](hyp:p). -/
lemma trainingThresholdGhostEnvelope_nonneg {A Z : Type*} [MeasurableSpace Z]
    {n : ℕ} (μ : Measure Z) (R : Z → ℝ) (f : A × Z → ℝ) (ell : ℝ)
    (p : A × (Fin n → Z)) :
    0 ≤ trainingThresholdGhostEnvelope μ R f ell p :=
  integral_nonneg (fun y => thresholdGhostSquareMax_nonneg R _ ell (p.2, y))

/-- If [the threshold score is measurable](hyp:hR), [the parameter-dependent score is measurable](hyp:hf), [every thresholded score is integrable](hyp:hMark), and [the thresholded squared empirical energy is integrable](hyp:hEnergy), then [the training ghost envelope is integrable, has expectation at most four times the signed ghost average, and almost surely uniformly bounds every centered threshold sum squared](goal).

The same measurable envelope works for all training parameters, including parameters in null sets. Its domination assertion uses the appropriate almost-everywhere fibers. -/
-- @node: training_threshold_square_symmetrization
lemma training_threshold_square_symmetrization {A Z : Type*}
    [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure A) [IsProbabilityMeasure P]
    (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (R : Z → ℝ) (f : A × Z → ℝ) (ell : ℝ)
    (hR : Measurable R) (hf : Measurable f)
    (hMark : ∀ a, ∀ t ≥ ell, Integrable (fun z => if t < R z then f (a, z) else 0) μ)
    (hEnergy : Integrable (fun p : A × (Fin n → Z) =>
      ∑ i : Fin n, if ell < R (p.2 i) then f (p.1, p.2 i) ^ 2 else 0)
      (P.prod (Measure.pi (fun _ : Fin n => μ)))) :
    Integrable (trainingThresholdGhostEnvelope (n := n) μ R f ell)
        (P.prod (Measure.pi (fun _ : Fin n => μ))) ∧
    (∫ p, trainingThresholdGhostEnvelope (n := n) μ R f ell p
        ∂P.prod (Measure.pi (fun _ : Fin n => μ))) ≤
      4 * ∫ p : A × (Fin n → Z),
        signAverage (thresholdSignedSquareMax (R ∘ p.2) (fun i => f (p.1, p.2 i)) ell)
        ∂P.prod (Measure.pi (fun _ : Fin n => μ)) ∧
    ∀ᵐ a ∂P, ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ t ≥ ell,
      ((∑ i : Fin n, if t < R (x i) then f (a, x i) else 0) -
        (n : ℝ) * ∫ z, (if t < R z then f (a, z) else 0) ∂μ) ^ 2 ≤
          trainingThresholdGhostEnvelope μ R f ell (a, x) := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  let H := trainingThresholdGhostEnvelope (n := n) μ R f ell
  let S : A × (Fin n → Z) → ℝ := fun p =>
    signAverage (thresholdSignedSquareMax (R ∘ p.2) (fun i => f (p.1, p.2 i)) ell)
  have hHmeas : Measurable H :=
    measurable_trainingThresholdGhostEnvelope μ R f ell hR hf
  have hSmeas : Measurable S := by
    unfold S signAverage
    apply Measurable.div_const
    apply Finset.measurable_fun_sum
    intro s _
    exact measurable_thresholdSignedSquareMax
      (fun p : A × (Fin n → Z) => R ∘ p.2)
      (fun p i => f (p.1, p.2 i)) ell s
      (fun i => by fun_prop) (fun i => by fun_prop)
  have hSint : Integrable S (P.prod ν) :=
    (integral_thresholdSignedSquareMax_le_energy (P.prod ν)
      (fun p => R ∘ p.2) (fun p i => f (p.1, p.2 i)) ell
      hSmeas.aestronglyMeasurable hEnergy).1
  have hS0 (p) : 0 ≤ S p := signAverage_nonneg _
    (thresholdSignedSquareMax_properties _ _ ell).1
  have hFibers : ∀ᵐ a ∂P,
      Integrable (fun x => H (a, x)) ν ∧
      (∫ x, H (a, x) ∂ν) ≤ 4 * ∫ x, S (a, x) ∂ν ∧
      ∀ᵐ x ∂ν, ∀ t ≥ ell,
        ((∑ i : Fin n, if t < R (x i) then f (a, x i) else 0) -
          (n : ℝ) * ∫ z, (if t < R z then f (a, z) else 0) ∂μ) ^ 2 ≤ H (a, x) := by
    filter_upwards [hEnergy.prod_right_ae] with a ha
    obtain ⟨hGint, hGbound⟩ := threshold_ghost_square_comparison_of_energy
      μ R (fun z => f (a, z)) ell hR (hf.comp (measurable_const.prodMk measurable_id)) ha
    refine ⟨hGint.integral_prod_left, ?_, ?_⟩
    · dsimp only [H, trainingThresholdGhostEnvelope, S, ν]
      rw [← integral_prod _ hGint]
      exact hGbound
    · filter_upwards [hGint.prod_right_ae] with x hx
      intro t ht
      exact threshold_centered_square_le_ghost μ R (fun z => f (a, z)) ell t ht x
        (hMark a t ht) hx
  have hOuter : Integrable (fun a => ∫ x, ‖H (a, x)‖ ∂ν) P := by
    apply (hSint.integral_prod_left.const_mul 4).mono'
      hHmeas.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hFibers] with a ha
    rw [integral_congr_ae (Filter.Eventually.of_forall
      (fun x => Real.norm_of_nonneg (trainingThresholdGhostEnvelope_nonneg μ R f ell (a, x))))]
    rw [Real.norm_of_nonneg (integral_nonneg (fun x =>
      trainingThresholdGhostEnvelope_nonneg μ R f ell (a, x)))]
    exact ha.2.1
  have hHint : Integrable H (P.prod ν) :=
    (integrable_prod_iff hHmeas.aestronglyMeasurable).mpr
      ⟨hFibers.mono (fun _ ha => ha.1), hOuter⟩
  refine ⟨hHint, ?_, hFibers.mono (fun _ ha => ha.2.2)⟩
  rw [integral_prod H hHint, integral_prod S hSint, ← integral_const_mul]
  exact integral_mono_ae hHint.integral_prod_left
    (hSint.integral_prod_left.const_mul 4) (hFibers.mono (fun _ ha => ha.2.1))

/-- If [the threshold score is measurable](hyp:hR), [the parameter-dependent score is measurable](hyp:hf), and [the score clipped above the lower endpoint is integrable for each training parameter](hyp:hMark), then [the event that the envelope uniformly bounds all centered threshold sums is measurable](goal).

Clipping at the lower endpoint leaves every threshold in the band unchanged. -/
-- @node: measurableSet_training_threshold_ghost_domination
lemma measurableSet_training_threshold_ghost_domination {A Z : Type*}
    [MeasurableSpace A] [MeasurableSpace Z] {n : ℕ}
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (R : Z → ℝ) (f : A × Z → ℝ) (ell : ℝ)
    (hR : Measurable R) (hf : Measurable f)
    (hMark : ∀ a, Integrable (fun z => if ell < R z then f (a, z) else 0) μ) :
    MeasurableSet {p : A × (Fin n → Z) | ∀ t ≥ ell,
      ((∑ i : Fin n, if t < R (p.2 i) then f (p.1, p.2 i) else 0) -
        (n : ℝ) * ∫ z, (if t < R z then f (p.1, z) else 0) ∂μ) ^ 2 ≤
          trainingThresholdGhostEnvelope μ R f ell p} := by
  let g : (A × (Fin n → Z)) → Z → ℝ :=
    fun p z => if ell < R z then f (p.1, z) else 0
  have hg : Measurable (Function.uncurry g) := by
    first | fun_prop | skip
    exact Measurable.ite (measurableSet_lt measurable_const (hR.comp measurable_snd))
      (hf.comp (measurable_fst.fst.prodMk measurable_snd)) measurable_const
  have hclip (a : A) (t : ℝ) (ht : ell ≤ t) (z : Z) :
      (if t < R z then (if ell < R z then f (a, z) else 0) else 0) =
        (if t < R z then f (a, z) else 0) := by
    by_cases hz : t < R z
    · simp only [hz, ht.trans_lt hz, if_true]
    · simp only [hz, if_false]
  have hEvent := measurableSet_centered_strict_threshold_uniform_event μ R hR g hg
    (fun i (p : A × (Fin n → Z)) => p.2 i) (fun i => by fun_prop)
    (Set.Ici ell) Set.univ MeasurableSet.univ (fun p _ => hMark p.1)
    (fun p => Real.sqrt (trainingThresholdGhostEnvelope μ R f ell p))
    (by fun_prop)
  convert hEvent using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, Set.mem_Ici]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  simp only [g, hclip p.1 t ht]
  rw [← sq_abs ((∑ i : Fin n, if t < R (p.2 i) then f (p.1, p.2 i) else 0) -
    (n : ℝ) * ∫ z, (if t < R z then f (p.1, z) else 0) ∂μ)]
  apply Iff.symm
  exact Real.le_sqrt (abs_nonneg _) (trainingThresholdGhostEnvelope_nonneg μ R f ell p)

/-- If [the training map is measurable](hyp:hF), [the evaluation sample map is measurable](hyp:hX), [their joint law factors into the training law and independent observations](hyp:hlaw), [the threshold score is measurable](hyp:hR), [the parameter-dependent score is measurable](hyp:hf), [every thresholded score is integrable](hyp:hMark), and [the original thresholded squared energy is integrable](hyp:hEnergy), then [there is a nonnegative integrable envelope whose expectation is bounded by sixteen times that energy and which almost surely dominates every centered threshold sum squared](goal).

The energy is supplied on the original experiment, rather than assumed on a new conditional probability space. -/
-- @node: training_threshold_square_symmetrization_of_joint_law
lemma training_threshold_square_symmetrization_of_joint_law {W A Z : Type*}
    [MeasurableSpace W] [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure W) [IsProbabilityMeasure P]
    (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (F : W → A) (X : W → Fin n → Z) (hF : Measurable F) (hX : Measurable X)
    (hlaw : P.map (fun w => (F w, X w)) =
      (P.map F).prod (Measure.pi (fun _ : Fin n => μ)))
    (R : Z → ℝ) (f : A × Z → ℝ) (ell : ℝ)
    (hR : Measurable R) (hf : Measurable f)
    (hMark : ∀ a, ∀ t ≥ ell, Integrable (fun z => if t < R z then f (a, z) else 0) μ)
    (hEnergy : Integrable (fun w =>
      ∑ i : Fin n, if ell < R (X w i) then f (F w, X w i) ^ 2 else 0) P) :
    ∃ H : W → ℝ, Measurable H ∧ Integrable H P ∧ (∀ w, 0 ≤ H w) ∧
      (∫ w, H w ∂P) ≤ 16 * ∫ w,
        (∑ i : Fin n, if ell < R (X w i) then f (F w, X w i) ^ 2 else 0) ∂P ∧
      ∀ᵐ w ∂P, ∀ t ≥ ell,
        ((∑ i : Fin n, if t < R (X w i) then f (F w, X w i) else 0) -
          (n : ℝ) * ∫ z, (if t < R z then f (F w, z) else 0) ∂μ) ^ 2 ≤ H w := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  let e : A × (Fin n → Z) → ℝ := fun p =>
    ∑ i : Fin n, if ell < R (p.2 i) then f (p.1, p.2 i) ^ 2 else 0
  have he : Measurable e := by
    first | fun_prop | skip
    apply Finset.measurable_fun_sum
    intro i _
    exact Measurable.ite (measurableSet_lt measurable_const
      (hR.comp ((measurable_pi_apply i).comp measurable_snd)))
      ((hf.comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp measurable_snd))).pow_const 2) measurable_const
  have hpair : Measurable (fun w => (F w, X w)) := hF.prodMk hX
  have hEprod : Integrable e ((P.map F).prod ν) := by
    rw [← hlaw]
    exact (integrable_map_measure he.aestronglyMeasurable hpair.aemeasurable).mpr hEnergy
  letI : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  obtain ⟨hInt, hBound, hDom⟩ := training_threshold_square_symmetrization
    (P.map F) μ R f ell hR hf hMark hEprod
  let H := trainingThresholdGhostEnvelope (n := n) μ R f ell
  have hH : Measurable H := measurable_trainingThresholdGhostEnvelope μ R f ell hR hf
  have hOriginal : Integrable (fun w => H (F w, X w)) P := by
    have hm : Integrable H (P.map (fun w => (F w, X w))) := by rwa [hlaw]
    exact hm.comp_aemeasurable hpair.aemeasurable
  refine ⟨fun w => H (F w, X w), hH.comp hpair, hOriginal,
    fun w => trainingThresholdGhostEnvelope_nonneg μ R f ell _, ?_, ?_⟩
  · have hSigned := integral_thresholdSignedSquareMax_le_energy ((P.map F).prod ν)
      (fun p => R ∘ p.2) (fun p i => f (p.1, p.2 i)) ell
      (by
        apply Measurable.aestronglyMeasurable
        unfold signAverage
        apply Measurable.div_const
        apply Finset.measurable_fun_sum
        intro s _
        exact measurable_thresholdSignedSquareMax
          (fun p : A × (Fin n → Z) => R ∘ p.2)
          (fun p i => f (p.1, p.2 i)) ell s
          (fun i => by fun_prop) (fun i => by fun_prop)) hEprod
    have hBudget := hBound.trans (mul_le_mul_of_nonneg_left hSigned.2 (by norm_num : (0 : ℝ) ≤ 4))
    rw [← hlaw] at hBudget
    change (∫ p, H p ∂P.map (fun w => (F w, X w))) ≤
      4 * (4 * ∫ p, e p ∂P.map (fun w => (F w, X w))) at hBudget
    rw [integral_map hpair.aemeasurable hH.aestronglyMeasurable,
      integral_map hpair.aemeasurable he.aestronglyMeasurable] at hBudget
    convert hBudget using 1 <;> first | rfl | ring
  · have hEvent := measurableSet_training_threshold_ghost_domination (n := n) μ R f ell hR hf
      (fun a => hMark a ell le_rfl)
    have hProduct := (Measure.ae_prod_iff_ae_ae hEvent).mpr hDom
    rw [← hlaw] at hProduct
    exact (ae_map_iff hpair.aemeasurable hEvent).mp hProduct

open ProbabilityTheory
open scoped Classical

variable {q d : ℕ} {M : ExtremeModel q d}

-- @node: evaluation_vector_indep_training_map
/-- If [the sample size is even](hyp:hn), [the experiment is sampled independently and identically](hyp:hiid), and [the map built from the training half is measurable with respect to the training information](hyp:hF), then [that training map is independent of the vector of evaluation observations](goal). -/
lemma evaluation_vector_indep_training_map (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A)
    (hF : Measurable[trainSigma E n] F) :
    IndepFun F (fun w (j : Fin (evalIndices n).card) =>
      obs E n w (((evalIndices n).equivFin).symm j)) E.P := by
  let mask := fun w (i : Fin n) =>
    if n / 2 ≤ i.val then obs E n w i else (0, false, 0, 0)
  let H := MeasurableSpace.comap mask inferInstance
  have hmask : Measurable[H] mask := Measurable.of_comap_le le_rfl
  have heval : Measurable[H] (fun w (j : Fin (evalIndices n).card) =>
      obs E n w (((evalIndices n).equivFin).symm j)) := by
    apply measurable_pi_lambda
    intro j
    let i : evalIndices n := ((evalIndices n).equivFin).symm j
    have hi : n / 2 ≤ i.val.val := by simpa [evalIndices] using i.property
    simpa only [mask, hi, if_true, Function.comp_def] using
      (measurable_pi_apply i.val).comp hmask
  apply (IndepFun_iff _ _ _).mpr
  intro S T hS hT
  exact (Indep_iff _ _ _).mp (evaluation_independent_training M E n hn hiid)
    _ _ (hF.comap_le _ hS) (heval.comap_le _ hT)

-- @node: evaluation_vector_population_law
/-- If [the sample size is even](hyp:hn) and [the experiment is sampled independently and identically](hyp:hiid), then [the evaluation-observation vector has the product population-observation law](goal). -/
lemma evaluation_vector_population_law (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n) :
    E.P.map (fun w (j : Fin (evalIndices n).card) =>
      obs E n w (((evalIndices n).equivFin).symm j)) =
      Measure.pi (fun _ : Fin (evalIndices n).card => M.mu.map (observation M)) := by
  let S := evalIndices n
  let μ := M.mu.map (observation M)
  have hobs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk (M.measurable_D.prodMk
      (M.measurable_Y.prodMk M.measurable_U))
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hSelected : E.P.map (fun w (i : S) => obs E n w i) =
      Measure.pi (fun _ : S => μ) := by
    have hrestrict : Measurable (fun z : Fin n → Obs q d => fun i : S => z i) := by fun_prop
    rw [show (fun w (i : S) => obs E n w i) =
      (fun z : Fin n → Obs q d => fun i : S => z i) ∘ (fun w => obs E n w) from rfl,
      ← Measure.map_map hrestrict (measurable_obs_tuple M E n),
      relabelled_joint_law M E n hn hiid]
    exact sample_pi_subtype_law (fun _ : Fin n => μ) S
  have h := (measurePreserving_piCongrLeft (fun _ : Fin S.card => μ) S.equivFin).map_eq
  have hm : Measurable (fun w (i : S) => obs E n w i) := by
    exact measurable_pi_lambda _ (fun i => (measurable_pi_apply (i : Fin n)).comp
      (measurable_obs_tuple M E n))
  rw [← hSelected, Measure.map_map (MeasurableEquiv.measurable _) hm] at h
  convert h using 1
  congr 1
  funext w j
  simp [S, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

-- @node: evaluation_vector_training_joint_law
/-- If [the sample size is even](hyp:hn), [the experiment is sampled independently and identically](hyp:hiid), and [the training map is measurable with respect to the training information](hyp:hF), then [the joint law of that map and the evaluation-observation vector is the product of their marginal laws](goal). -/
lemma evaluation_vector_training_joint_law (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A)
    (hF : Measurable[trainSigma E n] F) :
    E.P.map (fun w => (F w, fun j : Fin (evalIndices n).card =>
      obs E n w (((evalIndices n).equivFin).symm j))) =
      (E.P.map F).prod (Measure.pi
        (fun _ : Fin (evalIndices n).card => M.mu.map (observation M))) := by
  have hX : Measurable (fun w (j : Fin (evalIndices n).card) =>
      obs E n w (((evalIndices n).equivFin).symm j)) := by
    exact measurable_pi_lambda _ (fun j => (measurable_pi_apply _).comp
      (measurable_obs_tuple M E n))
  rw [(evaluation_vector_indep_training_map E n hn hiid F hF).map_prod_eq_prod_map_map
    (hF.mono (trainSigma_le E n) le_rfl).aemeasurable hX.aemeasurable,
    evaluation_vector_population_law E n hn hiid]

/-- If [the sample size is even](hyp:hn), [the experiment is sampled independently and identically](hyp:hiid), [the training map is measurable with respect to the training information](hyp:hF), [the score depending on training output and an observation is measurable](hyp:hf), [every thresholded score is integrable](hyp:hMark), and [the evaluation-half thresholded squared energy is integrable](hyp:hEnergy), then [there is a nonnegative integrable envelope on the split experiment, with expectation at most sixteen times that energy, that almost surely bounds every centered evaluation threshold sum squared](goal).

This is the conditional lift of frozen-score symmetrization. -/
-- @node: evaluation_training_threshold_square_envelope
lemma evaluation_training_threshold_square_envelope (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    {A : Type*} [MeasurableSpace A] (F : E.Om → A)
    (hF : Measurable[trainSigma E n] F)
    (f : A × Obs q d → ℝ) (hf : Measurable f) (ell : ℝ)
    (hMark : ∀ a, ∀ t ≥ ell, Integrable
      (fun z => if t < l1Norm z.2.2.2 then f (a, z) else 0)
      (M.mu.map (observation M)))
    (hEnergy : Integrable (fun w => ∑ j : Fin (evalIndices n).card,
      if ell < l1Norm (obs E n w (((evalIndices n).equivFin).symm j)).2.2.2 then
        f (F w, obs E n w (((evalIndices n).equivFin).symm j)) ^ 2 else 0) E.P) :
    ∃ H : E.Om → ℝ, Measurable H ∧ Integrable H E.P ∧ (∀ w, 0 ≤ H w) ∧
      (∫ w, H w ∂E.P) ≤ 16 * ∫ w, (∑ j : Fin (evalIndices n).card,
        if ell < l1Norm (obs E n w (((evalIndices n).equivFin).symm j)).2.2.2 then
          f (F w, obs E n w (((evalIndices n).equivFin).symm j)) ^ 2 else 0) ∂E.P ∧
      ∀ᵐ w ∂E.P, ∀ t ≥ ell,
        ((∑ j : Fin (evalIndices n).card,
          if t < l1Norm (obs E n w (((evalIndices n).equivFin).symm j)).2.2.2 then
            f (F w, obs E n w (((evalIndices n).equivFin).symm j)) else 0) -
          ((evalIndices n).card : ℝ) * ∫ z,
            (if t < l1Norm z.2.2.2 then f (F w, z) else 0)
            ∂M.mu.map (observation M)) ^ 2 ≤ H w := by
  have hobs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk (M.measurable_D.prodMk
      (M.measurable_Y.prodMk M.measurable_U))
  letI : IsProbabilityMeasure (M.mu.map (observation M)) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hX : Measurable (fun w (j : Fin (evalIndices n).card) =>
      obs E n w (((evalIndices n).equivFin).symm j)) := by
    exact measurable_pi_lambda _ (fun j => (measurable_pi_apply _).comp
      (measurable_obs_tuple M E n))
  exact training_threshold_square_symmetrization_of_joint_law E.P
    (M.mu.map (observation M)) F _ (hF.mono (trainSigma_le E n) le_rfl) hX
    (evaluation_vector_training_joint_law E n hn hiid F hF)
    (fun z => l1Norm z.2.2.2) f ell (by fun_prop) hf hMark hEnergy

end Papers.TbsExtremeEffects
