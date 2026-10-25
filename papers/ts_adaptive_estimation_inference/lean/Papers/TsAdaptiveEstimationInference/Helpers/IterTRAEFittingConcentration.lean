module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEVectorConcentration
/-! Transport calibrated fixed-anchor concentration to the actual fitting block.
The original representatives and empirical objectives are preserved.
-/
public section
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- For [a measurable event of independent observations](hyp:hE), [there is a
measurable event in the sampling space with exactly the same probability, and
every outcome in it yields a tuple in the original event whose sample averages
equal the fitting-block averages for every real-valued function](goal). -/
-- @node: iter_trae_iid_event_to_fitting
lemma iter_trae_iid_event_to_fitting (n : ℕ) (E : Set (Fin n → W))
    (hE : MeasurableSet E) :
    ∃ F : Set Ω, MeasurableSet F ∧
      P.real F = (Measure.pi (fun _ : Fin n => V.law)).real E ∧
      ∀ ω ∈ F, ∃ x ∈ E, ∀ f : W → ℝ,
        (n : ℝ)⁻¹ * ∑ i, f (x i) =
          blockAverage V P sample (split.fit n) f ω := by
  classical
  let tuple : Ω → Fin n → W := fun ω i =>
    sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) ω
  have htuple : Measurable tuple := by
    fun_prop
  have hlaw : P.map tuple = Measure.pi (fun _ : Fin n => V.law) := by
    have hinj : Function.Injective (fun i : Fin n =>
        ((Finset.equivFinOfCardEq (split.card_fit n)).symm i : ℕ)) :=
      Subtype.val_injective.comp (Equiv.injective _)
    have hiid := sample.indep.precomp hinj
    have he := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (sample.meas _).aemeasurable)).mp hiid
    change P.map tuple = _ at he
    rw [he]
    simp_rw [sample.map_eq]
  refine ⟨tuple ⁻¹' E, hE.preimage htuple, ?_, ?_⟩
  · change (P (tuple ⁻¹' E)).toReal = _
    rw [← Measure.map_apply htuple hE, hlaw]
    rfl
  · intro ω hω
    refine ⟨tuple ω, hω, ?_⟩
    intro f
    unfold blockAverage
    rw [split.card_fit]
    congr 1
    rw [← Finset.sum_coe_sort (split.fit n)]
    exact Equiv.sum_comp (Finset.equivFinOfCardEq (split.card_fit n)).symm
      (fun i : split.fit n => f (sample.Z i ω))

/-- Under [fixed-center squared-loss concentration](hyp:hSource), [model
boundedness](hyp:hBound), [a common null-set envelope](hyp:hCommon), and [a
critical-radius complexity bound](hyp:hComplexity), [one positive constant
ensures that every calibrated accuracy curve and valid allocation, positive
sample size, admissible population iterate, and adjacent center that is zero or
in the hypothesis class with measurable localized processes admits a measurable
fitting event of probability at least one minus half the allocation, uniformly
bounding the difference between empirical and population squared-distance
increments by the constant times accuracy times distance from the iterate plus
squared accuracy](goal). -/
-- @node: iter_trae_fixed_center_fitting_at_allocation
lemma iter_trae_fixed_center_fitting_at_allocation
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t j : ℕ),
      GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ j → j ≤ t →
      let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) →
      ∀ lam ∈ regGrid ρ n, oraclePoint ρ n radius ≤ lam → lam ≤ 2 → 0 < lam →
      populationIterate V lam j ∈ V.H →
      ∀ center : V.Hbar.toSubmodule,
      (center = populationIterate V lam (j - 1) ∨ center = populationIterate V lam j) →
      (center = 0 ∨ center ∈ V.H) →
      LocalizedSupremaMeasurableAt V.law
        (iterTraeScalarClass (primalObservationClass V))
        (fun w => fun _ : Fin 1 => primalVersion V (populationIterate V lam j) (V.xOf w))
        (fun w v => (v 0 - primalVersion V center (V.xOf w)) ^ 2) n →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H,
          |(primalEmpDistanceSq V P sample split n ω h center -
              primalEmpDistanceSq V P sample split n ω (populationIterate V lam j) center) -
            (‖h - center‖ ^ 2 - ‖populationIterate V lam j - center‖ ^ 2)| ≤
          C * (accuracy n * ‖h - populationIterate V lam j‖ + accuracy n ^ 2) := by
  obtain ⟨Cs, hCs, hsource⟩ := iter_trae_fixed_center_calibrated_at_allocation
    V hSource B tildeδ hBound hCommon hComplexity
  let s := 2 * max 1 B
  have hs : 0 < s := by dsimp [s]; positivity
  have hBs : 2 * B ≤ s := by dsimp [s]; gcongr; exact le_max_right _ _
  refine ⟨s ^ 2 * Cs, by positivity, ?_⟩
  intro accuracy allocation hScale n hn halloc ρ c b β δ t j hρ hc hb hβ hj hjt
  dsimp only
  intro hDefined lam hlam hlow hu hp hmem center hcenter hcenterMem hMeas
  have hEnvelope : ∀ᵐ w ∂V.law, |primalVersion V center (V.xOf w)| ≤ B := by
    filter_upwards [hBound.2.2.1, primalVersion_zero_ae V] with w hw hzero
    exact iter_trae_zero_or_class_bound V B hBound.1 w hw center hcenterMem hzero
  obtain ⟨E, hE, hpE, hgood⟩ := hsource accuracy allocation hScale n hn halloc
    ρ c b β δ t j hρ hc hb hβ hj hjt hDefined lam hlam hlow hu hp hmem center
    hcenter hEnvelope hMeas
  obtain ⟨F, hF, hpF, htuple⟩ := iter_trae_iid_event_to_fitting V P sample split n E hE
  obtain ⟨S, hS, hSae, hbounded⟩ := trae_fitting_bounded_event V P sample split B hBound hCommon n
  refine ⟨F \ Sᶜ, hF.diff hS.compl, ?_, ?_⟩
  · change _ ≤ (P (F \ Sᶜ)).toReal
    have hnull : P Sᶜ = 0 := ae_iff.mp hSae
    have heq : P (F \ Sᶜ) = P F := measure_sdiff_null hnull
    rw [heq]
    change _ ≤ P.real F
    rw [hpF]
    exact hpE
  · intro ω hω h hh
    obtain ⟨x, hx, havg⟩ := htuple ω hω.1
    have hωS : ω ∈ S := by simpa using hω.2
    have he := hgood x hx h hh
    change |(n : ℝ)⁻¹ * (∑ i,
        (iterTraeClippedDistance V s h center (x i) -
          iterTraeClippedDistance V s (populationIterate V lam j) center (x i))) -
        ∫ w, (iterTraeClippedDistance V s h center w -
          iterTraeClippedDistance V s (populationIterate V lam j) center w) ∂V.law| ≤ _ at he
    rw [havg (fun w => iterTraeClippedDistance V s h center w -
      iterTraeClippedDistance V s (populationIterate V lam j) center w)] at he
    have hint (a : V.Hbar.toSubmodule) :
        Integrable (iterTraeClippedDistance V s a center) V.law :=
      Integrable.of_mem_Icc 0 1
        (iter_trae_clipped_distance_measurable V s a center).aemeasurable
        (Filter.Eventually.of_forall (iter_trae_clipped_distance_mem_Icc V s a center))
    have htransfer := iter_trae_clipped_center_transfer V P sample split s B hs hBs
      hBound hCommon n ω (hbounded ω hωS).2 (hbounded ω hωS).1 (populationIterate V lam j) h center hmem hh hcenterMem
    have heq :
        (primalEmpDistanceSq V P sample split n ω h center -
          primalEmpDistanceSq V P sample split n ω (populationIterate V lam j) center) -
        (‖h - center‖ ^ 2 - ‖populationIterate V lam j - center‖ ^ 2) =
        s ^ 2 * (blockAverage V P sample (split.fit n)
          (fun w => iterTraeClippedDistance V s h center w -
            iterTraeClippedDistance V s (populationIterate V lam j) center w) ω -
          ∫ w, (iterTraeClippedDistance V s h center w -
            iterTraeClippedDistance V s (populationIterate V lam j) center w) ∂V.law) := by
      rw [htransfer, integral_sub (hint h) (hint (populationIterate V lam j))]
      simp only [blockAverage, Finset.sum_sub_distrib, mul_sub]
      ring
    rw [heq, abs_mul, abs_of_nonneg (sq_nonneg s)]
    exact (mul_le_mul_of_nonneg_left he (sq_nonneg s)).trans_eq (by ring)

/-- If [the primal candidate belongs to the hypothesis class](hyp:hh) and
[the critic belongs to the critic class](hyp:hf), [their moment, primal–critic
product, and critic observation functions together belong to the loss class
used for concentration](goal). -/
-- @node: iter_trae_loss_class_member
lemma iter_trae_loss_class_member (h : V.Hbar.toSubmodule) (f : V.Qbar.toSubmodule)
    (hh : h ∈ V.H) (hf : f ∈ V.F) :
    (fun w => ![V.m f w, primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
      dualVersion V f (V.zOf w)]) ∈ traeLossClass V := by
  have hstar {F : Set (W → ℝ)} {u : W → ℝ} (hu : u ∈ F) : u ∈ starClass F := by
    exact ⟨1, ⟨by norm_num, by norm_num⟩, u, hu, by simp⟩
  exact ⟨_, hstar ⟨f, hf, rfl⟩, _, hstar ⟨h, hh, f, hf, rfl⟩,
    _, hstar ⟨f, hf, rfl⟩, rfl⟩

/-- Under [anchored localized concentration](hyp:hSource), [model
boundedness](hyp:hBound), [a common null-set envelope](hyp:hCommon), and [the
critical-radius complexity bound](hyp:hComplexity), [one positive constant works
for every calibrated accuracy curve: for valid allocations and admissible grid
penalties and population anchors whose primal and critic belong to their classes
and whose localized processes are measurable, a measurable fitting event of
probability at least one minus half the allocation uniformly bounds centered
loss-increment deviations for every primal–critic pair by the constant times
accuracy times the sum of the three coordinate L2 distances from the anchor
plus squared accuracy](goal). -/
-- @node: iter_trae_anchored_fitting_at_allocation
lemma iter_trae_anchored_fitting_at_allocation
    (hSource : IterTRAEAnchoredLocalizedConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t j : ℕ),
      GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ j → j ≤ t →
      let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) →
      ∀ lam ∈ regGrid ρ n, oraclePoint ρ n radius ≤ lam → lam ≤ 2 → 0 < lam →
      populationIterate V lam j ∈ V.H →
      projCondExpOp V (minNormSolution V - populationIterate V lam j) ∈ V.F →
      LocalizedSupremaMeasurableAt V.law (traeLossClass V)
        (iterTraePopulationAnchor V j lam) (traeClippedLoss B) n →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H, ∀ f ∈ V.F,
          let g := populationIterate V lam j
          let k := projCondExpOp V (minNormSolution V - g)
          |blockAverage V P sample (split.fit n)
              (fun w => traeIntegrand V h f w - traeIntegrand V g k w) ω -
            ∫ w, traeIntegrand V h f w - traeIntegrand V g k w ∂V.law| ≤
          C * (accuracy n * (∑ i : Fin 3, inputL2Norm V.law (fun w =>
            (![V.m f w, primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
              dualVersion V f (V.zOf w)] : Fin 3 → ℝ) i -
              iterTraePopulationAnchor V j lam w i)) + accuracy n ^ 2) := by
  obtain ⟨C, hC, hsource⟩ := iter_trae_anchored_calibrated_at_allocation
    V hSource B tildeδ hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro accuracy allocation hScale n hn halloc ρ c b β δ t j hρ hc hb hβ hj hjt
  dsimp only
  intro hDefined lam hlam hlow hu hp hmem hcritic hMeas
  have ht : 1 ≤ t := hj.trans hjt
  have hAnchor : iterTraePopulationAnchor V j lam ∈ traeLossClass V :=
    iter_trae_loss_class_member V _ _ hmem hcritic
  have hMeasAE : AELocalizedSupremaMeasurableAt V.law (traeLossClass V)
      (iterTraePopulationAnchor V j lam) (traeClippedLoss B) n := by
    intro r hr
    exact ⟨(hMeas r hr).1.aemeasurable, (hMeas r hr).2.aemeasurable⟩
  obtain ⟨E, hE, hpE, hgood⟩ := hsource accuracy allocation hScale n hn halloc
    ρ c b β δ t hρ hc hb hβ ht (iterTraePopulationAnchor V j lam)
    (Or.inr ⟨j, hj, hjt, lam, hlam, hDefined, hlow, hu, hp, hmem, hcritic, rfl⟩)
    hAnchor hMeasAE
  obtain ⟨F, hF, hpF, htuple⟩ := iter_trae_iid_event_to_fitting V P sample split n E hE
  have ha : ∀ᵐ ω ∂P, ∀ i : ℕ, ∀ f ∈ V.F,
      |dualVersion V f (V.zOf (sample.Z i ω))| ≤ B := by
    apply ae_all_iff.mpr
    intro i
    have hi : ∀ᵐ w ∂P.map (sample.Z i), ∀ f ∈ V.F,
        |dualVersion V f (V.zOf w)| ≤ B := by
      simpa only [sample.map_eq i] using hBound.2.2.2.1
    exact ae_of_ae_map (sample.meas i).aemeasurable hi
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp ha)
  refine ⟨F \ N, hF.diff hN, ?_, ?_⟩
  · change _ ≤ (P (F \ N)).toReal
    rw [measure_sdiff_null hnull]
    change _ ≤ P.real F
    rw [hpF]
    exact hpE
  · intro ω hω h hh f hf
    obtain ⟨x, hx, havg⟩ := htuple ω hω.1
    have henv : ∀ i : ℕ, ∀ f ∈ V.F,
        |dualVersion V f (V.zOf (sample.Z i ω))| ≤ B := by
      by_contra h
      exact hω.2 (hsub h)
    have he := hgood x hx _ (iter_trae_loss_class_member V h f hh hf)
    rw [havg (fun w => traeClippedLoss B w
        ![V.m f w, primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
          dualVersion V f (V.zOf w)] -
        traeClippedLoss B w (iterTraePopulationAnchor V j lam w))] at he
    have hmean : (∫ w, traeClippedLoss B w
        ![V.m f w, primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
          dualVersion V f (V.zOf w)] -
        traeClippedLoss B w (iterTraePopulationAnchor V j lam w) ∂V.law) =
        ∫ w, traeIntegrand V h f w - traeIntegrand V (populationIterate V lam j)
          (projCondExpOp V (minNormSolution V - populationIterate V lam j)) w ∂V.law := by
      apply integral_congr_ae
      filter_upwards [hBound.2.2.2.1] with w hw
      rw [trae_clipped_loss_eq_integrand V B w h f (hw f hf)]
      simp only [iterTraePopulationAnchor]
      rw [trae_clipped_loss_eq_integrand V B w (populationIterate V lam j) _ (hw _ hcritic)]
    rw [hmean] at he
    have hemp : blockAverage V P sample (split.fit n)
        (fun w => traeClippedLoss B w
          ![V.m f w, primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
            dualVersion V f (V.zOf w)] -
          traeClippedLoss B w (iterTraePopulationAnchor V j lam w)) ω =
        blockAverage V P sample (split.fit n)
          (fun w => traeIntegrand V h f w - traeIntegrand V (populationIterate V lam j)
            (projCondExpOp V (minNormSolution V - populationIterate V lam j)) w) ω := by
      unfold blockAverage
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only
      rw [trae_clipped_loss_eq_integrand V B _ h f (henv i f hf)]
      simp only [iterTraePopulationAnchor]
      rw [trae_clipped_loss_eq_integrand V B _ (populationIterate V lam j) _ (henv i _ hcritic)]
    rw [hemp] at he
    exact he

/-- Suppose [the clipping scale is positive](hyp:hs) and [at least twice the
envelope bound](hyp:hBs), [the model is bounded](hyp:hBound), [its envelope holds
outside a common null set](hyp:hCommon), [all fitting observations simultaneously
satisfy the primal envelope](hyp:hω), and [the outcome respects the zero
representative](hyp:hZero). If [the first candidate is in the hypothesis
class](hyp:hh), [the comparator is in that class](hyp:ha), [the center is zero or
in that class](hyp:hc), and [their empirical-minus-population squared-distance
increment has absolute value at most the error bound](hyp:hcomparison), then
[the absolute difference of their centered clipped fitting averages, multiplied
by the squared clipping scale, is at most the same error bound](goal). -/
-- @node: iter_trae_clipped_center_bound
lemma iter_trae_clipped_center_bound
    (s B R : ℝ) (hs : 0 < s) (hBs : 2 * B ≤ s)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (n : ℕ) (ω : Ω)
    (hω : ∀ i ∈ split.fit n, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B)
    (hZero : ω ∈ sampleZeroEvent V P sample)
    (h a center : V.Hbar.toSubmodule)
    (hh : h ∈ V.H) (ha : a ∈ V.H) (hc : center = 0 ∨ center ∈ V.H)
    (hcomparison :
      |(primalEmpDistanceSq V P sample split n ω h center -
          primalEmpDistanceSq V P sample split n ω a center) -
        (‖h - center‖ ^ 2 - ‖a - center‖ ^ 2)| ≤ R) :
    s ^ 2 * |(blockAverage V P sample (split.fit n)
        (iterTraeClippedDistance V s a center) ω -
          ∫ w, iterTraeClippedDistance V s a center w ∂V.law) -
      (blockAverage V P sample (split.fit n)
        (iterTraeClippedDistance V s h center) ω -
          ∫ w, iterTraeClippedDistance V s h center w ∂V.law)| ≤ R := by
  have heq := iter_trae_clipped_center_transfer V P sample split
    s B hs hBs hBound hCommon n ω hω hZero h a center hh ha hc
  rw [← abs_of_nonneg (sq_nonneg s), ← abs_mul, ← heq]
  have hneg :
      (primalEmpDistanceSq V P sample split n ω a center -
          primalEmpDistanceSq V P sample split n ω h center) -
        (‖a - center‖ ^ 2 - ‖h - center‖ ^ 2) =
      -((primalEmpDistanceSq V P sample split n ω h center -
          primalEmpDistanceSq V P sample split n ω a center) -
        (‖h - center‖ ^ 2 - ‖a - center‖ ^ 2)) := by ring
  simpa only [hneg, abs_neg] using hcomparison

/-- Suppose [the clipping scale is positive](hyp:hs) and [at least twice the
envelope bound](hyp:hBs), [the model is bounded](hyp:hBound), [a common null-set
envelope holds](hyp:hCommon), [all fitting observations satisfy the simultaneous
primal envelope](hyp:hω), and [the outcome respects the zero representative](hyp:hZero).
If [the candidate belongs to the hypothesis class](hyp:hh), [its center also
belongs to that class](hyp:ha), and [their self-centered empirical-minus-population quadratic increment is
bounded by the error bound](hyp:hcomparison), then [the centered clipped
squared-distance fitting average, in absolute value and multiplied by the squared
clipping scale, is bounded by the same error bound](goal). -/
-- @node: iter_trae_clipped_self_bound
lemma iter_trae_clipped_self_bound
    (s B R : ℝ) (hs : 0 < s) (hBs : 2 * B ≤ s)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (n : ℕ) (ω : Ω)
    (hω : ∀ i ∈ split.fit n, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B)
    (hZero : ω ∈ sampleZeroEvent V P sample)
    (h a : V.Hbar.toSubmodule) (hh : h ∈ V.H) (ha : a ∈ V.H)
    (hcomparison :
      |(primalEmpDistanceSq V P sample split n ω h a -
          primalEmpDistanceSq V P sample split n ω a a) -
        (‖h - a‖ ^ 2 - ‖a - a‖ ^ 2)| ≤ R) :
    s ^ 2 * |blockAverage V P sample (split.fit n)
        (iterTraeClippedDistance V s h a) ω -
          ∫ w, iterTraeClippedDistance V s h a w ∂V.law| ≤ R := by
  have hself : primalEmpDistanceSq V P sample split n ω a a = 0 := by
    simp [primalEmpDistanceSq, blockAverage]
  have heq := iter_trae_clipped_distance_transfer V P sample split
    s B hs hBs hBound hCommon n ω hω hZero h a hh (Or.inr ha)
  rw [← abs_of_nonneg (sq_nonneg s), ← abs_mul, ← heq]
  simpa only [hself, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
    using hcomparison

/-- Under [fixed-center squared-loss concentration](hyp:hSource), [a positive
clipping scale](hyp:hs) [at least twice the envelope bound](hyp:hBs), [model
boundedness](hyp:hBound), [a common null-set envelope](hyp:hCommon), and [the
critical-radius complexity bound](hyp:hComplexity), [there is a positive constant
uniform over calibrated accuracy curves such that each valid sample size,
allocation, admissible population iterate, and adjacent center that is zero or a
class member with measurable localized processes admits a measurable fitting
event of probability at least one minus half the allocation, bounding the
absolute difference of centered clipped squared distances, multiplied by the
squared clipping scale, by the constant times accuracy times distance from the
iterate plus squared accuracy for every hypothesis](goal). -/
-- @node: iter_trae_fixed_center_clipped_fitting_at_allocation
lemma iter_trae_fixed_center_clipped_fitting_at_allocation
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V)
    (B s : ℝ) (hs : 0 < s) (hBs : 2 * B ≤ s) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t j : ℕ),
      GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ j → j ≤ t →
      let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) →
      ∀ lam ∈ regGrid ρ n, oraclePoint ρ n radius ≤ lam → lam ≤ 2 → 0 < lam →
      populationIterate V lam j ∈ V.H →
      ∀ center : V.Hbar.toSubmodule,
      (center = populationIterate V lam (j - 1) ∨ center = populationIterate V lam j) →
      (center = 0 ∨ center ∈ V.H) →
      LocalizedSupremaMeasurableAt V.law
        (iterTraeScalarClass (primalObservationClass V))
        (fun w => fun _ : Fin 1 => primalVersion V (populationIterate V lam j) (V.xOf w))
        (fun w v => (v 0 - primalVersion V center (V.xOf w)) ^ 2) n →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H,
          s ^ 2 * |(blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s (populationIterate V lam j) center) ω -
                ∫ w, iterTraeClippedDistance V s (populationIterate V lam j) center w ∂V.law) -
            (blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s h center) ω -
                ∫ w, iterTraeClippedDistance V s h center w ∂V.law)| ≤
          C * (accuracy n * ‖h - populationIterate V lam j‖ + accuracy n ^ 2) := by
  obtain ⟨C, hC, hsource⟩ := iter_trae_fixed_center_fitting_at_allocation
    V P sample split hSource B tildeδ hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro accuracy allocation hScale n hn halloc ρ c b β δ t j hρ hc hb hβ hj hjt
  dsimp only
  intro hDefined lam hlam hlow hu hp hmem center hcenter hcenterMem hMeas
  obtain ⟨E, hE, hpE, hgood⟩ := hsource accuracy allocation hScale n hn halloc
    ρ c b β δ t j hρ hc hb hβ hj hjt hDefined lam hlam hlow hu hp hmem center
    hcenter hcenterMem hMeas
  obtain ⟨S, hS, hSae, hbounded⟩ := trae_fitting_bounded_event V P sample split B hBound hCommon n
  refine ⟨E \ Sᶜ, hE.diff hS.compl, ?_, ?_⟩
  · change _ ≤ (P (E \ Sᶜ)).toReal
    have hnull : P Sᶜ = 0 := ae_iff.mp hSae
    have heq : P (E \ Sᶜ) = P E := measure_sdiff_null hnull
    rw [heq]
    exact hpE
  · intro ω hω h hh
    have hωS : ω ∈ S := by simpa using hω.2
    exact iter_trae_clipped_center_bound V P sample split s B _ hs hBs hBound hCommon
      n ω (hbounded ω hωS).2 (hbounded ω hωS).1 h (populationIterate V lam j) center hh hmem
      hcenterMem (hgood ω hω.1 h hh)

/-- Under [fixed-center squared-loss concentration](hyp:hSource), [a positive
clipping scale](hyp:hs) [at least twice the envelope bound](hyp:hBs), [model
boundedness](hyp:hBound), [a common null-set envelope](hyp:hCommon), and [the
critical-radius complexity bound](hyp:hComplexity), [one positive constant works
for every calibrated accuracy curve: each valid sample size, allocation, and
admissible population iterate in the hypothesis class with measurable localized
processes admits a measurable fitting event of probability at least one minus
half the allocation on which every hypothesis's centered clipped squared distance
from that iterate, in absolute value and multiplied by squared clipping scale,
is bounded by the constant times accuracy times distance plus squared accuracy](goal). -/
-- @node: iter_trae_self_center_fitting_at_allocation
lemma iter_trae_self_center_fitting_at_allocation
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V)
    (B s : ℝ) (hs : 0 < s) (hBs : 2 * B ≤ s) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t j : ℕ),
      GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ j → j ≤ t →
      let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) →
      ∀ lam ∈ regGrid ρ n, oraclePoint ρ n radius ≤ lam → lam ≤ 2 → 0 < lam →
      populationIterate V lam j ∈ V.H →
      LocalizedSupremaMeasurableAt V.law
        (iterTraeScalarClass (primalObservationClass V))
        (fun w => fun _ : Fin 1 => primalVersion V (populationIterate V lam j) (V.xOf w))
        (fun w v => (v 0 - primalVersion V (populationIterate V lam j) (V.xOf w)) ^ 2) n →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H,
          s ^ 2 * |blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s h (populationIterate V lam j)) ω -
                ∫ w, iterTraeClippedDistance V s h (populationIterate V lam j) w ∂V.law| ≤
          C * (accuracy n * ‖h - populationIterate V lam j‖ + accuracy n ^ 2) := by
  obtain ⟨C, hC, hsource⟩ := iter_trae_fixed_center_fitting_at_allocation
    V P sample split hSource B tildeδ hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro accuracy allocation hScale n hn halloc ρ c b β δ t j hρ hc hb hβ hj hjt
  dsimp only
  intro hDefined lam hlam hlow hu hp hmem hMeas
  obtain ⟨E, hE, hpE, hgood⟩ := hsource accuracy allocation hScale n hn halloc
    ρ c b β δ t j hρ hc hb hβ hj hjt hDefined lam hlam hlow hu hp hmem
    (populationIterate V lam j) (Or.inr rfl) (Or.inr hmem) hMeas
  obtain ⟨S, hS, hSae, hbounded⟩ := trae_fitting_bounded_event V P sample split B hBound hCommon n
  refine ⟨E \ Sᶜ, hE.diff hS.compl, ?_, ?_⟩
  · change _ ≤ (P (E \ Sᶜ)).toReal
    have hnull : P Sᶜ = 0 := ae_iff.mp hSae
    have heq : P (E \ Sᶜ) = P E := measure_sdiff_null hnull
    rw [heq]
    exact hpE
  · intro ω hω h hh
    have hωS : ω ∈ S := by simpa using hω.2
    exact iter_trae_clipped_self_bound V P sample split s B _ hs hBs hBound hCommon
      n ω (hbounded ω hωS).2 (hbounded ω hωS).1 h (populationIterate V lam j) hh hmem
      (hgood ω hω.1 h hh)

end Papers.TsAdaptiveEstimationInference
