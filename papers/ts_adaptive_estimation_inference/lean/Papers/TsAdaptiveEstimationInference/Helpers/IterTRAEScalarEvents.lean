module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEAnchoredEvents
/-! Fixed population-center scalar events on the iterative oracle grid. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- [The scalar observation class consists exactly of the one-coordinate encodings
of the hypothesis class's chosen representatives](goal). -/
-- @node: iter_trae_scalar_primal_class_eq
lemma iter_trae_scalar_primal_class_eq :
    iterTraeScalarClass (primalObservationClass V) =
      {u | ∃ h ∈ V.H, u = fun w => fun _ : Fin 1 => primalVersion V h (V.xOf w)} := by
  ext u
  constructor
  · rintro ⟨f, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨_, ⟨h, hh, rfl⟩, rfl⟩

/-- Under [fixed-center squared-loss concentration](hyp:hSource), [a positive clipping scale](hyp:hs)
that [is at least twice the envelope bound](hyp:hBs), [boundedness](hyp:hBound),
[a common almost-sure envelope](hyp:hCommon), and [the critical-radius bound](hyp:hComplexity),
[one positive constant, chosen before the accuracy and allocation curves, bounds the
centered clipped-loss comparison by accuracy times distance plus squared accuracy,
uniformly over hypotheses, on a measurable event of probability at least one minus
half the allocation, for every admissible grid point and realizable population center
with measurable localized suprema](goal). -/
-- @node: iter_trae_fixed_center_grid_fitting_at_allocation
lemma iter_trae_fixed_center_grid_fitting_at_allocation
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V)
    (B s : ℝ) (hs : 0 < s) (hBs : 2 * B ≤ s) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (ρ : ℝ) (t j : ℕ), GridDomain ρ → 1 ≤ j → j ≤ t →
      ∀ lam ∈ regGrid ρ n,
      populationIterate V lam j ∈ V.H →
      (populationIterate V lam (j - 1) = 0 ∨ populationIterate V lam (j - 1) ∈ V.H) →
      LocalizedSupremaMeasurableAt V.law
        (iterTraeScalarClass (primalObservationClass V))
        (fun w => fun _ : Fin 1 => primalVersion V (populationIterate V lam j) (V.xOf w))
        (fun w v => (v 0 - primalVersion V (populationIterate V lam (j - 1)) (V.xOf w)) ^ 2) n →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H,
          s ^ 2 * |(blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s (populationIterate V lam j)
                (populationIterate V lam (j - 1))) ω -
            ∫ w, iterTraeClippedDistance V s (populationIterate V lam j)
              (populationIterate V lam (j - 1)) w ∂V.law) -
            (blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s h (populationIterate V lam (j - 1))) ω -
            ∫ w, iterTraeClippedDistance V s h (populationIterate V lam (j - 1)) w ∂V.law)| ≤
          C * (accuracy n * ‖h - populationIterate V lam j‖ + accuracy n ^ 2) := by
  obtain ⟨C, hC, hsource⟩ := iter_trae_fixed_center_clipped_fitting_at_allocation
    V P sample split hSource B s hs hBs tildeδ hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro accuracy allocation hScale n hn hv ρ t j hρ hj hjt lam hlam hmem hcenter hMeas
  obtain ⟨c, hc, heq, hcross, hlow, hu, hp⟩ :=
    iter_trae_grid_anchor_parameters ρ n t hρ lam hlam
  have hradius : c * (2 * (fun _ : ℕ => (1 : ℝ)) n ^ 2) ^
      (1 / (qualificationExponent 1 t + 1)) = lam := heq
  have hdev := hsource accuracy allocation hScale n hn hv ρ c 2 1
    (fun _ => 1) t j hρ hc le_rfl zero_lt_one hj hjt
  dsimp only at hdev
  rw [hradius] at hdev
  exact hdev hcross lam hlam hlow hu hp hmem (populationIterate V lam (j - 1))
    (Or.inl rfl) hcenter hMeas

/-- Given [fixed-center squared-loss concentration](hyp:hSource), [positive clipping](hyp:hs)
[at least twice the envelope bound](hyp:hBs), [boundedness](hyp:hBound),
[a common almost-sure envelope](hyp:hCommon), and [critical-radius control](hyp:hComplexity),
[there is a positive constant, uniform in calibrated accuracy and allocation curves,
such that every realizable iteration on the oracle grid segment has a measurable
fixed-center clipped-loss comparison event with failure probability at most one eighth
of its allocation and deviation bounded by accuracy times distance plus squared accuracy,
provided the localized processes are measurable and the oracle lies above the grid floor](goal). -/
-- @node: iter_trae_fixed_center_segment_at_eighth_allocation
lemma iter_trae_fixed_center_segment_at_eighth_allocation
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V)
    (B s : ℝ) (hs : 0 < s) (hBs : 2 * B ≤ s) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t : ℕ), GridDomain ρ →
      IterRealizableTRAE V ρ c b β t δ →
      IterTRAELocalizedProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      gridValue ρ (terminalIndex ρ n) ≤
        c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) →
      ∀ j : ℕ, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
        lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 8 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H,
          s ^ 2 * |(blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s (populationIterate V lam j)
                (populationIterate V lam (j - 1))) ω -
            ∫ w, iterTraeClippedDistance V s (populationIterate V lam j)
              (populationIterate V lam (j - 1)) w ∂V.law) -
            (blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s h (populationIterate V lam (j - 1))) ω -
            ∫ w, iterTraeClippedDistance V s h (populationIterate V lam (j - 1)) w ∂V.law)| ≤
          C * (accuracy n * ‖h - populationIterate V lam j‖ + accuracy n ^ 2) := by
  obtain ⟨radius, hcomplex, M, hM, hcal⟩ :=
    iter_trae_quarter_scale_calibration V tildeδ hComplexity
  obtain ⟨D, hD, hdev⟩ := iter_trae_fixed_center_grid_fitting_at_allocation
    V P sample split hSource B s hs hBs radius hBound hCommon hcomplex
  have hMp : 0 < M := zero_lt_one.trans_le hM
  refine ⟨D * (M ^ 2 + M), by positivity, ?_⟩
  intro accuracy allocation hScale ρ c b β δ t hρ hIter hProcesses
    n hn hv hOracle j hj hjt lam hlam hsegment
  have halloc : (if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 4 else 1)
      ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [if_pos hv]
    constructor <;> linarith [hv.1, hv.2]
  have hmem := hIter n hOracle j hj hjt lam hlam hsegment
  have hcenter : populationIterate V lam (j - 1) = 0 ∨
      populationIterate V lam (j - 1) ∈ V.H := by
    by_cases hj1 : j = 1
    · left
      simp [hj1, populationIterate]
    · right
      exact hIter n hOracle (j - 1) (by omega) (by omega) lam hlam hsegment
  have hprocess := (hProcesses.2 n hn hOracle j hj hjt lam hlam hsegment).1
  obtain ⟨E, hE, hpE, hgood⟩ := hdev (fun n => M * accuracy n)
    (fun n => if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 4 else 1)
    (hcal accuracy allocation hScale) n hn halloc ρ t j hρ hj hjt
    lam hlam hmem hcenter (by
      simpa only [iter_trae_scalar_primal_class_eq] using hprocess)
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [if_pos hv, div_div, show (4 : ℝ) * 2 = 8 by norm_num] using hpE
  · intro ω hω h hh
    have he := hgood ω hω h hh
    have hd : 0 ≤ accuracy n :=
      (Real.rpow_nonneg (by positivity) _).trans
        ((le_max_right _ _).trans (hScale.1 n hn))
    apply he.trans
    have hk : M ≤ M ^ 2 + M := by nlinarith only [sq_nonneg M]
    have hk2 : M ^ 2 ≤ M ^ 2 + M := by linarith only [hMp]
    calc
      _ = D * (M * (accuracy n * ‖h - populationIterate V lam j‖) +
          M ^ 2 * accuracy n ^ 2) := by ring
      _ ≤ D * ((M ^ 2 + M) * (accuracy n * ‖h - populationIterate V lam j‖) +
          (M ^ 2 + M) * accuracy n ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hD.le
        exact add_le_add (mul_le_mul_of_nonneg_right hk (by positivity))
          (mul_le_mul_of_nonneg_right hk2 (sq_nonneg _))
      _ = _ := by ring

/-- Assuming [fixed-center squared-loss concentration](hyp:hSource), [positive clipping](hyp:hs)
[at least twice the envelope bound](hyp:hBs), [boundedness](hyp:hBound),
[a common almost-sure envelope](hyp:hCommon), and [critical-radius control](hyp:hComplexity),
[a positive constant uniform in calibrated scales gives a measurable event for each
iteration and grid index, each with failure probability at most one eighth of the
allocation; on their intersection, whenever the oracle is above the grid floor,
all realizable oracle-segment fixed-center clipped-loss comparisons are bounded by
accuracy times distance plus squared accuracy, assuming localized measurability](goal). -/
-- @node: iter_trae_fixed_center_iteration_grid_events
lemma iter_trae_fixed_center_iteration_grid_events
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V)
    (B s : ℝ) (hs : 0 < s) (hBs : 2 * B ≤ s) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t : ℕ), GridDomain ρ →
      IterRealizableTRAE V ρ c b β t δ →
      IterTRAELocalizedProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ A : Fin t → Fin (terminalIndex ρ n + 1) → Set Ω,
        (∀ j k, MeasurableSet (A j k) ∧ 1 - allocation n / 8 ≤ P.real (A j k)) ∧
        ∀ (_hOracle : gridValue ρ (terminalIndex ρ n) ≤
          c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))),
        ∀ ω ∈ (⋂ j, ⋂ k, A j k), ∀ lam ∈ regGrid ρ n,
          lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
          ∀ j, 1 ≤ j → j ≤ t → ∀ h ∈ V.H,
          s ^ 2 * |(blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s (populationIterate V lam j)
                (populationIterate V lam (j - 1))) ω -
            ∫ w, iterTraeClippedDistance V s (populationIterate V lam j)
              (populationIterate V lam (j - 1)) w ∂V.law) -
            (blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s h (populationIterate V lam (j - 1))) ω -
            ∫ w, iterTraeClippedDistance V s h (populationIterate V lam (j - 1)) w ∂V.law)| ≤
          C * (accuracy n * ‖h - populationIterate V lam j‖ + accuracy n ^ 2) := by
  classical
  obtain ⟨C, hC, hsource⟩ := iter_trae_fixed_center_segment_at_eighth_allocation
    V P sample split hSource B s hs hBs tildeδ hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro accuracy allocation hScale ρ c b β δ t hρ hIter hProcesses n hn hv
  let defined := gridValue ρ (terminalIndex ρ n) ≤
    c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
  let segment := fun lam => lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2
  have hex : ∀ j : Fin t, ∀ k : Fin (terminalIndex ρ n + 1),
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 8 ≤ P.real E ∧
        ∀ (_hd : defined) (_hs : segment (gridValue ρ k)),
        ∀ ω ∈ E, ∀ h ∈ V.H,
          s ^ 2 * |(blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s (populationIterate V (gridValue ρ k) (j + 1))
                (populationIterate V (gridValue ρ k) (j + 1 - 1))) ω -
            ∫ w, iterTraeClippedDistance V s (populationIterate V (gridValue ρ k) (j + 1))
              (populationIterate V (gridValue ρ k) (j + 1 - 1)) w ∂V.law) -
            (blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s h (populationIterate V (gridValue ρ k) (j + 1 - 1))) ω -
            ∫ w, iterTraeClippedDistance V s h (populationIterate V (gridValue ρ k) (j + 1 - 1)) w ∂V.law)| ≤
          C * (accuracy n * ‖h - populationIterate V (gridValue ρ k) (j + 1)‖ + accuracy n ^ 2) := by
    intro j k
    by_cases hd : defined
    · by_cases hs : segment (gridValue ρ k)
      · obtain ⟨E, hE, hpE, hgood⟩ := hsource accuracy allocation hScale
          ρ c b β δ t hρ hIter hProcesses n hn hv hd (j + 1)
          (by omega) (by omega) (gridValue ρ k)
          (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr k.isLt, rfl⟩) hs
        exact ⟨E, hE, hpE, fun _ _ => hgood⟩
      · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
        · simpa using (show 1 - allocation n / 8 ≤ 1 by linarith [hv.1])
        · intro _ h; exact (hs h).elim
    · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
      · simpa using (show 1 - allocation n / 8 ≤ 1 by linarith [hv.1])
      · intro h; exact (hd h).elim
  choose A hA hpA hgA using hex
  refine ⟨A, fun j k => ⟨hA j k, hpA j k⟩, ?_⟩
  intro hd ω hω lam hlam hs j hj hjt h hh
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hlam
  let ji : Fin t := ⟨j - 1, by omega⟩
  let ki : Fin (terminalIndex ρ n + 1) := ⟨k, Finset.mem_range.mp hk⟩
  have hmem : ω ∈ A ji ki := Set.mem_iInter.mp (Set.mem_iInter.mp hω ji) ki
  have he := hgA ji ki hd hs ω hmem h hh
  simpa only [ji, ki, show j - 1 + 1 = j by omega] using he

end Papers.TsAdaptiveEstimationInference
