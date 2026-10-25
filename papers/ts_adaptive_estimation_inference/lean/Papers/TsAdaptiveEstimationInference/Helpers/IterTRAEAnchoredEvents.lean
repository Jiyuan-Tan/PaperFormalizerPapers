module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAECore
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEFittingConcentration
/-! Fixed population-anchor events on the actual iterative oracle segment.
The source parameters only describe deterministic anchors; the fitted scales and
confidence curves are retained unchanged.
-/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- If [the grid ratio is in its admissible domain](hyp:hρ) and [the penalty
belongs to the regularization grid](hyp:hlam), [there is a positive source
multiplier representing that penalty with source exponent one and accuracy one;
a grid index no larger than the terminal index crosses below the penalty, its
oracle point is no larger than the penalty, and the penalty is positive and at
most two](goal). -/
-- @node: iter_trae_grid_anchor_parameters
lemma iter_trae_grid_anchor_parameters (ρ : ℝ) (n t : ℕ)
    (hρ : GridDomain ρ) (lam : ℝ) (hlam : lam ∈ regGrid ρ n) :
    ∃ c > 0,
      c * ((2 : ℝ) * (1 : ℝ) ^ 2) ^ (1 / (qualificationExponent 1 t + 1)) = lam ∧
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ lam) ∧
      oraclePoint ρ n lam ≤ lam ∧ lam ≤ 2 ∧ 0 < lam := by
  classical
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hlam
  have hk' : k ≤ terminalIndex ρ n := by
    have := Finset.mem_range.mp hk
    omega
  have hr : 0 < ρ := by linarith [hρ.1]
  have hp : 0 < gridValue ρ k := by unfold gridValue; positivity
  have hu : gridValue ρ k ≤ 2 := by
    unfold gridValue
    exact mul_le_of_le_one_right (by norm_num) (pow_le_one₀ hr.le hρ.2.le)
  have hterminal : gridValue ρ (terminalIndex ρ n) ≤ gridValue ρ k := by
    unfold gridValue
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hr.le hρ.2.le hk') (by norm_num)
  let q := ((2 : ℝ) * (1 : ℝ) ^ 2) ^ (1 / (qualificationExponent 1 t + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨gridValue ρ k / q, div_pos hp hq, ?_, ⟨k, hk', le_rfl⟩,
    (oraclePoint_radius_bounds ρ _ n hρ hu hterminal).2.2, hu, hp⟩
  exact div_mul_cancel₀ _ hq.ne'

/-- Under [anchored localized concentration](hyp:hSource), [TRAE
boundedness](hyp:hBound), [a common almost-sure envelope](hyp:hCommon), and
[critical-radius bounds for the accuracy family](hyp:hComplexity), [a positive
constant can be chosen so that calibrated accuracies and valid allocations yield,
at each feasible measurable population grid anchor, a measurable fitting event
with failure probability at most half the allocation, on which all anchored
game deviations are bounded by the constant times the accuracy times the sum of
the three input distances plus the squared accuracy](goal). -/
-- @node: iter_trae_anchored_grid_fitting_at_allocation
lemma iter_trae_anchored_grid_fitting_at_allocation
    (hSource : IterTRAEAnchoredLocalizedConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (ρ : ℝ) (t j : ℕ), GridDomain ρ → 1 ≤ j → j ≤ t →
      ∀ lam ∈ regGrid ρ n,
      populationIterate V lam j ∈ V.H →
      projCondExpOp V (minNormSolution V - populationIterate V lam j) ∈ V.F →
      LocalizedSupremaMeasurableAt V.law (traeLossClass V)
        (iterTraePopulationAnchor V j lam) (traeClippedLoss B) n →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H, ∀ f ∈ V.F,
          |blockAverage V P sample (split.fit n)
              (fun w => traeIntegrand V h f w - traeIntegrand V (populationIterate V lam j)
                (projCondExpOp V (minNormSolution V - populationIterate V lam j)) w) ω -
            ∫ w, traeIntegrand V h f w - traeIntegrand V (populationIterate V lam j)
              (projCondExpOp V (minNormSolution V - populationIterate V lam j)) w ∂V.law| ≤
          C * (accuracy n * (∑ i : Fin 3, inputL2Norm V.law (fun w =>
            (![V.m f w, primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
              dualVersion V f (V.zOf w)] : Fin 3 → ℝ) i -
              iterTraePopulationAnchor V j lam w i)) + accuracy n ^ 2) := by
  obtain ⟨C, hC, hsource⟩ := iter_trae_anchored_fitting_at_allocation
    V P sample split hSource B tildeδ hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro accuracy allocation hScale n hn halloc ρ t j hρ hj hjt lam hlam hmem hcritic hMeas
  obtain ⟨c, hc, heq, hcross, hlow, hu, hp⟩ :=
    iter_trae_grid_anchor_parameters ρ n t hρ lam hlam
  have hradius : c * (2 * (fun _ : ℕ => (1 : ℝ)) n ^ 2) ^
      (1 / (qualificationExponent 1 t + 1)) = lam := heq
  have hs := hsource accuracy allocation hScale n hn halloc ρ c 2 1
    (fun _ => 1) t j hρ hc le_rfl zero_lt_one hj hjt
  dsimp only at hs
  rw [hradius] at hs
  exact hs hcross lam hlam hlow hu hp hmem hcritic hMeas

/-- Given [critical-radius bounds for the original confidence-indexed
family](hyp:hComplexity), [there exist another family satisfying critical-radius
bounds and a multiplier at least one such that every accuracy curve calibrated
to the original family remains calibrated after multiplication when the
allocation is divided by four inside the unit interval and replaced by one
otherwise](goal). -/
-- @node: iter_trae_quarter_scale_calibration
lemma iter_trae_quarter_scale_calibration
    (tildeδ : ℕ → ℝ → ℝ) (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ radius : ℕ → ℝ → ℝ, TRAECriticalRadiusBound V radius ∧
      ∃ M ≥ (1 : ℝ), ∀ (δ allocation : ℕ → ℝ),
        TRAEScaleCalibration δ tildeδ allocation →
        TRAEScaleCalibration (fun n => M * δ n) radius
          (fun n => if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 4 else 1) := by
  classical
  let forward : ℝ → ℝ := fun ζ => if ζ < 1 / 4 then 4 * ζ else ζ
  let radius : ℕ → ℝ → ℝ := fun n ζ =>
    if ζ ∈ Set.Ioo (0 : ℝ) 1 then
      max (tildeδ n (forward ζ)) (confidenceFloor n ζ) else 0
  have hforward (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
      forward ζ ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [forward]
    split <;> constructor <;> linarith [hζ.1, hζ.2]
  have hcomplex : TRAECriticalRadiusBound V radius := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro n hn ζ hζ
    obtain ⟨_, hp, hm, hf, hh, hdiff⟩ := hComplexity.choose_spec.2 n hn
      (forward ζ) (hforward ζ hζ)
    have hmono : tildeδ n (forward ζ) ≤ radius n ζ := by
      dsimp [radius]
      rw [if_pos hζ]
      exact le_max_left _ _
    refine ⟨?_, criticalRadiusBound_mono _ _ _ _ _ hp hmono,
      criticalRadiusBound_mono _ _ _ _ _ hm hmono,
      criticalRadiusBound_mono _ _ _ _ _ hf hmono,
      criticalRadiusBound_mono _ _ _ _ _ hh hmono,
      criticalRadiusBound_mono _ _ _ _ _ hdiff hmono⟩
    simpa only [radius, if_pos hζ, one_mul] using
      (le_max_right (tildeδ n (forward ζ)) (confidenceFloor n ζ))
  obtain ⟨K, hK, hfloor⟩ := trae_radius_uniform_at_allocation V tildeδ hComplexity
  let M := K + 2
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  refine ⟨radius, hcomplex, M, hM, ?_⟩
  intro δ allocation hScale
  let allocated : ℕ → ℝ := fun n =>
    if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 4 else 1
  have hd (n : ℕ) (hn : 0 < n) : 0 ≤ δ n :=
    (Real.rpow_nonneg (by positivity) _).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  have hdM (n : ℕ) (hn : 0 < n) : δ n ≤ M * δ n := by
    nlinarith only [hd n hn, hM]
  have hcal : TRAEScaleCalibration (fun n => M * δ n) radius allocated := by
    constructor
    · intro n hn
      apply max_le
      · by_cases hv : allocation n ∈ Set.Ioo (0 : ℝ) 1
        · have hvquarter : allocation n / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
            constructor <;> linarith [hv.1, hv.2]
          have hvhalf : allocation n / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
            constructor <;> linarith [hv.1, hv.2]
          have hfwd : forward (allocation n / 4) = allocation n := by
            dsimp only [forward]
            rw [if_pos (by linarith [hv.2])]
            ring
          simp only [allocated, if_pos hv, radius, if_pos hvquarter, hfwd]
          apply max_le
          · exact ((le_max_left _ _).trans (hScale.1 n hn)).trans (hdM n hn)
          · have hhalf := confidenceFloor_half_le n (allocation n / 2) hn hvhalf
            have hsmall := (le_max_right _ _).trans (hScale.1 n hn)
            have hfirst := (hfloor δ allocation hScale n hn hv).1
            rw [show allocation n / 2 / 2 = allocation n / 4 by ring] at hhalf
            dsimp only [M]
            linarith only [hhalf, hsmall, hfirst, hd n hn]
        · simpa only [allocated, if_neg hv, radius,
            show ¬ (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by simp, if_false] using
              (show 0 ≤ M * δ n by positivity [hd n hn])
      · exact ((le_max_right _ _).trans (hScale.1 n hn)).trans (hdM n hn)
    · simpa using hScale.2.const_mul M
  exact hcal

/-- Under [anchored localized concentration](hyp:hSource), [TRAE
boundedness](hyp:hBound), [a common almost-sure envelope](hyp:hCommon), and
[critical-radius bounds](hyp:hComplexity), [there is a positive constant such
that calibrated accuracies, a valid grid, residual-critic feasibility, iterative
realizability, and measurable localized processes yield, for each positive sample
size with a valid allocation and oracle crossing, each positive iteration up to
the horizon, and each grid penalty in the oracle segment, a measurable event
with failure probability at most one eighth of the allocation, on which all
anchored game deviations are bounded by the constant times the accuracy times
the sum of the moment, prediction-product, and critic input distances plus the
squared accuracy](goal). -/
-- @node: iter_trae_anchored_segment_at_eighth_allocation
lemma iter_trae_anchored_segment_at_eighth_allocation
    (hSource : IterTRAEAnchoredLocalizedConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t : ℕ), GridDomain ρ →
      ClosenessCondition V → IterRealizableTRAE V ρ c b β t δ →
      IterTRAELocalizedProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      gridValue ρ (terminalIndex ρ n) ≤
        c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) →
      ∀ j : ℕ, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
        lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 8 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H, ∀ f ∈ V.F,
          let g := populationIterate V lam j
          let k := projCondExpOp V (minNormSolution V - g)
          |blockAverage V P sample (split.fit n)
              (fun w => traeIntegrand V h f w - traeIntegrand V g k w) ω -
            ∫ w, traeIntegrand V h f w - traeIntegrand V g k w ∂V.law| ≤
          C * (accuracy n * (inputL2Norm V.law (V.m f - V.m k) +
            inputL2Norm V.law (fun w =>
              primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
                primalVersion V g (V.xOf w) * dualVersion V k (V.zOf w)) +
            inputL2Norm V.law (fun w =>
              dualVersion V f (V.zOf w) - dualVersion V k (V.zOf w))) +
            accuracy n ^ 2) := by
  obtain ⟨radius, hcomplex, M, hM, hcal⟩ :=
    iter_trae_quarter_scale_calibration V tildeδ hComplexity
  obtain ⟨D, hD, hdev⟩ := iter_trae_anchored_grid_fitting_at_allocation
    V P sample split hSource B radius hBound hCommon hcomplex
  have hMp : 0 < M := zero_lt_one.trans_le hM
  refine ⟨D * (M ^ 2 + M), by positivity, ?_⟩
  intro accuracy allocation hScale ρ c b β δ t hρ hClose hIter hProcesses
    n hn hv hOracle j hj hjt lam hlam hsegment
  have halloc : (if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 4 else 1)
      ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [if_pos hv]
    constructor <;> linarith [hv.1, hv.2]
  have hmem := hIter n hOracle j hj hjt lam hlam hsegment
  have hcritic := hClose _ hmem
  have hprocess := hProcesses.1 n hn hOracle j hj hjt lam hlam hsegment
  obtain ⟨E, hE, hpE, hgood⟩ := hdev (fun n => M * accuracy n)
    (fun n => if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 4 else 1)
    (hcal accuracy allocation hScale) n hn halloc ρ t j hρ hj hjt
    lam hlam hmem hcritic hprocess
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [if_pos hv, div_div, show (4 : ℝ) * 2 = 8 by norm_num] using hpE
  · intro ω hω h hh f hf
    have he := hgood ω hω h hh f hf
    simp only [Fin.sum_univ_succ, iterTraePopulationAnchor, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero] at he
    rw [← add_assoc] at he
    dsimp only
    have hd : 0 ≤ accuracy n :=
      (Real.rpow_nonneg (by positivity) _).trans
        ((le_max_right _ _).trans (hScale.1 n hn))
    let L := inputL2Norm V.law (V.m f -
          V.m (projCondExpOp V (minNormSolution V - populationIterate V lam j))) +
        inputL2Norm V.law (fun w =>
          primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
            primalVersion V (populationIterate V lam j) (V.xOf w) *
              dualVersion V (projCondExpOp V (minNormSolution V -
                populationIterate V lam j)) (V.zOf w)) +
        inputL2Norm V.law (fun w => dualVersion V f (V.zOf w) -
          dualVersion V (projCondExpOp V (minNormSolution V - populationIterate V lam j))
            (V.zOf w))
    have hnorm : 0 ≤ L := by dsimp [L, inputL2Norm]; positivity
    change _ ≤ D * (M * accuracy n * L + (M * accuracy n) ^ 2) at he
    change _ ≤ D * (M ^ 2 + M) * (accuracy n * L + accuracy n ^ 2)
    have hk : M ≤ M ^ 2 + M := by nlinarith only [sq_nonneg M]
    have hk2 : M ^ 2 ≤ M ^ 2 + M := by linarith only [hMp]
    apply he.trans
    calc
      _ = D * (M * (accuracy n * L) + M ^ 2 * accuracy n ^ 2) := by ring
      _ ≤ D * ((M ^ 2 + M) * (accuracy n * L) +
          (M ^ 2 + M) * accuracy n ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hD.le
        exact add_le_add (mul_le_mul_of_nonneg_right hk (mul_nonneg hd hnorm))
          (mul_le_mul_of_nonneg_right hk2 (sq_nonneg _))
      _ = _ := by ring

/-- Under [anchored localized concentration](hyp:hSource), [TRAE
boundedness](hyp:hBound), [a common almost-sure envelope](hyp:hCommon), and
[critical-radius bounds](hyp:hComplexity), [there is a positive constant such
that calibrated accuracies, a valid grid, residual-critic feasibility, iterative
realizability, and measurable localized processes yield a finite family of
measurable iteration-grid events, each with failure probability at most one
eighth of the allocation; whenever the oracle crossing holds, their intersection
controls every anchored game deviation on the oracle segment by the constant
times the accuracy times the sum of the three input distances plus the squared
accuracy](goal). -/
-- @node: iter_trae_anchored_iteration_grid_events
lemma iter_trae_anchored_iteration_grid_events
    (hSource : IterTRAEAnchoredLocalizedConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t : ℕ), GridDomain ρ →
      ClosenessCondition V → IterRealizableTRAE V ρ c b β t δ →
      IterTRAELocalizedProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ A : Fin t → Fin (terminalIndex ρ n + 1) → Set Ω,
        (∀ j k, MeasurableSet (A j k) ∧ 1 - allocation n / 8 ≤ P.real (A j k)) ∧
        ∀ (_hOracle : gridValue ρ (terminalIndex ρ n) ≤
          c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))),
        ∀ ω ∈ (⋂ j, ⋂ k, A j k), ∀ lam ∈ regGrid ρ n,
          lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
          ∀ j, 1 ≤ j → j ≤ t → ∀ h ∈ V.H, ∀ f ∈ V.F,
          let g := populationIterate V lam j
          let k := projCondExpOp V (minNormSolution V - g)
          |blockAverage V P sample (split.fit n)
              (fun w => traeIntegrand V h f w - traeIntegrand V g k w) ω -
            ∫ w, traeIntegrand V h f w - traeIntegrand V g k w ∂V.law| ≤
          C * (accuracy n * (inputL2Norm V.law (V.m f - V.m k) +
            inputL2Norm V.law (fun w =>
              primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
                primalVersion V g (V.xOf w) * dualVersion V k (V.zOf w)) +
            inputL2Norm V.law (fun w =>
              dualVersion V f (V.zOf w) - dualVersion V k (V.zOf w))) +
            accuracy n ^ 2) := by
  classical
  obtain ⟨C, hC, hsource⟩ := iter_trae_anchored_segment_at_eighth_allocation
    V P sample split hSource B tildeδ hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro accuracy allocation hScale ρ c b β δ t hρ hClose hIter hProcesses n hn hv
  let defined := gridValue ρ (terminalIndex ρ n) ≤
    c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
  let segment := fun lam => lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2
  have hex : ∀ j : Fin t, ∀ k : Fin (terminalIndex ρ n + 1),
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 8 ≤ P.real E ∧
        ∀ (_hd : defined) (_hs : segment (gridValue ρ k)),
        ∀ ω ∈ E, ∀ h ∈ V.H, ∀ f ∈ V.F,
          let g := populationIterate V (gridValue ρ k) (j + 1)
          let k := projCondExpOp V (minNormSolution V - g)
          |blockAverage V P sample (split.fit n)
              (fun w => traeIntegrand V h f w - traeIntegrand V g k w) ω -
            ∫ w, traeIntegrand V h f w - traeIntegrand V g k w ∂V.law| ≤
          C * (accuracy n * (inputL2Norm V.law (V.m f - V.m k) +
            inputL2Norm V.law (fun w =>
              primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
                primalVersion V g (V.xOf w) * dualVersion V k (V.zOf w)) +
            inputL2Norm V.law (fun w =>
              dualVersion V f (V.zOf w) - dualVersion V k (V.zOf w))) +
            accuracy n ^ 2) := by
    intro j k
    by_cases hd : defined
    · by_cases hs : segment (gridValue ρ k)
      · obtain ⟨E, hE, hpE, hgood⟩ := hsource accuracy allocation hScale
          ρ c b β δ t hρ hClose hIter hProcesses n hn hv hd (j + 1)
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
  intro hd ω hω lam hlam hs j hj hjt h hh f hf
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hlam
  let ji : Fin t := ⟨j - 1, by omega⟩
  let ki : Fin (terminalIndex ρ n + 1) := ⟨k, Finset.mem_range.mp hk⟩
  have hmem : ω ∈ A ji ki := Set.mem_iInter.mp (Set.mem_iInter.mp hω ji) ki
  have he := hgA ji ki hd hs ω hmem h hh f hf
  simpa only [ji, ki, show j - 1 + 1 = j by omega] using he

end Papers.TsAdaptiveEstimationInference
