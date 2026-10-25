module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAESetup
/-! Transport the common concentration event along identical oracle radii. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- If [the multiplier is nonnegative](hyp:hb), [the rescaling constant is positive](hyp:hc),
and [the exponent plus one is positive](hyp:hq), then [raising the multiplier times
squared rescaled accuracy to the reciprocal of the exponent plus one equals the
rescaling constant times the same power of the multiplier times the original squared
accuracy, when accuracy is rescaled by the constant to half the exponent plus one](goal). -/
-- @node: iterTrae_oracle_radius_rescale
lemma iterTrae_oracle_radius_rescale (b d c q : ℝ)
    (hb : 0 ≤ b) (hc : 0 < c) (hq : 0 < q + 1) :
    1 * (b * (c ^ ((q + 1) / 2) * d) ^ 2) ^ (1 / (q + 1)) =
      c * (b * d ^ 2) ^ (1 / (q + 1)) := by
  rw [one_mul, mul_pow]
  have hp : (c ^ ((q + 1) / 2)) ^ 2 = c ^ (q + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    congr 1
    norm_num
  rw [hp, show b * (c ^ (q + 1) * d ^ 2) = c ^ (q + 1) * (b * d ^ 2) by ring,
    Real.mul_rpow (Real.rpow_nonneg hc.le _) (by positivity),
    ← Real.rpow_mul hc.le, mul_one_div_cancel (ne_of_gt hq), Real.rpow_one]

/-- Assume [localized TRAE concentration](hyp:hBennett_of_gate), [anchored localized
concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[scalar Lipschitz concentration](hyp:hNorm_of_gate), [an admissible grid ratio](hyp:hρ),
[horizon at least one](hyp:ht), [multiplier at least two](hyp:hb), [mean-square continuity](hyp:hMSC),
[iterative mean-square continuity](hyp:hIterMSC), [boundedness](hyp:hBound),
[boundedness outside a common null set](hyp:hCommon), and [the critical-radius bound](hyp:hComplexity).
Then [a positive event constant can be fixed before confidence, balancing constant,
source exponent, and oracle accuracy: for every calibrated confidence budget strictly
between zero and one, positive balancing constant and source exponent, range,
realizability and closeness conditions, attained ordinary and iterative minima, and
measurable localized processes, each positive sample size admits three measurable
component events per iteration and grid index, each spending at most a third of the
per-grid allocation; their intersection has probability at least one minus the budget,
carries the iterative concentration certificate, and bounds every hypothesis function
by the envelope on all fitting observations](goal). -/
lemma iter_trae_concentration_event_uniform_allocation_with_bounds
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : ScalarLipschitzLocalizedConcentration V P sample split)
    (ρ B b : ℝ) (t : ℕ) (baseδ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : GridDomain ρ) (ht : 1 ≤ t) (hb : 2 ≤ b)
    (hMSC : MeanSquareContinuity V) (hIterMSC : IterMeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ Cevent > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
      ∀ (c β : ℝ) (δ : ℕ → ℝ), 0 < c → 0 < β →
      RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
      IterRealizableTRAE V ρ c b β t δ →
      TRAEMinimaAttained V P sample split ρ candidate →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAELocalizedProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n →
      ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
        (∀ j k a, MeasurableSet (component j k a) ∧
          1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
        let E := iterTraeCommonEvent ρ n t component
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
        IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Cevent ∧
        (∀ ω ∈ E, ∀ i ∈ split.fit n, ∀ h ∈ V.H,
          |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B) := by
  obtain ⟨Ce, hCe, hevent⟩ := iter_trae_concentration_event_uniform_confidence_with_bounds
    (hAnchored_of_gate := hAnchored_of_gate)
    (hFixedSq_of_gate := hFixedSq_of_gate) (hNorm_of_gate := hNorm_of_gate)
    (hBennett_of_gate := hBennett_of_gate) V P sample split
    (ρ := ρ) (B := B) (baseδ := baseδ) (tildeδ := tildeδ)
    (candidate := candidate) (iter := iter) (b := b) (c := 1) (t := t)
    hρ ht zero_lt_one hb hMSC hIterMSC hBound hCommon hComplexity
  refine ⟨Ce, hCe, ?_⟩
  intro ξ hξ hScale c β δ hc hβ hRange hRealizable hClose hIterRealizable
    hMinima hIterMinima hProcesses n hn
  let δ' := fun n => c ^ ((qualificationExponent β t + 1) / 2) * δ n
  have hq : 0 < qualificationExponent β t + 1 := by
    unfold qualificationExponent
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have : 0 < min (β + 1) (2 * (t : ℝ)) := lt_min (by linarith) (by linarith)
    linarith
  have hrad (n : ℕ) : 1 * (b * δ' n ^ 2) ^ (1 / (qualificationExponent β t + 1)) =
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) :=
    iterTrae_oracle_radius_rescale b (δ n) c _ (by linarith) hc hq
  have hReal' : IterRealizableTRAE V ρ 1 b β t δ' := by
    simpa only [IterRealizableTRAE, iterTraeOraclePoint, hrad] using hIterRealizable
  have hProcesses' : IterTRAELocalizedProcessesMeasurable V B ρ t
      (fun n => 1 * (b * δ' n ^ 2) ^ (1 / (qualificationExponent β t + 1))) := by
    simpa only [IterTRAELocalizedProcessesMeasurable, hrad] using hProcesses
  obtain ⟨component, hcomponent, hE, hp, hcon, hbounded⟩ :=
    hevent ξ hξ hScale β δ' hRange hRealizable hClose hReal' hMinima hIterMinima hProcesses' n hn
  refine ⟨component, hcomponent, hE, hp, ?_, hbounded⟩
  simpa only [IterTRAEConcentrationOn, iterTraeOraclePoint, hrad] using hcon

-- @node: iter_trae_concentration_event_uniform_allocation
/-- Under [localized TRAE concentration](hyp:hBennett_of_gate), [anchored localized
concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[scalar Lipschitz concentration](hyp:hNorm_of_gate), [an admissible grid ratio](hyp:hρ),
[horizon at least one](hyp:ht), [multiplier at least two](hyp:hb), [mean-square continuity](hyp:hMSC),
[iterative mean-square continuity](hyp:hIterMSC), [boundedness](hyp:hBound),
[boundedness outside a common null set](hyp:hCommon), and [the critical-radius bound](hyp:hComplexity),
[there is a positive event constant uniform over confidence budgets, balancing constants,
source exponents, and oracle accuracies: calibrated budgets strictly between zero and
one, positive balancing constant and source exponent, range, realizability and closeness,
attained ordinary and iterative minima, and measurable localized processes yield, at
every positive sample size, three measurable component events per iteration and grid
index, each with failure probability at most a third of the per-grid allocation, whose
intersection is measurable, has probability at least one minus the budget, and carries
the iterative TRAE concentration certificate](goal). -/
lemma iter_trae_concentration_event_uniform_allocation
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : ScalarLipschitzLocalizedConcentration V P sample split)
    (ρ B b : ℝ) (t : ℕ) (baseδ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : GridDomain ρ) (ht : 1 ≤ t) (hb : 2 ≤ b)
    (hMSC : MeanSquareContinuity V) (hIterMSC : IterMeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ Cevent > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
      ∀ (c β : ℝ) (δ : ℕ → ℝ), 0 < c → 0 < β →
      RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
      IterRealizableTRAE V ρ c b β t δ →
      TRAEMinimaAttained V P sample split ρ candidate →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAELocalizedProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n →
      ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
        (∀ j k a, MeasurableSet (component j k a) ∧
          1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
        let E := iterTraeCommonEvent ρ n t component
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
        IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Cevent := by
  obtain ⟨C, hC, hevent⟩ := iter_trae_concentration_event_uniform_allocation_with_bounds
    V P sample split hBennett_of_gate hAnchored_of_gate hFixedSq_of_gate hNorm_of_gate
    ρ B b t baseδ tildeδ candidate iter hρ ht hb hMSC hIterMSC hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hScale c β δ hc hβ hRange hRealizable hClose hIterRealizable
    hMinima hIterMinima hProcesses n hn
  obtain ⟨component, hcomponent, hE, hpE, hcon, _hbounded⟩ :=
    hevent ξ hξ hScale c β δ hc hβ hRange hRealizable hClose hIterRealizable
      hMinima hIterMinima hProcesses n hn
  exact ⟨component, hcomponent, hE, hpE, hcon⟩

/-- Assume [localized TRAE concentration](hyp:hBennett_of_gate), [anchored localized
concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[scalar Lipschitz concentration](hyp:hNorm_of_gate), [an admissible grid ratio](hyp:hρ),
[a confidence budget strictly between zero and one](hyp:hξ), [horizon at least one](hyp:ht),
[multiplier at least two](hyp:hb), [mean-square continuity](hyp:hMSC),
[iterative mean-square continuity](hyp:hIterMSC), [boundedness](hyp:hBound),
[boundedness outside a common null set](hyp:hCommon), [the critical-radius bound](hyp:hComplexity),
and [base accuracy calibrated to the per-grid confidence allocation](hyp:hScale).
Then [one positive event constant works for every positive balancing constant and
source exponent and every oracle accuracy sequence: under range, realizability,
closeness, attained ordinary and iterative minima, and localized-process measurability,
each positive sample size admits three measurable component events per iteration and
grid index, each spending at most a third of the per-grid allocation, whose measurable
intersection has probability at least one minus the confidence budget and carries the
iterative TRAE concentration certificate](goal). -/
-- @node: iter_trae_concentration_event_uniform
lemma iter_trae_concentration_event_uniform
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : ScalarLipschitzLocalizedConcentration V P sample split)
    (ρ ξ B b : ℝ) (t : ℕ) (baseδ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : GridDomain ρ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (ht : 1 ≤ t) (hb : 2 ≤ b)
    (hMSC : MeanSquareContinuity V) (hIterMSC : IterMeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ)
    (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t)) :
    ∃ Cevent > 0, ∀ (c β : ℝ) (δ : ℕ → ℝ), 0 < c → 0 < β →
      RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
      IterRealizableTRAE V ρ c b β t δ →
      TRAEMinimaAttained V P sample split ρ candidate →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAELocalizedProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n →
      ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
        (∀ j k a, MeasurableSet (component j k a) ∧
          1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
        let E := iterTraeCommonEvent ρ n t component
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
        IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Cevent := by
  obtain ⟨C, hC, hevent⟩ := iter_trae_concentration_event_uniform_allocation
    V P sample split hBennett_of_gate hAnchored_of_gate hFixedSq_of_gate hNorm_of_gate
    ρ B b t baseδ tildeδ candidate iter
    hρ ht hb hMSC hIterMSC hBound hCommon hComplexity
  exact ⟨C, hC, hevent ξ hξ hScale⟩

end Papers.TsAdaptiveEstimationInference
