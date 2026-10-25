module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.TCommonDp
public import Papers.TsAdaptiveEstimationInference.Helpers.TikhonovOracle
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEUniformRates
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEUniformCalibration
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEConfidenceEvents
/-! Confidence-independent deterministic assembly for discrepancy-selected TRAE fits. -/
public section
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 600000
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- Assume [the grid ratio lies in $[1/2,1)$](hyp:hρ), [the range condition
holds](hyp:hRange), [the beta source condition holds with vector w₀](hyp:hSource),
[the minimum-norm solution is admissible](hyp:hRealizable), [projected residuals
are admissible critics](hyp:hClose), [the model classes obey the envelope bound
B](hyp:hBound) and [the same bound holds outside one common null set](hyp:hCommon),
[the candidate fits attain their grid minima](hyp:hMinima), [the accuracy
sequences satisfy deterministic calibration](hyp:hDeterministic), [squared
accuracy is at least reciprocal sample size](hyp:hFloor), and [the comparison
constant is positive](hyp:hCe). Then [one positive constant bounds the
discrepancy-selected fit's squared projected error by squared accuracy and its
squared structural error by accuracy raised to twice the truncated source
exponent divided by one plus that exponent, on every measurable event carrying
the comparison and discrepancy-envelope bounds, for all sufficiently large
sample sizes](goal). -/
lemma trae_selected_rate_of_comparisons
    (ρ B β : ℝ) (w₀ : V.Hbar.toSubmodule) (δ ν : ℕ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (hRealizable : H0MemHypothesisClass V) (hClose : ClosenessCondition V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hMinima : TRAEMinimaAttained V P sample split ρ candidate)
    (hDeterministic : CalibrationDeterministic δ ν)
    (hFloor : ∀ n : ℕ, 0 < n → 1 / (n : ℝ) ≤ δ n ^ 2)
    (Ce : ℝ) (hCe : 0 < Ce) :
    ∃ C > 0, ∀ n : ℕ, traeMinSampleSize B ≤ n →
      ∀ E : Set Ω, MeasurableSet E →
      TRAEComparisonsOn V P sample split δ n E Ce →
      TRAEDiscrepancyEnvelope V P sample split ρ β δ w₀ candidate n E Ce →
      ∀ ω ∈ E,
        ‖projCondExpOp V (candidate n (traeSelected V P sample split ρ δ candidate n ω) ω -
          minNormSolution V)‖ ^ 2 ≤ C * δ n ^ 2 ∧
        ‖candidate n (traeSelected V P sample split ρ δ candidate n ω) ω -
          minNormSolution V‖ ^ 2 ≤
            C * δ n ^ (2 * truncatedSource β / (1 + truncatedSource β)) := by
  obtain ⟨C, hC, hrates⟩ := trae_selected_rate_uniform V P sample split
    ρ B β w₀ candidate hρ hRange hSource hRealizable hClose hBound hCommon hMinima Ce hCe
  exact ⟨C, hC, hrates δ ν hDeterministic hFloor⟩

/-- If [the grid ratio lies in $[1/2,1)$](hyp:hρ), [the initial comparison
constant is positive](hyp:hCe), and [the baseline accuracy is nonnegative at
every positive sample size](hyp:hBase), then [there is a positive calibration
threshold, fixed before the source parameters, such that the range, source,
realizability, closeness, attainment and calibration conditions yield one
positive constant for both calibrated comparisons and a discrepancy envelope
on every event carrying the baseline comparisons, at every positive sample
size](goal). -/
lemma trae_discrepancy_of_comparisons
    (ρ : ℝ) (baseδ baseν : ℕ → ℝ) (Ce : ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hCe : 0 < Ce)
    (hBase : ∀ n : ℕ, 0 < n → 0 ≤ baseδ n) :
    ∃ required > 0, ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ) (κδ κν : ℝ),
      RangeCondition V → BetaSourceCondition V β w₀ →
      H0MemHypothesisClass V → ClosenessCondition V →
      TRAEMinimaAttained V P sample split ρ candidate →
      CalibratedValidBounds δ ν baseδ baseν κδ κν required →
      CalibrationDeterministic δ ν →
      ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ E : Set Ω,
        TRAEComparisonsOn V P sample split baseδ n E Ce →
        TRAEComparisonsOn V P sample split δ n E C ∧
        TRAEDiscrepancyEnvelope V P sample split ρ β δ w₀ candidate n E C := by
  obtain ⟨required, hrequired, hcalibrate⟩ := trae_discrepancy_uniform V P sample split
    ρ candidate hρ
  refine ⟨required Ce, hrequired Ce hCe, ?_⟩
  intro β w₀ δ ν κδ κν hRange hSource hRealizable hClose hMinima hInflation hDeterministic
  obtain ⟨C, hC, hcompare⟩ := hcalibrate β w₀ hRange hSource hRealizable hClose hMinima
  exact ⟨C, hC, hcompare Ce hCe baseδ baseν δ ν κδ κν hBase hInflation hDeterministic⟩

/-- Given [localized concentration for the adversarial loss](hyp:hBennett_of_gate),
[localized squared-norm comparisons](hyp:hNorm), and [a grid ratio in
$[1/2,1)$](hyp:hρ), [there is a positive calibration threshold, fixed before
the source parameters, such that the range, source, realizability, closeness,
continuity, boundedness, complexity, scale, attainment and calibration conditions
yield a single positive rate constant: at every sufficiently large sample size
whose allocated confidence lies strictly between zero and one, a measurable
event of probability at least one minus twice that allocation bounds the
discrepancy-selected fit's squared projected error by squared accuracy and its
squared structural error by accuracy raised to twice the truncated source
exponent divided by one plus that exponent](goal). -/
lemma trae_rate_events_at_allocation
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (ρ B : ℝ) (baseδ baseν : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (allocation : ℕ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hNorm : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    ∃ required > 0, ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ) (κδ κν : ℝ),
      RangeCondition V → BetaSourceCondition V β w₀ →
      H0MemHypothesisClass V → ClosenessCondition V →
      MeanSquareContinuity V → TRAEBoundedness V B → TRAECommonNullSetBoundedness V B →
      TRAECriticalRadiusBound V tildeδ →
      TRAEScaleCalibration baseδ tildeδ allocation →
      TRAEMinimaAttained V P sample split ρ candidate →
      CalibratedValidBounds δ ν baseδ baseν κδ κν required →
      CalibrationDeterministic δ ν →
      ∃ C > 0, ∀ n : ℕ, traeMinSampleSize B ≤ n →
        allocation n ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ E : Set Ω, MeasurableSet E ∧ 1 - 2 * allocation n ≤ P.real E ∧
          ∀ ω ∈ E,
            ‖projCondExpOp V (candidate n
              (traeSelected V P sample split ρ δ candidate n ω) ω -
                minNormSolution V)‖ ^ 2 ≤ C * δ n ^ 2 ∧
            ‖candidate n (traeSelected V P sample split ρ δ candidate n ω) ω -
              minNormSolution V‖ ^ 2 ≤
                C * δ n ^ (2 * truncatedSource β / (1 + truncatedSource β)) := by
  classical
  by_cases hSetup : RangeCondition V ∧ H0MemHypothesisClass V ∧ ClosenessCondition V ∧
      MeanSquareContinuity V ∧ TRAEBoundedness V B ∧ TRAECommonNullSetBoundedness V B ∧ TRAECriticalRadiusBound V tildeδ ∧
      TRAEScaleCalibration baseδ tildeδ allocation
  · obtain ⟨hr, hh0, hcl, hm, hb, hcb, hcx, hsc⟩ := hSetup
    obtain ⟨Ce, hCe, hevents⟩ := trae_common_event_at_allocation (hBennett_of_gate := hBennett_of_gate) V P sample split 
      B baseδ tildeδ allocation hNorm hr hh0 hcl hm hb hcb hcx hsc
    have hbase : ∀ n : ℕ, 0 < n → 0 ≤ baseδ n := by
      intro n hn
      exact (show 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) by positivity).trans
        ((le_max_right _ _).trans (hsc.1 n hn))
    obtain ⟨required, hrequired, hdiscrepancy⟩ := trae_discrepancy_of_comparisons
      V P sample split ρ baseδ baseν Ce candidate hρ hCe hbase
    refine ⟨required, hrequired, ?_⟩
    intro β w₀ δ ν κδ κν hRange hSource hRealizable hClose hMSC hBound hCommon
      hComplexity hScale hMinima hInflation hDeterministic
    obtain ⟨Cd, hCd, henvelope⟩ := hdiscrepancy β w₀ δ ν κδ κν
      hRange hSource hRealizable hClose hMinima hInflation hDeterministic
    have hFloor : ∀ n : ℕ, 0 < n → 1 / (n : ℝ) ≤ δ n ^ 2 :=
      trae_calibrated_square_floor baseδ δ tildeδ allocation ν baseν κδ κν required
        hScale hInflation
    obtain ⟨C, hC, hrates⟩ := trae_selected_rate_of_comparisons V P sample split
      ρ B β w₀ δ ν candidate hρ hRange hSource hRealizable hClose hBound hCommon hMinima
      hDeterministic hFloor Cd hCd
    refine ⟨C, hC, ?_⟩
    intro n hn hValid
    have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
    obtain ⟨E, hE, hp, hc⟩ := hevents n hn0 hValid
    obtain ⟨hc', he⟩ := henvelope n hn0 E hc
    exact ⟨E, hE, hp, hrates n hn E hE hc' he⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro β w₀ δ ν κδ κν hRange hSource hRealizable hClose hMSC hBound hCommon
      hComplexity hScale hMinima hInflation hDeterministic
    exact (hSetup ⟨hRange, hRealizable, hClose, hMSC, hBound, hCommon, hComplexity, hScale⟩).elim

end Papers.TsAdaptiveEstimationInference
