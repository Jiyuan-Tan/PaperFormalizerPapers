module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.TCommonDp
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRateEvents
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRateComparisons
/-! TIterRdivRate for adaptive inverse problems. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  {pilotInputSupport : Set 𝒵}
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
-- The prescribed accuracy curves retain their original confidence domains.
-- Calibration uses these same curves at ξ and the iteration-grid allocation.
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (rawG rawH rawR tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
/-- Assuming [fixed-center concentration](hyp:hFix_of_gate), [squared-loss concentration](hyp:hSq_of_gate),
[localized likelihood concentration](hyp:hLi_of_gate), [an admissible grid factor](hyp:hρ),
[a failure level strictly between zero and one](hyp:hξ), [a positive iteration
count](hyp:ht), [a valid IV density model](hyp:hIV), and [a propagation multiplier
at least one](hyp:hprop), [there is a positive calibration threshold such that
the range and source conditions, solution and density
realizability, density bounds and the pilot rate,
bounded outcomes, hypotheses, and pilot,
measurable fitting and likelihood processes, the fitting,
selected density, selected pilot, and fixed-center versions,
density and hypothesis radius bounds and their floor,
iteration scale calibration, attained fitting minima,
sufficient inflation, and deterministic accuracy curves
give a positive upper bound on the oracle scale for which iterative realizability,
attained iterative minima, and likelihood-maximizing density
estimates yield uniform high-probability iterative RDIV rates at all
eligible sizes, eventual discrepancy and oracle rates, and, under comparable
noise and sufficient qualification, the simplified estimation and prediction rates](goal).

Derive eventual oracle-grid existence and apply common_dp on the oracle segment.
Enlarge the constant over the finite prefix using the recorded boundedness and positive rate scales;
no oracle-existence hypothesis is added to this rate theorem.
The prescribed curves carry the density, hypothesis and pilot guarantees on their
original domains. RDIVIterationScaleCalibration uses rdivEvaluatedAccuracy of
those curves: density/pilot at ξ/4 and hypothesis at iterGridConfidence ρ ξ n t/4,
with the fixed public logarithmic floor. The public δ and ν are unchanged.
Confidence allocation and the common-event construction remain local proof
obligations; no comparison with quarter-budget curve values is assumed. -/
-- @node: thm:iter-rdiv-rate
theorem iter_rdiv_rate
    (hFix_of_gate : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq_of_gate : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi_of_gate : LiLocalizedConcentration V)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (ht : 1 ≤ t)
    (hIV : RDIVSetting V mu g₀)
    (hprop : 1 ≤ a)
    : ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable V mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hPilotRate : PilotRegressionRate V P sample split rHat rawR) →
      (hOutcome : OutcomeBounded V B) →
      (hHypBound : HypothesisClassBounded V support B) →
      (hPilotBound : PilotBounded V P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hFixedCenterVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ rawG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G rawH ρ) →
      (hRadiusFloor : RDIVRadiusFloor rawG rawH ρ) →
      (hScale : RDIVIterationScaleCalibration ρ ξ baseδ baseν
        (rdivEvaluatedAccuracy rawG) (rdivEvaluatedAccuracy rawH)
        (rdivEvaluatedAccuracy rawR) t) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      ∃ cmax > 0, ∀ c ∈ Set.Ioc (0 : ℝ) cmax,
      (hIterRealizable : IterRealizableRDIV V ρ c a β t δ ν) →
      (hIterMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      (∃ C > 0, ∀ n : ℕ, rdivMinSampleSize B ≤ n →
        IterRDIVRateOnEvent
          (V := V) (P := P) (sample := sample) (split := split) (ρ := ρ) (ξ := ξ)
          (β := β) (δ := δ) (ν := ν) (mu := mu) (gHat := gHat) (rHat := rHat) (iter := iter) (a := a) (t := t)
          n C) ∧
      (∃ C > 0, ∀ᶠ n in atTop, ∃ E : Set Ω,
        IterRDIVDiscrepancyEnvelope V P sample split mu gHat rHat
          ρ ξ c a β t δ ν w₀ iter n E 3 ∧ ∀ ω ∈ E,
        ‖projCondExpOp V (iter n t
          (iterRdivSelected V P sample split mu gHat rHat ρ a t δ ν iter n ω) ω -
            minNormSolution V)‖ ^ 2 ≤ C * iterRdivErrorScale β a (δ n) (ν n) t ∧
        ‖iter n t (iterRdivSelected V P sample split mu gHat rHat ρ a t δ ν iter n ω) ω -
          minNormSolution V‖ ^ 2 ≤ C *
          ((a * δ n ^ 2) ^ ((qualificationExponent β t - 1) /
            (qualificationExponent β t + 1)) +
            iterRdivErrorScale β a (δ n) (ν n) t ^ (β / (β + 1)))) ∧
      (ComparableNoise δ ν ∧ IterQualificationRDIV β t → ∃ Cs > 0, ∀ᶠ n in atTop, ∃ E : Set Ω,
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
          ‖iter n t (iterRdivSelected V P sample split mu gHat rHat ρ a t δ ν iter n ω) ω - minNormSolution V‖ ^ 2 ≤ Cs * δ n ^ (2 * β / (β + 2)) ∧
          ‖projCondExpOp V (iter n t (iterRdivSelected V P sample split mu gHat rHat ρ a t δ ν iter n ω) ω - minNormSolution V)‖ ^ 2 ≤ Cs * δ n ^ (2 * (β + 1) / (β + 2))) := by
  -- Construct eventual oracle-event rates, extend them over the bounded finite
  -- prefix, then simplify the powers on the same events under qualification.
  have htail :
    ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable V mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hPilotRate : PilotRegressionRate V P sample split rHat rawR) →
      (hOutcome : OutcomeBounded V B) →
      (hHypBound : HypothesisClassBounded V support B) →
      (hPilotBound : PilotBounded V P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hFixedCenterVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ rawG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G rawH ρ) →
      (hRadiusFloor : RDIVRadiusFloor rawG rawH ρ) →
      (hScale : RDIVIterationScaleCalibration ρ ξ baseδ baseν
        (rdivEvaluatedAccuracy rawG) (rdivEvaluatedAccuracy rawH)
        (rdivEvaluatedAccuracy rawR) t) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      ∃ cmax > 0, ∀ c ∈ Set.Ioc (0 : ℝ) cmax,
      (hIterRealizable : IterRealizableRDIV V ρ c a β t δ ν) →
      (hIterMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      ∃ C > 0, ∀ᶠ n in atTop, rdivMinSampleSize B ≤ n → ∃ E : Set Ω,
        IterRDIVDiscrepancyEnvelope V P sample split mu gHat rHat
          ρ ξ c a β t δ ν w₀ iter n E 3 ∧ ∀ ω ∈ E,
        ‖projCondExpOp V (iter n t
          (iterRdivSelected V P sample split mu gHat rHat ρ a t δ ν iter n ω) ω -
            minNormSolution V)‖ ^ 2 ≤ C * iterRdivErrorScale β a (δ n) (ν n) t ∧
        ‖iter n t (iterRdivSelected V P sample split mu gHat rHat ρ a t δ ν iter n ω) ω -
          minNormSolution V‖ ^ 2 ≤ C *
          ((a * δ n ^ 2) ^ ((qualificationExponent β t - 1) /
            (qualificationExponent β t + 1)) +
            iterRdivErrorScale β a (δ n) (ν n) t ^ (β / (β + 1))) := by
    classical
    -- All these properties concern the fixed experiment and population, so
    -- their witnesses can be selected before the source and inflated scales.
    by_cases hInputs : RangeCondition V ∧ DensityRealizable V mu G g₀ ∧
        DensityBounds G g₀ support c₀ CG ∧
        PilotRegressionRate V P sample split rHat rawR ∧ OutcomeBounded V B ∧
        HypothesisClassBounded V support B ∧ PilotBounded V P rHat pilotInputSupport B ∧
        RDIVClassesMeasurable V P sample split mu G g₀ gHat ∧
        RDIVLikelihoodProcessesMeasurable V G g₀ ∧
        RDIVSelectedDensityVersion V P sample split mu gHat ∧
        RDIVSelectedPilotVersion V P sample split rHat ∧
        IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ ∧
        DensityCriticalRadiusBound V G g₀ rawG ∧
        HypothesisCriticalRadiusBound V mu G rawH ρ ∧ RDIVRadiusFloor rawG rawH ρ ∧
        RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t ∧
        MLEMaximizerSelected V P sample split G gHat
    · obtain ⟨hRange, hDensity, hBounds, hPilot, hY, hHyp, hPilotBound,
        hMeas, hLik, hDV, hPV, hVersion, hG, hH, hFloor, hScale, hMLE⟩ := hInputs
      obtain ⟨R, hR, hrate⟩ := iter_rdiv_eventual_rate_from_joint_event
        (pilotInputSupport := pilotInputSupport) V hFix_of_gate hSq_of_gate hLi_of_gate
        mu G g₀ support B c₀ CG ρ ξ a t hIV hRange hDensity hBounds hY hHyp
        P sample split gHat rHat rawG rawH rawR baseδ baseν hρ hξ hprop ht
        hPilot hMLE hMeas hLik hDV hPV hPilotBound hVersion hG hH hFloor hScale
      refine ⟨R, lt_of_lt_of_le zero_lt_one hR, ?_⟩
      intro κ₀ β w₀ δ ν _ hSource _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hInflation hNonneg
      obtain ⟨cmax, hcmax, hrate⟩ := hrate (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2
        β w₀ δ ν hInflation hNonneg hSource
      refine ⟨cmax, hcmax, ?_⟩
      intro c hc hRealizable hMinima _
      obtain ⟨C, hC, hrate⟩ := hrate c hc iter hRealizable hMinima
      refine ⟨C, hC, hrate.mono ?_⟩
      intro n hn _
      simpa only [IterRDIVRateOnEvent, iterRdivSelected] using hn
    · refine ⟨1, zero_lt_one, ?_⟩
      intro κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hBounds hPilot hY hHyp
        hPilotBound hMeas hLik hFV hDV hPV hVersion hG hH hFloor hScale hMinima
        hInflation hNonneg
      refine ⟨1, zero_lt_one, ?_⟩
      intro c hc hIterRealizable hIterMinima hMLE
      exact (hInputs ⟨hRange, hDensity, hBounds, hPilot, hY, hHyp, hPilotBound,
        hMeas, hLik, hDV, hPV, hVersion, hG, hH, hFloor, hScale, hMLE⟩).elim
  obtain ⟨required, hrequired, htail⟩ := htail
  refine ⟨required, hrequired, ?_⟩
  intro κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hDensityBounds
    hPilotRate hOutcome hHypBound hPilotBound hSupMeas hLikMeas hFittingVersion
    hSelectedDensityVersion hSelectedPilotVersion hFixedCenterVersion hDensityRadius
    hHypRadius hRadiusFloor hScale hMinima hInflation hDeterministic
  obtain ⟨cmax, hcmax, htail⟩ := htail κ₀ β w₀ δ ν hRange hSource
    hRealizable hDensity hDensityBounds hPilotRate hOutcome hHypBound hPilotBound
    hSupMeas hLikMeas hFittingVersion hSelectedDensityVersion hSelectedPilotVersion
    hFixedCenterVersion hDensityRadius hHypRadius hRadiusFloor hScale hMinima
    hInflation hDeterministic
  refine ⟨cmax, hcmax, ?_⟩
  intro c hc hIterRealizable hIterMinima hMLE
  have htailEnvelope := htail c hc hIterRealizable hIterMinima hMLE
  have hrateTail : ∃ C > 0, ∀ᶠ n in atTop, rdivMinSampleSize B ≤ n →
      IterRDIVRateOnEvent V P sample split ρ ξ β a δ ν mu gHat rHat iter t n C := by
    obtain ⟨C, hC, htailN⟩ := htailEnvelope
    refine ⟨C, hC, htailN.mono ?_⟩
    intro n hn hsize
    obtain ⟨E, henv, hrates⟩ := hn hsize
    exact ⟨E, henv.1, henv.2.1, hrates⟩
  have hScaleRaw : RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t := hScale
  obtain ⟨K, hK, hradii⟩ := iter_rdiv_calibrated_radii V mu G g₀ ρ
    rawG rawH rawR hDensityRadius hHypRadius hRadiusFloor
  have hδpos (n : ℕ) (hn : rdivMinSampleSize B ≤ n) : 0 < δ n := by
    have hn0 : 0 < n := lt_of_lt_of_le (by
      unfold rdivMinSampleSize
      exact lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) (le_max_left _ _)) hn
    exact (hradii ξ t δ ν baseδ baseν (κ₀ B c₀ CG Cm).1
      (κ₀ B c₀ CG Cm).2 required hξ hScaleRaw hInflation n hn0).1
  have hrate := iter_rdiv_selected_rate_of_eventual V P sample split mu G g₀
    gHat rHat support B c₀ CG ρ ξ a β t δ ν iter hIV hDensity hDensityBounds
    hHypBound hOutcome.1 hRealizable ht hIterMinima
    (lt_of_lt_of_le zero_lt_one hprop) hξ.1.le
    (fun n hn => (hδpos n hn).ne') hrateTail
  refine ⟨hrate, ?_, ?_⟩
  · obtain ⟨C, hC, htailN⟩ := htailEnvelope
    refine ⟨C, hC, ?_⟩
    filter_upwards [htailN, eventually_ge_atTop (rdivMinSampleSize B)] with n hn hsize
    exact hn hsize
  intro hqualified
  have hlim := (iter_rdiv_inflated_scales_tendsto δ ν baseδ baseν
    (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required
    hInflation hDeterministic hScale.2.2).1
  apply iter_rdiv_qualified_rate_events P (projCondExpOp V) (minNormSolution V)
    (fun n ω => iter n t
      (iterRdivSelected V P sample split mu gHat rHat ρ a t δ ν iter n ω) ω)
    ξ a β t δ ν (by linarith only [hprop]) hSource.1
    (Eventually.of_forall hDeterministic.1) (Eventually.of_forall hDeterministic.2)
    hlim hqualified.1 hqualified.2
  obtain ⟨C, hC, hrate⟩ := hrate
  exact ⟨C, hC, (eventually_ge_atTop (rdivMinSampleSize B)).mono
    (fun n hn => hrate n hn)⟩


end Papers.TsAdaptiveEstimationInference
