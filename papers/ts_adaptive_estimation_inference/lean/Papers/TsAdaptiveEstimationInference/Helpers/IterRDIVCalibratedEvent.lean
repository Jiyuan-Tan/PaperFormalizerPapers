module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVPilotStability
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVFinalCalibration
/-! The joint recursive fitting, pilot and calibration event for iterative RDIV.
The propagation sequence is chosen before the sampling experiment. Calibration
uses the remaining quarter budget and coherent versions of the actual fits.
-/
public section
set_option linter.style.longLine false
set_option linter.style.haveILetI false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]

/-- Given [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [Li's localized likelihood concentration](hyp:hLi),
[the RDIV model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [density bounds](hyp:hBounds), [the outcome
envelope B](hyp:hY), and [the hypothesis envelope B](hyp:hHyp), [there are a
propagation constant at least one and a positive calibration constant, chosen
before sampling, such that likelihood-selected densities, a bounded pilot with
its regression rate, measurable classes and likelihood processes, coherent
density, pilot and supremum versions, and valid critical-radius curves admit
an inflation threshold: for sufficiently inflated calibrated scales, positive
sample size, admissible grid segment and source scope, class-valued population
iterates, empirical iterates, and training-measurable class-valued final
candidates, one measurable event of probability at least one minus the failure
probability gives every positive iterate's recursive energy and squared-error
bounds and bounds final calibration error by C times nuisance scale times
projected error plus C times squared nuisance scale, uniformly on the grid](goal).

Construct recursive stability and final calibration on one event, retaining
exactly the population-only propagation coefficients of the fitting event. -/
-- @node: iter_rdiv_joint_stability_calibration_event
lemma iter_rdiv_joint_stability_calibration_event
    {pilotInputSupport : Set Z} (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ), ∃ C > (0 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ) (ρ : ℝ)
      (rawG rawH rawR : ℕ → ℝ → ℝ),
    PilotRegressionRate V P sample split rHat rawR →
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    RDIVLikelihoodProcessesMeasurable V G g₀ →
    RDIVSelectedDensityVersion V P sample split mu gHat →
    RDIVSelectedPilotVersion V P sample split rHat →
    PilotBounded V P rHat pilotInputSupport B →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    DensityCriticalRadiusBound V G g₀ rawG →
    HypothesisCriticalRadiusBound V mu G rawH ρ →
    RDIVRadiusFloor rawG rawH ρ →
    ∃ required ≥ (1 : ℝ), ∀ (ξ : ℝ) (t : ℕ)
      (δ ν baseδ baseν : ℕ → ℝ) (κδ κν : ℝ),
    ρ ∈ Set.Ico (1 / 2 : ℝ) 1 → ξ ∈ Set.Ioo (0 : ℝ) 1 →
    RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t →
    CalibratedValidBounds δ ν baseδ baseν κδ κν required →
    ∀ (n : ℕ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam) (iter : ℕ → ℝ → Ω → V.Hbar.toSubmodule),
    0 < n →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment →
      IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
        (primalEmpDistanceSq V P sample split n) (fun j => iter j lam) t lam) →
    (∀ lam ∈ regGrid ρ n, ∀ ω, iter t lam ω ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, @Measurable Ω V.Hbar.toSubmodule
      (⨆ i ∈ split.pre n ∪ split.fit n,
        MeasurableSpace.comap (sample.Z i) inferInstance) (borel _) (iter t lam)) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment →
        ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ^ 2) ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter t lam ω) -
          ‖projCondExpOp V (iter t lam ω - minNormSolution V)‖ ^ 2| ≤
          C * ν n * ‖projCondExpOp V (iter t lam ω - minNormSolution V)‖ + C * ν n ^ 2) := by
  obtain ⟨D, hD, _, _, hfit⟩ := iter_rdiv_pilot_fitting_stability_event V hFix hSq hLi
    mu G g₀ support B c₀ CG hIV hRange hDensity hBounds hY hHyp
  refine ⟨D, hD, 16 * (4 * B + 8 * B ^ 2 + 3) + 9, by positivity [hY.1], ?_⟩
  intro P hProbability sample split gHat rHat ρ rawG rawH rawR hPilot hMLE
    hMeas hLikMeas hDensityVersion hPilotVersion hPilotBound hVersion hG hH hFloor
  letI : IsProbabilityMeasure P := hProbability
  obtain ⟨required, hrequired, hfit⟩ := hfit P hProbability sample split gHat rHat ρ
    rawG rawH rawR hPilot hMLE hMeas hLikMeas hDensityVersion hVersion hG hH hFloor
  refine ⟨required, hrequired, ?_⟩
  intro ξ t δ ν baseδ baseν κδ κν hρ hξ hScale hInflation n segment sourceRadius hSourceScope iter hn
    hdom hstar hEst hCandidate hCandidateMeas
  obtain ⟨F, hF, hpF, hgood⟩ := hfit ξ t δ ν baseδ baseν κδ κν hξ hScale
    hInflation n segment sourceRadius hSourceScope iter hn hdom hstar hEst
  obtain ⟨q, hq, hbound, hidentify⟩ := iter_rdiv_calibration_residual_version
    V P sample split mu G g₀ gHat rHat support B c₀ CG ρ n (iter t)
    hIV hDensity hBounds hHyp hY.1 hMLE hDensityVersion hPilotVersion
    hPilotBound hn hCandidate hCandidateMeas
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  have hRadius := iter_rdiv_calibration_radius_of_scales ρ ξ t n δ ν baseδ baseν
    rawG rawH rawR κδ κν required hρ hξ hn hScale hInflation
    (hG n hn _ hquarter).1.le (hPilot.2 n hn _ hquarter).1
  obtain ⟨E, hE, hEF, hpE, hcal⟩ := iter_rdiv_calibration_event_of_versions
    V P sample split mu G g₀ gHat rHat support B c₀ CG ρ ξ (ν n) n (iter t)
    hIV hRange hDensity hBounds hHyp hY.1 hξ hn hRadius F hF hpF
    (fun ω hω => by
      obtain ⟨hg, _, hr, _, hpilot, hop, _⟩ := hgood ω hω
      exact ⟨hg, hr, hpilot, fun lam hl =>
        ⟨hCandidate lam hl ω, hop _ (hCandidate lam hl ω)⟩⟩)
    q hq hbound hidentify
  refine ⟨E, hE, hpE, ?_, hcal⟩
  intro ω hω lam hl hs j hj hjt
  exact (hgood ω (hEF hω)).2.2.2.2.2.2.2 lam hl hs j hj hjt

/-- Assume [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [Li's localized likelihood concentration](hyp:hLi),
[the RDIV model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [density bounds](hyp:hBounds), [bounded
outcomes](hyp:hY), and [bounded hypotheses](hyp:hHyp). Then [a propagation
constant at least one and a positive calibration constant can be chosen before
sampling so that admissible likelihood selection, pilot regression rate and
bound, measurable processes, coherent versions, and critical-radius curves
admit an inflation threshold; for every factor L at least one, public scales
inflated to L times that threshold, admissible grid and source scope,
class-valued population iterates, empirical iterates, and measurable class-valued
final candidates yield one measurable event of probability at least one minus
the failure probability with recursive energy and squared-error bounds using
structural scale divided by L, and calibration error bounded by C times nuisance
scale divided by L times projected error plus C times the square of nuisance
scale divided by L](goal).

Retain the recursive and calibration estimates before public inflation.
A fixed factor `L` is removed from both public scales, and from both calibration
multipliers. Increasing the required public multiplier therefore gives actual
slack, rather than a fixed multiple of the public noise level. The event is the
single existing joint event, with its original total failure budget. -/
lemma iter_rdiv_joint_stability_calibration_event_preinflation
    {pilotInputSupport : Set Z} (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ), ∃ C > (0 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ) (ρ : ℝ)
      (rawG rawH rawR : ℕ → ℝ → ℝ),
    PilotRegressionRate V P sample split rHat rawR →
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    RDIVLikelihoodProcessesMeasurable V G g₀ →
    RDIVSelectedDensityVersion V P sample split mu gHat →
    RDIVSelectedPilotVersion V P sample split rHat →
    PilotBounded V P rHat pilotInputSupport B →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    DensityCriticalRadiusBound V G g₀ rawG →
    HypothesisCriticalRadiusBound V mu G rawH ρ →
    RDIVRadiusFloor rawG rawH ρ →
    ∃ required ≥ (1 : ℝ), ∀ (L : ℝ), 1 ≤ L → ∀ (ξ : ℝ) (t : ℕ)
      (δ ν baseδ baseν : ℕ → ℝ) (κδ κν : ℝ),
    ρ ∈ Set.Ico (1 / 2 : ℝ) 1 → ξ ∈ Set.Ioo (0 : ℝ) 1 →
    RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t →
    CalibratedValidBounds δ ν baseδ baseν κδ κν (L * required) →
    ∀ (n : ℕ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam) (iter : ℕ → ℝ → Ω → V.Hbar.toSubmodule),
    0 < n →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment →
      IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
        (primalEmpDistanceSq V P sample split n) (fun j => iter j lam) t lam) →
    (∀ lam ∈ regGrid ρ n, ∀ ω, iter t lam ω ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, @Measurable Ω V.Hbar.toSubmodule
      (⨆ i ∈ split.pre n ∪ split.fit n,
        MeasurableSpace.comap (sample.Z i) inferInstance) (borel _) (iter t lam)) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment →
        ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * (δ n / L) ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * (δ n / L) ^ 2 / lam ^ 2) ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter t lam ω) -
          ‖projCondExpOp V (iter t lam ω - minNormSolution V)‖ ^ 2| ≤
          C * (ν n / L) * ‖projCondExpOp V (iter t lam ω - minNormSolution V)‖ +
            C * (ν n / L) ^ 2) := by
  obtain ⟨D, hD, C, hC, hevent⟩ :=
    iter_rdiv_joint_stability_calibration_event (pilotInputSupport := pilotInputSupport) V
      hFix hSq hLi mu G g₀ support B c₀ CG hIV hRange hDensity hBounds hY hHyp
  refine ⟨D, hD, C, hC, ?_⟩
  intro P hProbability sample split gHat rHat ρ rawG rawH rawR
    hPilot hMLE hMeas hLikMeas hDensityVersion hPilotVersion hPilotBound
    hVersion hG hH hFloor
  obtain ⟨R, hR, hevent⟩ := hevent P hProbability sample split gHat rHat ρ
    rawG rawH rawR hPilot hMLE hMeas hLikMeas hDensityVersion hPilotVersion
    hPilotBound hVersion hG hH hFloor
  refine ⟨R, hR, ?_⟩
  intro L hL ξ t δ ν baseδ baseν κδ κν hρ hξ hScale hInflation
    n segment sourceRadius hSourceScope iter hn hdom hstar hEst hCandidate hCandidateMeas
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hκδ : R ≤ κδ / L := (le_div_iff₀ hLpos).2 (by
    simpa only [mul_comm] using hInflation.2.2.1)
  have hκν : R ≤ κν / L := (le_div_iff₀ hLpos).2 (by
    simpa only [mul_comm] using hInflation.2.2.2.1)
  have hReduced : CalibratedValidBounds (fun n => δ n / L) (fun n => ν n / L)
      baseδ baseν (κδ / L) (κν / L) R := by
    refine ⟨hR.trans hκδ, hR.trans hκν, hκδ, hκν, ?_, ?_⟩
    · intro n
      change δ n / L = _
      rw [hInflation.2.2.2.2.1 n]
      ring
    · intro n
      change ν n / L = _
      rw [hInflation.2.2.2.2.2 n]
      ring
  -- The public segment and the supplied iterates are passed verbatim. In
  -- particular neither the oracle radius nor the fitting penalty is rescaled.
  exact hevent ξ t (fun n => δ n / L) (fun n => ν n / L) baseδ baseν
    (κδ / L) (κν / L) hρ hξ hScale hReduced n segment sourceRadius hSourceScope iter hn hdom hstar
    hEst hCandidate hCandidateMeas

/-- Under [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [Li's localized likelihood concentration](hyp:hLi),
[the RDIV model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [density bounds](hyp:hBounds), [the outcome
envelope B](hyp:hY), and [the hypothesis envelope B](hyp:hHyp), [propagation
and calibration constants can be fixed before sampling, with a positive raw
comparison constant and an inflation threshold chosen for admissible
likelihood selections, bounded rate-controlled pilots, measurable processes,
coherent versions and critical-radius curves, so that sufficiently inflated
calibrated scales and admissible empirical iterates give a measurable event
of probability at least one minus the failure probability: it retains recursive
energy and squared-error bounds on the grid segment, final calibration error
at most C times nuisance scale times projected error plus C times squared
nuisance scale on the whole grid, density membership, raw preliminary density
and pilot comparisons, and raw quarter-grid centered fitting-deviation bounds
uniformly over hypotheses and positive iterations through the horizon](goal).

Calibration of the retained pilot/fitting event. The original coherent
residual construction, calibration quarter and subset proof are reused, so the
raw fitting and preliminary data survive on that very same event. -/
lemma iter_rdiv_joint_retained_calibration_event
    {pilotInputSupport : Set Z} (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ), ∃ C > (0 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ) (ρ : ℝ)
      (rawG rawH rawR : ℕ → ℝ → ℝ),
    PilotRegressionRate V P sample split rHat rawR →
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    RDIVLikelihoodProcessesMeasurable V G g₀ →
    RDIVSelectedDensityVersion V P sample split mu gHat →
    RDIVSelectedPilotVersion V P sample split rHat →
    PilotBounded V P rHat pilotInputSupport B →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    DensityCriticalRadiusBound V G g₀ rawG →
    HypothesisCriticalRadiusBound V mu G rawH ρ →
    RDIVRadiusFloor rawG rawH ρ →
    ∃ Ccmp > (0 : ℝ), ∃ required ≥ (1 : ℝ), ∀ (ξ : ℝ) (t : ℕ)
      (δ ν baseδ baseν : ℕ → ℝ) (κδ κν : ℝ),
    ρ ∈ Set.Ico (1 / 2 : ℝ) 1 → ξ ∈ Set.Ioo (0 : ℝ) 1 →
    RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t →
    CalibratedValidBounds δ ν baseδ baseν κδ κν required →
    ∀ (n : ℕ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam) (iter : ℕ → ℝ → Ω → V.Hbar.toSubmodule),
    0 < n →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment →
      IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
        (primalEmpDistanceSq V P sample split n) (fun j => iter j lam) t lam) →
    (∀ lam ∈ regGrid ρ n, ∀ ω, iter t lam ω ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, @Measurable Ω V.Hbar.toSubmodule
      (⨆ i ∈ split.pre n ∪ split.fit n,
        MeasurableSpace.comap (sample.Z i) inferInstance) (borel _) (iter t lam)) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment →
        ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ^ 2) ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter t lam ω) -
          ‖projCondExpOp V (iter t lam ω - minNormSolution V)‖ ^ 2| ≤
          C * ν n * ‖projCondExpOp V (iter t lam ω - minNormSolution V)‖ + C * ν n ^ 2) ∧
      (∀ ω ∈ E,
        gHat n ω ∈ G ∧
        RDIVPreliminaryOn V mu g₀ gHat rHat ξ rawG rawR n ω Ccmp ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          Ccmp * (rawH n (iterGridConfidence ρ ξ n t / 4) *
            ‖h - populationIterate V lam j‖ +
            rawH n (iterGridConfidence ρ ξ n t / 4) ^ 2)) := by
  obtain ⟨D, hD, _, _, hfit⟩ := iter_rdiv_pilot_fitting_retained_event V hFix hSq hLi
    mu G g₀ support B c₀ CG hIV hRange hDensity hBounds hY hHyp
  refine ⟨D, hD, 16 * (4 * B + 8 * B ^ 2 + 3) + 9, by positivity [hY.1], ?_⟩
  intro P hProbability sample split gHat rHat ρ rawG rawH rawR hPilot hMLE
    hMeas hLikMeas hDensityVersion hPilotVersion hPilotBound hVersion hG hH hFloor
  letI : IsProbabilityMeasure P := hProbability
  obtain ⟨Ccmp, hCcmp, required, hrequired, hfit⟩ := hfit P hProbability sample split gHat rHat ρ
    rawG rawH rawR hPilot hMLE hMeas hLikMeas hDensityVersion hVersion hG hH hFloor
  refine ⟨Ccmp, hCcmp, required, hrequired, ?_⟩
  intro ξ t δ ν baseδ baseν κδ κν hρ hξ hScale hInflation n segment sourceRadius hSourceScope iter hn
    hdom hstar hEst hCandidate hCandidateMeas
  obtain ⟨F, hF, hpF, hgood, hretained⟩ := hfit ξ t δ ν baseδ baseν κδ κν hξ hScale
    hInflation n segment sourceRadius hSourceScope iter hn hdom hstar hEst
  obtain ⟨q, hq, hbound, hidentify⟩ := iter_rdiv_calibration_residual_version
    V P sample split mu G g₀ gHat rHat support B c₀ CG ρ n (iter t)
    hIV hDensity hBounds hHyp hY.1 hMLE hDensityVersion hPilotVersion
    hPilotBound hn hCandidate hCandidateMeas
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  have hRadius := iter_rdiv_calibration_radius_of_scales ρ ξ t n δ ν baseδ baseν
    rawG rawH rawR κδ κν required hρ hξ hn hScale hInflation
    (hG n hn _ hquarter).1.le (hPilot.2 n hn _ hquarter).1
  obtain ⟨E, hE, hEF, hpE, hcal⟩ := iter_rdiv_calibration_event_of_versions
    V P sample split mu G g₀ gHat rHat support B c₀ CG ρ ξ (ν n) n (iter t)
    hIV hRange hDensity hBounds hHyp hY.1 hξ hn hRadius F hF hpF
    (fun ω hω => by
      obtain ⟨hg, _, hr, _, hpilot, hop, _⟩ := hgood ω hω
      exact ⟨hg, hr, hpilot, fun lam hl =>
        ⟨hCandidate lam hl ω, hop _ (hCandidate lam hl ω)⟩⟩)
    q hq hbound hidentify
  refine ⟨E, hE, hpE, ?_, hcal, fun ω hω => hretained ω (hEF hω)⟩
  intro ω hω lam hl hs j hj hjt
  exact (hgood ω (hEF hω)).2.2.2.2.2.2.2 lam hl hs j hj hjt
/-- Given [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [Li's localized likelihood concentration](hyp:hLi),
[the RDIV model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [density bounds](hyp:hBounds), [bounded
outcomes](hyp:hY), and [bounded hypotheses](hyp:hHyp), [there are propagation
and calibration constants fixed before sampling and, for admissible measurable
selections, bounded rate-controlled pilots, coherent versions and critical-radius
curves, a positive raw comparison constant and an inflation threshold such that
every factor L at least one and calibrated scales inflated to L times the
threshold yield, for admissible empirical iterates, one measurable event of
probability at least one minus the failure probability: recursive energy and
squared-error bounds use structural scale divided by L, final calibration error
uses nuisance scale divided by L, and density membership, raw preliminary
density and pilot comparisons, and uniform raw quarter-grid fixed-center
deviation bounds are retained on the same event](goal).

Pre-inflation estimates together with raw fixed-center increments and
preliminary comparisons. Only the recursive/calibration scales and their
multipliers are divided by L; raw curves, the supplied segment, penalty centers,
selected fits and total confidence budget are preserved verbatim. -/
lemma iter_rdiv_joint_retained_event_preinflation
    {pilotInputSupport : Set Z} (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ), ∃ C > (0 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ) (ρ : ℝ)
      (rawG rawH rawR : ℕ → ℝ → ℝ),
    PilotRegressionRate V P sample split rHat rawR →
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    RDIVLikelihoodProcessesMeasurable V G g₀ →
    RDIVSelectedDensityVersion V P sample split mu gHat →
    RDIVSelectedPilotVersion V P sample split rHat →
    PilotBounded V P rHat pilotInputSupport B →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    DensityCriticalRadiusBound V G g₀ rawG →
    HypothesisCriticalRadiusBound V mu G rawH ρ →
    RDIVRadiusFloor rawG rawH ρ →
    ∃ Ccmp > (0 : ℝ), ∃ required ≥ (1 : ℝ), ∀ (L : ℝ), 1 ≤ L → ∀ (ξ : ℝ) (t : ℕ)
      (δ ν baseδ baseν : ℕ → ℝ) (κδ κν : ℝ),
    ρ ∈ Set.Ico (1 / 2 : ℝ) 1 → ξ ∈ Set.Ioo (0 : ℝ) 1 →
    RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t →
    CalibratedValidBounds δ ν baseδ baseν κδ κν (L * required) →
    ∀ (n : ℕ) (segment : Set ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → oraclePoint ρ n sourceRadius ≤ lam) (iter : ℕ → ℝ → Ω → V.Hbar.toSubmodule),
    0 < n →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → lam ∈ Set.Ioc (0 : ℝ) 2) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
      populationIterate V lam j ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, lam ∈ segment →
      IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
        (primalEmpDistanceSq V P sample split n) (fun j => iter j lam) t lam) →
    (∀ lam ∈ regGrid ρ n, ∀ ω, iter t lam ω ∈ V.H) →
    (∀ lam ∈ regGrid ρ n, @Measurable Ω V.Hbar.toSubmodule
      (⨆ i ∈ split.pre n ∪ split.fit n,
        MeasurableSpace.comap (sample.Z i) inferInstance) (borel _) (iter t lam)) →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ segment →
        ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * (δ n / L) ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * (δ n / L) ^ 2 / lam ^ 2) ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter t lam ω) -
          ‖projCondExpOp V (iter t lam ω - minNormSolution V)‖ ^ 2| ≤
          C * (ν n / L) * ‖projCondExpOp V (iter t lam ω - minNormSolution V)‖ +
            C * (ν n / L) ^ 2) ∧
      (∀ ω ∈ E,
        gHat n ω ∈ G ∧
        RDIVPreliminaryOn V mu g₀ gHat rHat ξ rawG rawR n ω Ccmp ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          Ccmp * (rawH n (iterGridConfidence ρ ξ n t / 4) *
            ‖h - populationIterate V lam j‖ +
            rawH n (iterGridConfidence ρ ξ n t / 4) ^ 2)) := by
  obtain ⟨D, hD, C, hC, hevent⟩ :=
    iter_rdiv_joint_retained_calibration_event (pilotInputSupport := pilotInputSupport) V
      hFix hSq hLi mu G g₀ support B c₀ CG hIV hRange hDensity hBounds hY hHyp
  refine ⟨D, hD, C, hC, ?_⟩
  intro P hProbability sample split gHat rHat ρ rawG rawH rawR
    hPilot hMLE hMeas hLikMeas hDensityVersion hPilotVersion hPilotBound
    hVersion hG hH hFloor
  obtain ⟨Ccmp, hCcmp, R, hR, hevent⟩ := hevent P hProbability sample split gHat rHat ρ
    rawG rawH rawR hPilot hMLE hMeas hLikMeas hDensityVersion hPilotVersion
    hPilotBound hVersion hG hH hFloor
  refine ⟨Ccmp, hCcmp, R, hR, ?_⟩
  intro L hL ξ t δ ν baseδ baseν κδ κν hρ hξ hScale hInflation
    n segment sourceRadius hSourceScope iter hn hdom hstar hEst hCandidate hCandidateMeas
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hκδ : R ≤ κδ / L := (le_div_iff₀ hLpos).2 (by
    simpa only [mul_comm] using hInflation.2.2.1)
  have hκν : R ≤ κν / L := (le_div_iff₀ hLpos).2 (by
    simpa only [mul_comm] using hInflation.2.2.2.1)
  have hReduced : CalibratedValidBounds (fun n => δ n / L) (fun n => ν n / L)
      baseδ baseν (κδ / L) (κν / L) R := by
    refine ⟨hR.trans hκδ, hR.trans hκν, hκδ, hκν, ?_, ?_⟩
    · intro n
      change δ n / L = _
      rw [hInflation.2.2.2.2.1 n]
      ring
    · intro n
      change ν n / L = _
      rw [hInflation.2.2.2.2.2 n]
      ring
  -- The public segment and the supplied iterates are passed verbatim. In
  -- particular neither the oracle radius nor the fitting penalty is rescaled.
  exact hevent ξ t (fun n => δ n / L) (fun n => ν n / L) baseδ baseν
    (κδ / L) (κν / L) hρ hξ hScale hReduced n segment sourceRadius hSourceScope iter hn hdom hstar
    hEst hCandidate hCandidateMeas
end Papers.TsAdaptiveEstimationInference
