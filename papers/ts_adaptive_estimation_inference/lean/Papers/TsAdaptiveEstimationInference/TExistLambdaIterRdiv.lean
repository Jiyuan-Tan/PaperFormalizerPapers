module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVAcceptance
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVZeroSelection
/-! TExistLambdaIterRdiv for adaptive inverse problems. -/
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
-- The prescribed accuracy curves carry their original confidence-parametric
-- guarantees. Calibration evaluates these same curves at ξ and η_(n,t).
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (rawG rawH rawR tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
/-- With [fixed-center concentration](hyp:hFix_of_gate), [squared-loss concentration](hyp:hSq_of_gate),
[localized likelihood concentration](hyp:hLi_of_gate), [a grid factor between
one-half inclusive and one exclusive](hyp:hρ), [a failure level strictly between
zero and one](hyp:hξ), [at least one iteration](hyp:ht), [a valid IV density
model](hyp:hIV), [a propagation multiplier at least one](hyp:hprop), and [a
positive oracle scale](hyp:_hc), [a positive calibration threshold ensures that
the range and source conditions, solution and density
realizability, density bounds and the pilot rate,
bounded outcomes, hypotheses, and pilot,
measurable fitting and likelihood processes, the fitting
and fixed-center supremum versions,
the selected density and pilot versions,
density and hypothesis critical-radius bounds and their floor,
iteration scale calibration, attained one-step and iterative minima,
sufficient inflation and deterministic accuracy curves,
and likelihood-maximizing density estimates yield an iteration-times-logarithmic
fit bound and, at every eligible size, a measurable event of probability at least
one minus the failure level carrying iterative RDIV acceptance and its return alternatives](goal).

For the prescribed positive horizon, calibration uses the supplied curves
at ξ and η_(n,t) for the public curves rdivEvaluatedAccuracy rawG/H/R.
The conclusion constructs one measurable event for
each admissible n, carrying acceptance and the conditional zero-case branch.
The public curves are the raw bounds evaluated at the component quarter budgets,
under the recorded relabelling convention. No comparison between arbitrary
confidence curves is assumed; allocation and the joint event remain local proofs.
The full printed selection guarantee, without any supplied oracle-segment
condition. The fixed-penalty proof below constructs initial acceptance directly, using
the existing bk-owner-4 fixed-center version convention inherited from
iterative stability. At zero source every population comparator is zero;
the fixed-penalty event requires no oracle-segment condition. -/
theorem exist_lambda_iter_rdiv_without_oracle
    (hFix_of_gate : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq_of_gate : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi_of_gate : LiLocalizedConcentration V)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (ht : 1 ≤ t)
    (hIV : RDIVSetting V mu g₀)
    (hprop : 1 ≤ a) (_hc : 0 < c)
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
      (hFixedCenterVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ rawG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G rawH ρ) →
      (hRadiusFloor : RDIVRadiusFloor rawG rawH ρ) →
      (hScale : RDIVIterationScaleCalibration ρ ξ baseδ baseν
        (rdivEvaluatedAccuracy rawG) (rdivEvaluatedAccuracy rawH)
        (rdivEvaluatedAccuracy rawR) t) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      (∃ Clog > 0, ∀ n : ℕ, rdivMinSampleSize B ≤ n →
        (t * (terminalIndex ρ n + 1) : ℕ) ≤ Clog * t * Real.log n) ∧
      ∀ n : ℕ, rdivMinSampleSize B ≤ n →
        ∃ E : Set Ω,
        IterRDIVSelectionOnEvent
          (V := V) (P := P) (sample := sample) (split := split) (ρ := ρ) (ξ := ξ)
          (δ := δ) (ν := ν) (mu := mu) (gHat := gHat) (rHat := rHat)
          (iter := iter) (a := a) (t := t)
          (fun _ => E) n := by
  classical
  -- These fixed inputs precede the source parameters and the calibrated curves.
  -- Selecting their witnesses here preserves the threshold's quantifier order.
  by_cases hSetup : RangeCondition V ∧ H0MemHypothesisClass V ∧
      DensityRealizable V mu G g₀ ∧ DensityBounds G g₀ support c₀ CG ∧
      PilotRegressionRate V P sample split rHat rawR ∧ OutcomeBounded V B ∧
      HypothesisClassBounded V support B ∧ PilotBounded V P rHat pilotInputSupport B ∧
      RDIVClassesMeasurable V P sample split mu G g₀ gHat ∧
      RDIVLikelihoodProcessesMeasurable V G g₀ ∧
      RDIVFittingSupremumVersion V P sample split mu gHat ρ ∧
      IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ ∧
      RDIVSelectedDensityVersion V P sample split mu gHat ∧
      RDIVSelectedPilotVersion V P sample split rHat ∧
      DensityCriticalRadiusBound V G g₀ rawG ∧ HypothesisCriticalRadiusBound V mu G rawH ρ ∧
      RDIVRadiusFloor rawG rawH ρ ∧
      RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t ∧
      MLEMaximizerSelected V P sample split G gHat
  · obtain ⟨hRange, hRealizable, hDensity, hBounds, hPilot, hY, hHyp, hPilotBound,
      hMeas, hLik, hFitting, hFixedCenter, hDV, hPV, hG, hH, hFloor, hScale, hMLE⟩ := hSetup
    obtain ⟨R, hR, hevent⟩ := iter_rdiv_zero_initial_acceptance_event
      (pilotInputSupport := pilotInputSupport) V hFix_of_gate hSq_of_gate hLi_of_gate
      mu G g₀ support B c₀ CG ρ ξ a t hIV hRange hRealizable hDensity hBounds hY hHyp
      P sample split gHat rHat rawG rawH rawR baseδ baseν hρ hξ hprop ht
      hPilot hMLE hMeas hLik hDV hPV hPilotBound hFixedCenter hG hH hFloor hScale
    refine ⟨R, zero_lt_one.trans_le hR, ?_⟩
    intro κ₀ β w₀ δ ν hRange' hSource hRealizable' hDensity' hBounds'
      hPilot' hY' hHyp' hPilotBound' hMeas' hLik' hFittingVersion hFixedCenterVersion hDV' hPV'
      hG' hH' hFloor' hScale' hMinima hInflation hNonneg hIterMinima hMLE'
    constructor
    · obtain ⟨Clog, hClog, hlog⟩ := terminalIndex_log_bound ρ hρ
      refine ⟨Clog, hClog, ?_⟩
      intro n hn
      have hb := mul_le_mul_of_nonneg_left
        (hlog n ((le_max_left _ _).trans hn)) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
      simpa only [Nat.cast_mul, mul_left_comm, mul_assoc] using hb
    · intro n hn
      have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2)
        ((le_max_left _ _).trans hn)
      obtain ⟨E, hE, hpE, hzero⟩ := hevent (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2
        δ ν hInflation hNonneg iter hIterMinima n hn0
      obtain ⟨S, hS, hSae, hbound⟩ := iter_rdiv_calibration_bounded_event
        (pilotInputSupport := pilotInputSupport) V P sample split mu G g₀ gHat rHat
        support B c₀ CG ρ rawR t iter hIV hDensity hBounds hHyp hY.1
        hPilot hPilotBound hMLE hDV hPV hIterMinima ht n hn0
      have hlog := iter_rdiv_calibrated_public_log_floor V
        mu G g₀ ρ ξ hξ rawG rawH rawR δ ν baseδ baseν
        (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 R t hG hH hScale' hInflation n hn0
      obtain ⟨hES, hpES, hsearch⟩ := iter_rdiv_acceptance_event_intersection V P sample split
        mu gHat rHat ρ ξ B a (δ n) (ν n) t n iter hρ hξ hprop hn hlog
        E S hE hS hpE hSae hbound
      refine ⟨E ∩ S, hES, hpES, ?_⟩
      intro ω hω
      obtain ⟨haccept, hcount, hcases⟩ := hsearch ω hω
      refine ⟨haccept, hcount, ?_, hcases⟩
      intro hz
      have hi := hzero ω hω.1 hz
      have hex : ∃ k ≤ terminalIndex ρ n,
          rdivCalibrationStat V P sample split mu gHat rHat n ω
            (iter n t (gridValue ρ k) ω) ≤
            3 / 2 * iterRdivNoiseLevel a (δ n) (ν n) (gridValue ρ k) := by
        refine ⟨0, Nat.zero_le _, ?_⟩
        simpa only [gridValue, pow_zero, mul_one] using hi
      change discrepancyIndex ρ n _ _ = 0
      unfold discrepancyIndex
      rw [dif_pos hex]
      exact Nat.le_zero.mp (Nat.find_min' hex (by
        simpa only [gridValue, pow_zero, mul_one] using And.intro (Nat.zero_le _) hi))
  · refine ⟨1, zero_lt_one, ?_⟩
    intro κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hBounds
      hPilot hY hHyp hPilotBound hMeas hLik hFittingVersion hFixedCenterVersion hDV hPV
      hG hH hFloor hScale hMinima hInflation hNonneg hIterMinima hMLE
    exact (hSetup ⟨hRange, hRealizable, hDensity, hBounds, hPilot, hY, hHyp,
      hPilotBound, hMeas, hLik, hFittingVersion, hFixedCenterVersion, hDV, hPV, hG, hH, hFloor, hScale, hMLE⟩).elim

-- @node: prop:exist-lambda-iter-rdiv
/-- Assuming [fixed-center concentration](hyp:hFix_of_gate), [squared-loss concentration](hyp:hSq_of_gate),
[localized likelihood concentration](hyp:hLi_of_gate), [a grid factor between
one-half inclusive and one exclusive](hyp:hρ), [a failure level strictly between
zero and one](hyp:hξ), [at least one iteration](hyp:ht), [a valid IV density
model](hyp:hIV), [a propagation multiplier at least one](hyp:hprop), and [a
positive oracle scale](hyp:hc), [there is a positive calibration threshold such
that the range and source conditions, solution and density
realizability, density bounds and the pilot rate,
bounded outcomes, hypotheses, and pilot,
measurable fitting and likelihood processes, the fitting
and fixed-center supremum versions,
selected density and pilot versions,
density and hypothesis critical-radius bounds and their floor,
iteration scale calibration, attained one-step and iterative minima,
sufficient inflation and deterministic accuracy curves,
and likelihood-maximizing density estimates imply an iteration-times-logarithmic
bound on fits and high-probability iterative RDIV selection on a measurable
event at every eligible sample size](goal). -/
theorem exist_lambda_iter_rdiv
    (hFix_of_gate : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq_of_gate : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi_of_gate : LiLocalizedConcentration V)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (ht : 1 ≤ t)
    (hIV : RDIVSetting V mu g₀)
    (hprop : 1 ≤ a) (hc : 0 < c)
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
      (hFixedCenterVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ rawG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G rawH ρ) →
      (hRadiusFloor : RDIVRadiusFloor rawG rawH ρ) →
      (hScale : RDIVIterationScaleCalibration ρ ξ baseδ baseν
        (rdivEvaluatedAccuracy rawG) (rdivEvaluatedAccuracy rawH)
        (rdivEvaluatedAccuracy rawR) t) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      (∃ Clog > 0, ∀ n : ℕ, rdivMinSampleSize B ≤ n →
        (t * (terminalIndex ρ n + 1) : ℕ) ≤ Clog * t * Real.log n) ∧
      ∀ n : ℕ, rdivMinSampleSize B ≤ n →
        ∃ E : Set Ω,
        IterRDIVSelectionOnEvent
          (V := V) (P := P) (sample := sample) (split := split) (ρ := ρ) (ξ := ξ)
          (δ := δ) (ν := ν) (mu := mu) (gHat := gHat) (rHat := rHat)
          (iter := iter) (a := a) (t := t)
          (fun _ => E) n := by
  obtain ⟨required, hrequired, hselection⟩ :=
    exist_lambda_iter_rdiv_without_oracle
      (V := V) (P := P) (sample := sample) (split := split)
      (ρ := ρ) (ξ := ξ) (B := B) (baseδ := baseδ) (baseν := baseν)
      (rawG := rawG) (rawH := rawH) (rawR := rawR)
      (c₀ := c₀) (CG := CG) (Cm := Cm) (mu := mu) (G := G) (g₀ := g₀)
      (gHat := gHat) (rHat := rHat) (support := support) (candidate := candidate)
      (iter := iter) (a := a) (c := c) (t := t)
      hFix_of_gate hSq_of_gate hLi_of_gate hρ hξ ht hIV hprop hc
  refine ⟨required, hrequired, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro β w₀ δ ν hRange hSource hRealizable hDensity hDensityBounds
    hPilotRate hOutcome hHypBound hPilotBound hSupMeas hLikMeas hFittingVersion
    hFixedCenterVersion
    hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius
    hRadiusFloor hScale hMinima hInflation hDeterministic hIterMinima hMLE
  obtain ⟨hcount, hevent⟩ := hselection κ₀ β w₀ δ ν hRange hSource hRealizable
    hDensity hDensityBounds hPilotRate hOutcome hHypBound hPilotBound hSupMeas hLikMeas
    hFittingVersion hFixedCenterVersion hSelectedDensityVersion hSelectedPilotVersion hDensityRadius
    hHypRadius hRadiusFloor hScale hMinima hInflation hDeterministic
    hIterMinima hMLE
  exact ⟨hcount, hevent⟩


end Papers.TsAdaptiveEstimationInference
