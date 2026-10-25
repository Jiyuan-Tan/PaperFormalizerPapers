module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVAcceptance
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVDensityReduction
public import Papers.TsAdaptiveEstimationInference.TRdivDiscrepancyBound
/-! TExistLambdaDeepiv for adaptive inverse problems. -/
public section
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  {pilotInputSupport : Set 𝒵}
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
-- rawG/rawH/rawR are the confidence-parametric input bounds. The hScale
-- premise explicitly instantiates their evaluated public curves; the public
-- δ and ν in every conclusion are calibrated from exactly that instantiation.
-- The public log floor is rdivPublicLogScale ρ ξ; component-budget floors
-- are handled locally through the fixed calibration multipliers.
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (rawG rawH rawR tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
/-- Given [localized likelihood concentration](hyp:hLi_of_gate), [localized vector
concentration](hyp:hVector_of_gate), [a grid factor between one-half inclusive and
one exclusive](hyp:hρ), [a failure level strictly between zero and one](hyp:hξ),
and [a valid instrumental-variable density model](hyp:hIV), [a positive calibration
threshold ensures that the range condition, the source condition,
solution realizability, density realizability,
density bounds, the pilot rate,
bounded outcomes, bounded hypotheses, a bounded
pilot, measurable fitting classes, measurable
likelihood processes, the fitting supremum version,
the selected density version, the selected pilot
version, density critical-radius control,
hypothesis critical-radius control, the radius floor,
public scale calibration, attained fitting minima,
sufficient inflation, deterministic accuracy curves,
and likelihood-maximizing density estimates imply a logarithmic grid-size
bound and, at every eligible size, one measurable event with probability at least
one minus the failure level carrying the comparisons, discrepancy envelope,
acceptance, fit-count bound, initial selection for a zero solution, and the
initial-or-adjacent return alternative](goal).

One-step RDIV calibrates the explicitly defined public accuracy curves at
`ξ` and `gridConfidence ρ ξ n`, exactly as in `RDIVPublicScaleCalibration`.
Following main.tex:258 and appendices.tex:126–129, these public curves are
defined by evaluating the raw bounds at the allocated component budgets before
relabelling: `ξ / 4` for density and pilot estimation and
`gridConfidence ρ ξ n / 4` for fitting-grid comparisons. The primitive rate
and critical-radius hypotheses retain their original raw confidence domains.
The inflated public `δ` and `ν` appear unchanged in the envelope and search
thresholds, jointly on the event certified by `RDIVComparisonsOn`.
The public base fitting and calibration sums are computed by
`rdivFittingBaseScale` and `rdivCalibrationBaseScale`, with horizon one;
they evaluate raw curves rather than compare curves at distinct confidences. -/
-- @node: prop:exist-lambda-deepiv
theorem exist_lambda_deepiv
    (hLi_of_gate : LiLocalizedConcentration V)
    (hVector_of_gate : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V mu g₀)
    : let publicG := rdivEvaluatedAccuracy rawG; -- @realizes \delta_{n,\mathcal G}(public density radius after component-budget evaluation)
      let publicH := rdivEvaluatedAccuracy rawH; -- @realizes \delta_{n,\mathcal H}(public hypothesis radius after component-budget evaluation)
      let publicR := rdivEvaluatedAccuracy rawR; -- @realizes \delta_{n,r}(public pilot accuracy after component-budget evaluation)
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
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ rawG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G rawH ρ) →
      (hRadiusFloor : RDIVRadiusFloor rawG rawH ρ) →
      (hScale : RDIVPublicScaleCalibration ρ ξ baseδ baseν publicG publicH publicR) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      (∃ Clog > 0, ∀ n : ℕ, rdivMinSampleSize B ≤ n →
        (terminalIndex ρ n + 1 : ℕ) ≤ Clog * Real.log n) ∧
      ∃ C > 0, ∀ n : ℕ, rdivMinSampleSize B ≤ n → ∃ E : Set Ω,
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν rawG rawH rawR candidate n E C ∧
      RDIVDiscrepancyEnvelope V P sample split mu gHat rHat ρ β δ ν w₀ candidate n E C ∧
      ∀ ω ∈ E,
          Accepts ρ n (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω)) (rdivNoiseLevel (δ n) (ν n)) ∧
          discrepancyIndex ρ n (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω)) (rdivNoiseLevel (δ n) (ν n)) + 1 ≤ terminalIndex ρ n + 1 ∧
          (ZeroSolutionCase V → discrepancyIndex ρ n (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω)) (rdivNoiseLevel (δ n) (ν n)) = 0) ∧
          (discrepancyIndex ρ n (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω)) (rdivNoiseLevel (δ n) (ν n)) = 0 ∨
            (0 < discrepancyIndex ρ n (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω)) (rdivNoiseLevel (δ n) (ν n)) ∧ AdjacentDiscrepancyRelation ρ (selectedPenalty ρ n (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω)) (rdivNoiseLevel (δ n) (ν n))) (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω)) (rdivNoiseLevel (δ n) (ν n)))) := by
  classical
  obtain ⟨required, hrequired, hdiscrepancy⟩ := rdiv_discrepancy_bound_at_versions (hLi_of_gate := hLi_of_gate) (hVector_of_gate := hVector_of_gate)
    (V := V) (P := P) (sample := sample) (split := split)
    (ρ := ρ) (ξ := ξ) (B := B) (baseδ := baseδ) (baseν := baseν)
    (rawG := rawG) (rawH := rawH) (rawR := rawR)
    (c₀ := c₀) (CG := CG) (Cm := Cm) (mu := mu) (G := G) (g₀ := g₀)
    (gHat := gHat) (rHat := rHat) (support := support) (candidate := candidate)
    hρ hξ hIV
  refine ⟨required, hrequired, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro β w₀ δ ν hRange hSource hRealizable hDensity hDensityBounds
    hPilotRate hOutcome hHypBound hPilotBound hSupMeas hLikMeas hFittingVersion hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius
    hRadiusFloor hScale hMinima hInflation hDeterministic hMLE
  -- Choose the zero witness in the zero-solution case, at the same exponent.
  let w : V.Hbar.toSubmodule := if ZeroSolutionCase V then 0 else w₀
  have hwSource : BetaSourceCondition V β w := by
    dsimp [w]
    split_ifs with hz
    · exact rdiv_zero_source_witness V β hSource.1 hz
    · exact hSource
  have hwnorm : ‖w‖ ^ 2 ≤ ‖w₀‖ ^ 2 := by
    dsimp [w]
    split_ifs <;> simp [sq_nonneg]
  obtain ⟨C, hC, hevent⟩ := hdiscrepancy κ₀ β w δ ν hRange hwSource
    hRealizable hDensity hDensityBounds hPilotRate hOutcome hHypBound hPilotBound
    hSupMeas hLikMeas hFittingVersion hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius hRadiusFloor hScale hMinima hInflation
    hDeterministic hMLE
  constructor
  · obtain ⟨Clog, hClog, hlog⟩ := terminalIndex_log_bound ρ hρ
    exact ⟨Clog, hClog, fun n hn => hlog n ((le_max_left _ _).trans hn)⟩
  · refine ⟨C, hC, ?_⟩
    intro n hn
    have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
    have hn0 : 0 < n := by omega
    obtain ⟨E, hE, hpE, hcomp, henv⟩ := hevent n hn0
    obtain ⟨S, hS, hSae, hSgood⟩ := rdiv_density_calibration_event (hSelectedDensityVersion := hSelectedDensityVersion) V P sample split
      mu G g₀ gHat support c₀ CG hIV hDensity hDensityBounds hMLE n hn0
    obtain ⟨R, hR, hRae, hRgood⟩ := rdiv_pilot_calibration_event (hSelectedPilotVersion := hSelectedPilotVersion) V P sample split
      rHat rawR B hPilotRate hPilotBound n hn0
    refine ⟨E ∩ S ∩ R, (hE.inter hS).inter hR, ?_, ?_, ?_, ?_⟩
    · have heq : (E ∩ S ∩ R : Set Ω) =ᵐ[P] E := by
        filter_upwards [hSae, hRae] with ω hωS hωR
        exact propext ⟨fun h => h.1.1, fun h => ⟨⟨h, hωS⟩, hωR⟩⟩
      rwa [measureReal_congr heq]
    · exact fun ω hω => hcomp ω hω.1.1
    · refine ⟨henv.1, ?_⟩
      intro ω hω lam hlam
      apply (henv.2 ω hω.1.1 lam hlam).trans
      have hlpos : 0 < lam := by
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
        exact mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwnorm hC.le)
          (Real.rpow_nonneg hlpos.le _))
    · intro ω hω
      have hlam : gridValue ρ (terminalIndex ρ n) ∈ regGrid ρ n := by
        exact Finset.mem_image.mpr
          ⟨terminalIndex ρ n, Finset.mem_range.mpr (Nat.lt_succ_self _), rfl⟩
      have hbound := rdiv_calibration_stat_le_four_of_density V P sample split
        mu G g₀ gHat rHat support B c₀ CG hDensity hDensityBounds hHypBound
        hOutcome.1 n hn0 ω (hSgood ω hω.1.2).1
        (candidate n (gridValue ρ (terminalIndex ρ n)) ω)
        ((hMinima n hn0 _ hlam).1 ω).1 (hRgood ω hω.2)
        (hSgood ω hω.1.2).2
      have hfloor := rdiv_calibrated_public_log_floor V mu G g₀ ρ ξ hξ
        rawG rawH rawR δ ν baseδ baseν κδ κν required hDensityRadius hHypRadius
        hScale hInflation n hn0
      obtain ⟨haccept, hcount, hcases⟩ := rdiv_search_of_terminal_bound
        ρ ξ B (δ n) (ν n) hρ hξ n hn
        (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
          (candidate n lam ω)) hfloor hbound
      refine ⟨haccept, hcount, ?_, hcases⟩
      intro hz
      have hwzero : w = 0 := by simp [w, hz]
      have hzero := henv
      rw [hwzero] at hzero
      exact rdiv_zero_envelope_initial_index V P sample split mu gHat rHat
        ρ β δ ν candidate n E C hzero ω hω.1.1


end Papers.TsAdaptiveEstimationInference
