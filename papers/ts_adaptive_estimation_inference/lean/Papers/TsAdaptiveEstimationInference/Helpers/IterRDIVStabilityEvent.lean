module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVSetup
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVProjectedEnvelope
/-! Recursive stability and calibration on the oracle segment.

This proves the stability lemma's two error bounds and final calibration bound
without relying on its additional internal risk-comparison certificate.
The propagation sequence and calibration constant precede the experiment.
-/
public section
set_option linter.style.longLine false
set_option linter.style.haveILetI false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  {pilotInputSupport : Set 𝒵} (V : IVWorld 𝒲 𝒳 𝒵)

/-- Under [fixed-center localized concentration](hyp:hFix_of_gate),
[squared-loss localized concentration](hyp:hSq_of_gate), [Li localized
concentration](hyp:hLi_of_gate), and [the RDIV model conditions](hyp:hIV),
[there exist population-dependent propagation coefficients, zero initially and
at least one thereafter, a positive calibration constant, and an inflation
factor at least one whose square dominates both three and the squared constant
plus the constant; for every admissible sampling setup there is a positive
threshold, chosen before source parameters, such that the range, source,
realizability, density, boundedness, pilot-rate, measurability, representative,
critical-radius, scale-calibration, attained-minimum, inflation, and likelihood
conditions yield at each positive sample size satisfying oracle-segment
stability a measurable event of probability at least one minus the failure
budget carrying both the iterative stability and calibration bounds and their
pre-inflation certificate](goal). -/
-- @node: iter_rdiv_stability_and_calibration_preinflation
lemma iter_rdiv_stability_and_calibration_preinflation
    (hFix_of_gate : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq_of_gate : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi_of_gate : LiLocalizedConcentration V) (B c₀ CG : ℝ) (mu : Measure 𝒳)
    (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
    (hIV : RDIVSetting V mu g₀) :
    ∃ aSeq : ℕ → ℝ, aSeq 0 = 0 ∧ (∀ j, 1 ≤ j → 1 ≤ aSeq j) ∧ -- @realizes a_j(sequence depending only on its index and fixed population quantities)
      ∃ C > 0, ∃ L ≥ (1 : ℝ),
      3 ≤ L ^ 2 ∧ C ^ 2 + C ≤ L ^ 2 ∧
      ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
        (sample : AnalysisSample V P) (split : SampleSplit)
        (ρ ξ c Cm : ℝ) (t : ℕ)
        (baseδ baseν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
        (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
        (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
        (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      let a := aSeq t -- @realizes a_t(terminal member of the same population-only sequence)
      (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) → (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) →
      (ht : 1 ≤ t) → (hc : 0 < c) →
      ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable V mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hPilotRate : PilotRegressionRate V P sample split rHat δr) →
      (hOutcome : OutcomeBounded V B) →
      (hHypBound : HypothesisClassBounded V support B) →
      (hPilotBound : PilotBounded V P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hFixedCenterVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ) →
      (hRadiusFloor : RDIVRadiusFloor δG δH ρ) →
      (hScale : RDIVScaleCalibration ρ ξ baseδ baseν δG δH δr t) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterRealizable : IterRealizableRDIV V ρ c a β t δ ν) →
      (hIterMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      ∀ n : ℕ, 0 < n →
      (hOracle : IterRDIVOracleSegmentStability ρ c a β t δ ν n) → ∃ E : Set Ω, -- @realizes \mathcal E_{n,t}^{\mathrm{IR}}(joint iteration-grid and calibration event per n)
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      IterRDIVStabilityOn V P sample split mu gHat rHat ρ c β aSeq t δ ν iter n E C ∧
      IterRDIVPreinflationOn V P sample split mu gHat rHat ρ c β aSeq t δ ν iter n E C L := by
  classical
  by_cases hPopulation : RangeCondition V ∧ DensityRealizable V mu G g₀ ∧
      DensityBounds G g₀ support c₀ CG ∧ OutcomeBounded V B ∧
      HypothesisClassBounded V support B
  · obtain ⟨hRange, hDensity, hBounds, hY, hHyp⟩ := hPopulation
    obtain ⟨D, hD, Ccal, hCcal, hevent⟩ :=
      iter_rdiv_joint_stability_calibration_event_preinflation (pilotInputSupport := pilotInputSupport) V
        hFix_of_gate hSq_of_gate hLi_of_gate mu G g₀ support B c₀ CG
        hIV hRange hDensity hBounds hY hHyp
    obtain ⟨hzero, _, hpositive⟩ := iterRdivStabilityCoefficients_bounds D hD
    let L := Ccal + 4
    have hL : 1 ≤ L := by dsimp [L]; linarith only [hCcal]
    have hLpos : 0 < L := zero_lt_one.trans_le hL
    have hLsq : 3 ≤ L ^ 2 := by dsimp [L]; nlinarith only [sq_nonneg Ccal, hCcal]
    have hCL : Ccal ^ 2 + Ccal ≤ L ^ 2 := by dsimp [L]; nlinarith only [hCcal]
    refine ⟨iterRdivStabilityCoefficients D, hzero, hpositive, Ccal, hCcal,
      L, hL, hLsq, hCL, ?_⟩
    intro P hProbability sample split ρ ξ c Cm t baseδ baseν δG δH δr
      gHat rHat candidate iter
    dsimp only
    intro hρ hξ ht hc
    letI : IsProbabilityMeasure P := hProbability
    by_cases hSetup : PilotRegressionRate V P sample split rHat δr ∧
        MLEMaximizerSelected V P sample split G gHat ∧
        RDIVClassesMeasurable V P sample split mu G g₀ gHat ∧
        RDIVLikelihoodProcessesMeasurable V G g₀ ∧
        RDIVSelectedDensityVersion V P sample split mu gHat ∧
        RDIVSelectedPilotVersion V P sample split rHat ∧
        PilotBounded V P rHat pilotInputSupport B ∧
        IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ ∧
        DensityCriticalRadiusBound V G g₀ δG ∧
        HypothesisCriticalRadiusBound V mu G δH ρ ∧ RDIVRadiusFloor δG δH ρ
    · obtain ⟨hPilot, hMLE, hMeas, hLik, hDV, hPV, hPB, hFV, hG, hH, hFloor⟩ := hSetup
      obtain ⟨R, hR, hevent⟩ := hevent P hProbability sample split gHat rHat ρ
        δG δH δr hPilot hMLE hMeas hLik hDV hPV hPB hFV hG hH hFloor
      refine ⟨L * R, mul_pos hLpos (zero_lt_one.trans_le hR), ?_⟩
      intro κ₀ β w₀ δ ν hRange' hSource hRealizable hDensity' hBounds'
        hPilot' hY' hHyp' hPB' hMeas' hLik' hFitting hDV' hPV' hFV'
        hG' hH' hFloor' hScale hMinima hInflation hDeterministic
        hIterRealizable hIterMinima hMLE' n hn hOracle
      let segment := Set.Icc
        (iterRdivOraclePoint ρ c (iterRdivStabilityCoefficients D t) β t δ ν n) 2
      have hdom (lam : ℝ) (hlam : lam ∈ regGrid ρ n) (_ : lam ∈ segment) :
          lam ∈ Set.Ioc (0 : ℝ) 2 := by
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
        have hρpos : 0 < ρ := by linarith only [hρ.1]
        refine ⟨mul_pos (by norm_num) (pow_pos hρpos k), ?_⟩
        have hp := pow_le_pow_of_le_one hρpos.le hρ.2.le (Nat.zero_le k)
        simpa only [gridValue, pow_zero, mul_one] using
          mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
      obtain ⟨E, hE, hpE, hfit, hcal⟩ := hevent L hL ξ t δ ν baseδ baseν
        (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 hρ hξ hScale hInflation
        n segment (iterRdivOracleRadius c (iterRdivStabilityCoefficients D t) β t δ ν n)
        ⟨hOracle, fun lam _ hs => hs.1⟩ (fun j lam => iter n j lam) hn hdom
        (fun lam hl hs j hj hjt => hIterRealizable n hOracle j hj hjt lam hl hs)
        (fun lam hl _ => (hIterMinima n hn lam hl).1)
        (fun lam hl ω => ((hIterMinima n hn lam hl).1.2 t ht le_rfl ω).1)
        (fun lam hl => (hIterMinima n hn lam hl).2 t le_rfl)
      refine ⟨E, hE, hpE, ?_⟩
      constructor
      · intro ω hω
        constructor
        · intro j hj hjt lam hl hs
          have hstep := hfit ω hω lam hl hs j hj hjt
          have hδsq : (δ n / L) ^ 2 ≤ δ n ^ 2 := by
            rw [div_pow]
            exact div_le_self (sq_nonneg _) (by nlinarith only [hLsq])
          have hnum := mul_le_mul_of_nonneg_left hδsq
            ((iterRdivStabilityCoefficients_bounds D hD).2.1 j)
          have hlam := (hdom lam hl hs).1
          exact ⟨hstep.1.trans (div_le_div_of_nonneg_right hnum hlam.le),
            hstep.2.trans (div_le_div_of_nonneg_right hnum (sq_nonneg lam))⟩
        · intro lam hl hs
          have hν : ν n / L ≤ ν n := div_le_self (hDeterministic.2 n) hL
          have hνsq : (ν n / L) ^ 2 ≤ ν n ^ 2 := by
            rw [div_pow]
            exact div_le_self (sq_nonneg _) (by nlinarith only [hLsq])
          apply (hcal ω hω lam hl).trans
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hν hCcal.le) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hνsq hCcal.le)
      · intro ω hω
        exact ⟨fun j hj hjt lam hl hs => hfit ω hω lam hl hs j hj hjt,
          fun lam hl _ => hcal ω hω lam hl⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      intro κ₀ β w₀ δ ν hRange' hSource hRealizable hDensity' hBounds'
        hPilot hY' hHyp' hPB hMeas hLik hFitting hDV hPV hFV hG hH hFloor
        hScale hMinima hInflation hDeterministic hIterRealizable hIterMinima hMLE
      exact (hSetup ⟨hPilot, hMLE, hMeas, hLik, hDV, hPV, hPB, hFV, hG, hH, hFloor⟩).elim
  · refine ⟨iterRdivStabilityCoefficients 1, rfl,
      (iterRdivStabilityCoefficients_bounds 1 le_rfl).2.2, 1, zero_lt_one,
      5, by norm_num, by norm_num, by norm_num, ?_⟩
    intro P hProbability sample split ρ ξ c Cm t baseδ baseν δG δH δr
      gHat rHat candidate iter
    dsimp only
    intro hρ hξ ht hc
    refine ⟨1, zero_lt_one, ?_⟩
    intro κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hBounds
      hPilotRate hY hHyp
    exact (hPopulation ⟨hRange, hDensity, hBounds, hY, hHyp⟩).elim

/-- Given [fixed-center localized concentration](hyp:hFix_of_gate),
[squared-loss localized concentration](hyp:hSq_of_gate), [Li localized
concentration](hyp:hLi_of_gate), and [the RDIV model conditions](hyp:hIV),
[there are population-dependent propagation coefficients, zero at initialization
and at least one at every positive iteration, and a positive calibration
constant such that each admissible sampling setup has a positive inflation
threshold selected before the source parameters; under the range, source,
realizability, density, boundedness, pilot-rate, measurability, representative,
critical-radius, scale-calibration, attained-minimum, inflation, and likelihood
requirements, every positive sample size satisfying oracle-segment stability
admits a measurable event of probability at least one minus the failure budget
on which the recursive stability and calibration bounds hold](goal). -/
-- @node: iter_rdiv_stability_and_calibration
lemma iter_rdiv_stability_and_calibration
    (hFix_of_gate : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq_of_gate : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi_of_gate : LiLocalizedConcentration V) (B c₀ CG : ℝ) (mu : Measure 𝒳)
    (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
    (hIV : RDIVSetting V mu g₀) :
    ∃ aSeq : ℕ → ℝ, aSeq 0 = 0 ∧ (∀ j, 1 ≤ j → 1 ≤ aSeq j) ∧ -- @realizes a_j(sequence depending only on its index and fixed population quantities)
      ∃ C > 0,
      ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
        (sample : AnalysisSample V P) (split : SampleSplit)
        (ρ ξ c Cm : ℝ) (t : ℕ)
        (baseδ baseν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
        (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
        (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
        (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      let a := aSeq t -- @realizes a_t(terminal member of the same population-only sequence)
      (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) → (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) →
      (ht : 1 ≤ t) → (hc : 0 < c) →
      ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable V mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hPilotRate : PilotRegressionRate V P sample split rHat δr) →
      (hOutcome : OutcomeBounded V B) →
      (hHypBound : HypothesisClassBounded V support B) →
      (hPilotBound : PilotBounded V P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hFixedCenterVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ) →
      (hRadiusFloor : RDIVRadiusFloor δG δH ρ) →
      (hScale : RDIVScaleCalibration ρ ξ baseδ baseν δG δH δr t) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterRealizable : IterRealizableRDIV V ρ c a β t δ ν) →
      (hIterMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      ∀ n : ℕ, 0 < n →
      (hOracle : IterRDIVOracleSegmentStability ρ c a β t δ ν n) → ∃ E : Set Ω, -- @realizes \mathcal E_{n,t}^{\mathrm{IR}}(joint iteration-grid and calibration event per n)
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      IterRDIVStabilityOn V P sample split mu gHat rHat ρ c β aSeq t δ ν iter n E C := by
  obtain ⟨aSeq, hzero, hseq, C, hC, L, hL, hLsq, hCL, hevent⟩ :=
    iter_rdiv_stability_and_calibration_preinflation (pilotInputSupport := pilotInputSupport)
      V hFix_of_gate hSq_of_gate hLi_of_gate B c₀ CG mu G g₀ support hIV
  refine ⟨aSeq, hzero, hseq, C, hC, ?_⟩
  intro P hProbability sample split ρ ξ c Cm t baseδ baseν δG δH δr
    gHat rHat candidate iter
  dsimp only
  intro hρ hξ ht hc
  obtain ⟨R, hR, hevent⟩ := hevent P hProbability sample split ρ ξ c Cm t
    baseδ baseν δG δH δr gHat rHat candidate iter hρ hξ ht hc
  refine ⟨R, hR, ?_⟩
  intro κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hBounds
    hPilot hY hHyp hPB hMeas hLik hFitting hDV hPV hFV hG hH hFloor
    hScale hMinima hInflation hDeterministic hIterRealizable hIterMinima hMLE n hn hOracle
  obtain ⟨E, hE, hpE, hstab, _⟩ := hevent κ₀ β w₀ δ ν hRange hSource
    hRealizable hDensity hBounds hPilot hY hHyp hPB hMeas hLik hFitting hDV hPV
    hFV hG hH hFloor hScale hMinima hInflation hDeterministic
    hIterRealizable hIterMinima hMLE n hn hOracle
  exact ⟨E, hE, hpE, hstab⟩

/-- Under [fixed-center localized concentration](hyp:hFix_of_gate),
[squared-loss localized concentration](hyp:hSq_of_gate), [Li localized
concentration](hyp:hLi_of_gate), and [the RDIV model conditions](hyp:hIV),
[population-dependent propagation coefficients, zero initially and at least one
thereafter, and a positive calibration constant can be chosen so that every
admissible sampling setup has a positive inflation threshold preceding the
source parameters; under the range, source, realizability, density, boundedness,
pilot-rate, measurability, representative, critical-radius, scale-calibration,
attained-minimum, inflation, and likelihood requirements, a positive envelope
constant exists such that every positive sample size satisfying the discrepancy
oracle-segment conditions admits a measurable event of probability at least
one minus the failure budget carrying both the iterative stability and
calibration bounds and the discrepancy envelope](goal).

The additional raw-risk comparison certificate of `iter_rdiv_constructed_event`
is a separate obligation. -/
-- @node: iter_rdiv_constructed_discrepancy_event
lemma iter_rdiv_constructed_discrepancy_event
    (hFix_of_gate : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq_of_gate : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi_of_gate : LiLocalizedConcentration V) (B c₀ CG : ℝ) (mu : Measure 𝒳)
    (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
    (hIV : RDIVSetting V mu g₀) :
    ∃ aSeq : ℕ → ℝ, aSeq 0 = 0 ∧ (∀ j, 1 ≤ j → 1 ≤ aSeq j) ∧ -- @realizes a_j(sequence depending only on its index and fixed population quantities)
      ∃ C > 0,
      ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
        (sample : AnalysisSample V P) (split : SampleSplit)
        (ρ ξ c Cm : ℝ) (t : ℕ)
        (baseδ baseν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
        (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
        (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
        (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      let a := aSeq t -- @realizes a_t(terminal member of the same population-only sequence)
      (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) → (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) →
      (ht : 1 ≤ t) → (hc : 0 < c) →
      ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable V mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hPilotRate : PilotRegressionRate V P sample split rHat δr) →
      (hOutcome : OutcomeBounded V B) →
      (hHypBound : HypothesisClassBounded V support B) →
      (hPilotBound : PilotBounded V P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hFixedCenterVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ) →
      (hRadiusFloor : RDIVRadiusFloor δG δH ρ) →
      (hScale : RDIVScaleCalibration ρ ξ baseδ baseν δG δH δr t) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterRealizable : IterRealizableRDIV V ρ c a β t δ ν) →
      (hIterMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      ∃ Cenv > 0, ∀ n : ℕ, 0 < n →
      (hOracle : IterRDIVOracleSegmentDiscrepancy ρ c a β t δ ν n) → ∃ E : Set Ω, -- @realizes \mathcal E_{n,t}^{\mathrm{IR}}(joint iteration-grid and calibration event per n)
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      IterRDIVStabilityOn V P sample split mu gHat rHat ρ c β aSeq t δ ν iter n E C ∧
      IterRDIVDiscrepancyEnvelope V P sample split mu gHat rHat ρ ξ c a β t δ ν w₀ iter n E Cenv := by
  obtain ⟨aSeq, hzero, hseq, Cevent, hCevent, L, hL, hLsq, hCL, hjoint⟩ :=
    iter_rdiv_stability_and_calibration_preinflation (pilotInputSupport := pilotInputSupport)
      V hFix_of_gate hSq_of_gate hLi_of_gate B c₀ CG mu G g₀ support hIV
  refine ⟨aSeq, hzero, hseq, Cevent, hCevent, ?_⟩
  intro P hProbability sample split ρ ξ c Cm t baseδ baseν δG δH δr
    gHat rHat candidate iter
  dsimp only
  intro hρ hξ ht hc
  letI : IsProbabilityMeasure P := hProbability
  obtain ⟨R, hR, hjoint⟩ := hjoint P hProbability sample split ρ ξ c Cm t
    baseδ baseν δG δH δr gHat rHat candidate iter hρ hξ ht hc
  refine ⟨R, hR, ?_⟩
  intro κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hBounds
    hPilot hY hHyp hPB hMeas hLik hFitting hDV hPV hFV hG hH hFloor
    hScale hMinima hInflation hDeterministic hIterRealizable hIterMinima hMLE
  obtain ⟨Cenv, hCenv, hupper⟩ := iter_rdiv_projected_upper_from_preinflation
    V β w₀ hRange hSource t ht Cevent L hCevent.le
    (zero_lt_one.trans_le hL) hLsq hCL
  refine ⟨Cenv, hCenv, ?_⟩
  intro n hn hOracle
  obtain ⟨E, hE, hpE, hstab, hraw⟩ := hjoint κ₀ β w₀ δ ν hRange hSource
    hRealizable hDensity hBounds hPilot hY hHyp hPB hMeas hLik hFitting hDV hPV
    hFV hG hH hFloor hScale hMinima hInflation hDeterministic
    hIterRealizable hIterMinima hMLE n hn hOracle
  refine ⟨E, hE, hpE, hstab, hE, hpE, hCenv, ?_⟩
  intro ω hω lam hl hs
  have hstep := (hraw ω hω).1 t ht le_rfl lam hl hs
  have hcal := (hraw ω hω).2 lam hl hs
  have hnum : 0 ≤ aSeq t := (by norm_num : (0 : ℝ) ≤ 1).trans (hseq t ht)
  have hlam : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    exact mul_pos (by norm_num) (pow_pos (by linarith only [hρ.1]) k)
  exact hupper (iter n t lam ω) lam (aSeq t) (δ n) (ν n)
    (rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω))
    hlam hnum (hDeterministic.2 n) hstep.1 hcal

end Papers.TsAdaptiveEstimationInference
