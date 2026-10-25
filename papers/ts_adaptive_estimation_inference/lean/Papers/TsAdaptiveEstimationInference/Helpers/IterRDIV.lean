module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVSetup
/-! Common-event construction and accepted bounds for iterative RDIV. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  {pilotInputSupport : Set 𝒵}
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (δG δH δr tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
/-- Given [localized concentration for fixed-center iterative losses](hyp:hFix_of_gate), [localized concentration for iterative squared losses](hyp:hSq_of_gate), [localized likelihood concentration](hyp:hLi_of_gate), and [the IV sampling and density identities](hyp:hIV), [there exist a population-only propagation sequence starting at zero and at least one at every positive index, positive raw and public comparison constants, and an inflation factor at least one whose square dominates both three and the raw constant squared plus itself; for each sampling experiment, admissible grid ratio and confidence, and positive horizon, a positive calibration requirement can then be chosen so that, under the range, source, realizability, boundedness, pilot, measurability, version, critical-radius, calibration, minimization, deterministic-accuracy and oracle-stability conditions, a measurable event of probability at least one minus the failure probability carries the joint comparisons, recursive stability, and preinflation bounds](goal).

The terminal propagation coefficient is the horizon's entry in this same sequence. The calibration requirement is chosen before the source and public accuracy curves; the event retains the raw estimates as well as the public certificates. -/
lemma iter_rdiv_constructed_event
    (hFix_of_gate : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq_of_gate : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi_of_gate : LiLocalizedConcentration V) (B c₀ CG : ℝ) (mu : Measure 𝒳)
    (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
    (hIV : RDIVSetting V mu g₀) :
    ∃ aSeq : ℕ → ℝ, aSeq 0 = 0 ∧ (∀ j, 1 ≤ j → 1 ≤ aSeq j) ∧ -- @realizes a_j(sequence depending only on its index and fixed population quantities)
      ∃ Craw > 0, ∃ L ≥ (1 : ℝ),
      3 ≤ L ^ 2 ∧ Craw ^ 2 + Craw ≤ L ^ 2 ∧ ∃ C > 0,
      ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
        (sample : AnalysisSample V P) (split : SampleSplit)
        (ρ ξ Cm : ℝ) (t : ℕ)
        (baseδ baseν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
        (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
        (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
        (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      let a := aSeq t -- @realizes a_t(terminal member of the same population-only sequence)
      (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) → (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) →
      (ht : 1 ≤ t) →
      ∃ required > 0, ∀ (c : ℝ), 0 < c → ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
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
      IterRDIVComparisonsOn V P sample split mu g₀ gHat rHat ξ δG δH δr ρ c a β t δ ν iter n E C ∧
      IterRDIVStabilityOn V P sample split mu gHat rHat ρ c β aSeq t δ ν iter n E C ∧
      IterRDIVPreinflationOn V P sample split mu gHat rHat ρ c β aSeq t δ ν iter n E Craw L := by
  classical
  -- Population hypotheses are tested before selecting the sequence. The
  -- impossible branch below is discharged only after those same hypotheses
  -- arrive in the theorem's unchanged interface.
  by_cases hPopulation : RangeCondition V ∧ DensityRealizable V mu G g₀ ∧
      DensityBounds G g₀ support c₀ CG ∧ OutcomeBounded V B ∧
      HypothesisClassBounded V support B
  · obtain ⟨hRange, hDensity, hBounds, hY, hHyp⟩ := hPopulation
    obtain ⟨D, hD, Ccal, hCcal, hevent⟩ :=
      iter_rdiv_joint_retained_event_preinflation (pilotInputSupport := pilotInputSupport) V
        hFix_of_gate hSq_of_gate hLi_of_gate mu G g₀ support B c₀ CG
        hIV hRange hDensity hBounds hY hHyp
    obtain ⟨hzero, _, hpositive⟩ := iterRdivStabilityCoefficients_bounds D hD
    let L := Ccal + 4
    have hL : 1 ≤ L := by dsimp [L]; linarith only [hCcal]
    have hLpos : 0 < L := zero_lt_one.trans_le hL
    have hLsq : 3 ≤ L ^ 2 := by dsimp [L]; nlinarith only [sq_nonneg Ccal, hCcal]
    have hCL : Ccal ^ 2 + Ccal ≤ L ^ 2 := by dsimp [L]; nlinarith only [hCcal]
    let Cevent := max 1 Ccal
    refine ⟨iterRdivStabilityCoefficients D, hzero, hpositive,
      Ccal, hCcal, L, hL, hLsq, hCL,
      Cevent, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro P hProbability sample split ρ ξ Cm t baseδ baseν δG δH δr
      gHat rHat candidate iter
    dsimp only
    intro hρ hξ ht
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
      obtain ⟨Ccmp, hCcmp, R, hR, hevent⟩ := hevent P hProbability sample split gHat rHat ρ
        δG δH δr hPilot hMLE hMeas hLik hDV hPV hPB hFV hG hH hFloor
      refine ⟨L * R, mul_pos hLpos (zero_lt_one.trans_le hR), ?_⟩
      intro c hc κ₀ β w₀ δ ν hRange' hSource hRealizable hDensity' hBounds'
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
      obtain ⟨E, hE, hpE, hfit, hcal, hretained⟩ := hevent L hL ξ t δ ν baseδ baseν
        (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 hρ hξ hScale hInflation
        n segment (iterRdivOracleRadius c (iterRdivStabilityCoefficients D t) β t δ ν n)
        ⟨hOracle, fun lam _ hs => hs.1⟩ (fun j lam => iter n j lam) hn hdom
        (fun lam hl hs j hj hjt => hIterRealizable n hOracle j hj hjt lam hl hs)
        (fun lam hl _ => (hIterMinima n hn lam hl).1)
        (fun lam hl ω => ((hIterMinima n hn lam hl).1.2 t ht le_rfl ω).1)
        (fun lam hl => (hIterMinima n hn lam hl).2 t le_rfl)
      have hcert :
          IterRDIVStabilityOn V P sample split mu gHat rHat ρ c β
            (iterRdivStabilityCoefficients D) t δ ν iter n E Ccal ∧
          IterRDIVPreinflationOn V P sample split mu gHat rHat ρ c β
            (iterRdivStabilityCoefficients D) t δ ν iter n E Ccal L := by
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
      have hC1 : 1 ≤ Cevent := le_max_left _ _
      have hCalC : Ccal ≤ Cevent := le_max_right _ _
      have hcalPublic (ω : Ω) (hω : ω ∈ E) (lam : ℝ)
          (hl : lam ∈ regGrid ρ n) (hs : lam ∈ segment) :=
        (hcert.1 ω hω).2 lam hl hs
      have hstabPublic : IterRDIVStabilityOn V P sample split mu gHat rHat
          ρ c β (iterRdivStabilityCoefficients D) t δ ν iter n E Cevent := by
        intro ω hω
        refine ⟨(hcert.1 ω hω).1, ?_⟩
        intro lam hl hs
        exact (hcalPublic ω hω lam hl hs).trans (add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCalC (hDeterministic.2 n)) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hCalC (sq_nonneg _)))
      refine ⟨E, hE, hpE, ?_, hstabPublic, hcert.2⟩
      refine ⟨Ccmp, hCcmp, ?_⟩
      intro ω hω
      obtain ⟨hg, hpre, hraw⟩ := hretained ω hω
      refine ⟨hpre, ?_, ?_, (hstabPublic ω hω).2⟩
      · intro j hj hjt lam hl hs h hh
        have hstar := hIterRealizable n hOracle j hj hjt lam hl hs
        have hb := hraw lam hl hs j hj hjt h hh
        rw [iter_rdiv_fixed_center_deviation_eq_risks V P sample split
          mu G g₀ gHat support B c₀ CG n j ω ω lam hIV hDensity hBounds
          hHyp hY hg h (populationIterate V lam j) hh hstar] at hb
        exact hb
      · intro j hj hjt lam hl hs
        have hb := (hstabPublic ω hω).1 j hj hjt lam hl hs
        have hmono : Monotone (iterRdivStabilityCoefficients D) := by
          apply monotone_nat_of_le_succ
          intro k
          change iterRdivStabilityCoefficients D k ≤
            D * (1 + iterRdivStabilityCoefficients D k)
          have hk := (iterRdivStabilityCoefficients_bounds D hD).2.1 k
          nlinarith only [hD, hk, mul_nonneg (sub_nonneg.mpr hD) hk]
        have hcoef : iterRdivStabilityCoefficients D j ≤
            Cevent * iterRdivStabilityCoefficients D t :=
          (hmono hjt).trans (le_mul_of_one_le_left
            ((iterRdivStabilityCoefficients_bounds D hD).2.1 t) hC1)
        have hnum := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (δ n))
        exact ⟨hb.1.trans (div_le_div_of_nonneg_right hnum (hdom lam hl hs).1.le),
          hb.2.trans (div_le_div_of_nonneg_right hnum (sq_nonneg lam))⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      intro c hc κ₀ β w₀ δ ν hRange' hSource hRealizable hDensity' hBounds'
        hPilot hY' hHyp' hPB hMeas hLik hFitting hDV hPV hFV hG hH hFloor
        hScale hMinima hInflation hDeterministic hIterRealizable hIterMinima hMLE
      exact (hSetup ⟨hPilot, hMLE, hMeas, hLik, hDV, hPV, hPB, hFV, hG, hH, hFloor⟩).elim
  · refine ⟨iterRdivStabilityCoefficients 1, rfl,
      (iterRdivStabilityCoefficients_bounds 1 le_rfl).2.2,
      1, zero_lt_one, 5, by norm_num, by norm_num, by norm_num,
      1, zero_lt_one, ?_⟩
    intro P hProbability sample split ρ ξ Cm t baseδ baseν δG δH δr
      gHat rHat candidate iter
    dsimp only
    intro hρ hξ ht
    refine ⟨1, zero_lt_one, ?_⟩
    intro c hc κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hBounds
      hPilotRate hY hHyp
    exact (hPopulation ⟨hRange, hDensity, hBounds, hY, hHyp⟩).elim


-- @node: lem:iter-rdiv-stability
/-- Given [localized concentration for fixed-center iterative losses](hyp:hFix_of_gate), [localized concentration for iterative squared losses](hyp:hSq_of_gate), [localized likelihood concentration](hyp:hLi_of_gate), and [the IV sampling and density identities](hyp:hIV), [there exist a population-only propagation sequence starting at zero and at least one at each positive index, and a positive comparison constant, such that for every sampling experiment, admissible grid ratio and confidence, positive horizon and positive oracle scale, a positive calibration requirement can be chosen before the source and accuracy curves; under the range, source, realizability, boundedness, pilot, measurability, version, critical-radius, calibration, minimization, deterministic-accuracy and oracle-stability conditions, a measurable event of probability at least one minus the failure probability carries both the joint comparisons and recursive stability with the horizon's entry of that sequence](goal). -/
lemma iter_rdiv_stability
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
      IterRDIVComparisonsOn V P sample split mu g₀ gHat rHat ξ δG δH δr ρ c a β t δ ν iter n E C ∧
      IterRDIVStabilityOn V P sample split mu gHat rHat ρ c β aSeq t δ ν iter n E C := by
  obtain ⟨aSeq, hzero, hseq, Craw, hCraw, L, hL, hLsq, hCL, C, hC, hjoint⟩ :=
    iter_rdiv_constructed_event (V := V) (Ω := Ω) hFix_of_gate hSq_of_gate
      hLi_of_gate B c₀ CG mu G g₀ support hIV
  refine ⟨aSeq, hzero, hseq, C, hC, ?_⟩
  intro P hProbability sample split ρ ξ c Cm t baseδ baseν δG δH δr
    gHat rHat candidate iter
  dsimp only
  intro hρ hξ ht hc
  obtain ⟨R, hR, hjoint⟩ := hjoint P hProbability sample split ρ ξ Cm t
    baseδ baseν δG δH δr gHat rHat candidate iter hρ hξ ht
  refine ⟨R, hR, ?_⟩
  intro κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hBounds
    hPilot hY hHyp hPB hMeas hLik hFitting hDV hPV hFV hG hH hFloor
    hScale hMinima hInflation hDeterministic hIterRealizable hIterMinima hMLE n hn hOracle
  obtain ⟨E, hE, hpE, hcomp, hstab, _⟩ := hjoint c hc κ₀ β w₀ δ ν hRange hSource
    hRealizable hDensity hBounds hPilot hY hHyp hPB hMeas hLik hFitting hDV hPV
    hFV hG hH hFloor hScale hMinima hInflation hDeterministic
    hIterRealizable hIterMinima hMLE n hn hOracle
  exact ⟨E, hE, hpE, hcomp, hstab⟩


variable (rawG rawH rawR : ℕ → ℝ → ℝ)


/-- For [an IV world](hyp:V), [a sampling law](hyp:P), [an analysis sample](hyp:sample), [a sample split](hyp:split), [a grid ratio](hyp:ρ), [a failure probability](hyp:ξ), [an oracle scale](hyp:c), [an iteration multiplier](hyp:a), [a source exponent](hyp:β), [an iteration horizon](hyp:t), [density accuracy](hyp:δ), [pilot accuracy](hyp:ν), [raw density radii](hyp:rawG), [raw hypothesis radii](hyp:rawH), [raw pilot radii](hyp:rawR), [an integration measure](hyp:mu), [the true density](hyp:g₀), [fitted densities](hyp:gHat), [fitted pilots](hyp:rHat), [fitted iterative estimates](hyp:iter), [an event-comparison constant](hyp:Cevent), and [an error constant](hyp:C), [the accepted-bounds property](goal) requires that, at every positive sample size satisfying oracle-segment acceptance, every measurable event of probability at least 1−ξ carrying the joint comparisons with the event constant has, throughout its oracle grid segment, [projected squared error at most the error constant times the sum of the calibration statistic and iterative noise](step:1) and [strong squared error at most the error constant times the sum of iterative stability and that same calibration-plus-noise quantity raised to β/(β+1)](step:2). -/
noncomputable def PinIterRdivAcceptedBoundsConstant (Cevent C : ℝ) : Prop :=
      ∀ n : ℕ, 0 < n →
      (hOracle : IterRDIVOracleSegmentAccepted ρ c a β t δ ν n) →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      IterRDIVComparisonsOn V P sample split mu g₀ gHat rHat ξ rawG rawH rawR ρ c a β t δ ν iter n E Cevent →
      ∀ ω ∈ E,
      ∀ lam ∈ regGrid ρ n,
        lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2 ≤
          C * (rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) + iterRdivNoiseLevel a (δ n) (ν n) lam) ∧
        ‖iter n t lam ω - minNormSolution V‖ ^ 2 ≤ C * (iterRdivStability a (δ n) lam +
          (rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) + iterRdivNoiseLevel a (δ n) (ν n) lam) ^ (β / (β + 1)))

-- @node: lem:iter-rdiv-accepted-bounds
/-- For [a grid ratio in `[1/2, 1)`](hyp:hρ), [a positive iteration horizon](hyp:ht), [the IV sampling and density identities](hyp:hIV), [a positive oracle scale](hyp:hc), and [an iteration multiplier at least one](hyp:ha), [there is a positive calibration requirement such that, for each source and population satisfying the range, source, realizability, density and envelope conditions, and each positive event-comparison constant, a positive error constant can be chosen before sampling, fitting and confidence; under the pilot, measurability, version, critical-radius, minimization, calibration and deterministic-accuracy conditions, on every measurable oracle-segment event with probability at least one minus the failure probability carrying the joint comparisons, projected squared error is bounded by the error constant times the sum of the calibration statistic and iterative noise, while strong squared error is bounded by the same constant times the sum of iterative stability and that calibration-plus-noise sum raised to β/(β+1)](goal). -/
lemma iter_rdiv_accepted_bounds
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (ht : 1 ≤ t)
    (hIV : RDIVSetting V mu g₀)
    (hc : 0 < c) (ha : 1 ≤ a)
    : ∃ required > 0, ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable V mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hOutcome : OutcomeBounded V B) →
      (hHypBound : HypothesisClassBounded V support B) →
      ∀ Cevent : ℝ, 0 < Cevent → ∃ C > 0,
      ∀ (P : Measure Ω) [IsProbabilityMeasure P]
        (sample : AnalysisSample V P) (split : SampleSplit)
        (rawG rawH rawR : ℕ → ℝ → ℝ)
        (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
        (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
        (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      (hPilotRate : PilotRegressionRate V P sample split rHat rawR) →
      (hPilotBound : PilotBounded V P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ rawG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G rawH ρ) →
      (hRadiusFloor : RDIVRadiusFloor rawG rawH ρ) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hIterMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (ξ : ℝ) (baseδ baseν δ ν : ℕ → ℝ),
      (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) →
      (hScale : RDIVIterationScaleCalibration ρ ξ baseδ baseν
        (rdivEvaluatedAccuracy rawG) (rdivEvaluatedAccuracy rawH)
        (rdivEvaluatedAccuracy rawR) t) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterRealizable : IterRealizableRDIV V ρ c a β t δ ν) →
      PinIterRdivAcceptedBoundsConstant (V := V) (P := P) (sample := sample)
        (split := split) (ρ := ρ) (ξ := ξ) (β := β) (c := c) (a := a) (t := t)
        (δ := δ) (ν := ν) (rawG := rawG) (rawH := rawH) (rawR := rawR)
        (mu := mu) (g₀ := g₀) (gHat := gHat) (rHat := rHat) (iter := iter) Cevent C := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro β w₀ hRange hSource hRealizable hDensity hDensityBounds
    hOutcome hHypBound Cevent hCevent
  obtain ⟨Cb, hCb, hbias⟩ := iter_bias V β w₀ hRange hSource t ht
  let α := β / (β + 1)
  let K := 2 + Cevent ^ 2 + 2 * Cevent
  let D := 2 * K + 2 * Cevent + 1
  let S := ‖w₀‖ ^ (2 / (β + 1)) * D ^ α
  let C := K + 2 * Cevent + 2 * S + 1
  have hα : 0 ≤ α := by dsimp [α]; positivity [hSource.1]
  have hK : 0 < K := by dsimp [K]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro P hProbability sample split rawG rawH rawR gHat rHat candidate iter
    hPilotRate hPilotBound hSupMeas hLikMeas hFittingVersion
    hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius
    hRadiusFloor hMinima hIterMinima hMLE κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro ξ baseδ baseν δ ν hξ hScale hInflation hDeterministic hIterRealizable n hn hOracle E hE hp hcomp
  obtain ⟨Cdata, hCdata, hcomp⟩ := hcomp
  intro ω hω lam hlam hsegment
  have hlpos : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
    exact mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
  let h := iter n t lam ω
  let hstar := populationIterate V lam t
  let Q := rdivCalibrationStat V P sample split mu gHat rHat n ω h +
    iterRdivNoiseLevel a (δ n) (ν n) lam
  let U := ‖projCondExpOp V (h - minNormSolution V)‖
  let W := ‖projCondExpOp V (h - hstar)‖
  let R := ‖projCondExpOp V (hstar - minNormSolution V)‖
  have hstat : 0 ≤ rdivCalibrationStat V P sample split mu gHat rHat n ω h := by
    unfold rdivCalibrationStat blockAverage
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hnoise : 0 ≤ a * δ n ^ 2 / lam := by
    exact div_nonneg (mul_nonneg (by linarith [ha]) (sq_nonneg _)) hlpos.le
  have hQ : 0 ≤ Q := by
    dsimp [Q, iterRdivNoiseLevel, iterRdivScale]
    linarith only [hstat, hnoise, sq_nonneg (ν n)]
  have hνQ : ν n ^ 2 ≤ Q := by
    dsimp [Q, iterRdivNoiseLevel, iterRdivScale]
    linarith only [hstat, hnoise]
  have hδQ : a * δ n ^ 2 / lam ≤ Q := by
    dsimp [Q, iterRdivNoiseLevel, iterRdivScale]
    linarith only [hstat, sq_nonneg (ν n)]
  have hcal := (hcomp ω hω).2.2.2 lam hlam hsegment
  have hcal' := (abs_le.mp hcal).1
  change -(Cevent * ν n * U + Cevent * ν n ^ 2) ≤
    rdivCalibrationStat V P sample split mu gHat rHat n ω h - U ^ 2 at hcal'
  have hweak : U ^ 2 ≤ K * Q := by
    have hy := sq_nonneg (U - Cevent * ν n)
    have hmul := mul_le_mul_of_nonneg_left hνQ
      (show 0 ≤ Cevent ^ 2 + 2 * Cevent by positivity)
    have hstatQ : rdivCalibrationStat V P sample split mu gHat rHat n ω h ≤ Q := by
      dsimp [Q, iterRdivNoiseLevel, iterRdivScale]
      linarith only [hnoise, sq_nonneg (ν n)]
    dsimp [K]
    nlinarith only [hcal', hy, hmul, hstatQ]
  have hstab := (hcomp ω hω).2.2.1 t ht le_rfl lam hlam hsegment
  have hvar : W ^ 2 ≤ Cevent * Q := by
    have hi := hstab.1
    change lam * ‖h - hstar‖ ^ 2 + W ^ 2 ≤ Cevent * a * δ n ^ 2 / lam at hi
    have hm := mul_le_mul_of_nonneg_left hδQ hCevent.le
    have heq : Cevent * (a * δ n ^ 2 / lam) = Cevent * a * δ n ^ 2 / lam := by ring
    rw [heq] at hm
    nlinarith only [hi, hm, mul_nonneg hlpos.le (sq_nonneg ‖h - hstar‖)]
  have hstrongvar : ‖h - hstar‖ ^ 2 ≤ Cevent * iterRdivStability a (δ n) lam := by
    simpa only [h, hstar, iterRdivStability, iterRdivScale, mul_div_assoc, mul_assoc]
      using hstab.2
  have htriangle : R ^ 2 ≤ 2 * U ^ 2 + 2 * W ^ 2 := by
    have heq : projCondExpOp V (hstar - minNormSolution V) =
        projCondExpOp V (h - minNormSolution V) - projCondExpOp V (h - hstar) := by
      simp only [map_sub]; abel
    dsimp only [R, U, W]
    rw [heq]
    simpa only [mul_add] using
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2).trans add_sq_le
  have hR : R ^ 2 ≤ D * Q := by
    dsimp [D]
    nlinarith only [htriangle, hweak, hvar, hQ]
  have hstrongbias : ‖hstar - minNormSolution V‖ ^ 2 ≤ S * Q ^ α := by
    have hi := (hbias lam hlpos).2.2.2.2.2
    have heq : R ^ (2 * β / (β + 1)) = (R ^ 2) ^ α := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      dsimp [α]; ring
    change _ ≤ ‖w₀‖ ^ (2 / (β + 1)) * R ^ (2 * β / (β + 1)) at hi
    rw [heq] at hi
    have hm := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (sq_nonneg R) hR hα)
      (show 0 ≤ ‖w₀‖ ^ (2 / (β + 1)) by positivity)
    rw [Real.mul_rpow hD.le hQ] at hm
    exact hi.trans (by simpa only [S, mul_assoc] using hm)
  have htotal : ‖h - minNormSolution V‖ ^ 2 ≤
      2 * ‖h - hstar‖ ^ 2 + 2 * ‖hstar - minNormSolution V‖ ^ 2 := by
    have heq : h - minNormSolution V = (h - hstar) + (hstar - minNormSolution V) := by abel
    rw [heq]
    simpa only [mul_add] using
      (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
  have hV : 0 ≤ iterRdivStability a (δ n) lam := by
    unfold iterRdivStability iterRdivScale
    positivity
  have hpow : 0 ≤ Q ^ α := Real.rpow_nonneg hQ _
  have hCK : K ≤ C := by dsimp [C]; linarith only [hCevent, hS]
  have hCV : 2 * Cevent ≤ C := by dsimp [C]; linarith only [hK, hS]
  have hCS : 2 * S ≤ C := by dsimp [C]; linarith only [hK, hCevent]
  refine ⟨hweak.trans (mul_le_mul_of_nonneg_right hCK hQ), ?_⟩
  have hv := mul_le_mul_of_nonneg_right hCV hV
  have hs := mul_le_mul_of_nonneg_right hCS hpow
  change ‖h - minNormSolution V‖ ^ 2 ≤ C * (iterRdivStability a (δ n) lam + Q ^ α)
  nlinarith only [htotal, hstrongvar, hstrongbias, hv, hs]


-- @node: ass:pin-187
/-- For [an IV world](hyp:V), [a sampling law](hyp:P), [an analysis sample](hyp:sample), [a sample split](hyp:split), [an integration measure](hyp:mu), [fitted densities](hyp:gHat), [fitted pilots](hyp:rHat), [a grid ratio](hyp:ρ), [a failure probability](hyp:ξ), [an oracle scale](hyp:c), [an iteration multiplier](hyp:a), [a source exponent](hyp:β), [an iteration horizon](hyp:t), [density accuracy](hyp:δ), [pilot accuracy](hyp:ν), [a source vector](hyp:w₀), [fitted iterative estimates](hyp:iter), [a sample size](hyp:n), [an event](hyp:E), and [an envelope constant](hyp:C), [the pinned iterative RDIV envelope reading](goal) is the assertion that the event is measurable, has probability at least 1−ξ, and carries a positive-constant discrepancy bound: throughout the oracle grid segment, the final calibration statistic is at most the iterative noise plus the envelope constant times the squared source norm times the penalty to the qualification exponent. -/
noncomputable def PinIterRDIVEnvelopeReading (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ ξ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ) (w₀ : V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  IterRDIVDiscrepancyEnvelope V P sample split mu gHat rHat
    ρ ξ c a β t δ ν w₀ iter n E C







end Papers.TsAdaptiveEstimationInference
