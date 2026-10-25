module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVDensityStability
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVCalibration
/-! The recursive RDIV fitting event with the preliminary pilot comparison.

The same population-only propagation sequence is retained. Density and fitting
spend half the confidence budget, and the pilot spends one quarter at the
prescribed curve value. Pilot L2 membership costs no probability.
-/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]

/-- Assume [fixed-center loss concentration](hyp:hFix), [squared-loss concentration](hyp:hSq),
[localized density concentration](hyp:hLi), [the instrumental-variable model](hyp:hIV),
[the range condition](hyp:hRange), [density realizability](hyp:hDensity), [the density
bounds](hyp:hBounds), [the outcome bound](hyp:hY), and [the hypothesis-class bound](hyp:hHyp).
Then [population recursion and calibration constants and a sufficient inflation threshold
give a measurable event of probability at least one minus three quarters of the confidence
level, simultaneously controlling density Hellinger error, pilot square integrability and
raw and public pilot errors, uniform operator error, calibration transfer, and recursive
weighted and Hilbert fitting errors on the chosen grid segment, for calibrated accuracies,
admissible penalties, realizable population iterates and empirical minimizers satisfying
the pilot, selection, measurability, version and radius assumptions](goal). -/
-- @node: iter_rdiv_pilot_fitting_stability_event
lemma iter_rdiv_pilot_fitting_stability_event (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ), ∃ Ccal > (0 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ) (ρ : ℝ)
      (rawG rawH rawR : ℕ → ℝ → ℝ),
    PilotRegressionRate V P sample split rHat rawR →
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    RDIVLikelihoodProcessesMeasurable V G g₀ →
    RDIVSelectedDensityVersion V P sample split mu gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    DensityCriticalRadiusBound V G g₀ rawG →
    HypothesisCriticalRadiusBound V mu G rawH ρ →
    RDIVRadiusFloor rawG rawH ρ →
    ∃ required ≥ (1 : ℝ), ∀ (ξ : ℝ) (t : ℕ)
      (δ ν baseδ baseν : ℕ → ℝ) (κδ κν : ℝ),
    ξ ∈ Set.Ioo (0 : ℝ) 1 →
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
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - 3 * ξ / 4 ≤ P.real E ∧
      ∀ ω ∈ E, gHat n ω ∈ G ∧
      (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ δ n ^ 2 ∧
      MemLp (rHat n ω) 2 (V.law.map V.zOf) ∧
      inputL2Norm (V.law.map V.zOf)
        (rHat n ω - dualVersion V (momentRepresenter V)) ≤ rawR n (ξ / 4) ∧
      inputL2Norm (V.law.map V.zOf)
        (rHat n ω - dualVersion V (momentRepresenter V)) ≤ ν n ∧
      (∀ h ∈ V.H, inputL2Norm (V.law.map V.zOf)
        (estimatedOperator V mu gHat n ω h - dualVersion V (projCondExpOp V h)) ≤ ν n) ∧
      (∀ h ∈ V.H, ∀ (stat radius : ℝ), 0 ≤ radius → radius ≤ 2 * ν n →
        |stat - inputL2Norm (V.law.map V.zOf)
          (rHat n ω - estimatedOperator V mu gHat n ω h) ^ 2| ≤
          (4 * B + 8 * B ^ 2 + 3) *
            (radius * inputL2Norm (V.law.map V.zOf)
              (rHat n ω - estimatedOperator V mu gHat n ω h) + radius ^ 2) →
        |stat - ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2| ≤
          Ccal * ν n * ‖projCondExpOp V (h - minNormSolution V)‖ + Ccal * ν n ^ 2) ∧
      ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ^ 2 := by
  obtain ⟨D, hD, hfit⟩ := iter_rdiv_density_fitting_stability_event V hFix hSq hLi
    mu G g₀ support B c₀ CG hIV hRange hDensity hBounds hY hHyp
  -- The calibration transfer constant is fixed before sampling and horizon.
  -- Its explicit value is independent of both selected representatives.
  let K := 4 * B + 8 * B ^ 2 + 3
  let Ccal := 16 * K + 9
  have hK : 0 ≤ K := by dsimp [K]; positivity [hY.1]
  refine ⟨D, hD, Ccal, by dsimp [Ccal]; positivity, ?_⟩
  intro P hProbability sample split gHat rHat ρ rawG rawH rawR hPilot hMLE hMeas
    hLikMeas hDensityVersion hVersion hG hH hFloor
  let : IsProbabilityMeasure P := hProbability
  obtain ⟨required, hrequired, hfit⟩ := hfit P hProbability sample split gHat ρ
    rawG rawH rawR hMLE hMeas hLikMeas hDensityVersion hVersion hG hH hFloor
    (fun n hn η hη => (hPilot.2 n hn η hη).1)
  refine ⟨required, hrequired, ?_⟩
  intro ξ t δ ν baseδ baseν κδ κν hξ hScale hInflation n segment sourceRadius hSourceScope iter hn
    hdom hstar hEst
  obtain ⟨F, hF, hpF, hgood⟩ := hfit ξ t δ ν baseδ baseν κδ κν hξ hScale
    hInflation n segment sourceRadius hSourceScope iter hn hdom hstar hEst
  have hhalf : ξ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  obtain ⟨R, hR, hpR, hpilot⟩ := rdiv_pilot_half_confidence_event V P sample split
    rHat rawR hPilot (ξ / 2) hhalf n hn
  have heq : ξ / 2 / 2 = ξ / 4 := by ring
  simp only [heq] at hpR hpilot
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null
    (hPilot.2 n hn (ξ / 4) hquarter).2.1
  have hpFR : 1 - 3 * ξ / 4 ≤ P.real (F ∩ R) := by
    have hbad : P.real (F ∩ R)ᶜ ≤ P.real Fᶜ + P.real Rᶜ := by
      rw [Set.compl_inter]
      exact measureReal_union_le _ _
    linarith only [hbad, hpF, hpR, probReal_add_probReal_compl (μ := P) hF,
      probReal_add_probReal_compl (μ := P) hR,
      probReal_add_probReal_compl (μ := P) (hF.inter hR)]
  refine ⟨(F ∩ R) \ N, (hF.inter hR).diff hN, ?_, ?_⟩
  · simpa only [measureReal_def, measure_sdiff_null hN0] using hpFR
  · intro ω hω
    obtain ⟨hg, hdensity, hop, hstability⟩ := hgood ω hω.1.1
    have hmem : MemLp (rHat n ω) 2 (V.law.map V.zOf) := by
      by_contra hbad
      exact hω.2 (hsub hbad)
    have hpilot := hpilot ω hω.1.2
    have hG0 := (hG n hn (ξ / 4) hquarter).1.le
    have hs := (hScale.2.1 n hn).2
    change rawG n (ξ / 4) + rawR n (ξ / 4) +
      rdivPublicLogScale ρ ξ n ≤ baseν n at hs
    have hrbase : rawR n (ξ / 4) ≤ baseν n := by
      have hlog : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
      linarith only [hs, hG0, hlog]
    have hbase0 : 0 ≤ baseν n := (hPilot.2 n hn _ hquarter).1.trans hrbase
    have hrν : rawR n (ξ / 4) ≤ ν n := by
      apply hrbase.trans
      rw [hInflation.2.2.2.2.2 n]
      exact le_mul_of_one_le_left hbase0 hInflation.2.1
    refine ⟨hg, hdensity, hmem, hpilot, hpilot.trans hrν, hop, ?_, hstability⟩
    intro h hh stat radius hradius hradiusν hBernstein
    exact iter_rdiv_calibration_comparison_of_nuisance_bounds V mu G g₀ gHat rHat
      support B c₀ CG K hIV hRange hDensity hBounds hHyp hY.1 hK
      n ω h stat radius (ν n) hg hh hmem hradius hradiusν (hpilot.trans hrν)
      (hop h hh) hBernstein

/-- Assume [fixed-center loss concentration](hyp:hFix), [squared-loss concentration](hyp:hSq),
[localized density concentration](hyp:hLi), [the instrumental-variable model](hyp:hIV),
[the range condition](hyp:hRange), [density realizability](hyp:hDensity), [the density
bounds](hyp:hBounds), [the outcome bound](hyp:hY), and [the hypothesis-class bound](hyp:hHyp).
Then [population constants and an inflation threshold give, under calibrated accuracies
and the pilot, selection, measurability, version, radius, source-scope and minimization
requirements, a measurable event of probability at least one minus three quarters of the
confidence level that simultaneously retains density and pilot errors, operator and
calibration comparisons, recursive fitting stability, the preliminary certificate, and
every fixed-center loss-difference deviation bounded by a constant times the raw hypothesis
radius times distance to the population iterate plus its squared radius](goal). -/
lemma iter_rdiv_pilot_fitting_retained_event (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ), ∃ Ccal > (0 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ) (ρ : ℝ)
      (rawG rawH rawR : ℕ → ℝ → ℝ),
    PilotRegressionRate V P sample split rHat rawR →
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    RDIVLikelihoodProcessesMeasurable V G g₀ →
    RDIVSelectedDensityVersion V P sample split mu gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    DensityCriticalRadiusBound V G g₀ rawG →
    HypothesisCriticalRadiusBound V mu G rawH ρ →
    RDIVRadiusFloor rawG rawH ρ →
    ∃ Ccmp > (0 : ℝ), ∃ required ≥ (1 : ℝ), ∀ (ξ : ℝ) (t : ℕ)
      (δ ν baseδ baseν : ℕ → ℝ) (κδ κν : ℝ),
    ξ ∈ Set.Ioo (0 : ℝ) 1 →
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
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - 3 * ξ / 4 ≤ P.real E ∧
      (∀ ω ∈ E, gHat n ω ∈ G ∧
      (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ δ n ^ 2 ∧
      MemLp (rHat n ω) 2 (V.law.map V.zOf) ∧
      inputL2Norm (V.law.map V.zOf)
        (rHat n ω - dualVersion V (momentRepresenter V)) ≤ rawR n (ξ / 4) ∧
      inputL2Norm (V.law.map V.zOf)
        (rHat n ω - dualVersion V (momentRepresenter V)) ≤ ν n ∧
      (∀ h ∈ V.H, inputL2Norm (V.law.map V.zOf)
        (estimatedOperator V mu gHat n ω h - dualVersion V (projCondExpOp V h)) ≤ ν n) ∧
      (∀ h ∈ V.H, ∀ (stat radius : ℝ), 0 ≤ radius → radius ≤ 2 * ν n →
        |stat - inputL2Norm (V.law.map V.zOf)
          (rHat n ω - estimatedOperator V mu gHat n ω h) ^ 2| ≤
          (4 * B + 8 * B ^ 2 + 3) *
            (radius * inputL2Norm (V.law.map V.zOf)
              (rHat n ω - estimatedOperator V mu gHat n ω h) + radius ^ 2) →
        |stat - ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2| ≤
          Ccal * ν n * ‖projCondExpOp V (h - minNormSolution V)‖ + Ccal * ν n ^ 2) ∧
      ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ^ 2) ∧
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
  obtain ⟨D, hD, hfit⟩ :=
    iter_rdiv_density_fitting_retained_event V hFix hSq hLi
    mu G g₀ support B c₀ CG hIV hRange hDensity hBounds hY hHyp
  -- The calibration transfer constant is fixed before sampling and horizon.
  -- Its explicit value is independent of both selected representatives.
  let K := 4 * B + 8 * B ^ 2 + 3
  let Ccal := 16 * K + 9
  have hK : 0 ≤ K := by dsimp [K]; positivity [hY.1]
  refine ⟨D, hD, Ccal, by dsimp [Ccal]; positivity, ?_⟩
  intro P hProbability sample split gHat rHat ρ rawG rawH rawR hPilot hMLE hMeas
    hLikMeas hDensityVersion hVersion hG hH hFloor
  let : IsProbabilityMeasure P := hProbability
  obtain ⟨Cpre, hCpre, Cfit, hCfit, required, hrequired, hfit⟩ :=
    hfit P hProbability sample split gHat ρ
    rawG rawH rawR hMLE hMeas hLikMeas hDensityVersion hVersion hG hH hFloor
    (fun n hn η hη => (hPilot.2 n hn η hη).1)
  let Cg := 2 * B * Real.sqrt Cpre
  let Cr := Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt Cpre
  let Cl := 4 * B * Cr + 2 * Cg
  let Ccmp := Cpre + Cg + Cr + Cl + Cfit + 1
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity [hY.1]
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCl : 0 ≤ Cl := by dsimp [Cl]; positivity [hY.1]
  have hdC : Cpre ≤ Ccmp := by dsimp [Ccmp]; linarith only [hCg, hCr, hCl, hCfit]
  have hgC : Cg ≤ Ccmp := by dsimp [Ccmp]; linarith only [hCpre, hCr, hCl, hCfit]
  have hrC : Cr ≤ Ccmp := by dsimp [Ccmp]; linarith only [hCpre, hCg, hCl, hCfit]
  have hlC : Cl ≤ Ccmp := by dsimp [Ccmp]; linarith only [hCpre, hCg, hCr, hCfit]
  have hfC : Cfit ≤ Ccmp := by dsimp [Ccmp]; linarith only [hCpre, hCg, hCr, hCl]
  refine ⟨Ccmp, by dsimp [Ccmp]; positivity, required, hrequired, ?_⟩
  intro ξ t δ ν baseδ baseν κδ κν hξ hScale hInflation n segment sourceRadius hSourceScope iter hn
    hdom hstar hEst
  obtain ⟨F, hF, hpF, hgood, hraw⟩ := hfit ξ t δ ν baseδ baseν κδ κν hξ hScale
    hInflation n segment sourceRadius hSourceScope iter hn hdom hstar hEst
  have hhalf : ξ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  obtain ⟨R, hR, hpR, hpilot⟩ := rdiv_pilot_half_confidence_event V P sample split
    rHat rawR hPilot (ξ / 2) hhalf n hn
  have heq : ξ / 2 / 2 = ξ / 4 := by ring
  simp only [heq] at hpR hpilot
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null
    (hPilot.2 n hn (ξ / 4) hquarter).2.1
  have hpFR : 1 - 3 * ξ / 4 ≤ P.real (F ∩ R) := by
    have hbad : P.real (F ∩ R)ᶜ ≤ P.real Fᶜ + P.real Rᶜ := by
      rw [Set.compl_inter]
      exact measureReal_union_le _ _
    linarith only [hbad, hpF, hpR, probReal_add_probReal_compl (μ := P) hF,
      probReal_add_probReal_compl (μ := P) hR,
      probReal_add_probReal_compl (μ := P) (hF.inter hR)]
  refine ⟨(F ∩ R) \ N, (hF.inter hR).diff hN, ?_, ?_, ?_⟩
  · simpa only [measureReal_def, measure_sdiff_null hN0] using hpFR
  · intro ω hω
    obtain ⟨hg, hdensity, hop, hstability⟩ := hgood ω hω.1.1
    have hmem : MemLp (rHat n ω) 2 (V.law.map V.zOf) := by
      by_contra hbad
      exact hω.2 (hsub hbad)
    have hpilot := hpilot ω hω.1.2
    have hG0 := (hG n hn (ξ / 4) hquarter).1.le
    have hs := (hScale.2.1 n hn).2
    change rawG n (ξ / 4) + rawR n (ξ / 4) +
      rdivPublicLogScale ρ ξ n ≤ baseν n at hs
    have hrbase : rawR n (ξ / 4) ≤ baseν n := by
      have hlog : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
      linarith only [hs, hG0, hlog]
    have hbase0 : 0 ≤ baseν n := (hPilot.2 n hn _ hquarter).1.trans hrbase
    have hrν : rawR n (ξ / 4) ≤ ν n := by
      apply hrbase.trans
      rw [hInflation.2.2.2.2.2 n]
      exact le_mul_of_one_le_left hbase0 hInflation.2.1
    refine ⟨hg, hdensity, hmem, hpilot, hpilot.trans hrν, hop, ?_, hstability⟩
    intro h hh stat radius hradius hradiusν hBernstein
    exact iter_rdiv_calibration_comparison_of_nuisance_bounds V mu G g₀ gHat rHat
      support B c₀ CG K hIV hRange hDensity hBounds hHyp hY.1 hK
      n ω h stat radius (ν n) hg hh hmem hradius hradiusν (hpilot.trans hrν)
      (hop h hh) hBernstein
  · intro ω hω
    obtain ⟨hg, _, _, _⟩ := hgood ω hω.1.1
    obtain ⟨hrate, hdev⟩ := hraw ω hω.1.1
    have hmem : MemLp (rHat n ω) 2 (V.law.map V.zOf) := by
      by_contra hbad
      exact hω.2 (hsub hbad)
    have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith only [hξ.1, hξ.2]
    have hd : 0 ≤ rawG n (ξ / 4) := (hG n hn _ hquarter).1.le
    refine ⟨hg, ?_, ?_⟩
    · refine ⟨hrate.trans (mul_le_mul_of_nonneg_right hdC (sq_nonneg _)),
        hmem, hpilot ω hω.1.2, ?_, ?_, ?_⟩
      · intro h hh
        exact (rdiv_estimated_operator_global_rate V mu G g₀ gHat support B c₀ CG
          Cpre (rawG n (ξ / 4)) n ω hIV hDensity hBounds hHyp hY.1 hg
          hCpre.le hd hrate h hh).trans (mul_le_mul_of_nonneg_right hgC hd)
      · intro h hh h' hh'
        exact (rdiv_estimated_operator_relative_rate V mu G g₀ gHat support c₀ CG
          Cpre (rawG n (ξ / 4)) n ω hIV hDensity hBounds hg hCpre.le hd hrate
          (h - h')).trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hrC hd) (norm_nonneg _))
      · intro h hh h' hh'
        exact (rdiv_conditional_population_loss_rate V mu G g₀ gHat support B c₀ CG
          Cpre (rawG n (ξ / 4)) n ω hIV hDensity hBounds hHyp hY hg hCpre.le
          hd hrate h hh h' hh').trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hlC hd) (norm_nonneg _))
    · intro lam hl hs j hj hjt h hh
      have hη := iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1
      have hh0 := (hH n hn _ hη.1).1.1.le
      rw [hη.2] at hh0
      exact (hdev lam hl hs j hj hjt h hh).trans
        (mul_le_mul_of_nonneg_right hfC (by positivity))


end Papers.TsAdaptiveEstimationInference
