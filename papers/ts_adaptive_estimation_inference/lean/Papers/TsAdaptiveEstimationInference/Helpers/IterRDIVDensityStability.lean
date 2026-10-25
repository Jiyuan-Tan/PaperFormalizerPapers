module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVCalibratedStability
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVPreliminaryRateEvent
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVCalibration
/-! Recursive RDIV stability after constructing the preliminary density event.

The propagation coefficient uses density coefficient one and is fixed before
sampling or accuracy curves. The locally proved likelihood constant is absorbed
only into the later calibration threshold. The intersection explicitly spends
half of the confidence budget, retaining quarters for pilot and calibration.
-/
public section
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]

/-- If [the sample size is positive](hyp:hn) and [the confidence allocation is
in $(0,1/2]$](hyp:hη), then [halving that allocation increases the confidence
floor by at most a factor of two](goal).

Halving a small failure allocation costs at most a fixed factor two in
its explicit logarithmic floor, including at sample size one. -/
-- @node: iter_rdiv_half_confidence_floor
lemma iter_rdiv_half_confidence_floor (n : ℕ) (η : ℝ)
    (hn : 0 < n) (hη : η ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    confidenceFloor n (η / 2) ≤ 2 * confidenceFloor n η := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hinner : Real.log (Real.exp 1 * n) = 1 + Real.log (n : ℝ) := by
    rw [Real.log_mul (Real.exp_pos _).ne' hnR.ne', Real.log_exp]
  have hloglog : 0 ≤ Real.log (Real.log (Real.exp 1 * n)) := by
    apply Real.log_nonneg
    rw [hinner]
    linarith only [hlogn]
  have htwo : (2 : ℝ) ≤ 1 / η := (le_div_iff₀ hη.1).2 (by linarith only [hη.2])
  have hlogtwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
  have hlogη : 0 ≤ Real.log (1 / η) :=
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hlogtwo
  have heq : Real.log (1 / (η / 2)) = Real.log (1 / η) + Real.log 2 := by
    rw [show 1 / (η / 2) = (1 / η) * 2 by ring,
      Real.log_mul (by positivity) (by norm_num)]
  unfold confidenceFloor
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (div_nonneg (add_nonneg hloglog hlogη) hnR.le), heq]
  have hnum : Real.log (Real.log (Real.exp 1 * n)) +
      (Real.log (1 / η) + Real.log 2) ≤
      4 * (Real.log (Real.log (Real.exp 1 * n)) + Real.log (1 / η)) := by
    linarith only [hloglog, hlogη, hlogtwo]
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hnum hnR.le

/-- Given [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [a nonnegative density-rate constant C](hyp:hC), [the
RDIV model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [density bounds](hyp:hBounds), [bounded
outcomes](hyp:hY), and [bounded hypotheses](hyp:hHyp), [a propagation constant
at least one can be fixed before sampling so that admissible selections,
versions, critical-radius curves, and sufficiently inflated calibrated scales
give a measurable event of probability at least one minus a quarter of the
failure probability; on that event, class membership and integrated squared
Hellinger error at most C times squared structural scale imply recursive energy
and squared-error bounds for all empirical iterates in the admissible grid
segment, with denominators equal to the penalty and its square](goal).

Instantiate recursive fitting stability with the paper's actual scales.
The propagation coefficient is fixed before the sampling experiment, curves,
confidence, horizon and deterministic population centers. Density membership
and its rate remain explicit on-event implications for intersection with the
locally constructed preliminary event. -/
-- @node: iter_rdiv_quarter_fitting_stability_event
lemma iter_rdiv_quarter_fitting_stability_event (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG C : ℝ) (hC : 0 ≤ C)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ : ℝ)
      (rawG rawH rawR : ℕ → ℝ → ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
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
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 4 ≤ P.real E ∧
      ∀ ω ∈ E, gHat n ω ∈ G →
      (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ C * δ n ^ 2 →
      ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ^ 2 := by
  obtain ⟨D, hD, hfit⟩ := iter_rdiv_uniform_fitting_stability_event V hFix hSq
    mu G g₀ support B c₀ CG 2 C (by norm_num) hC hIV hRange hDensity hBounds hY hHyp
  refine ⟨D, hD, ?_⟩
  intro P hProbability sample split gHat ρ rawG rawH rawR hMLE hMeas hVersion
    hG hH hFloor
  obtain ⟨required, hrequired, hradii⟩ := iter_rdiv_calibrated_stability_radii V
    mu G g₀ ρ rawG rawH rawR hG hH hFloor
  refine ⟨required, hrequired, ?_⟩
  intro ξ t δ ν baseδ baseν κδ κν hξ hScale hInflation n segment sourceRadius hSourceScope iter hn
    hdom hstar hEst
  obtain ⟨hd, hfloor, hconfidence, hx, hz⟩ := hradii ξ t δ ν baseδ baseν
    κδ κν hξ hScale hInflation n hn
  have hhalf : ξ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast hScale.1
  have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
  have hη : iterGridConfidence ρ ξ n t / 4 ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    have hle : iterGridConfidence ρ ξ n t ≤ ξ := by
      unfold iterGridConfidence
      rw [Nat.cast_mul]
      apply (div_le_iff₀ (by positivity)).2
      nlinarith only [hden, hξ.1]
    constructor
    · unfold iterGridConfidence
      rw [Nat.cast_mul]
      exact div_pos (div_pos hξ.1 (lt_of_lt_of_le zero_lt_one hden)) (by norm_num)
    · linarith only [hle, hξ.2]
  have hηeq : iterGridConfidence ρ (ξ / 2) n t / 4 =
      (iterGridConfidence ρ ξ n t / 4) / 2 := by
    unfold iterGridConfidence
    ring
  have hcf : confidenceFloor n (iterGridConfidence ρ (ξ / 2) n t / 4) ≤
      2 * δ n := by
    rw [hηeq]
    exact (iter_rdiv_half_confidence_floor n _ hn hη).trans
      (mul_le_mul_of_nonneg_left hconfidence (by norm_num))
  have hevent := hfit P hProbability sample split gHat ρ (ξ / 2)
    hMLE hMeas hVersion n t (δ n) segment sourceRadius hSourceScope iter hn hScale.1 hhalf hd hfloor hcf
    hx hz hdom hstar hEst
  simpa only [show ξ / 2 / 2 = ξ / 4 by ring] using hevent

/-- Assume [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [Li's localized likelihood concentration](hyp:hLi),
[the RDIV model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [density bounds](hyp:hBounds), [bounded
outcomes](hyp:hY), and [bounded hypotheses](hyp:hHyp). Then [a propagation
constant at least one can be fixed before sampling such that likelihood
selection, process measurability, coherent density and supremum versions,
critical-radius curves, radius floors, and sufficiently inflated calibrated
scales yield a measurable event of probability at least one minus half the
failure probability, where the selected density belongs to its class, its
integrated squared Hellinger error is at most squared structural scale, operator
error is uniformly at most nuisance scale, and every empirical iterate in the
admissible grid segment satisfies the recursive energy and squared-error bounds](goal).

Remove the density-rate implication from recursive fitting stability by
intersecting with the actual locally proved MLE event. Neither a density rate
nor a probability certificate is supplied by the caller. -/
-- @node: iter_rdiv_density_fitting_stability_event
lemma iter_rdiv_density_fitting_stability_event (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ : ℝ)
      (rawG rawH rawR : ℕ → ℝ → ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    RDIVLikelihoodProcessesMeasurable V G g₀ →
    RDIVSelectedDensityVersion V P sample split mu gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    DensityCriticalRadiusBound V G g₀ rawG →
    HypothesisCriticalRadiusBound V mu G rawH ρ →
    RDIVRadiusFloor rawG rawH ρ →
    (∀ n, 0 < n → ∀ η ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ rawR n η) →
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
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧
      ∀ ω ∈ E, gHat n ω ∈ G ∧
      (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ δ n ^ 2 ∧
      (∀ h ∈ V.H, inputL2Norm (V.law.map V.zOf)
        (estimatedOperator V mu gHat n ω h - dualVersion V (projCondExpOp V h)) ≤ ν n) ∧
      ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ^ 2 := by
  obtain ⟨D, hD, hfit⟩ := iter_rdiv_quarter_fitting_stability_event V hFix hSq
    mu G g₀ support B c₀ CG 1 (by norm_num) hIV hRange hDensity hBounds hY hHyp
  refine ⟨D, hD, ?_⟩
  intro P hProbability sample split gHat ρ rawG rawH rawR hMLE hMeas hLikMeas
    hDensityVersion hVersion hG hH hFloor hRnonneg
  letI : IsProbabilityMeasure P := hProbability
  obtain ⟨K, hK, hfit⟩ := hfit P hProbability sample split gHat ρ rawG rawH rawR
    hMLE hMeas hVersion hG hH hFloor
  obtain ⟨Cd, hCd, hdensity⟩ := rdiv_density_event_uniform_confidence V P sample split
    hLi mu G g₀ gHat support c₀ CG rawG rawH ρ hIV hDensity hBounds
    hDensityVersion hMLE hMeas hLikMeas hG hFloor
  let R := Cd + 1 + 2 * B * Real.sqrt Cd
  have hCdR : Cd + 1 ≤ R := by
    dsimp [R]
    exact le_add_of_nonneg_right (by positivity [hY.1])
  have hopR : 2 * B * Real.sqrt Cd ≤ R := by
    dsimp [R]
    linarith only [hCd]
  refine ⟨max K R, hK.trans (le_max_left _ _), ?_⟩
  intro ξ t δ ν baseδ baseν κδ κν hξ hScale hInflation n segment sourceRadius hSourceScope iter hn
    hdom hstar hEst
  have hInflationK : CalibratedValidBounds δ ν baseδ baseν κδ κν K :=
    ⟨hInflation.1, hInflation.2.1,
      (le_max_left _ _).trans hInflation.2.2.1,
      (le_max_left _ _).trans hInflation.2.2.2.1,
      hInflation.2.2.2.2⟩
  obtain ⟨Ef, hEf, hpEf, hgoodf⟩ := hfit ξ t δ ν baseδ baseν κδ κν
    hξ hScale hInflationK n segment sourceRadius hSourceScope iter hn hdom hstar hEst
  have hhalf : ξ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  obtain ⟨Ed, hEd, hpEd, hgoodd⟩ := hdensity (ξ / 2) hhalf n hn
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  have hbudget := (iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1).1
  have hHpos := (hH n hn _ hbudget).1.1.le
  have hscale := (hScale.2.1 n hn).1
  change rawG n (ξ / 4) + rawH n (iterGridConfidence ρ ξ n t / 4) +
    rdivPublicLogScale ρ ξ n ≤ baseδ n at hscale
  rw [(iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1).2] at hHpos
  have hg0 := (hG n hn _ hquarter).1.le
  have hgbase : rawG n (ξ / 4) ≤ baseδ n := by
    have hlog : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
    linarith only [hscale, hHpos, hlog]
  have hCdκ : Cd ≤ κδ ^ 2 := by
    have hk := hCdR.trans ((le_max_right K R).trans hInflation.2.2.1)
    nlinarith only [hk, hCd, hInflation.1]
  have habsorb : Cd * rawG n (ξ / 4) ^ 2 ≤ δ n ^ 2 := by
    calc
      _ ≤ Cd * baseδ n ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hg0 hgbase 2) hCd.le
      _ ≤ κδ ^ 2 * baseδ n ^ 2 :=
        mul_le_mul_of_nonneg_right hCdκ (sq_nonneg _)
      _ = δ n ^ 2 := by rw [hInflation.2.2.2.2.1 n, mul_pow]
  refine ⟨Ef ∩ Ed, hEf.inter hEd, ?_, ?_⟩
  · have hbad : P.real (Ef ∩ Ed)ᶜ ≤ P.real Efᶜ + P.real Edᶜ := by
      rw [Set.compl_inter]
      exact measureReal_union_le _ _
    linarith only [hbad, hpEf, hpEd, probReal_add_probReal_compl (μ := P) hEf,
      probReal_add_probReal_compl (μ := P) hEd,
      probReal_add_probReal_compl (μ := P) (hEf.inter hEd)]
  · intro ω hω
    obtain ⟨hg, hrate⟩ := hgoodd ω hω.2
    have hrate' : (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z)
        (fun x => g₀ x z) ∂V.law.map V.zOf) ≤ δ n ^ 2 := by
      apply le_trans _ habsorb
      convert hrate using 1 <;> congr 3 <;> ring
    have hraw : (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z)
        (fun x => g₀ x z) ∂V.law.map V.zOf) ≤ Cd * rawG n (ξ / 4) ^ 2 := by
      simpa only [show ξ / 2 / 2 = ξ / 4 by ring] using hrate
    have hr0 : 0 ≤ rawR n (ξ / 4) :=
      hRnonneg n hn _ hquarter
    have hgν : rawG n (ξ / 4) ≤ baseν n := by
      have hs := (hScale.2.1 n hn).2
      change rawG n (ξ / 4) + rawR n (ξ / 4) + rdivPublicLogScale ρ ξ n ≤ baseν n at hs
      have hlog : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
      linarith only [hs, hr0, hlog]
    refine ⟨hg, hrate', ?_, ?_⟩
    · exact iter_rdiv_operator_rate_of_inflation V mu G g₀ gHat support
        B c₀ CG Cd _ _ κν (ν n) n ω hIV hDensity hBounds hHyp hY.1 hg hCd.le
        hg0 hraw hgν (hopR.trans ((le_max_right K R).trans hInflation.2.2.2.1))
        (hInflation.2.2.2.2.2 n)
    exact hgoodf ω hω.1 hg (by simpa only [one_mul] using hrate')

/-- Under [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [Li's localized likelihood concentration](hyp:hLi),
[the RDIV model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [density bounds](hyp:hBounds), [bounded
outcomes](hyp:hY), and [bounded hypotheses](hyp:hHyp), [there is a propagation
constant fixed before sampling and, for admissible measurable selections,
coherent versions and raw radius curves, positive preliminary and fitting
constants and an inflation threshold such that every sufficiently inflated
calibrated scale yields a measurable event of probability at least one minus
half the failure probability; it simultaneously retains density membership,
calibrated density and operator error bounds, recursive energy and squared-error
bounds, a raw quarter-confidence density rate, and uniform raw quarter-grid
fixed-center deviation bounds on the admissible iteration-grid segment](goal).

Retain raw density and fixed-center fitting data on the constructed half-budget
event, alongside the original calibrated recursive estimates. The propagation
coefficient precedes the experiment. The auxiliary raw-data constants and later
calibration threshold may use the fixed raw curves and
their recorded radius-floor data. This is the remaining local event
construction obligation, not a cited theorem or an additional assumption. -/
lemma iter_rdiv_density_fitting_retained_event (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B) :
    ∃ D ≥ (1 : ℝ),
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → X → Z → ℝ) (ρ : ℝ)
      (rawG rawH rawR : ℕ → ℝ → ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    RDIVLikelihoodProcessesMeasurable V G g₀ →
    RDIVSelectedDensityVersion V P sample split mu gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    DensityCriticalRadiusBound V G g₀ rawG →
    HypothesisCriticalRadiusBound V mu G rawH ρ →
    RDIVRadiusFloor rawG rawH ρ →
    (∀ n, 0 < n → ∀ η ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ rawR n η) →
    ∃ Cpre > (0 : ℝ), ∃ Cfit > (0 : ℝ), ∃ required ≥ (1 : ℝ), ∀ (ξ : ℝ) (t : ℕ)
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
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧
      (∀ ω ∈ E, gHat n ω ∈ G ∧
      (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ δ n ^ 2 ∧
      (∀ h ∈ V.H, inputL2Norm (V.law.map V.zOf)
        (estimatedOperator V mu gHat n ω h - dualVersion V (projCondExpOp V h)) ≤ ν n) ∧
      ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ∧
        ‖iter j lam ω - populationIterate V lam j‖ ^ 2 ≤
          iterRdivStabilityCoefficients D j * δ n ^ 2 / lam ^ 2) ∧
      (∀ ω ∈ E,
        (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
          ∂V.law.map V.zOf) ≤ Cpre * rawG n (ξ / 4) ^ 2 ∧
        ∀ lam ∈ regGrid ρ n, lam ∈ segment → ∀ j, 1 ≤ j → j ≤ t →
        ∀ h ∈ V.H,
        |blockAverage V P sample (split.fit n)
            (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
              iterRdivFixedCenterLoss V mu (gHat n ω) lam j
                (populationIterate V lam j) w) ω -
          ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w ∂V.law| ≤
          Cfit * (rawH n (iterGridConfidence ρ ξ n t / 4) *
            ‖h - populationIterate V lam j‖ +
            rawH n (iterGridConfidence ρ ξ n t / 4) ^ 2)) := by
  obtain ⟨D, hD, Kfit, hKfit, hfit⟩ := iter_rdiv_uniform_fitting_stability_two_radii_event V hFix hSq
    mu G g₀ support B c₀ CG 2 1 (by norm_num) (by norm_num) hIV hRange hDensity hBounds hY hHyp
  refine ⟨D, hD, ?_⟩
  intro P hProbability sample split gHat ρ rawG rawH rawR hMLE hMeas hLikMeas
    hDensityVersion hVersion hG hH hFloor hRnonneg
  letI : IsProbabilityMeasure P := hProbability
  have hFloorCopy := hFloor
  obtain ⟨c, hc, hfloorRaw⟩ := hFloorCopy
  let M := max 1 c⁻¹
  have hM : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  obtain ⟨Cd, hCd, hdensity⟩ := rdiv_density_event_uniform_confidence V P sample split
    hLi mu G g₀ gHat support c₀ CG rawG rawH ρ hIV hDensity hBounds
    hDensityVersion hMLE hMeas hLikMeas hG hFloor
  let R := Cd + 1 + 2 * B * Real.sqrt Cd
  have hCdR : Cd + 1 ≤ R := by
    dsimp [R]
    exact le_add_of_nonneg_right (by positivity [hY.1])
  have hopR : 2 * B * Real.sqrt Cd ≤ R := by
    dsimp [R]
    linarith only [hCd]
  refine ⟨Cd, hCd, Kfit * M ^ 2, by positivity, max M R, hM.trans (le_max_left _ _), ?_⟩
  intro ξ t δ ν baseδ baseν κδ κν hξ hScale hInflation n segment sourceRadius hSourceScope iter hn
    hdom hstar hEst
  have hhalf : ξ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  obtain ⟨Ed, hEd, hpEd, hgoodd⟩ := hdensity (ξ / 2) hhalf n hn
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  have hbudget := (iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1).1
  have hHpos := (hH n hn _ hbudget).1.1.le
  have hscale := (hScale.2.1 n hn).1
  change rawG n (ξ / 4) + rawH n (iterGridConfidence ρ ξ n t / 4) +
    rdivPublicLogScale ρ ξ n ≤ baseδ n at hscale
  rw [(iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1).2] at hHpos
  have hg0 := (hG n hn _ hquarter).1.le
  have hgbase : rawG n (ξ / 4) ≤ baseδ n := by
    have hlog : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
    linarith only [hscale, hHpos, hlog]
  have hCdκ : Cd ≤ κδ ^ 2 := by
    have hk := hCdR.trans ((le_max_right M R).trans hInflation.2.2.1)
    nlinarith only [hk, hCd, hInflation.1]
  have habsorb : Cd * rawG n (ξ / 4) ^ 2 ≤ δ n ^ 2 := by
    calc
      _ ≤ Cd * baseδ n ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hg0 hgbase 2) hCd.le
      _ ≤ κδ ^ 2 * baseδ n ^ 2 :=
        mul_le_mul_of_nonneg_right hCdκ (sq_nonneg _)
      _ = δ n ^ 2 := by rw [hInflation.2.2.2.2.1 n, mul_pow]
  obtain ⟨hx, hz⟩ := hH n hn _ hbudget
  rw [(iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1).2] at hx hz
  let r := M * rawH n (iterGridConfidence ρ ξ n t / 4)
  have hr : 0 < r := mul_pos hMpos hx.1
  have hrawr : rawH n (iterGridConfidence ρ ξ n t / 4) ≤ r := by
    dsimp only [r]
    nlinarith only [hM, hx.1]
  have hrawbase : rawH n (iterGridConfidence ρ ξ n t / 4) ≤ baseδ n := by
    have hlog : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
    linarith only [hscale, hg0, hlog]
  have hrd : r ≤ δ n := by
    rw [hInflation.2.2.2.2.1 n]
    exact mul_le_mul ((le_max_left M R).trans hInflation.2.2.1) hrawbase
      hx.1.le (by linarith only [hInflation.1])
  have hη : iterGridConfidence ρ ξ n t / 4 ∈ Set.Ioc (0 : ℝ) (1 / 4) := by
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast hScale.1
    have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
    have hpos : 0 < iterGridConfidence ρ ξ n t := by
      unfold iterGridConfidence
      rw [Nat.cast_mul]
      exact div_pos hξ.1 (lt_of_lt_of_le zero_lt_one hden)
    have hupper : iterGridConfidence ρ ξ n t ≤ 1 := by
      unfold iterGridConfidence
      rw [Nat.cast_mul]
      exact (div_le_one (by positivity)).2 (hξ.2.le.trans hden)
    constructor <;> linarith only [hpos, hupper]
  have hcf : confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ r := by
    have hf := (hfloorRaw n hn _ hbudget).2
    rw [(iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1).2] at hf
    have hi := mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hc.le)
    have hi' : confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤
        c⁻¹ * rawH n (iterGridConfidence ρ ξ n t / 4) := by
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hi
    exact hi'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.1.le)
  have hsquare : 1 / (n : ℝ) ≤ r ^ 2 :=
    (iter_rdiv_quarter_confidence_square_floor n _ hn hη).trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) hcf 2)
  have hηhalf : iterGridConfidence ρ ξ n t / 4 ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
    ⟨hη.1, by linarith only [hη.2]⟩
  have hcfhalf : confidenceFloor n (iterGridConfidence ρ (ξ / 2) n t / 4) ≤
      2 * r := by
    rw [show iterGridConfidence ρ (ξ / 2) n t / 4 =
      (iterGridConfidence ρ ξ n t / 4) / 2 by unfold iterGridConfidence; ring]
    exact (iter_rdiv_half_confidence_floor n _ hn hηhalf).trans
      (mul_le_mul_of_nonneg_left hcf (by norm_num))
  obtain ⟨Ef, hEf, hpEf, hgoodf, hrawf⟩ := hfit P hProbability sample split gHat ρ
    (ξ / 2) hMLE hMeas hVersion n t r (δ n) segment sourceRadius hSourceScope iter hn hScale.1 hhalf hr hrd
    hsquare hcfhalf (criticalRadiusBound_mono _ _ _ _ _ hx hrawr)
    (fun g hg => criticalRadiusBound_mono _ _ _ _ _ (hz g hg) hrawr) hdom hstar hEst
  have hpEf' : 1 - ξ / 4 ≤ P.real Ef := by
    simpa only [show ξ / 2 / 2 = ξ / 4 by ring] using hpEf
  refine ⟨Ef ∩ Ed, hEf.inter hEd, ?_, ?_, ?_⟩
  · have hbad : P.real (Ef ∩ Ed)ᶜ ≤ P.real Efᶜ + P.real Edᶜ := by
      rw [Set.compl_inter]
      exact measureReal_union_le _ _
    linarith only [hbad, hpEf', hpEd, probReal_add_probReal_compl (μ := P) hEf,
      probReal_add_probReal_compl (μ := P) hEd,
      probReal_add_probReal_compl (μ := P) (hEf.inter hEd)]
  · intro ω hω
    obtain ⟨hg, hrate⟩ := hgoodd ω hω.2
    have hrate' : (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z)
        (fun x => g₀ x z) ∂V.law.map V.zOf) ≤ δ n ^ 2 := by
      apply le_trans _ habsorb
      convert hrate using 1 <;> congr 3 <;> ring
    have hraw : (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z)
        (fun x => g₀ x z) ∂V.law.map V.zOf) ≤ Cd * rawG n (ξ / 4) ^ 2 := by
      simpa only [show ξ / 2 / 2 = ξ / 4 by ring] using hrate
    have hr0 : 0 ≤ rawR n (ξ / 4) :=
      hRnonneg n hn _ hquarter
    have hgν : rawG n (ξ / 4) ≤ baseν n := by
      have hs := (hScale.2.1 n hn).2
      change rawG n (ξ / 4) + rawR n (ξ / 4) + rdivPublicLogScale ρ ξ n ≤ baseν n at hs
      have hlog : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
      linarith only [hs, hr0, hlog]
    refine ⟨hg, hrate', ?_, ?_⟩
    · exact iter_rdiv_operator_rate_of_inflation V mu G g₀ gHat support
        B c₀ CG Cd _ _ κν (ν n) n ω hIV hDensity hBounds hHyp hY.1 hg hCd.le
        hg0 hraw hgν (hopR.trans ((le_max_right M R).trans hInflation.2.2.2.1))
        (hInflation.2.2.2.2.2 n)
    exact hgoodf ω hω.1 hg (by simpa only [one_mul] using hrate')
  · intro ω hω
    refine ⟨?_, ?_⟩
    · simpa only [show ξ / 2 / 2 = ξ / 4 by ring] using (hgoodd ω hω.2).2
    · intro lam hl hs j hj hjt h hh
      apply (hrawf ω hω.1 lam hl hs j hj hjt h hh).trans
      have hM2 : M ≤ M ^ 2 := by nlinarith only [hM]
      have hm := mul_le_mul_of_nonneg_right hM2
        (mul_nonneg hx.1.le (norm_nonneg (h - populationIterate V lam j)))
      have hkm := mul_le_mul_of_nonneg_left hm (show 0 ≤ Kfit by linarith only [hKfit])
      dsimp only [r]
      nlinarith only [hkm]

end Papers.TsAdaptiveEstimationInference
