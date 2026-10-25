module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIV
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRateEvents
/-! Recursive stability on the actual RDIV oracle segment.

The population-only coefficients of the joint fitting/calibration construction
are retained. Membership and training measurability are obtained from the actual
selected iterates, and population membership uses precisely the recorded oracle
realizability condition. No comparison certificate or oracle event is assumed.
-/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]

/-- Assume [fixed-center loss concentration](hyp:hFix), [squared-loss concentration](hyp:hSq),
[localized density concentration](hyp:hLi), [the instrumental-variable model](hyp:hIV),
[the range condition](hyp:hRange), [density realizability](hyp:hDensity), [the density
bounds](hyp:hBounds), [the outcome bound](hyp:hY), and [the hypothesis-class bound](hyp:hHyp).
Then [there are a population propagation sequence, a positive calibration constant, and
a sufficient inflation threshold such that calibrated, realizable selected iterates on
any stable oracle segment share a measurable event of probability at least one minus the
confidence level: their weighted Hilbert and projected squared fitting errors are bounded
by the iteration coefficient times squared fitting accuracy divided by penalty, their
Hilbert squared errors by the same numerator divided by squared penalty, and their terminal
calibration errors by the calibration constant times calibration accuracy times projected
error plus squared calibration accuracy, provided the pilot, selection, measurability,
version, boundedness, and critical-radius requirements hold](goal). -/
-- @node: iter_rdiv_selected_oracle_segment_event
lemma iter_rdiv_selected_oracle_segment_event
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
    ∃ aSeq : ℕ → ℝ, aSeq 0 = 0 ∧ (∀ j, 1 ≤ j → 1 ≤ aSeq j) ∧
    ∃ C > (0 : ℝ),
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
    ∃ required ≥ (1 : ℝ), ∀ (ξ c a β : ℝ) (t : ℕ)
      (δ ν baseδ baseν : ℕ → ℝ) (κδ κν : ℝ)
      (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
    ρ ∈ Set.Ico (1 / 2 : ℝ) 1 → ξ ∈ Set.Ioo (0 : ℝ) 1 →
    RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t →
    CalibratedValidBounds δ ν baseδ baseν κδ κν required →
    IterRealizableRDIV V ρ c a β t δ ν →
    IterRDIVMinimaAttained V P sample split mu gHat ρ t iter →
    ∀ n, 0 < n → IterRDIVOracleSegmentStability ρ c a β t δ ν n →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
        ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter n j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          aSeq j * δ n ^ 2 / lam ∧
        ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 ≤
          aSeq j * δ n ^ 2 / lam ^ 2) ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) -
          ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2| ≤
          C * ν n * ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ + C * ν n ^ 2) := by
  obtain ⟨D, hD, C, hC, hevent⟩ := iter_rdiv_joint_stability_calibration_event
    (pilotInputSupport := pilotInputSupport) V hFix hSq hLi mu G g₀ support B c₀ CG
    hIV hRange hDensity hBounds hY hHyp
  obtain ⟨hzero, _, hpositive⟩ := iterRdivStabilityCoefficients_bounds D hD
  refine ⟨iterRdivStabilityCoefficients D, hzero, hpositive, C, hC, ?_⟩
  intro P hProbability sample split gHat rHat ρ rawG rawH rawR hPilot hMLE
    hMeas hLikMeas hDensityVersion hPilotVersion hPilotBound hVersion hG hH hFloor
  obtain ⟨required, hrequired, hevent⟩ := hevent P hProbability sample split
    gHat rHat ρ rawG rawH rawR hPilot hMLE hMeas hLikMeas hDensityVersion
    hPilotVersion hPilotBound hVersion hG hH hFloor
  refine ⟨required, hrequired, ?_⟩
  intro ξ c a β t δ ν baseδ baseν κδ κν iter hρ hξ hScale hInflation
    hRealizable hMinima n hn hOracle
  have hρpos : 0 < ρ := by linarith only [hρ.1]
  have hdomain (lam : ℝ) (hlam : lam ∈ regGrid ρ n)
      (_ : lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2) :
      lam ∈ Set.Ioc (0 : ℝ) 2 := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
    refine ⟨mul_pos (by norm_num) (pow_pos hρpos _), ?_⟩
    have hp := pow_le_pow_of_le_one hρpos.le hρ.2.le (Nat.zero_le k)
    simpa only [pow_zero, mul_one, gridValue] using
      mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  exact hevent ξ t δ ν baseδ baseν κδ κν hρ hξ hScale hInflation n
    (Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2)
    (iterRdivOracleRadius c a β t δ ν n) ⟨hOracle, fun lam _ hs => hs.1⟩
    (fun j lam => iter n j lam)
    hn hdomain
    (fun lam hlam hs j hj hjt => hRealizable n hOracle j hj hjt lam hlam hs)
    (fun lam hlam _ => (hMinima n hn lam hlam).1)
    (fun lam hlam ω => ((hMinima n hn lam hlam).1.2 t hScale.1 le_rfl ω).1)
    (fun lam hlam => (hMinima n hn lam hlam).2 t le_rfl)

/-- Suppose [the grid ratio is at least one half and below one](hyp:hρ), [the oracle multiplier
is positive](hyp:hc), [the propagation coefficient is at least one](hyp:ha), [the source
exponent is positive](hyp:hβ), and [the confidence level lies strictly between zero and
one](hyp:hξ). If [the base accuracies dominate the raw fitting and calibration scales
and their sum converges to zero, with a horizon of at least one](hyp:hScale),
[the public accuracies are valid inflations of those bases](hyp:hInflation), [the public
accuracies are nonnegative](hyp:hNonneg), and [the three raw rates
are nonnegative at their prescribed confidence arguments for every positive sample
size](hyp:hRates), then [the oracle segment satisfies its stability conditions for all
sufficiently large sample sizes](goal). -/
-- @node: iter_rdiv_oracle_exists_of_inflation
lemma iter_rdiv_oracle_exists_of_inflation (ρ c a β ξ : ℝ) (t : ℕ)
    (δ ν baseδ baseν : ℕ → ℝ) (rawG rawH rawR : ℕ → ℝ → ℝ)
    (κδ κν required : ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hc : 0 < c) (ha : 1 ≤ a)
    (hβ : 0 < β) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hScale : RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t)
    (hInflation : CalibratedValidBounds δ ν baseδ baseν κδ κν required)
    (hNonneg : CalibrationDeterministic δ ν)
    (hRates : ∀ n, 0 < n →
      0 ≤ rawG n (ξ / 4) ∧
      0 ≤ rawH n (iterGridConfidence ρ ξ n t / 4) ∧ 0 ≤ rawR n (ξ / 4)) :
    ∀ᶠ n in atTop, IterRDIVOracleSegmentStability ρ c a β t δ ν n := by
  have hlim := iter_rdiv_inflated_scales_tendsto δ ν baseδ baseν κδ κν required
    hInflation hNonneg hScale.2.2
  have hbaseδ (n : ℕ) : 0 ≤ baseδ n := by
    apply (mul_nonneg_iff_of_pos_left (by linarith only [hInflation.1] : 0 < κδ)).1
    simpa only [hInflation.2.2.2.2.1 n] using hNonneg.1 n
  have hbaseν (n : ℕ) : 0 ≤ baseν n := by
    apply (mul_nonneg_iff_of_pos_left (by linarith only [hInflation.2.1] : 0 < κν)).1
    simpa only [hInflation.2.2.2.2.2 n] using hNonneg.2 n
  have hcal : RDIVScaleCalibration ρ ξ δ ν rawG rawH rawR t := by
    refine ⟨hScale.1, ?_, ?_⟩
    · intro n hn
      constructor
      · apply (hScale.2.1 n hn).1.trans
        rw [hInflation.2.2.2.2.1 n]
        exact le_mul_of_one_le_left (hbaseδ n) hInflation.1
      · apply (hScale.2.1 n hn).2.trans
        rw [hInflation.2.2.2.2.2 n]
        exact le_mul_of_one_le_left (hbaseν n) hInflation.2.1
    · simpa only [add_zero] using hlim.1.add hlim.2
  -- The older oracle lemma asks for nonnegativity even at unused confidence
  -- arguments. Truncation fills only those irrelevant values; at every actual
  -- allocated argument it is the identity, as proved from hRates.
  have hclipped : RDIVScaleCalibration ρ ξ δ ν
      (fun n η => max (rawG n η) 0) (fun n η => max (rawH n η) 0)
      (fun n η => max (rawR n η) 0) t := by
    refine ⟨hcal.1, ?_, hcal.2.2⟩
    intro n hn
    obtain ⟨hg, hh, hr⟩ := hRates n hn
    simpa only [rdivEvaluatedAccuracy, max_eq_left hg, max_eq_left hh,
      max_eq_left hr] using hcal.2.1 n hn
  exact iterRdivOracleExists ρ c a β ξ t δ ν
    (fun n η => max (rawG n η) 0) (fun n η => max (rawH n η) 0)
    (fun n η => max (rawR n η) 0)
    hρ hc ha hβ hScale.1 hξ hclipped hNonneg
    (fun _ _ _ _ => ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _⟩)

/-- Under [fixed-center loss concentration](hyp:hFix), [squared-loss concentration](hyp:hSq),
[localized density concentration](hyp:hLi), [the instrumental-variable model](hyp:hIV),
[the range condition](hyp:hRange), [density realizability](hyp:hDensity), [the density
bounds](hyp:hBounds), [the outcome bound](hyp:hY), and [the hypothesis-class bound](hyp:hHyp),
[population propagation and calibration constants and an inflation threshold exist such
that, for calibrated nonnegative vanishing accuracies, positive source parameters,
realizable population iterates and attained empirical minima, every sufficiently large
sample size admits one measurable event of probability at least one minus the confidence
level giving recursive weighted and Hilbert fitting-error bounds throughout the oracle
segment and terminal calibration bounds throughout the grid, whenever the pilot,
selection, measurability, version, boundedness and critical-radius requirements hold](goal). -/
-- @node: iter_rdiv_eventual_selected_stability
lemma iter_rdiv_eventual_selected_stability
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
    ∃ aSeq : ℕ → ℝ, aSeq 0 = 0 ∧ (∀ j, 1 ≤ j → 1 ≤ aSeq j) ∧
    ∃ C > (0 : ℝ),
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
    ∃ required ≥ (1 : ℝ), ∀ (ξ c a β : ℝ) (t : ℕ)
      (δ ν baseδ baseν : ℕ → ℝ) (κδ κν : ℝ)
      (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
    ρ ∈ Set.Ico (1 / 2 : ℝ) 1 → ξ ∈ Set.Ioo (0 : ℝ) 1 →
    RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t →
    CalibratedValidBounds δ ν baseδ baseν κδ κν required →
    CalibrationDeterministic δ ν → 0 < c → 1 ≤ a → 0 < β →
    IterRealizableRDIV V ρ c a β t δ ν →
    IterRDIVMinimaAttained V P sample split mu gHat ρ t iter →
    ∀ᶠ n in atTop, ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
        ∀ j, 1 ≤ j → j ≤ t →
        lam * ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 +
            ‖projCondExpOp V (iter n j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          aSeq j * δ n ^ 2 / lam ∧
        ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 ≤
          aSeq j * δ n ^ 2 / lam ^ 2) ∧
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) -
          ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2| ≤
          C * ν n * ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ + C * ν n ^ 2) := by
  obtain ⟨aSeq, hzero, hpositive, C, hC, hevent⟩ :=
    iter_rdiv_selected_oracle_segment_event (pilotInputSupport := pilotInputSupport)
      V hFix hSq hLi mu G g₀ support B c₀ CG hIV hRange hDensity hBounds hY hHyp
  refine ⟨aSeq, hzero, hpositive, C, hC, ?_⟩
  intro P hProbability sample split gHat rHat ρ rawG rawH rawR hPilot hMLE
    hMeas hLikMeas hDensityVersion hPilotVersion hPilotBound hVersion hG hH hFloor
  obtain ⟨required, hrequired, hevent⟩ := hevent P hProbability sample split
    gHat rHat ρ rawG rawH rawR hPilot hMLE hMeas hLikMeas hDensityVersion
    hPilotVersion hPilotBound hVersion hG hH hFloor
  refine ⟨required, hrequired, ?_⟩
  intro ξ c a β t δ ν baseδ baseν κδ κν iter hρ hξ hScale hInflation
    hNonneg hc ha hβ hRealizable hMinima
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  have hRates (n : ℕ) (hn : 0 < n) :
      0 ≤ rawG n (ξ / 4) ∧
      0 ≤ rawH n (iterGridConfidence ρ ξ n t / 4) ∧ 0 ≤ rawR n (ξ / 4) := by
    obtain ⟨hbudget, heq⟩ := iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1
    have hh := (hH n hn _ hbudget).1.1.le
    rw [heq] at hh
    exact ⟨(hG n hn _ hquarter).1.le, hh, (hPilot.2 n hn _ hquarter).1⟩
  have horacle := iter_rdiv_oracle_exists_of_inflation ρ c a β ξ t δ ν baseδ baseν
    rawG rawH rawR κδ κν required hρ hc ha hβ hξ hScale hInflation hNonneg hRates
  filter_upwards [horacle, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  exact hevent ξ c a β t δ ν baseδ baseν κδ κν iter hρ hξ hScale hInflation
    hRealizable hMinima n hn0 hn

end Papers.TsAdaptiveEstimationInference
