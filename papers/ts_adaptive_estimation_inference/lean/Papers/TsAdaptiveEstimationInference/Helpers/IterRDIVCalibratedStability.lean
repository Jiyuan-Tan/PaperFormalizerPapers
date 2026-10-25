module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRadius
public import Mathlib.Analysis.Complex.ExponentialBounds
/-! Calibrated radii for the recursive RDIV stability event.
The existing multiplier policy absorbs the fixed radius-floor constant.
No comparison between accuracy curves at different confidence levels is used.
-/
public section
set_option linter.style.longLine false

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]

/-- If [the sample size is positive](hyp:hn) and [the confidence allocation is
in $(0,1/4]$](hyp:hη), then [the squared confidence floor is at least the inverse
sample size](goal).

At a quarter allocation the confidence floor contains the inverse sample
size even at n=1. This is a scalar property of the recorded floor. -/
-- @node: iter_rdiv_quarter_confidence_square_floor
lemma iter_rdiv_quarter_confidence_square_floor (n : ℕ) (η : ℝ)
    (hn : 0 < n) (hη : η ∈ Set.Ioc (0 : ℝ) (1 / 4)) :
    1 / (n : ℝ) ≤ confidenceFloor n η ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hη1 : η < 1 := by linarith only [hη.2]
  have hlog := confidenceFloor_log_le n η hn ⟨hη.1, hη1⟩
  have hinv : (3 : ℝ) ≤ 1 / η := (le_div_iff₀ hη.1).2 (by linarith only [hη.2])
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hlogη := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hinv
  apply (div_le_iff₀ hnR).2
  nlinarith only [hlog, hlog3, hlogη]

/-- If [the density curve bounds its critical radius](hyp:hG), [the hypothesis
curve bounds the structural and density-induced critical radii](hyp:hH), and
[the raw curves satisfy the radius floor](hyp:hFloor), then [there is an
inflation threshold at least one such that every calibrated valid scale at any
positive sample size is positive, has square at least the inverse sample size,
dominates the quarter-grid confidence floor, and bounds both the structural
critical radius and every density-induced critical radius](goal).

Choose an inflation threshold once, before confidence and source data.
The actual calibrated radius satisfies both source radius conditions and the
small-sample squared floor, with confidence-floor multiplier exactly one. -/
-- @node: iter_rdiv_calibrated_stability_radii
lemma iter_rdiv_calibrated_stability_radii (V : IVWorld W X Z)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (ρ : ℝ) (rawG rawH rawR : ℕ → ℝ → ℝ)
    (hG : DensityCriticalRadiusBound V G g₀ rawG)
    (hH : HypothesisCriticalRadiusBound V mu G rawH ρ)
    (hFloor : RDIVRadiusFloor rawG rawH ρ) :
    ∃ required ≥ (1 : ℝ), ∀ (ξ : ℝ) (t : ℕ)
      (δ ν baseδ baseν : ℕ → ℝ) (κδ κν : ℝ),
      ξ ∈ Set.Ioo (0 : ℝ) 1 →
      RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t →
      CalibratedValidBounds δ ν baseδ baseν κδ κν required →
      ∀ n, 0 < n →
        0 < δ n ∧ 1 / (n : ℝ) ≤ δ n ^ 2 ∧
        confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ δ n ∧
        IsCriticalRadiusBound (V.law.map V.xOf) (primalVersion V '' V.H) n (δ n) ∧
        (∀ g ∈ G, IsCriticalRadiusBound (V.law.map V.zOf)
          (densityOperator mu g '' (primalVersion V '' V.H)) n (δ n)) := by
  obtain ⟨K, hK, hradii⟩ := iter_rdiv_calibrated_radii V mu G g₀ ρ
    rawG rawH rawR hG hH hFloor
  refine ⟨K, hK, ?_⟩
  intro ξ t δ ν baseδ baseν κδ κν hξ hScale hInflation n hn
  have hid : CalibratedValidBounds baseδ baseν baseδ baseν 1 1 1 :=
    ⟨le_rfl, le_rfl, le_rfl, le_rfl, fun _ => (one_mul _).symm,
      fun _ => (one_mul _).symm⟩
  obtain ⟨hbase, _, hconfidence, _, _⟩ := hradii ξ t baseδ baseν baseδ baseν
    1 1 1 hξ hScale hid n hn
  obtain ⟨hd, _, _, hx, hz⟩ := hradii ξ t δ ν baseδ baseν
    κδ κν K hξ hScale hInflation n hn
  have hcf : confidenceFloor n (iterGridConfidence ρ ξ n t / 4) ≤ δ n := by
    apply hconfidence.trans
    rw [hInflation.2.2.2.2.1 n]
    exact mul_le_mul_of_nonneg_right hInflation.2.2.1 hbase.le
  have hbudget := (iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1).1
  have hηpos : 0 < iterGridConfidence ρ ξ n t / 4 := by
    rw [← (iter_rdiv_quarter_budget ρ ξ n t hξ hScale.1).2]
    unfold gridConfidence
    positivity [hbudget.1]
  have hηupper : iterGridConfidence ρ ξ n t / 4 ≤ (1 / 4 : ℝ) := by
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast hScale.1
    have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
    unfold iterGridConfidence
    rw [Nat.cast_mul]
    have hη : ξ / ((t : ℝ) * (terminalIndex ρ n + 1 : ℕ)) ≤ 1 :=
      (div_le_one (by positivity)).2 (hξ.2.le.trans hden)
    linarith only [hη]
  refine ⟨hd, ?_, hcf, hx, hz⟩
  exact (iter_rdiv_quarter_confidence_square_floor n _ hn ⟨hηpos, hηupper⟩).trans
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) hcf 2)

/-- Given [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [a nonnegative density-rate constant C](hyp:hC), [the
RDIV model](hyp:hIV), [the range condition](hyp:hRange), [density
realizability](hyp:hDensity), [density bounds](hyp:hBounds), [outcomes bounded
by B](hyp:hY), and [hypotheses bounded by B](hyp:hHyp), [there is a propagation
constant at least one, fixed before sampling, such that admissible measurable
selections, coherent versions, critical-radius curves, and sufficiently inflated
calibrated scales yield a measurable event of probability at least one minus
half the failure probability; whenever the selected density is class-valued and
has integrated squared Hellinger error at most C times squared structural scale,
every empirical iterate on the admissible grid segment has recursive energy and
squared-error bounds with denominators equal to the penalty and its square,
respectively](goal).

Instantiate recursive fitting stability with the paper's actual scales.
The propagation coefficient is fixed before the sampling experiment, curves,
confidence, horizon and deterministic population centers. Density membership
and its rate remain explicit on-event implications for intersection with the
locally constructed preliminary event. -/
-- @node: iter_rdiv_calibrated_fitting_stability_event
lemma iter_rdiv_calibrated_fitting_stability_event (V : IVWorld W X Z)
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
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧
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
    mu G g₀ support B c₀ CG 1 C (by norm_num) hC hIV hRange hDensity hBounds hY hHyp
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
  exact hfit P hProbability sample split gHat ρ ξ hMLE hMeas hVersion
    n t (δ n) segment sourceRadius hSourceScope iter hn hScale.1 hξ hd hfloor
    (by simpa only [one_mul] using hconfidence) hx hz hdom hstar hEst

end Papers.TsAdaptiveEstimationInference
