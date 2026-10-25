module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAE
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAERefinedPropagation
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEEventTransport
public import Papers.TsAdaptiveEstimationInference.TExistLambdaIterTrae

/-! TIterTraeDiscrepancyBound for adaptive inverse problems. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
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
/-- Given [localized TRAE concentration](hyp:hBennett_of_gate), [anchored iterative
concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[an admissible grid factor](hyp:hρ), [a failure level strictly between zero and
one](hyp:hξ), [a positive iteration count](hyp:ht), [a positive oracle scale](hyp:hc),
[the mean-square bound on test functions](hyp:hMSCAt), [the mean-square bound on
test-function differences](hyp:hIterMSCAt), and [a positive event comparison
constant](hyp:hCevent), [a positive calibration threshold ensures that the range
and source conditions, solution realizability,
closeness, boundedness and common-null-set boundedness,
critical-radius control, iteration scale calibration,
attained fitting minima, sufficient inflation,
deterministic accuracy curves, iterative realizability,
attained iterative minima, measurable anchored loss processes,
and boundedness at recursive centers yield a uniform positive
constant such that, eventually in sample size, an oracle grid point exists above
the noise scale and every measurable high-probability event with the given
concentration certificate carries the iterative TRAE discrepancy bound](goal).

On the common event supplied by iter_trae_concentration_event, use
iter_trae_strong_propagation and the loss comparisons pointwise. This theorem
never constructs a second event: its event and concentration constant are
universally quantified, so it applies to the actual event family returned by
iter_trae_rate. The calibration threshold is chosen before the source and
public accuracy curves. Oracle-grid existence and the stable-segment threshold
remain local eventual conclusions. -/
-- @node: thm:iter-trae-discrepancy-bound
theorem iter_trae_discrepancy_bound
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (ht : 1 ≤ t)
    (hc : 0 < c)
    (C_m C_iter : ℝ)
    (hMSCAt : ∀ f ∈ V.F, Integrable (fun w => V.m f w ^ 2) V.law ∧
      (∫ w, V.m f w ^ 2 ∂V.law) ≤ C_m * ‖f‖ ^ 2)
    (hIterMSCAt : ∀ f ∈ V.F, ∀ f' ∈ V.F,
      Integrable (fun w => V.m (f - f') w ^ 2) V.law ∧
      (∫ w, V.m (f - f') w ^ 2 ∂V.law) ≤ C_iter * ‖f - f'‖ ^ 2)
    (Cevent : ℝ) (hCevent : 0 < Cevent)
    : let bSeq := iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter
      let b := bSeq t
      ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hClose : ClosenessCondition V) →
      (hBound : TRAEBoundedness V B) → (hCommon : TRAECommonNullSetBoundedness V B) →
      (hComplexity : TRAECriticalRadiusBound V tildeδ) →
      (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t)) →
      (hMinima : TRAEMinimaAttained V P sample split ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterRealizable : IterRealizableTRAE V ρ c b β t δ) →
      (hIterMinima : IterTRAEMinimaAttained V P sample split ρ t iter) →
      (hProcesses : IterTRAEAnchoredLossProcessesMeasurable V B ρ t (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))) →
      (hIterBound : TRAEBoundedness V B (some (ρ, t, (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))))) →
      ∃ C > 0, ∀ᶠ n in atTop,
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ c * (b * δ n ^ 2) ^
        (1 / (qualificationExponent β t + 1))) ∧
      Real.sqrt (b * δ n ^ 2) ≤ iterTraeOraclePoint ρ c b β t δ n ∧
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E → -- @realizes \mathcal E_{n,t}^{\mathrm{IT}}(any supplied shared event with its measurability, probability and concentration certificate)
      IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Cevent →
      IterTRAEDiscrepancyOn V P sample split ρ c b β t δ w₀ iter n E C := by
  classical
  dsimp only
  let b := iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t
  have hb : 2 ≤ b :=
    (Classical.choose_spec (iter_trae_strong_propagation
      (𝒲 := 𝒲) (𝒳 := 𝒳) (𝒵 := 𝒵) (Ω := Ω)) V B C_m C_iter
        hMSCAt hIterMSCAt).2.2.1 t ht
  let K := iterTraeNoiseConstant B Cevent t
  have hK : 0 ≤ K := by dsimp [K, iterTraeNoiseConstant]; positivity
  let required := 2 * K + Cevent + 1
  have hrequired : 0 < required := by dsimp [required]; positivity
  refine ⟨required, hrequired, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro β w₀ δ ν hRange hSource hRealizable hClose hBound hCommon hComplexity
    hScale hMinima hInflation hDeterministic hIterRealizable hIterMinima hProcesses hIterBound
  obtain ⟨Cb, hCb, hpop⟩ := iter_trae_preliminary_weak_bound V P sample split
    ρ c b β B Cevent t δ baseδ w₀ iter hρ ht (by linarith only [hb])
    hRange hSource hClose hBound hCommon hCevent hIterRealizable hIterMinima
  have hbase (n : ℕ) (hn : 0 < n) : 0 ≤ baseδ n :=
    (Real.rpow_nonneg (by positivity) _).trans ((le_max_right _ _).trans (hScale.1 n hn))
  have hScale' : TRAEScaleCalibration δ tildeδ (fun n => iterGridConfidence ρ ξ n t) := by
    constructor
    · intro n hn
      apply (hScale.1 n hn).trans
      rw [hInflation.2.2.2.2.1 n]
      exact le_mul_of_one_le_left (hbase n hn) hInflation.1
    · have he : δ = fun n => κδ * baseδ n := funext hInflation.2.2.2.2.1
      rw [he]
      simpa using hScale.2.const_mul κδ
  have hstable := iterTraeOraclePoint_stable_eventually ρ c b β t δ tildeδ
    (fun n => iterGridConfidence ρ ξ n t) hρ hc hb hSource.1 ht hScale'
  refine ⟨(5 / 4 : ℝ) * Cb + 1, by positivity, ?_⟩
  filter_upwards [hstable, eventually_gt_atTop 0] with n hn hn0
  refine ⟨hn.1, hn.2, ?_⟩
  intro E hE hp hEvent
  refine ⟨by positivity, ?_⟩
  intro ω hω lam hl hs
  have hlam : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    exact mul_pos (by norm_num) (pow_pos (by linarith only [hρ.1]) k)
  have hterminal : gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) := by
    obtain ⟨k, hk, hkr⟩ := hn.1
    exact (show gridValue ρ (terminalIndex ρ n) ≤ gridValue ρ k from
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by linarith only [hρ.1]) hρ.2.le hk) (by norm_num)).trans hkr
  have hweak := hpop n hn0 (hbase n hn0) hterminal E hEvent ω hω lam hl hs
  change traePopulationLoss V (iter n t lam ω) ≤
    K * (baseδ n ^ 2 + b * baseδ n ^ 2 / lam) +
      Cb * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t at hweak
  have hupper := ((hEvent.1 ω hω).1 _
    (((hIterMinima n hn0 lam hl).1.2 t ht le_rfl ω).1)).2
  have hcoeff : (5 / 4 : ℝ) * K + Cevent ≤ κδ ^ 2 := by
    have hk := hInflation.1
    have hr := hInflation.2.2.1
    change 2 * K + Cevent + 1 ≤ κδ at hr
    nlinarith only [hk, hr, hK]
  have hnoise : ((5 / 4 : ℝ) * K + Cevent) * baseδ n ^ 2 ≤ δ n ^ 2 := by
    rw [hInflation.2.2.2.2.1 n, mul_pow]
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
  have hnoise' : (5 / 4 : ℝ) * K * (b * baseδ n ^ 2 / lam) ≤ b * δ n ^ 2 / lam := by
    have hc : (5 / 4 : ℝ) * K ≤ κδ ^ 2 := by linarith only [hcoeff, hCevent]
    have hi := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ b * baseδ n ^ 2 / lam by positivity)
    rw [hInflation.2.2.2.2.1 n, mul_pow]
    convert hi using 1 <;> first | rfl | ring
  have hbranch : min lam (b * δ n ^ 2 / lam) = b * δ n ^ 2 / lam := by
    apply min_eq_right
    apply (div_le_iff₀ hlam).2
    have hsq : b * δ n ^ 2 ≤ lam ^ 2 :=
      (Real.sqrt_le_iff).1 (hn.2.trans hs.1) |>.2
    nlinarith only [hsq]
  change traeEmpiricalLoss V P sample split n ω (iter n t lam ω) ≤
    δ n ^ 2 + min lam (b * δ n ^ 2 / lam) +
      ((5 / 4 : ℝ) * Cb + 1) * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t
  rw [hbranch]
  have hbias : 0 ≤ ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t := by positivity
  nlinarith only [hweak, hupper, hnoise, hnoise', hbias]



/-- Under [localized TRAE concentration](hyp:hBennett_of_gate), [anchored iterative
concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[scalar Lipschitz concentration](hyp:hNorm_of_gate), [an admissible grid factor](hyp:hρ),
[a failure level strictly between zero and one](hyp:hξ), [a positive iteration
count](hyp:ht), [a positive oracle scale](hyp:hc), [the mean-square bound on test
functions](hyp:hMSCAt), and [the mean-square bound on their differences](hyp:hIterMSCAt),
[positive concentration and calibration constants can be chosen so that the
range, source, realizability, closeness, boundedness, complexity, calibration,
minimization, and process-measurability conditions give one family of iteration-grid
intersection events carrying concentration and joint selection, with eventual
oracle-grid existence, an oracle above the noise scale, and the discrepancy
envelope on those same events](goal).

Construct an iteration-grid intersection and apply the universal discrepancy
theorem to it. The calibration threshold precedes the source and public accuracy
curves. Selection and the envelope use this one constructed event; the universal
theorem also applies directly to the rate theorem's supplied common event. -/
-- keep: Constructed-event companion to the universal discrepancy theorem: exports the actual iteration-grid intersection, its probability, and selection on that same event without a caller-supplied event certificate.
lemma iter_trae_discrepancy_bound_constructed_event
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : ScalarLipschitzLocalizedConcentration V P sample split)
    (hρ : GridDomain ρ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (ht : 1 ≤ t)
    (hc : 0 < c) (C_m C_iter : ℝ)
    (hMSCAt : ∀ f ∈ V.F, Integrable (fun w => V.m f w ^ 2) V.law ∧
      (∫ w, V.m f w ^ 2 ∂V.law) ≤ C_m * ‖f‖ ^ 2)
    (hIterMSCAt : ∀ f ∈ V.F, ∀ f' ∈ V.F,
      Integrable (fun w => V.m (f - f') w ^ 2) V.law ∧
      (∫ w, V.m (f - f') w ^ 2 ∂V.law) ≤ C_iter * ‖f - f'‖ ^ 2) :
    let b := iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t
    ∃ Cevent > 0, ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
      (β : ℝ) (w₀ : V.Hbar.toSubmodule) (δ ν : ℕ → ℝ),
      RangeCondition V → BetaSourceCondition V β w₀ → H0MemHypothesisClass V →
      ClosenessCondition V → TRAEBoundedness V B → TRAECommonNullSetBoundedness V B →
      TRAECriticalRadiusBound V tildeδ →
      TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
      TRAEMinimaAttained V P sample split ρ candidate →
      CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required →
      CalibrationDeterministic δ ν → IterRealizableTRAE V ρ c b β t δ →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAEAnchoredLossProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      TRAEBoundedness V B (some (ρ, t,
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))))) →
      ∃ C > 0, ∃ events : ℕ → Set Ω,
      (∀ n : ℕ, 0 < n →
        ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
          events n = iterTraeCommonEvent ρ n t component ∧
          (∀ j k a, MeasurableSet (component j k a) ∧
            1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
          MeasurableSet (events n) ∧ 1 - ξ ≤ P.real (events n) ∧
          IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n (events n) Cevent) ∧
      (IterTRAESelectionOnFamily V P sample split ρ ξ B δ iter b t events ∧
        PinExistLambdaIterTraeOnEvent V P sample split ρ ξ B δ iter b t events) ∧
      (∀ᶠ n in atTop,
        (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ c * (b * δ n ^ 2) ^
          (1 / (qualificationExponent β t + 1))) ∧
        Real.sqrt (b * δ n ^ 2) ≤ iterTraeOraclePoint ρ c b β t δ n ∧
        IterTRAEDiscrepancyEnvelope V P sample split ρ ξ c b β t δ w₀ iter n (events n) C) := by
  classical
  dsimp only
  let b := iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t
  have hb : 2 ≤ b :=
    (Classical.choose_spec (iter_trae_strong_propagation
      (𝒲 := 𝒲) (𝒳 := 𝒳) (𝒵 := 𝒵) (Ω := Ω)) V B C_m C_iter
      hMSCAt hIterMSCAt).2.2.1 t ht
  by_cases hSetup : TRAEBoundedness V B ∧ TRAECommonNullSetBoundedness V B ∧
      TRAECriticalRadiusBound V tildeδ
  · obtain ⟨hBound0, hCommon0, hComplexity0⟩ := hSetup
    obtain ⟨Ce, hCe, hevent⟩ := iter_trae_concentration_event_uniform_allocation_with_bounds
      V P sample split hBennett_of_gate hAnchored_of_gate hFixedSq_of_gate hNorm_of_gate
      ρ B b t baseδ tildeδ candidate iter hρ ht hb
      ⟨C_m, hMSCAt⟩ ⟨C_iter, hIterMSCAt⟩ hBound0 hCommon0 hComplexity0
    obtain ⟨R, hR, hdiscrepancy⟩ := iter_trae_discrepancy_bound
      (V := V) (P := P) (sample := sample) (split := split)
      (ρ := ρ) (ξ := ξ) (B := B) (baseδ := baseδ) (baseν := baseν)
      (tildeδ := tildeδ) (c₀ := c₀) (CG := CG) (Cm := Cm)
      (candidate := candidate) (iter := iter) (c := c) (t := t)
      hBennett_of_gate hAnchored_of_gate hFixedSq_of_gate hρ hξ ht hc
      C_m C_iter hMSCAt hIterMSCAt Ce hCe
    refine ⟨Ce, hCe, max R (Ce + 1), lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
    intro κ₀ β w₀ δ ν hRange hSource hRealizable hClose hBound hCommon hComplexity
      hScale hMinima hInflation hDeterministic hIterRealizable hIterMinima hProcesses hIterBound
    have hInflationR : CalibratedValidBounds δ ν baseδ baseν
        (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 R :=
      ⟨hInflation.1, hInflation.2.1, (le_max_left _ _).trans hInflation.2.2.1,
        (le_max_left _ _).trans hInflation.2.2.2.1, hInflation.2.2.2.2⟩
    obtain ⟨C, hC, hbound⟩ := hdiscrepancy κ₀ β w₀ δ ν hRange hSource hRealizable
      hClose hBound hCommon hComplexity hScale hMinima hInflationR hDeterministic
      hIterRealizable hIterMinima hProcesses hIterBound
    have hex := hevent ξ hξ hScale c β δ hc hSource.1 hRange hRealizable hClose
      hIterRealizable hMinima hIterMinima (And.intro hProcesses hIterBound.2)
    let events : ℕ → Set Ω := fun n => if hn : 0 < n then
      iterTraeCommonEvent ρ n t (Classical.choose (hex n hn)) else Set.univ
    have hcertificate (n : ℕ) (hn : 0 < n) :
        ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
          events n = iterTraeCommonEvent ρ n t component ∧
          (∀ j k a, MeasurableSet (component j k a) ∧
            1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
          MeasurableSet (events n) ∧ 1 - ξ ≤ P.real (events n) ∧
          IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n (events n) Ce ∧
          (∀ ω ∈ events n, ∀ i ∈ split.fit n, ∀ h ∈ V.H,
            |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B) := by
      refine ⟨Classical.choose (hex n hn), by simp only [events, dif_pos hn], ?_⟩
      simpa only [events, dif_pos hn] using Classical.choose_spec (hex n hn)
    refine ⟨C, hC, events, ?_, ?_, ?_⟩
    · intro n hn
      obtain ⟨component, heq, hcomponent, hE, hpE, hcon, hbounded⟩ := hcertificate n hn
      exact ⟨component, heq, hcomponent, hE, hpE, hcon⟩
    · apply iterTRAESelectionOnFamily_and_pin
      intro n hn
      have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2)
        ((le_max_left _ _).trans hn)
      obtain ⟨component, heq, hcomponent, hE, hpE, hcon, hbounded⟩ := hcertificate n hn0
      have hk := hInflation.1
      have hr := (le_max_right R (Ce + 1)).trans hInflation.2.2.1
      have hcoeff : Ce ≤ (κ₀ B c₀ CG Cm).1 ^ 2 := by nlinarith
      have hnoise : Ce * baseδ n ^ 2 ≤ δ n ^ 2 := by
        rw [hInflation.2.2.2.2.1 n, mul_pow]
        exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      exact iter_trae_selection_on_bounded_common_event V P sample split
        ρ ξ B b t n δ baseδ iter (events n) Ce hρ ht hb hBound.1 hRealizable
        hIterMinima hn hE hpE hcon.1 hbounded hnoise
        (trae_calibrated_square_floor baseδ δ tildeδ
          (fun n => iterGridConfidence ρ ξ n t) ν baseν
          (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 (max R (Ce + 1)) hScale hInflation n hn0)
    · filter_upwards [hbound, eventually_gt_atTop 0] with n hn hn0
      obtain ⟨component, heq, hcomponent, hE, hpE, hcon, hbounded⟩ := hcertificate n hn0
      exact ⟨hn.1, hn.2.1, hE, hpE, hn.2.2 (events n) hE hpE hcon⟩
  · refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_⟩
    intro κ₀ β w₀ δ ν hRange hSource hRealizable hClose hBound hCommon hComplexity
    exact (hSetup ⟨hBound, hCommon, hComplexity⟩).elim

end Papers.TsAdaptiveEstimationInference
