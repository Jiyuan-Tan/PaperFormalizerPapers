module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterEmpiricalCenter
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEIncrementNorms
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.TCommonDp
public import Papers.TsAdaptiveEstimationInference.TIterTraeDiscrepancyBound
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEOracle
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEEventTransport
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEDiscrepancy
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEFinitePrefix
/-! TIterTraeRate for adaptive inverse problems. -/
public section
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
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
[the squared-norm comparison](hyp:hNorm_of_gate), [an admissible grid factor](hyp:hρ),
[a failure level strictly between zero and one](hyp:hξ), [a positive iteration
count](hyp:ht), [the mean-square bound on test functions](hyp:hMSCAt), and [the
mean-square bound on their differences](hyp:hIterMSCAt), [a positive calibration
threshold ensures that the range and source conditions,
solution realizability, closeness, boundedness
and common-null-set boundedness, critical-radius control,
iteration scale calibration, attained fitting minima,
sufficient inflation, and deterministic accuracy curves
give a positive upper bound on the oracle scale for which iterative realizability,
attained iterative minima, and measurable localized processes
yield one family of measurable iteration-grid intersection events with the
prescribed probability, concentration and joint selection, carrying uniform
prediction and estimation rates at every eligible sample size and the simplified
rates eventually under sufficient qualification](goal).

Derive eventual oracle-grid existence and apply common_dp on the oracle segment.
Enlarge the constant over the finite prefix using the recorded boundedness and positive rate scales;
no oracle-existence hypothesis is added to this rate theorem. Construct events n
once using iter_trae_concentration_event and its allocated union bound. Pass that
same E, Cevent, and terminal bSeq t to propagation, discrepancy, accepted stability
and common_dp. No intersection of separately budgeted 1-xi events is used.
The whole finite prefix is handled on these same events by deterministic boundedness;
selection and both qualified and unqualified rates below use this single event
family. The sample envelope retained by the constructor proves selection without
intersecting another event. -/
lemma iter_trae_rate_at_confidence
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (ht : 1 ≤ t) -- @realizes t(positive natural iteration count fixed before the source exponent)
    (C_m C_iter : ℝ)
    (hMSCAt : ∀ f ∈ V.F, Integrable (fun w => V.m f w ^ 2) V.law ∧
      (∫ w, V.m f w ^ 2 ∂V.law) ≤ C_m * ‖f‖ ^ 2)
    (hIterMSCAt : ∀ f ∈ V.F, ∀ f' ∈ V.F,
      Integrable (fun w => V.m (f - f') w ^ 2) V.law ∧
      (∫ w, V.m (f - f') w ^ 2 ∂V.law) ≤ C_iter * ‖f - f'‖ ^ 2)
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
      ∃ cmax > 0, ∀ c ∈ Set.Ioc (0 : ℝ) cmax,
      (hIterRealizable : IterRealizableTRAE V ρ c b β t δ) →
      (hIterMinima : IterTRAEMinimaAttained V P sample split ρ t iter) →
      (hProcesses : IterTRAELocalizedProcessesMeasurable V B ρ t (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))) →
      ∃ Cevent > 0, ∃ events : ℕ → Set Ω,
      (∀ n : ℕ, 0 < n →
        ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
          events n = iterTraeCommonEvent ρ n t component ∧
          (∀ j k a, MeasurableSet (component j k a) ∧
            1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
          MeasurableSet (events n) ∧ 1 - ξ ≤ P.real (events n) ∧ -- @realizes \mathcal E_{n,t}^{\mathrm{IT}}(the same measurable event and probability certificate for both rate conclusions)
          IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n (events n) Cevent) ∧
      (IterTRAESelectionOnFamily V P sample split ρ ξ B δ iter b t events ∧
        PinExistLambdaIterTraeOnEvent V P sample split ρ ξ B δ iter b t events) ∧
      (∃ C > 0, ∀ n : ℕ, iterTraeMinSampleSize B ≤ n → ∀ ω ∈ events n,
          ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2 ≤ C * ((b * δ n ^ 2) ^ (qualificationExponent β t / (qualificationExponent β t + 1))) ∧
          ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤ C * ((b * δ n ^ 2) ^ ((qualificationExponent β t - 1) / (qualificationExponent β t + 1)))) ∧
      (IterQualificationTRAE β t → ∃ Cs > 0, ∀ᶠ n in atTop, ∀ ω ∈ events n,
          ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤ Cs * δ n ^ (2 * β / (β + 2)) ∧
          ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2 ≤ Cs * δ n ^ (2 * (β + 1) / (β + 2))) := by
  classical
  dsimp only
  let b := iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t
  have hb : 2 ≤ b :=
    (Classical.choose_spec (iter_trae_strong_propagation
      (𝒲 := 𝒲) (𝒳 := 𝒳) (𝒵 := 𝒵) (Ω := Ω)) V B C_m C_iter
        hMSCAt hIterMSCAt).2.2.1 t ht
  by_cases hSetup : TRAEBoundedness V B ∧ TRAECommonNullSetBoundedness V B ∧ TRAECriticalRadiusBound V tildeδ ∧
      TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t)
  · obtain ⟨hBound0, hCommon0, hComplexity0, hScale0⟩ := hSetup
    obtain ⟨Ce, hCe, hevent⟩ := iter_trae_concentration_event_uniform_allocation_with_bounds
      V P sample split hBennett_of_gate hAnchored_of_gate hFixedSq_of_gate hNorm_of_gate
      ρ B b t baseδ tildeδ candidate iter hρ ht hb
      ⟨C_m, hMSCAt⟩ ⟨C_iter, hIterMSCAt⟩ hBound0 hCommon0 hComplexity0
    let K := iterTraeNoiseConstant B Ce t
    have hK : 0 ≤ K := by dsimp [K, iterTraeNoiseConstant]; positivity
    let required := 2 * K + Ce + 1
    refine ⟨required, by dsimp [required]; positivity, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hClose hBound hCommon hComplexity
      hScale hMinima hInflation hDeterministic
    let q := qualificationExponent β t
    have hq : 1 < q := by
      have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
      exact lt_min (by linarith [hSource.1]) (by linarith)
    have hqβ : q ≤ β + 1 := min_le_left _ _
    have hbase (n : ℕ) (hn : 0 < n) : 0 ≤ baseδ n :=
      (Real.rpow_nonneg (by positivity) _).trans ((le_max_right _ _).trans (hScale.1 n hn))
    have hdom (n : ℕ) (hn : 0 < n) : baseδ n ≤ δ n := by
      rw [hInflation.2.2.2.2.1 n]
      exact le_mul_of_one_le_left (hbase n hn) hInflation.1
    have hd (n : ℕ) (hn : 0 < n) : 0 < δ n :=
      ((Real.rpow_pos_of_pos (by positivity) _).trans_le
        ((le_max_right _ _).trans (hScale.1 n hn))).trans_le (hdom n hn)
    have hcoeff : (5 / 4 : ℝ) * K + Ce ≤ κδ ^ 2 := by
      have hk := hInflation.1
      have hr := hInflation.2.2.1
      change 2 * K + Ce + 1 ≤ κδ at hr
      nlinarith only [hk, hr, hK, hCe]
    obtain ⟨Cd, hCd, hdiscrepancy⟩ := iter_trae_discrepancy_uniform V P sample split
      ρ b β B Ce t δ baseδ κδ w₀ iter hρ ht hb hRange hSource hClose hBound hCommon hCe
      hbase hInflation.2.2.2.2.1 hcoeff
    let Cb := Cd * ‖w₀‖ ^ 2 + 1
    have hCb : 0 < Cb := by dsimp [Cb]; positivity
    obtain ⟨cmax, hcmax, hcrossSmall⟩ := iterTraeOracle_crossing_constant Cb q hCb.le hq
    refine ⟨cmax, hcmax, ?_⟩
    intro c hc hIterRealizable hIterMinima hProcesses
    have hex := fun n (hn : 0 < n) => hevent ξ hξ hScale c β δ hc.1 hSource.1 hRange
      hRealizable hClose hIterRealizable hMinima hIterMinima hProcesses n hn
    choose component hcomponent hE hprob hcon hsample using hex
    let events : ℕ → Set Ω := fun n =>
      if hn : 0 < n then iterTraeCommonEvent ρ n t (component n hn) else ∅
    have hEv (n : ℕ) (hn : 0 < n) : MeasurableSet (events n) ∧
        1 - ξ ≤ P.real (events n) ∧
        IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n (events n) Ce := by
      simpa only [events, dif_pos hn] using ⟨hE n hn, hprob n hn, hcon n hn⟩
    obtain ⟨Cs, hCs, hstability⟩ := iter_trae_accepted_stability_local V P sample split
      ρ c b β B Ce t δ baseδ w₀ iter hρ ht hb hRange hSource hRealizable
      hClose hBound hCommon hCe hbase hdom hIterRealizable hIterMinima
    specialize hstability ξ
    obtain ⟨Cr, hCr, hrate⟩ := iterTrae_rate_on_event Cs Cs Cb ρ c b β q
      hCs hCs hCb hρ hc.1 hb hSource.1 hq hqβ
    have hScale' : TRAEScaleCalibration δ tildeδ (fun n => iterGridConfidence ρ ξ n t) := by
      constructor
      · intro n hn
        exact (hScale.1 n hn).trans (hdom n hn)
      · rw [show δ = fun n => κδ * baseδ n from funext hInflation.2.2.2.2.1]
        simpa using hScale.2.const_mul κδ
    have hlimit : Tendsto (fun n => b * δ n ^ 2) atTop (𝓝 0) := by
      simpa using (hScale'.2.pow 2).const_mul b
    have hradius : Tendsto (fun n => c * (b * δ n ^ 2) ^ (1 / (q + 1))) atTop (𝓝 0) := by
      simpa using (hlimit.rpow_const_nhds_zero (by positivity : 0 < 1 / (q + 1))).const_mul c
    have htail : ∀ᶠ n in atTop, ∀ ω ∈ events n,
        ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2 ≤
          Cr * (b * δ n ^ 2) ^ (q / (q + 1)) ∧
        ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤
          Cr * (b * δ n ^ 2) ^ ((q - 1) / (q + 1)) := by
      filter_upwards [iterTraeOraclePoint_stable_eventually ρ c b β t δ tildeδ
        (fun n => iterGridConfidence ρ ξ n t) hρ hc.1 hb hSource.1 ht hScale',
        hlimit.eventually (gt_mem_nhds zero_lt_one),
        hradius.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2)),
        eventually_gt_atTop 0] with n hn hs hrad hn0
      obtain ⟨k, hk, hkr⟩ := hn.1
      have hterminal : gridValue ρ (terminalIndex ρ n) ≤
          c * (b * δ n ^ 2) ^ (1 / (q + 1)) :=
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by linarith [hρ.1]) hρ.2.le hk) (by norm_num)).trans hkr
      have hround := oraclePoint_radius_bounds ρ _ n hρ hrad.le hterminal
      let lo := iterTraeOraclePoint ρ c b β t δ n
      obtain ⟨hEn, hpn, hEvent⟩ := hEv n hn0
      have hcomp : GenericEventComparisons P (projCondExpOp V) (minNormSolution V)
          ρ ξ Cs Cs Cb (β / (β + 1)) q n (Set.Icc lo 2) (events n)
          (fun lam => iter n t lam) (fun ω h => traeEmpiricalLoss V P sample split n ω h)
          (iterTraeNoiseLevel b (δ n)) := by
        refine ⟨hEn, hpn, ?_⟩
        intro ω hω lam hl hsegment
        have hdis := (hdiscrepancy c hIterRealizable hIterMinima n hn0 hterminal hn.2
          (events n) hEvent).2 ω hω lam hl hsegment
        have hstab := hstability n hn0 hterminal (events n) hEn hpn hEvent ω hω lam
          ⟨hl, hsegment, hn.2.trans hsegment.1⟩
        refine ⟨?_, hstab.1, hstab.2.1⟩
        exact hdis.trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (show Cd * ‖w₀‖ ^ 2 ≤ Cb by dsimp [Cb]; linarith)
            (Real.rpow_nonneg (trae_grid_domain ρ hρ n lam hl).1.le q)))
      have hcross := iterTraeOracle_crossing Cb c b (δ n) q lo hCb.le hc.1
        (by linarith) hq (trae_grid_domain ρ hρ n lo hround.1).1 hn.2 hround.2.2
        (hcrossSmall c hc)
      exact hrate P (projCondExpOp V) (minNormSolution V) ξ n hn0 (δ n) lo (events n)
        (fun lam => iter n t lam) (fun ω h => traeEmpiricalLoss V P sample split n ω h)
        (by positivity [hd n hn0]) hs.le hround.1 hn.2 hround.2.1 hcomp hcross
    have hbounded (n : ℕ) (hn : iterTraeMinSampleSize B ≤ n) (ω : Ω) :
        ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2 ≤ 4 * B ^ 2 ∧
        ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤ 4 * B ^ 2 := by
      have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
      have hsel : iterTraeSelected V P sample split ρ b t δ iter n ω ∈ regGrid ρ n := by
        have hi : discrepancyIndex ρ n
            (fun lam => traeEmpiricalLoss V P sample split n ω (iter n t lam ω))
            (iterTraeNoiseLevel b (δ n)) ≤ terminalIndex ρ n := by
          unfold discrepancyIndex
          split
          next he => exact (Nat.find_spec he).1
          next => exact le_rfl
        exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
      have hh := ((hIterMinima n hn0 _ hsel).1.2 t ht le_rfl ω).1
      have hhB := trae_hypothesis_norm_le V B hBound _ hh
      have hh0B := trae_hypothesis_norm_le V B hBound _ hRealizable
      have herr : ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤ 4 * B ^ 2 := by
        calc
          _ ≤ (B + B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
            ((norm_sub_le _ _).trans (add_le_add hhB hh0B)) 2
          _ = _ := by ring
      have hcontract : ‖projCondExpOp V
          (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ≤
          ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ := by
        exact ((projCondExpOp V).le_opNorm _).trans (by
          simpa using mul_le_mul_of_nonneg_right (projCondExpOp_norm_le_one V) (norm_nonneg _))
      exact ⟨(pow_le_pow_left₀ (norm_nonneg _) hcontract 2).trans herr, herr⟩
    obtain ⟨C, hC, hall⟩ := iterTrae_rates_finite_prefix events
      (fun n ω => ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2)
      (fun n ω => ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2)
      (fun n => (b * δ n ^ 2) ^ (q / (q + 1)))
      (fun n => (b * δ n ^ 2) ^ ((q - 1) / (q + 1)))
      (iterTraeMinSampleSize B) (4 * B ^ 2)
      (by
        intro n hn
        have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
        constructor <;> exact Real.rpow_pos_of_pos (by positivity [hd n hn0]) _)
      (fun n hn ω _ => hbounded n hn ω) ⟨Cr, hCr, htail⟩
    refine ⟨Ce, hCe, events, ?_, ?_, ⟨C, hC, hall⟩, ?_⟩
    · intro n hn
      refine ⟨component n hn, ?_, hcomponent n hn, (hEv n hn).1, (hEv n hn).2⟩
      simp only [events, dif_pos hn]
    · apply iterTRAESelectionOnFamily_and_pin
      intro n hn
      have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
      have hnoise : Ce * baseδ n ^ 2 ≤ δ n ^ 2 := by
        rw [hInflation.2.2.2.2.1 n, mul_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        linarith only [hcoeff, hK]
      apply iter_trae_selection_on_bounded_common_event V P sample split
        ρ ξ B b t n δ baseδ iter (events n) Ce hρ ht hb hBound.1 hRealizable
        hIterMinima hn (hEv n hn0).1 (hEv n hn0).2.1 (hEv n hn0).2.2.1
      · simpa only [events, dif_pos hn0] using hsample n hn0
      · exact hnoise
      · exact trae_calibrated_square_floor baseδ δ tildeδ
          (fun n => iterGridConfidence ρ ξ n t) ν baseν κδ κν required
          hScale hInflation n hn0
    · intro hqual
      let Ks := b ^ (β / (β + 2))
      let Kw := b ^ ((β + 1) / (β + 2))
      let Cout := C * (Ks + Kw + 1)
      have hKs : 0 ≤ Ks := by dsimp [Ks]; positivity
      have hKw : 0 ≤ Kw := by dsimp [Kw]; positivity
      refine ⟨Cout, by dsimp [Cout]; positivity, ?_⟩
      filter_upwards [eventually_ge_atTop (iterTraeMinSampleSize B)] with n hn
      intro ω hω
      have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
      have hdn := hd n hn0
      have hscales := iterTrae_qualified_scale_identities b (δ n) β t
        (by linarith) (hd n hn0).le hqual
      obtain ⟨hw, hstrong⟩ := hall n hn ω hω
      rw [hscales.1] at hw
      rw [hscales.2] at hstrong
      constructor
      · exact hstrong.trans (by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [Cout, Ks, Kw] at *
          nlinarith only [hKs, hKw, hC, mul_nonneg hC.le hKw])
      · exact hw.trans (by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [Cout, Ks, Kw] at *
          nlinarith only [hKs, hKw, hC, mul_nonneg hC.le hKs])
  · refine ⟨1, zero_lt_one, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hClose hBound hCommon hComplexity hScale
    exact False.elim (hSetup ⟨hBound, hCommon, hComplexity, hScale⟩)




/-- Under [localized TRAE concentration](hyp:hBennett_of_gate), [anchored iterative
concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[scalar Lipschitz concentration](hyp:hNorm_of_gate), [an admissible grid factor](hyp:hρ),
[a positive iteration count](hyp:ht), [a noise multiplier at least two](hyp:hb),
[mean-square continuity](hyp:hMSC), [mean-square continuity for differences](hyp:hIterMSC),
[boundedness](hyp:hBound), [common-null-set boundedness](hyp:hCommon), and [critical-radius
control](hyp:hComplexity), [there is a positive concentration constant, chosen
before confidence, such that every valid failure level, calibrated scale and
positive source and oracle scale satisfying range, realizability, closeness,
iterative realizability, attainment of minima and localized process measurability
admit, at every positive sample size, measurable component events whose intersection
has probability at least one minus the failure level and carries both iterative
concentration and uniform bounds on all fitted hypothesis values](goal).

Construct the rate theorem's common event under its recorded hypotheses.
The calibrated absolute-deviation specialization, deterministic loss deductions
and three-family union bound are retained. The remaining localized increment,
squared-test and random-center construction is a local proof obligation; the
recorded bk-6 process atom is passed at the actual oracle radius. -/
lemma iter_trae_rate_concentration_event
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : ScalarLipschitzLocalizedConcentration V P sample split)
    (ρ B b : ℝ) (t : ℕ) (baseδ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : GridDomain ρ) (ht : 1 ≤ t) (hb : 2 ≤ b)
    (hMSC : MeanSquareContinuity V) (hIterMSC : IterMeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ Cevent > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
      ∀ (c β : ℝ) (δ : ℕ → ℝ), 0 < c → 0 < β →
      RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
      IterRealizableTRAE V ρ c b β t δ →
      TRAEMinimaAttained V P sample split ρ candidate →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAELocalizedProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n →
      ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
        (∀ j k a, MeasurableSet (component j k a) ∧
          1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
        let E := iterTraeCommonEvent ρ n t component
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
        IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Cevent ∧
        (∀ ω ∈ E, ∀ i ∈ split.fit n, ∀ h ∈ V.H,
          |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B) := by
  exact iter_trae_concentration_event_uniform_allocation_with_bounds V P sample split
    hBennett_of_gate hAnchored_of_gate hFixedSq_of_gate hNorm_of_gate
    ρ B b t baseδ tildeδ candidate iter hρ ht hb hMSC hIterMSC hBound hCommon hComplexity

/-- Given [localized TRAE concentration](hyp:hBennett_of_gate), [anchored iterative
concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[the squared-norm comparison](hyp:hNorm_of_gate), [an admissible grid factor](hyp:hρ),
[a positive iteration count](hyp:ht), [the mean-square bound on test functions](hyp:hMSCAt),
and [the mean-square bound on their differences](hyp:hIterMSCAt), [a positive
calibration threshold ensures that the range and source conditions,
solution realizability, closeness, boundedness
and common-null-set boundedness, critical-radius control,
attained fitting minima, sufficient inflation,
and deterministic accuracy curves give a positive upper
bound on the oracle scale for which iterative realizability,
attained iterative minima, measurable anchored loss processes,
and boundedness at recursive centers yield positive rate constants
chosen before confidence, with each valid confidence level and its calibrated
iteration scale producing one measurable common-event family carrying concentration,
joint selection, prediction and estimation rates at all eligible sizes, and
eventual simplified rates under sufficient qualification, provided the
scale is calibrated to that confidence level](goal).

Both rate constants precede confidence as prescribed by
PinIterTraeRateConstant. For each level, one event family witnesses the component
intersection, propagation comparisons, selection and both rate conclusions.
A deterministic envelope of eligible events fixes the finite-prefix constants
before confidence, while each confidence uses its own original common event. -/
-- @node: thm:iter-trae-rate
theorem iter_trae_rate
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (ht : 1 ≤ t) -- @realizes t(positive natural iteration count fixed before the source exponent)
    (C_m C_iter : ℝ)
    (hMSCAt : ∀ f ∈ V.F, Integrable (fun w => V.m f w ^ 2) V.law ∧
      (∫ w, V.m f w ^ 2 ∂V.law) ≤ C_m * ‖f‖ ^ 2)
    (hIterMSCAt : ∀ f ∈ V.F, ∀ f' ∈ V.F,
      Integrable (fun w => V.m (f - f') w ^ 2) V.law ∧
      (∫ w, V.m (f - f') w ^ 2 ∂V.law) ≤ C_iter * ‖f - f'‖ ^ 2)
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
      (hMinima : TRAEMinimaAttained V P sample split ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      ∃ cmax > 0, ∀ c ∈ Set.Ioc (0 : ℝ) cmax,
      (hIterRealizable : IterRealizableTRAE V ρ c b β t δ) →
      (hIterMinima : IterTRAEMinimaAttained V P sample split ρ t iter) →
      (hProcesses : IterTRAEAnchoredLossProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))) →
      (hIterBound : TRAEBoundedness V B (some (ρ, t, (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))))) →
      ∃ C > 0, ∃ Cs > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t)) →
      ∃ Cevent > 0, ∃ events : ℕ → Set Ω,
      (∀ n : ℕ, 0 < n →
        ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
          events n = iterTraeCommonEvent ρ n t component ∧
          (∀ j k a, MeasurableSet (component j k a) ∧
            1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
          MeasurableSet (events n) ∧ 1 - ξ ≤ P.real (events n) ∧ -- @realizes \mathcal E_{n,t}^{\mathrm{IT}}(the same measurable event and probability certificate for both rate conclusions)
          IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n (events n) Cevent) ∧
      (IterTRAESelectionOnFamily V P sample split ρ ξ B δ iter b t events ∧
        PinExistLambdaIterTraeOnEvent V P sample split ρ ξ B δ iter b t events) ∧
      (∀ n : ℕ, iterTraeMinSampleSize B ≤ n → ∀ ω ∈ events n,
          ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2 ≤ C * ((b * δ n ^ 2) ^ (qualificationExponent β t / (qualificationExponent β t + 1))) ∧
          ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤ C * ((b * δ n ^ 2) ^ ((qualificationExponent β t - 1) / (qualificationExponent β t + 1)))) ∧
      (IterQualificationTRAE β t → ∀ᶠ n in atTop, ∀ ω ∈ events n,
          ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤ Cs * δ n ^ (2 * β / (β + 2)) ∧
          ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2 ≤ Cs * δ n ^ (2 * (β + 1) / (β + 2))) := by
  classical
  dsimp only
  let b := iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t
  have hb : 2 ≤ b :=
    (Classical.choose_spec (iter_trae_strong_propagation
      (𝒲 := 𝒲) (𝒳 := 𝒳) (𝒵 := 𝒵) (Ω := Ω)) V B C_m C_iter
        hMSCAt hIterMSCAt).2.2.1 t ht
  by_cases hSetup : TRAEBoundedness V B ∧ TRAECommonNullSetBoundedness V B ∧ TRAECriticalRadiusBound V tildeδ
  · obtain ⟨hBound0, hCommon0, hComplexity0⟩ := hSetup
    obtain ⟨Ce, hCe, hevent⟩ := iter_trae_rate_concentration_event (hAnchored_of_gate := hAnchored_of_gate)
      (hFixedSq_of_gate := hFixedSq_of_gate) (hNorm_of_gate := hNorm_of_gate)
      (hBennett_of_gate := hBennett_of_gate) V P sample split
      ρ B b t baseδ tildeδ candidate iter hρ ht hb
      ⟨C_m, hMSCAt⟩ ⟨C_iter, hIterMSCAt⟩ hBound0 hCommon0 hComplexity0
    let K := iterTraeNoiseConstant B Ce t
    have hK : 0 ≤ K := by dsimp [K, iterTraeNoiseConstant]; positivity
    let required := 2 * K + Ce + 1
    refine ⟨required, by dsimp [required]; positivity, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hClose hBound hCommon hComplexity
      hMinima hInflation hDeterministic
    by_cases hAnyScale : ∃ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 ∧
        TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t)
    swap
    · refine ⟨1, zero_lt_one, ?_⟩
      intro c hc hIterRealizable hIterMinima hProcesses hIterBound
      have hProcesses := And.intro hProcesses hIterBound.2
      refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_⟩
      intro ξ hξ hScale
      exact False.elim (hAnyScale ⟨ξ, hξ, hScale⟩)
    obtain ⟨ξ₀, hξ₀, hScale⟩ := hAnyScale
    let q := qualificationExponent β t
    have hq : 1 < q := by
      have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
      exact lt_min (by linarith [hSource.1]) (by linarith)
    have hqβ : q ≤ β + 1 := min_le_left _ _
    have hbase (n : ℕ) (hn : 0 < n) : 0 ≤ baseδ n :=
      (Real.rpow_nonneg (by positivity) _).trans ((le_max_right _ _).trans (hScale.1 n hn))
    have hdom (n : ℕ) (hn : 0 < n) : baseδ n ≤ δ n := by
      rw [hInflation.2.2.2.2.1 n]
      exact le_mul_of_one_le_left (hbase n hn) hInflation.1
    have hd (n : ℕ) (hn : 0 < n) : 0 < δ n :=
      ((Real.rpow_pos_of_pos (by positivity) _).trans_le
        ((le_max_right _ _).trans (hScale.1 n hn))).trans_le (hdom n hn)
    have hcoeff : (5 / 4 : ℝ) * K + Ce ≤ κδ ^ 2 := by
      have hk := hInflation.1
      have hr := hInflation.2.2.1
      change 2 * K + Ce + 1 ≤ κδ at hr
      nlinarith only [hk, hr, hK, hCe]
    obtain ⟨Cd, hCd, hdiscrepancy⟩ := iter_trae_discrepancy_uniform V P sample split
      ρ b β B Ce t δ baseδ κδ w₀ iter hρ ht hb hRange hSource hClose hBound hCommon hCe
      hbase hInflation.2.2.2.2.1 hcoeff
    let Cb := Cd * ‖w₀‖ ^ 2 + 1
    have hCb : 0 < Cb := by dsimp [Cb]; positivity
    obtain ⟨cmax, hcmax, hcrossSmall⟩ := iterTraeOracle_crossing_constant Cb q hCb.le hq
    refine ⟨cmax, hcmax, ?_⟩
    intro c hc hIterRealizable hIterMinima hProcesses hIterBound
    have hProcesses := And.intro hProcesses hIterBound.2
    -- This deterministic envelope collects every eligible common event. It is
    -- used only for scalar constants; measurability is needed on its witnesses.
    let events : ℕ → Set Ω := fun n => {ω | ∃ (ξ : ℝ) (E : Set Ω),
      ξ ∈ Set.Ioo (0 : ℝ) 1 ∧ MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Ce ∧ ω ∈ E}
    obtain ⟨Cs, hCs, hstability⟩ := iter_trae_accepted_stability_local V P sample split
      ρ c b β B Ce t δ baseδ w₀ iter hρ ht hb hRange hSource hRealizable
      hClose hBound hCommon hCe hbase hdom hIterRealizable hIterMinima
    obtain ⟨Cr, hCr, hrate⟩ := iterTrae_rate_on_event Cs Cs Cb ρ c b β q
      hCs hCs hCb hρ hc.1 hb hSource.1 hq hqβ
    have hScale' : TRAEScaleCalibration δ tildeδ (fun n => iterGridConfidence ρ ξ₀ n t) := by
      constructor
      · intro n hn
        exact (hScale.1 n hn).trans (hdom n hn)
      · rw [show δ = fun n => κδ * baseδ n from funext hInflation.2.2.2.2.1]
        simpa using hScale.2.const_mul κδ
    have hlimit : Tendsto (fun n => b * δ n ^ 2) atTop (𝓝 0) := by
      simpa using (hScale'.2.pow 2).const_mul b
    have hradius : Tendsto (fun n => c * (b * δ n ^ 2) ^ (1 / (q + 1))) atTop (𝓝 0) := by
      simpa using (hlimit.rpow_const_nhds_zero (by positivity : 0 < 1 / (q + 1))).const_mul c
    have htail : ∀ᶠ n in atTop, ∀ ω ∈ events n,
        ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2 ≤
          Cr * (b * δ n ^ 2) ^ (q / (q + 1)) ∧
        ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤
          Cr * (b * δ n ^ 2) ^ ((q - 1) / (q + 1)) := by
      filter_upwards [iterTraeOraclePoint_stable_eventually ρ c b β t δ tildeδ
        (fun n => iterGridConfidence ρ ξ₀ n t) hρ hc.1 hb hSource.1 ht hScale',
        hlimit.eventually (gt_mem_nhds zero_lt_one),
        hradius.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2)),
        eventually_gt_atTop 0] with n hn hs hrad hn0
      obtain ⟨k, hk, hkr⟩ := hn.1
      have hterminal : gridValue ρ (terminalIndex ρ n) ≤
          c * (b * δ n ^ 2) ^ (1 / (q + 1)) :=
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by linarith [hρ.1]) hρ.2.le hk) (by norm_num)).trans hkr
      have hround := oraclePoint_radius_bounds ρ _ n hρ hrad.le hterminal
      let lo := iterTraeOraclePoint ρ c b β t δ n
      intro ω hωAll
      obtain ⟨ξ, E, hξ, hEn, hpn, hEvent, hω⟩ := hωAll
      have hcomp : GenericEventComparisons P (projCondExpOp V) (minNormSolution V)
          ρ ξ Cs Cs Cb (β / (β + 1)) q n (Set.Icc lo 2) E
          (fun lam => iter n t lam) (fun ω h => traeEmpiricalLoss V P sample split n ω h)
          (iterTraeNoiseLevel b (δ n)) := by
        refine ⟨hEn, hpn, ?_⟩
        intro ω hω lam hl hsegment
        have hdis := (hdiscrepancy c hIterRealizable hIterMinima n hn0 hterminal hn.2
          E hEvent).2 ω hω lam hl hsegment
        have hstab := hstability ξ n hn0 hterminal E hEn hpn hEvent ω hω lam
          ⟨hl, hsegment, hn.2.trans hsegment.1⟩
        refine ⟨?_, hstab.1, hstab.2.1⟩
        exact hdis.trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (show Cd * ‖w₀‖ ^ 2 ≤ Cb by dsimp [Cb]; linarith)
            (Real.rpow_nonneg (trae_grid_domain ρ hρ n lam hl).1.le q)))
      have hcross := iterTraeOracle_crossing Cb c b (δ n) q lo hCb.le hc.1
        (by linarith) hq (trae_grid_domain ρ hρ n lo hround.1).1 hn.2 hround.2.2
        (hcrossSmall c hc)
      exact hrate P (projCondExpOp V) (minNormSolution V) ξ n hn0 (δ n) lo E
        (fun lam => iter n t lam) (fun ω h => traeEmpiricalLoss V P sample split n ω h)
        (by positivity [hd n hn0]) hs.le hround.1 hn.2 hround.2.1 hcomp hcross ω hω
    have hbounded (n : ℕ) (hn : iterTraeMinSampleSize B ≤ n) (ω : Ω) :
        ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2 ≤ 4 * B ^ 2 ∧
        ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤ 4 * B ^ 2 := by
      have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
      have hsel : iterTraeSelected V P sample split ρ b t δ iter n ω ∈ regGrid ρ n := by
        have hi : discrepancyIndex ρ n
            (fun lam => traeEmpiricalLoss V P sample split n ω (iter n t lam ω))
            (iterTraeNoiseLevel b (δ n)) ≤ terminalIndex ρ n := by
          unfold discrepancyIndex
          split
          next he => exact (Nat.find_spec he).1
          next => exact le_rfl
        exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
      have hh := ((hIterMinima n hn0 _ hsel).1.2 t ht le_rfl ω).1
      have hhB := trae_hypothesis_norm_le V B hBound _ hh
      have hh0B := trae_hypothesis_norm_le V B hBound _ hRealizable
      have herr : ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2 ≤ 4 * B ^ 2 := by
        calc
          _ ≤ (B + B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
            ((norm_sub_le _ _).trans (add_le_add hhB hh0B)) 2
          _ = _ := by ring
      have hcontract : ‖projCondExpOp V
          (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ≤
          ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ := by
        exact ((projCondExpOp V).le_opNorm _).trans (by
          simpa using mul_le_mul_of_nonneg_right (projCondExpOp_norm_le_one V) (norm_nonneg _))
      exact ⟨(pow_le_pow_left₀ (norm_nonneg _) hcontract 2).trans herr, herr⟩
    obtain ⟨C, hC, hall⟩ := iterTrae_rates_finite_prefix events
      (fun n ω => ‖projCondExpOp V (iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V)‖ ^ 2)
      (fun n ω => ‖iter n t (iterTraeSelected V P sample split ρ b t δ iter n ω) ω - minNormSolution V‖ ^ 2)
      (fun n => (b * δ n ^ 2) ^ (q / (q + 1)))
      (fun n => (b * δ n ^ 2) ^ ((q - 1) / (q + 1)))
      (iterTraeMinSampleSize B) (4 * B ^ 2)
      (by
        intro n hn
        have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
        constructor <;> exact Real.rpow_pos_of_pos (by positivity [hd n hn0]) _)
      (fun n hn ω _ => hbounded n hn ω) ⟨Cr, hCr, htail⟩
    let Ks := b ^ (β / (β + 2))
    let Kw := b ^ ((β + 1) / (β + 2))
    let Cout := C * (Ks + Kw + 1)
    have hKs : 0 ≤ Ks := by dsimp [Ks]; positivity
    have hKw : 0 ≤ Kw := by dsimp [Kw]; positivity
    refine ⟨C, hC, Cout, by dsimp [Cout]; positivity, ?_⟩
    intro ξ hξ hScaleAt
    have hex := fun n (hn : 0 < n) => hevent ξ hξ hScaleAt c β δ hc.1 hSource.1 hRange
      hRealizable hClose hIterRealizable hMinima hIterMinima hProcesses n hn
    choose component hcomponent hE hprob hcon hsample using hex
    let Eξ : ℕ → Set Ω := fun n =>
      if hn : 0 < n then iterTraeCommonEvent ρ n t (component n hn) else ∅
    have hEv (n : ℕ) (hn : 0 < n) : MeasurableSet (Eξ n) ∧
        1 - ξ ≤ P.real (Eξ n) ∧
        IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n (Eξ n) Ce := by
      simpa only [Eξ, dif_pos hn] using ⟨hE n hn, hprob n hn, hcon n hn⟩
    have hsub (n : ℕ) (hn : 0 < n) (ω : Ω) (hω : ω ∈ Eξ n) : ω ∈ events n :=
      ⟨ξ, Eξ n, hξ, (hEv n hn).1, (hEv n hn).2.1, (hEv n hn).2.2, hω⟩
    refine ⟨Ce, hCe, Eξ, ?_, ?_, ?_, ?_⟩
    · intro n hn
      refine ⟨component n hn, ?_, hcomponent n hn, (hEv n hn).1, (hEv n hn).2⟩
      simp only [Eξ, dif_pos hn]
    · apply iterTRAESelectionOnFamily_and_pin
      intro n hn
      have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
      have hnoise : Ce * baseδ n ^ 2 ≤ δ n ^ 2 := by
        rw [hInflation.2.2.2.2.1 n, mul_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        linarith only [hcoeff, hK]
      apply iter_trae_selection_on_bounded_common_event V P sample split
        ρ ξ B b t n δ baseδ iter (Eξ n) Ce hρ ht hb hBound.1 hRealizable
        hIterMinima hn (hEv n hn0).1 (hEv n hn0).2.1 (hEv n hn0).2.2.1
      · simpa only [Eξ, dif_pos hn0] using hsample n hn0
      · exact hnoise
      · exact trae_calibrated_square_floor baseδ δ tildeδ
          (fun n => iterGridConfidence ρ ξ n t) ν baseν κδ κν required
          hScaleAt hInflation n hn0
    · intro n hn ω hω
      have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
      exact hall n hn ω (hsub n hn0 ω hω)
    · intro hqual
      filter_upwards [eventually_ge_atTop (iterTraeMinSampleSize B)] with n hn
      intro ω hω
      have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
      have hdn := hd n hn0
      have hscales := iterTrae_qualified_scale_identities b (δ n) β t
        (by linarith) (hd n hn0).le hqual
      obtain ⟨hw, hstrong⟩ := hall n hn ω (hsub n hn0 ω hω)
      rw [hscales.1] at hw
      rw [hscales.2] at hstrong
      constructor
      · exact hstrong.trans (by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [Cout, Ks, Kw] at *
          nlinarith only [hKs, hKw, hC, mul_nonneg hC.le hKw])
      · exact hw.trans (by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [Cout, Ks, Kw] at *
          nlinarith only [hKs, hKw, hC, mul_nonneg hC.le hKs])
  · refine ⟨1, zero_lt_one, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hClose hBound hCommon hComplexity
    exact False.elim (hSetup ⟨hBound, hCommon, hComplexity⟩)

end Papers.TsAdaptiveEstimationInference
