module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAESteps
/-! Deterministic iterative TRAE propagation on the common concentration event. -/
@[expose] public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
  (κδ κν c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (c : ℝ) (t : ℕ)
/-- [There is a multiplier rule, fixed before the model and sampling choices,
that assigns to each envelope bound and pair of moment continuity constants a
nondecreasing sequence starting at zero and at least two at positive indices,
such that models satisfying the corresponding square-integrability and moment
bounds have the following propagation property: under localized, anchored, and
fixed-center concentration, admissible grid and confidence parameters, range,
source, realizability, closeness, boundedness, common-envelope, complexity,
calibration, minima-attainment, deterministic inflation, and iterative process
conditions, a single positive constant bounds each intermediate squared strong
error by its step multiplier times squared accuracy divided by squared penalty,
and bounds terminal population loss by squared accuracy plus the smaller of the
penalty and terminal multiplier times squared accuracy divided by penalty, plus
the source bias, throughout the oracle segment on any supplied common
concentration event](goal).

The terminal multiplier determines the realizability segment, oracle, and
concentration event. The event constant is fixed before calibration, and the
required inflation is fixed before the source parameters. -/
-- @node: lem:iter-trae-strong-propagation
lemma iter_trae_strong_propagation :
    ∃ multipliers : ℝ → ℝ → ℝ → ℕ → ℝ,
      ∀ (V : IVWorld 𝒲 𝒳 𝒵) (B C_m C_iter : ℝ),
      (∀ f ∈ V.F, Integrable (fun w => V.m f w ^ 2) V.law ∧
        (∫ w, V.m f w ^ 2 ∂V.law) ≤ C_m * ‖f‖ ^ 2) →
      (∀ f ∈ V.F, ∀ f' ∈ V.F,
        Integrable (fun w => V.m (f - f') w ^ 2) V.law ∧
        (∫ w, V.m (f - f') w ^ 2 ∂V.law) ≤ C_iter * ‖f - f'‖ ^ 2) →
      let bSeq := multipliers B C_m C_iter
        -- @realizes b_j(sequence depending only on the index and the fixed envelope and continuity constants)
        -- @realizes b_t(terminal member bSeq t, used for the oracle, realizability, event and bounds)
      bSeq 0 = 0 ∧ Monotone bSeq ∧ (∀ j, 1 ≤ j → 2 ≤ bSeq j) ∧
      ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
        (sample : AnalysisSample V P) (split : SampleSplit)
        (ρ ξ c c₀ CG Cm : ℝ) (t : ℕ)
        (baseδ baseν : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
        (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
        (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      (hBennett_of_gate : TRAELocalizedConcentration V) →
      (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V) →
      (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V) →
      (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) → (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) →
      (ht : 1 ≤ t) → (hc : 0 < c) →
      ∀ Cevent : ℝ, 0 < Cevent → ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
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
      (hIterRealizable : IterRealizableTRAE V ρ c (bSeq t) β t δ) →
      (hIterMinima : IterTRAEMinimaAttained V P sample split ρ t iter) →
      (hProcesses : IterTRAEAnchoredLossProcessesMeasurable V B ρ t (fun n => c * ((bSeq t) * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))) →
      (hIterBound : TRAEBoundedness V B (some (ρ, t, (fun n => c * ((bSeq t) * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))))) →
      ∃ C > 0, ∀ n : ℕ, 0 < n →
      (hOracleDefined : gridValue ρ (terminalIndex ρ n) ≤
        c * (bSeq t * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ E : Set Ω,
      IterTRAEConcentrationOn V P sample split ρ c (bSeq t) β t δ baseδ iter n E Cevent →
      ∀ ω ∈ E,
      (∀ j, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
        lam ∈ Set.Icc (iterTraeOraclePoint ρ c (bSeq t) β t δ n) 2 →
        ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 ≤ C * bSeq j * δ n ^ 2 / lam ^ 2) ∧
      ∀ lam ∈ regGrid ρ n, lam ∈ Set.Icc (iterTraeOraclePoint ρ c (bSeq t) β t δ n) 2 →
        traePopulationLoss V (iter n t lam ω) ≤ C * (δ n ^ 2 + min lam (bSeq t * δ n ^ 2 / lam) +
          ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t) := by
  refine ⟨fun _ _ _ j => 2 * (j : ℝ), ?_⟩
  intro V B C_m C_iter hMSCAt hIterMSCAt
  dsimp only
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by norm_num)
  · intro j hj
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith only [this]
  intro P hProbability sample split ρ ξ c c₀ CG Cm t baseδ baseν tildeδ candidate iter
    hBennett_of_gate hAnchored_of_gate hFixedSq_of_gate hρ hξ ht hc Cevent hCevent
  let := hProbability
  refine ⟨1, zero_lt_one, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro β w₀ δ ν hRange hSource hRealizable hClose hBound hCommon hComplexity hScale
    hMinima hInflation hDeterministic hIterRealizable hIterMinima hProcesses hIterBound
  let A := 16 * ((Cevent ^ 2 + 2 * Cevent + 1) * (B + 1) + 2 * Cevent + 1) ^ 2
  let D := 2 * A + 1
  let W := 16 * ((Cevent ^ 2 + 4 * Cevent + 1) + Cevent + 1) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 1 ≤ D := by dsimp [D]; linarith only [hA]
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨Cb, hCb, hbias⟩ := iter_bias V β w₀ hRange hSource t ht
  let R := D ^ t
  have hR : 1 ≤ R := one_le_pow₀ hD
  let M := 4 * B ^ 2 + R + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let C := (2 * W + 2) * (M + Cb + 1) + R + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hRC : R ≤ C := by dsimp [C]; nlinarith only [hW, hM, hCb, mul_nonneg (show 0 ≤ 2 * W + 2 by linarith) (show 0 ≤ M + Cb + 1 by linarith)]
  have hCW : 2 * W ≤ C := by
    dsimp [C]
    nlinarith only [hW, hM, hCb, hR, mul_nonneg (show 0 ≤ 2 * W + 2 by linarith) (add_nonneg hM hCb.le)]
  have hCM : 2 * W * M ≤ C := by
    dsimp [C]
    nlinarith only [hW, hM, hCb, hR, mul_nonneg (show 0 ≤ 2 * W + 2 by linarith) hCb.le]
  have hCB : (2 * W + 2) * Cb ≤ C := by
    dsimp [C]
    nlinarith only [hW, hM, hR, mul_nonneg (show 0 ≤ 2 * W + 2 by linarith) hM]
  refine ⟨C, hC, ?_⟩
  intro n hn hOracle E hEvent ω hω
  have hr : 0 ≤ baseδ n :=
    (Real.rpow_nonneg (by positivity) _).trans ((le_max_right _ _).trans (hScale.1 n hn))
  have hδ : baseδ n ≤ δ n := by
    rw [hInflation.2.2.2.2.1 n]
    nlinarith only [hInflation.1, hr]
  have hδsq : baseδ n ^ 2 ≤ δ n ^ 2 := pow_le_pow_left₀ hr hδ 2
  have hgridDomain (lam : ℝ) (hl : lam ∈ regGrid ρ n) : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    exact mul_pos (by norm_num) (pow_pos (by linarith only [hρ.1]) k)
  have hstrong (lam : ℝ) (hl : lam ∈ regGrid ρ n)
      (hs : lam ∈ Set.Icc (iterTraeOraclePoint ρ c (2 * (t : ℝ)) β t δ n) 2) :
      ∀ j, j ≤ t → iterStrongVariance V j lam (iter n j lam ω) ^ 2 ≤
        D ^ j * (baseδ n ^ 2 / lam ^ 2) := by
    have hEst := (hIterMinima n hn lam hl).1
    have hlam := hgridDomain lam hl
    intro j
    induction j with
    | zero =>
        intro _
        simp only [iterStrongVariance, hEst.1 ω, populationIterate, sub_self, norm_zero,
          zero_pow (by decide : 2 ≠ 0), pow_zero, one_mul]
        positivity
    | succ j ih =>
        intro hjt
        have hj : 1 ≤ j + 1 := by omega
        have hStar := hIterRealizable n hOracle (j + 1) hj hjt lam hl hs
        have hstep := (iter_trae_step_bounds V P sample split ρ c (2 * (t : ℝ)) β B Cevent
          t n (j + 1) δ baseδ iter E hRange hClose hBound hCommon hCevent.le hr hOracle hEvent
          ω hω lam hl hs hlam hj hjt hStar hEst).1
        change iterStrongVariance V (j + 1) lam (iter n (j + 1) lam ω) ^ 2 ≤
          A * (baseδ n ^ 2 / lam ^ 2 + iterStrongVariance V j lam (iter n j lam ω) ^ 2) at hstep
        have hi := ih (by omega)
        have hjPow : 1 ≤ D ^ j := one_le_pow₀ hD
        have hcoef : A * (1 + D ^ j) ≤ D ^ (j + 1) := by
          rw [pow_succ]
          change A * (1 + D ^ j) ≤ D ^ j * (2 * A + 1)
          nlinarith only [hA, hjPow, mul_nonneg hA (sub_nonneg.mpr hjPow)]
        calc
          _ ≤ A * (baseδ n ^ 2 / lam ^ 2 + iterStrongVariance V j lam (iter n j lam ω) ^ 2) := hstep
          _ ≤ A * (baseδ n ^ 2 / lam ^ 2 + D ^ j * (baseδ n ^ 2 / lam ^ 2)) :=
            mul_le_mul_of_nonneg_left (add_le_add le_rfl hi) hA
          _ = (A * (1 + D ^ j)) * (baseδ n ^ 2 / lam ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
  constructor
  · intro j hj hjt lam hl hs
    have hb : 1 ≤ 2 * (j : ℝ) := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      linarith only [this]
    have hcoef : D ^ j ≤ C * (2 * (j : ℝ)) :=
      (pow_le_pow_right₀ hD hjt).trans
        (hRC.trans (le_mul_of_one_le_right hC.le hb))
    have hd : baseδ n ^ 2 / lam ^ 2 ≤ δ n ^ 2 / lam ^ 2 :=
      div_le_div_of_nonneg_right hδsq (sq_nonneg lam)
    calc
      ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 ≤
          D ^ j * (baseδ n ^ 2 / lam ^ 2) := hstrong lam hl hs j hjt
      _ ≤ C * (2 * (j : ℝ)) * δ n ^ 2 / lam ^ 2 := by
        simpa only [mul_div_assoc] using mul_le_mul hcoef hd (by positivity) (by positivity)
  · intro lam hl hs
    have hlam := hgridDomain lam hl
    have hEst := (hIterMinima n hn lam hl).1
    have hStar := hIterRealizable n hOracle t ht le_rfl lam hl hs
    have hstep := (iter_trae_step_bounds V P sample split ρ c (2 * (t : ℝ)) β B Cevent
      t n t δ baseδ iter E hRange hClose hBound hCommon hCevent.le hr hOracle hEvent
      ω hω lam hl hs hlam ht le_rfl hStar hEst).2
    let p := iterStrongVariance V (t - 1) lam (iter n (t - 1) lam ω)
    let u := iterWeakVariance V t lam (iter n t lam ω)
    let v := iterWeakBias V t lam
    change u ^ 2 ≤ W * (v ^ 2 + baseδ n ^ 2 + lam * p ^ 2) at hstep
    have hnorm (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) : ‖h‖ ≤ B := by
      have ha : ∀ᵐ w ∂V.law, ‖(h : Lp ℝ 2 V.law) w‖ ≤ B := by
        filter_upwards [hBound.2.2.1, V.primal_coherent h] with w hw heq
        simpa only [← heq, Real.norm_eq_abs, primalVersion] using hw h hh
      have hn := Lp.norm_le_of_ae_bound hBound.1 ha
      simpa [measureUnivNNReal] using hn
    have hpBound : p ^ 2 ≤ 4 * B ^ 2 := by
      by_cases hz : t - 1 = 0
      · simp only [p, iterStrongVariance, hz, hEst.1 ω, populationIterate, sub_self,
          norm_zero, zero_pow (by decide : 2 ≠ 0)]
        positivity
      · have hj : 1 ≤ t - 1 := by omega
        have hmem := (hEst.2 (t - 1) hj (by omega) ω).1
        have hstar := hIterRealizable n hOracle (t - 1) hj (by omega) lam hl hs
        have hp : p ≤ 2 * B := by
          dsimp only [p, iterStrongVariance]
          simpa only [two_mul] using
            (norm_sub_le _ _).trans (add_le_add (hnorm _ hmem) (hnorm _ hstar))
        have hp0 : 0 ≤ p := norm_nonneg _
        nlinarith only [hp, hp0, hBound.1]
    have hpStrong : p ^ 2 ≤ R * (δ n ^ 2 / lam ^ 2) := by
      have hj := hstrong lam hl hs (t - 1) (by omega)
      exact hj.trans (mul_le_mul (pow_le_pow_right₀ hD (by omega : t - 1 ≤ t))
        (div_le_div_of_nonneg_right hδsq (sq_nonneg lam)) (by positivity) (by positivity))
    have hpMin : lam * p ^ 2 ≤ M * min lam (2 * (t : ℝ) * δ n ^ 2 / lam) := by
      have hM₁ : 4 * B ^ 2 ≤ M := by dsimp [M]; linarith only [hR]
      have hM₂ : R ≤ M := by dsimp [M]; nlinarith only [sq_nonneg B]
      have hb : 1 ≤ 2 * (t : ℝ) := by
        have : (1 : ℝ) ≤ t := by exact_mod_cast ht
        linarith only [this]
      rw [mul_min_of_nonneg _ _ hM]
      apply le_min
      · have hp := mul_le_mul_of_nonneg_left hpBound hlam.le
        have hm := mul_le_mul_of_nonneg_right hM₁ hlam.le
        nlinarith only [hp, hm]
      · have hp := mul_le_mul_of_nonneg_left hpStrong hlam.le
        have hcancel : lam * (R * (δ n ^ 2 / lam ^ 2)) = R * δ n ^ 2 / lam := by
          field_simp
        rw [hcancel] at hp
        have hcoef : R ≤ M * (2 * (t : ℝ)) := hM₂.trans (le_mul_of_one_le_right hM hb)
        have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ δ n ^ 2 / lam by positivity)
        apply hp.trans
        convert hm using 1 <;> ring
    have hv : v ^ 2 ≤ Cb * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t :=
      (hbias lam hlam).2.2.2.1
    have htriangle : traePopulationLoss V (iter n t lam ω) ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
      rw [traePopulationLoss_eq V hRange hClose _ ((hEst.2 t ht le_rfl ω).1)]
      have heq : projCondExpOp V (iter n t lam ω - minNormSolution V) =
          projCondExpOp V (iter n t lam ω - populationIterate V lam t) +
            projCondExpOp V (populationIterate V lam t - minNormSolution V) := by
        simp only [map_sub]
        abel
      have hn := norm_add_le (projCondExpOp V (iter n t lam ω - populationIterate V lam t))
        (projCondExpOp V (populationIterate V lam t - minNormSolution V))
      rw [← heq] at hn
      change ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ≤ u + v at hn
      have hu : 0 ≤ u := norm_nonneg _
      have hv : 0 ≤ v := norm_nonneg _
      nlinarith only [hn, hu, hv, norm_nonneg (projCondExpOp V (iter n t lam ω - minNormSolution V)), sq_nonneg (u - v)]
    have hstep' : u ^ 2 ≤ W * (v ^ 2 + δ n ^ 2 +
        M * min lam (2 * (t : ℝ) * δ n ^ 2 / lam)) :=
      hstep.trans (mul_le_mul_of_nonneg_left (by linarith only [hδsq, hpMin]) hW)
    have hmin : 0 ≤ min lam (2 * (t : ℝ) * δ n ^ 2 / lam) := by positivity
    have hc₁ := mul_le_mul_of_nonneg_right hCW (sq_nonneg (δ n))
    have hc₂ := mul_le_mul_of_nonneg_right hCM hmin
    have hc₃ := mul_le_mul_of_nonneg_right hCB
      (show 0 ≤ ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t by positivity)
    have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * W + 2 by linarith only [hW])
    linarith only [htriangle, hstep', hc₁, hc₂, hc₃, hv']



/-- For [the observation space](hyp:𝒲), [the covariate space](hyp:𝒳), [the
instrument space](hyp:𝒵), and [the sampling outcome space](hyp:Ω), [the fixed
propagation multiplier rule](goal) is a chosen witness of uniform strong
propagation, mapping an envelope bound and two moment continuity constants to
an iteration-indexed multiplier sequence. -/
noncomputable def iterTraeMultipliers (𝒲 𝒳 𝒵 Ω : Type*)
    [MeasurableSpace 𝒲] [MeasurableSpace 𝒳] [MeasurableSpace 𝒵] [MeasurableSpace Ω] :
    ℝ → ℝ → ℝ → ℕ → ℝ := -- @realizes b_j(the fixed source-independent propagation multiplier map)
  Classical.choose (iter_trae_strong_propagation (𝒲 := 𝒲) (𝒳 := 𝒳) (𝒵 := 𝒵) (Ω := Ω))


/-- If [the penalty is positive](hyp:hlam) and [at most two](hyp:hlam2), [the
comparison coefficient is nonnegative](hyp:hC), and [penalty times squared
current error plus squared weak error is bounded by the loss remainder, one
quarter of squared weak bias, three times the coefficient times squared radius,
and penalty times the coefficient times the radius–error and current–previous
error products](hyp:hb), then [three quarters of penalty times squared current
error plus squared weak error is bounded by the loss remainder, one quarter of
squared weak bias, and eight times squared coefficient plus six times coefficient
plus one, multiplied by squared radius plus penalty times squared previous error](goal). -/
-- @node: iter_trae_refined_absorb
lemma iter_trae_refined_absorb (e p u v r lam C L : ℝ)
    (hlam : 0 < lam) (hlam2 : lam ≤ 2) (hC : 0 ≤ C)
    (hb : lam * e ^ 2 + u ^ 2 ≤ L + v ^ 2 / 4 + 3 * C * r ^ 2 +
      lam * C * (r * (e + p) + r ^ 2 + e * p)) :
    (3 / 4 : ℝ) * lam * e ^ 2 + u ^ 2 ≤ L + v ^ 2 / 4 +
      (8 * C ^ 2 + 6 * C + 1) * (r ^ 2 + lam * p ^ 2) := by
  have h₁ := mul_le_mul_of_nonneg_left
    (iter_trae_young e (C * r) (1 / 8) (by norm_num)) hlam.le
  have h₂ := mul_le_mul_of_nonneg_left
    (iter_trae_young e (C * p) (1 / 8) (by norm_num)) hlam.le
  have h₃ := mul_le_mul_of_nonneg_left
    (iter_trae_young r (C * p) (1 / 2) (by norm_num)) hlam.le
  norm_num at h₁ h₂ h₃
  have h₄ := mul_le_mul_of_nonneg_right hlam2 (sq_nonneg C)
  have h₅ := mul_le_mul_of_nonneg_right hlam2 hC
  have h₆ := mul_le_mul_of_nonneg_right
    (show 2 * lam * C ^ 2 + lam / 2 + lam * C + 3 * C ≤
      8 * C ^ 2 + 6 * C + 1 by nlinarith only [h₄, h₅, hlam2, sq_nonneg C, hC])
    (sq_nonneg r)
  have h₇ := mul_le_mul_of_nonneg_right
    (show (5 / 2 : ℝ) * C ^ 2 ≤ 8 * C ^ 2 + 6 * C + 1 by
      nlinarith only [sq_nonneg C, hC]) (show 0 ≤ lam * p ^ 2 by positivity)
  nlinarith only [hb, h₁, h₂, h₃, h₆, h₇]

/-- Suppose [the range condition holds](hyp:hRange), [the closeness condition
holds](hyp:hClose), [the event coefficient is nonnegative](hyp:hC), [the grid
reaches the balancing radius](hyp:hOracle), and [the common iterative
concentration comparisons hold on the event](hyp:hEvent). For [an outcome in
that event](hyp:hω) and [a grid penalty](hyp:hgrid) [between the oracle penalty
and two](hyp:hsegment) [that is positive](hyp:hlam), if [the horizon is at least
one](hyp:ht), [the population iterate belongs to the hypothesis class](hyp:hStar),
and [the candidate sequence is an iterative TRAE estimator](hyp:hEst), then
[three quarters of penalty times squared strong variance plus squared weak
variance is bounded by empirical loss, one quarter of squared weak bias, and
eight times squared event coefficient plus six times that coefficient plus one,
multiplied by squared radius plus penalty times the previous squared strong
variance](goal). -/
-- @node: iter_trae_refined_curvature
lemma iter_trae_refined_curvature (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
    (sample : AnalysisSample V P) (split : SampleSplit)
    (ρ c b β C : ℝ) (t n : ℕ) (δ r : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (E : Set Ω)
    (hRange : RangeCondition V) (hClose : ClosenessCondition V) (hC : 0 ≤ C)
    (hOracle : gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))
    (hEvent : IterTRAEConcentrationOn V P sample split ρ c b β t δ r iter n E C)
    (ω : Ω) (hω : ω ∈ E) (lam : ℝ) (hgrid : lam ∈ regGrid ρ n)
    (hsegment : lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2)
    (hlam : 0 < lam) (ht : 1 ≤ t)
    (hStar : populationIterate V lam t ∈ V.H)
    (hEst : IsIterTRAEEstimator V P sample split n t lam (fun k => iter n k lam)) :
    (3 / 4 : ℝ) * lam * iterStrongVariance V t lam (iter n t lam ω) ^ 2 +
      iterWeakVariance V t lam (iter n t lam ω) ^ 2 ≤
    traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterWeakBias V t lam ^ 2 / 4 +
      (8 * C ^ 2 + 6 * C + 1) * (r n ^ 2 +
        lam * iterStrongVariance V (t - 1) lam (iter n (t - 1) lam ω) ^ 2) := by
  have hh := (hEst.2 t ht le_rfl ω).1
  have hopt := (hEst.2 t ht le_rfl ω).2 _ hStar
  have hcurv := iter_trae_population_curvature V hRange hClose t ht lam hlam hStar _ hh
  have hlo := ((hEvent.1 ω hω).1 _ hh).1
  have hup := ((hEvent.1 ω hω).1 _ hStar).2
  have hcenter := (hEvent.2 hOracle ω hω lam hgrid hsegment t ht le_rfl).2.2
  have hc := mul_le_mul_of_nonneg_left (abs_le.mp hcenter).2 hlam.le
  apply iter_trae_refined_absorb _ _ _ _ _ _ _ _ hlam hsegment.2 hC
  rw [traePopulationLoss_eq V hRange hClose _ hStar] at hup hcurv
  dsimp only [iterStrongVariance, iterWeakVariance, iterWeakBias] at hcurv ⊢
  dsimp only [iterEmpiricalCenterDifference, iterPopulationCenterDifference] at hc hcurv
  nlinarith only [hopt, hcurv, hlo, hup, hc]

-- @node: ass:pin-188
/-- For [an instrumental-variable model](hyp:V), [a sampling law](hyp:P), [its
analysis sample](hyp:sample), [a sample split](hyp:split), [a grid ratio](hyp:ρ),
[a confidence level](hyp:ξ), [a balancing coefficient](hyp:c), [a noise
multiplier](hyp:b), [a source exponent](hyp:β), [an iteration horizon](hyp:t),
[an accuracy curve](hyp:δ), [a source witness](hyp:w₀), [an iterative estimator
family](hyp:iter), [a sample size](hyp:n), [an event](hyp:E), and [an envelope
constant](hyp:C), [the pinned envelope reading](goal) requires that the event be
measurable with probability at least one minus the confidence level, that the
envelope constant be positive, and that terminal empirical loss throughout the
oracle grid segment on this event be at most the noise level plus that constant
times squared source-witness norm times penalty to the qualification exponent. -/
noncomputable def PinIterTRAEEnvelopeReading (ρ ξ c b β : ℝ) (t : ℕ) (δ : ℕ → ℝ)
    (w₀ : V.Hbar.toSubmodule) (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  IterTRAEDiscrepancyEnvelope V P sample split ρ ξ c b β t δ w₀ iter n E C


/-- For [a geometric grid ratio](hyp:ρ) and [a family of rate constants indexed
by sample size and penalty](hyp:constants), [constancy of the rate
coefficient](goal) means that any two constants agree whenever their penalties
belong to the respective sample-size grids. -/
-- @node: ass:pin-204
def PinIterTRAERateConstants (ρ : ℝ) (constants : ℕ → ℝ → ℝ) : Prop :=
  ∀ n n' : ℕ, ∀ lam ∈ regGrid ρ n, ∀ lam' ∈ regGrid ρ n',
    constants n lam = constants n' lam'

end Papers.TsAdaptiveEstimationInference
