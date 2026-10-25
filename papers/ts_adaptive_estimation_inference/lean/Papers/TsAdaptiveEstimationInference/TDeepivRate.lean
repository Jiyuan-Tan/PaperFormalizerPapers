module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.TCommonDp
public import Papers.TsAdaptiveEstimationInference.TExistLambdaDeepiv
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVRateBounds
/-! TDeepivRate for adaptive inverse problems. -/
@[expose] public section
set_option linter.style.longLine false
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
set_option maxHeartbeats 800000 in
-- The assembly combines uniform event bounds, oracle rates, and finite-prefix estimates.
/-- Given [localized likelihood concentration](hyp:hLi_of_gate), [localized vector
concentration](hyp:hVector_of_gate), [a grid factor between one-half inclusive and
one exclusive](hyp:hρ), [a failure probability strictly between zero and one](hyp:hξ),
and [a valid instrumental-variable density model](hyp:hIV), [there is a positive
calibration threshold such that, under the range condition,
the source condition, realizability of the minimum-norm solution,
density realizability, density bounds,
the pilot regression rate, bounded outcomes,
bounded hypotheses, a bounded pilot,
measurable fitting classes, measurable likelihood processes,
the specified fitting supremum version, the selected density
version, the selected pilot version,
density critical-radius bounds, hypothesis critical-radius
bounds, the radius floor, public scale calibration,
attainment of fitted minima, sufficient calibration inflation,
deterministic accuracy curves, and likelihood-maximizing
density estimates, one positive rate constant gives, at every eligible
sample size, a measurable event of probability at least one minus the failure
level carrying the selected DeepIV prediction and estimation rates, their
interpolation comparison, and the sharper zero-solution rates](goal).

Calibration is at the frozen public arguments: publicG/publicR at ξ,
publicH at gridConfidence ρ ξ n, and the public logarithmic floor at ξ.
The three public curves are defined in the signature by evaluating the raw
bounds before relabelling, under main.tex:258 and appendices.tex:126–129.
The public `δ` and `ν` are calibrated from those same evaluated curves.
The same scales determine the selected penalty, common-event envelope, oracle
error scale, and both error bounds, including the zero-solution conclusion.
The raw-to-public identification is the function `rdivEvaluatedAccuracy`;
the base sums are `rdivFittingBaseScale` and `rdivCalibrationBaseScale`.
No value at ξ is substituted for an unrelated raw value at ξ/4. -/
-- @node: thm:deepiv-rate
theorem deepiv_rate
    (hLi_of_gate : LiLocalizedConcentration V)
    (hVector_of_gate : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) -- @realizes \xi(failure level in the open unit interval) -- @realizes \rho(fixed search factor in the half-open interval from one-half to one)
    (hIV : RDIVSetting V mu g₀)
    : let publicG := rdivEvaluatedAccuracy rawG; -- @realizes \delta_{n,\mathcal G}(public density radius evaluated before relabelling)
      let publicH := rdivEvaluatedAccuracy rawH; -- @realizes \delta_{n,\mathcal H}(public hypothesis radius evaluated before relabelling)
      let publicR := rdivEvaluatedAccuracy rawR; -- @realizes \delta_{n,r}(public pilot accuracy evaluated before relabelling)
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
      (∃ C > 0, ∀ n : ℕ, rdivMinSampleSize B ≤ n → ∃ E : Set Ω,
        RDIVRateOnEvent
          (V := V) (P := P) (sample := sample) (split := split) (ρ := ρ) (ξ := ξ)
          (β := β) (w₀ := w₀) (δ := δ) (ν := ν) (δG := rawG) (δH := rawH) (δr := rawR) (mu := mu) (g₀ := g₀) (gHat := gHat) (rHat := rHat) (candidate := candidate)
          (fun _ => E) n C) := by
  classical
  obtain ⟨required, hrequired, hexist⟩ := exist_lambda_deepiv (hLi_of_gate := hLi_of_gate) (hVector_of_gate := hVector_of_gate)
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
  obtain ⟨_, Ce, hCe, hevent⟩ := hexist κ₀ β w₀ δ ν hRange hSource
    hRealizable hDensity hDensityBounds hPilotRate hOutcome hHypBound hPilotBound
    hSupMeas hLikMeas hFittingVersion hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius hRadiusFloor hScale hMinima hInflation
    hDeterministic hMLE
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hraw (n : ℕ) (hn : 0 < n) :
      0 ≤ rawG n (ξ / 4) ∧ 0 ≤ rawH n (gridConfidence ρ ξ n / 4) ∧
      rawG n (ξ / 4) ≤ δ n ∧ rawH n (gridConfidence ρ ξ n / 4) ≤ δ n := by
    have hg := (hDensityRadius n hn _ hquarter).1.le
    have hh := (hHypRadius n hn _ hquarter).1.1.le
    have he : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
      unfold gridConfidence; ring
    rw [he] at hh
    have hs := (hScale.1 n hn).1
    change rawG n (ξ / 4) + rawH n (gridConfidence ρ ξ n / 4) +
      rdivPublicLogScale ρ ξ n ≤ baseδ n at hs
    have hl : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
    have hb : 0 ≤ baseδ n := by linarith only [hg, hh, hl, hs]
    have hbd : baseδ n ≤ δ n := by
      rw [hInflation.2.2.2.2.1 n]
      nlinarith only [hInflation.1, hb]
    exact ⟨hg, hh, by linarith, by linarith⟩
  have hlog (n : ℕ) (hn : 0 < n) := rdiv_calibrated_public_log_floor V mu G g₀
    ρ ξ hξ rawG rawH rawR δ ν baseδ baseν κδ κν required
    hDensityRadius hHypRadius hScale hInflation n hn
  have hdpos (n : ℕ) (hn : 0 < n) : 0 < δ n := by
    have hfloor := rdiv_public_log_square_floor ρ ξ hρ hξ n hn
    have hp : 0 < Real.log 2 / (n : ℝ) :=
      div_pos (Real.log_pos (by norm_num)) (by exact_mod_cast hn)
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hlog n hn) 2
    change rdivPublicLogScale ρ ξ n ^ 2 ≤ δ n ^ 2 at hsq
    nlinarith only [hfloor, hp, hsq, hDeterministic.1 n]
  obtain ⟨Ca, hCa, haccepted⟩ := rdiv_accepted_bounds_local V P sample split
    mu g₀ gHat rHat ρ ξ B β Ce δ ν rawG rawH rawR w₀ candidate hρ hCe
    hIV hRange hSource hRealizable hOutcome hMinima
    (fun n hn => (hraw n hn).1) (fun n hn => (hraw n hn).2.1)
    (fun n hn => (hraw n hn).2.2.1) (fun n hn => (hraw n hn).2.2.2)
  let Cb := Ce * ‖w₀‖ ^ 2 + 1
  have hCb : 0 < Cb := by dsimp [Cb]; positivity
  have hgeneric (n : ℕ) (hn : 0 < n) (E : Set Ω)
      (hE : MeasurableSet E) (hpE : 1 - ξ ≤ P.real E)
      (hcomp : RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν
        rawG rawH rawR candidate n E Ce)
      (henv : RDIVDiscrepancyEnvelope V P sample split mu gHat rHat ρ β δ ν
        w₀ candidate n E Ce) :
      GenericEventComparisons P (projCondExpOp V) (minNormSolution V) ρ ξ Ca Ca Cb
        (interpolationExponent β) (biasExponent β) n (Set.Ioc 0 2) E
        (candidate n) (fun ω h => rdivCalibrationStat V P sample split mu gHat rHat n ω h)
        (rdivNoiseLevel (δ n) (ν n)) := by
    apply rdiv_generic_comparisons_of_accepted_bounds P (projCondExpOp V)
      (minNormSolution V) ρ ξ Ca Ca Cb (interpolationExponent β) (biasExponent β)
      (δ n) (ν n) n E (candidate n)
      (fun ω h => rdivCalibrationStat V P sample split mu gHat rHat n ω h)
      hE hpE hCa.le
    · intro ω _ lam _
      unfold rdivCalibrationStat blockAverage; positivity
    · intro ω hω lam hlam
      have hl := (trae_grid_domain ρ hρ n lam hlam).1
      apply (henv.2 ω hω lam hlam).trans
      have hc : Ce * ‖w₀‖ ^ 2 ≤ Cb := by dsimp [Cb]; linarith
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hl.le _))
    · exact haccepted n hn E hcomp
  obtain ⟨hdl, hvl⟩ := rdiv_inflated_scales_tendsto_zero δ ν baseδ baseν
    κδ κν required hInflation hDeterministic hScale.2
  have hfloor : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) ≤ δ n ^ 2 := by
    filter_upwards [rdiv_public_log_eventual_square_floor ρ ξ hρ hξ,
      eventually_gt_atTop 0] with n hf hn
    exact hf.trans (pow_le_pow_left₀ (Real.sqrt_nonneg _) (hlog n hn) 2)
  obtain ⟨Cr, hCr, hrates⟩ := rdiv_eventual_rates_of_comparisons P
    (projCondExpOp V) (minNormSolution V) Ca Ca Cb ρ ξ β δ ν candidate
    (fun n ω h => rdivCalibrationStat V P sample split mu gHat rHat n ω h)
    hρ hSource.1 hCa hCa hCb hDeterministic.1 hDeterministic.2 hdl hvl hfloor
  obtain ⟨N, hN⟩ := eventually_atTop.1 hrates
  let A := fun n => rdivErrorScale β (δ n) (ν n)
  let S := fun n => δ n ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) +
    A n ^ interpolationExponent β
  have hn0 (n : ℕ) (hn : rdivMinSampleSize B ≤ n) : 0 < n := by
    have := (le_max_left _ _).trans hn
    omega
  have hA (n : ℕ) (hn : rdivMinSampleSize B ≤ n) : 0 < A n := by
    dsimp [A, rdivErrorScale]
    exact add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos (hdpos n (hn0 n hn)) _) (sq_nonneg _)
  have hS (n : ℕ) (hn : rdivMinSampleSize B ≤ n) : 0 < S n := by
    dsimp [S]
    exact add_pos_of_nonneg_of_pos (Real.rpow_nonneg (hDeterministic.1 n) _)
      (Real.rpow_pos_of_pos (hA n hn) _)
  obtain ⟨C, hC, hCbase, hprefix⟩ := rdiv_finite_prefix_constant A S (4 * B ^ 2)
    (Ce + Cr + (Ce ^ 2 + 2 * Ce) + 1) N (rdivMinSampleSize B)
    (by positivity) (by positivity) hA hS
  have hCeC : Ce ≤ C := by nlinarith only [hCbase, hCr, hCe, sq_nonneg Ce]
  have hCrC : Cr ≤ C := by nlinarith only [hCbase, hCr, hCe, sq_nonneg Ce]
  have hzC : Ce ^ 2 + 2 * Ce ≤ C := by linarith only [hCbase, hCr, hCe]
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hn' := hn0 n hn
  obtain ⟨E, hE, hpE, hcomp, henv, hsearch⟩ := hevent n hn
  refine ⟨E, hE, hpE, ?_, ?_, ?_⟩
  · intro ω hω
    refine ⟨rdiv_preliminaryOn_mono V mu g₀ gHat rHat ξ Ce C rawG rawR n ω
      (hraw n hn').1 hCeC (hcomp ω hω).1, ?_, ?_⟩
    · intro lam hlam h hh
      exact ((hcomp ω hω).2.1 lam hlam h hh).trans
        (mul_le_mul_of_nonneg_right hCeC (add_nonneg
          (mul_nonneg (hraw n hn').2.1 (norm_nonneg _)) (sq_nonneg _)))
    · intro lam hlam
      exact ((hcomp ω hω).2.2 lam hlam).trans (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCeC (hDeterministic.2 n))
          (norm_nonneg _)) (mul_le_mul_of_nonneg_right hCeC (sq_nonneg _)))
  · refine ⟨hC, ?_⟩
    intro ω hω lam hlam
    apply (henv.2 ω hω lam hlam).trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCeC (sq_nonneg _))
      (Real.rpow_nonneg (trae_grid_domain ρ hρ n lam hlam).1.le _))
  intro ω hω
  let lam := rdivSelected V P sample split mu gHat rHat ρ δ ν candidate n ω
  have hsel : lam ∈ regGrid ρ n := by
    have hi : discrepancyIndex ρ n
        (fun l => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n l ω))
        (rdivNoiseLevel (δ n) (ν n)) ≤ terminalIndex ρ n := by
      unfold discrepancyIndex
      split
      next he => exact (Nat.find_spec he).1
      next => exact le_rfl
    exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
  have hmain : ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2 ≤ C * A n ∧
      ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤ C * S n := by
    by_cases hlarge : N ≤ n
    · have h := hN n hlarge E (hgeneric n hn' E hE hpE hcomp henv) ω hω
      exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hCrC (hA n hn).le),
        h.2.1.trans (mul_le_mul_of_nonneg_right hCrC (hS n hn).le)⟩
    · have hh := ((hMinima n hn' lam hsel).1 ω).1
      have hb := rdiv_hypothesis_norm_le V mu G g₀ support B c₀ CG hIV hDensity
        hDensityBounds hHypBound hOutcome.1 _ hh
      have hb0 := rdiv_hypothesis_norm_le V mu G g₀ support B c₀ CG hIV hDensity
        hDensityBounds hHypBound hOutcome.1 _ hRealizable
      have hs : ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤ 4 * B ^ 2 := by
        have ht := (norm_sub_le (candidate n lam ω) (minNormSolution V)).trans (add_le_add hb hb0)
        nlinarith only [ht, sq_nonneg (‖candidate n lam ω - minNormSolution V‖),
          norm_nonneg (candidate n lam ω - minNormSolution V), hOutcome.1]
      have hw : ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2 ≤ 4 * B ^ 2 := by
        have ht := (projCondExpOp V).le_opNorm (candidate n lam ω - minNormSolution V)
        have hc := mul_le_mul_of_nonneg_right (projCondExpOp_norm_le_one V)
          (norm_nonneg (candidate n lam ω - minNormSolution V))
        have ht' : ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ≤
            ‖candidate n lam ω - minNormSolution V‖ := by simpa using ht.trans hc
        exact (pow_le_pow_left₀ (norm_nonneg _) ht' 2).trans hs
      exact ⟨hw.trans (hprefix n hn (by omega)).1, hs.trans (hprefix n hn (by omega)).2⟩
  refine ⟨hmain.1, hmain.2,
    rdiv_strong_rate_simplification β (δ n) (ν n) C hSource.1 (hDeterministic.1 n) hC.le, ?_⟩
  intro hz
  have hlam : lam = 2 := by
    change gridValue ρ (discrepancyIndex ρ n _ _) = 2
    rw [(hsearch ω hω).2.2.1 hz]
    simp [gridValue]
  have hzerr := rdiv_zero_solution_initial_errors V P sample split mu g₀ gHat rHat
    ρ ξ B Ce δ ν rawG rawH rawR candidate hCe hIV hRange hRealizable hOutcome
    hMinima n hn' E hcomp (hraw n hn').1 (hraw n hn').2.1
    (hraw n hn').2.2.1 (hraw n hn').2.2.2 hz ω hω
  change _ ≤ C * δ n ^ 2 ∧ _ ≤ C * δ n ^ 2
  change ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2 ≤ _ ∧
    ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤ _
  rw [hlam]
  exact ⟨hzerr.1.trans (mul_le_mul_of_nonneg_right hzC (sq_nonneg _)),
    hzerr.2.trans (mul_le_mul_of_nonneg_right hzC (sq_nonneg _))⟩


/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P),
[analysis sample](hyp:sample), [sample split](hyp:split), [grid factor](hyp:ρ),
[failure level](hyp:ξ), [boundedness scale](hyp:B), [source exponent](hyp:β),
[hypothesis accuracy curve](hyp:δ), [pilot accuracy curve](hyp:ν), [reference
measure for the density](hyp:mu), [estimated density family](hyp:gHat), [pilot
regression family](hyp:rHat), and [candidate estimator family](hyp:candidate),
[the joint DeepIV rate property](goal) requires a single positive constant such
that every eligible sample size admits a measurable event of probability at
least one minus the failure level carrying [the prediction rate](step:1),
[the estimation rate](step:2), [the comparison absorbing the direct bias term
into the interpolation rate](step:3), and [both sharper rates when the solution is zero](step:4).

Binding conclusion/scope reading: one positive rate constant works at every
admissible sample size, with a measurable high-probability event for that size.
All displayed bounds share that event. This is a conclusion, never a premise. -/
-- @node: ass:pin-190
noncomputable def PinDeepivRateJointEvent : Prop :=
  ∃ C > 0, ∀ n : ℕ, rdivMinSampleSize B ≤ n → ∃ E : Set Ω,
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      ∀ ω ∈ E,
          ‖projCondExpOp V (candidate n (rdivSelected V P sample split mu gHat rHat ρ δ ν candidate n ω) ω - minNormSolution V)‖ ^ 2 ≤ C * (rdivErrorScale β (δ n) (ν n)) ∧
          ‖candidate n (rdivSelected V P sample split mu gHat rHat ρ δ ν candidate n ω) ω - minNormSolution V‖ ^ 2 ≤
            C * (δ n ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) +
              (rdivErrorScale β (δ n) (ν n)) ^ interpolationExponent β) ∧
          C * (δ n ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) +
            (rdivErrorScale β (δ n) (ν n)) ^ interpolationExponent β) ≤
              (2 * C) * (rdivErrorScale β (δ n) (ν n)) ^ interpolationExponent β ∧
          (ZeroSolutionCaseRate V → ‖projCondExpOp V (candidate n (rdivSelected V P sample split mu gHat rHat ρ δ ν candidate n ω) ω - minNormSolution V)‖ ^ 2 ≤ C * δ n ^ 2 ∧ ‖candidate n (rdivSelected V P sample split mu gHat rHat ρ δ ν candidate n ω) ω - minNormSolution V‖ ^ 2 ≤ C * δ n ^ 2)

omit [IsProbabilityMeasure P] in
/-- If [one positive constant provides the full DeepIV rate-event bundle at every
eligible sample size](hyp:hRate), then [the joint DeepIV prediction, estimation,
interpolation, and zero-solution rate property holds](goal).

Project the stronger rate-event conclusion returned by `deepiv_rate` to its
binding reading, retaining the same constant and the same event at each size. -/
-- keep: Checked projection from the proved stronger RDIV event bundle to ass:pin-190; retained as the explicit mathematical link for the conclusion reading.
lemma pinDeepivRateJointEvent_of_rateEvents
    (hRate : ∃ C > 0, ∀ n : ℕ, rdivMinSampleSize B ≤ n → ∃ E : Set Ω,
      RDIVRateOnEvent V P sample split ρ ξ β w₀ δ ν rawG rawH rawR
        mu g₀ gHat rHat candidate (fun _ => E) n C) :
    PinDeepivRateJointEvent V P sample split ρ ξ B β δ ν mu gHat rHat candidate := by
  obtain ⟨C, hC, hRate⟩ := hRate
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨E, hE, hpE, _, _, hBounds⟩ := hRate n hn
  exact ⟨E, hE, hpE, hBounds⟩

end Papers.TsAdaptiveEstimationInference
