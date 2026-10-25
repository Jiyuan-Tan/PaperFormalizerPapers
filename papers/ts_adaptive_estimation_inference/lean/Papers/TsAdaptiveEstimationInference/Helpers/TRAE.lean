module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAELossEvents
/-! TRAE estimator comparisons for adaptive inverse problems. -/
public section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
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
/-- If [the minimum-norm solution belongs to the hypothesis class](hyp:hRealizable)
and [projected residuals of hypotheses belong to the critic class](hyp:hClose),
then, [on a sample outcome where the zero critic is represented by zero](hyp:hZero),
[the empirical adversarial loss of h is nonnegative](goal). -/
-- @node: traeEmpiricalLoss_nonneg
lemma traeEmpiricalLoss_nonneg (hRealizable : H0MemHypothesisClass V)
    (hClose : ClosenessCondition V) (n : ℕ) (ω : Ω) (h : V.Hbar.toSubmodule)
    (hZero : ω ∈ sampleZeroEvent V P sample) :
    0 ≤ traeEmpiricalLoss V P sample split n ω h := by
  have hz : (0 : V.Qbar.toSubmodule) ∈ V.F := by
    simpa using hClose (minNormSolution V) hRealizable
  have hv : blockAverage V P sample (split.fit n) (traeIntegrand V h 0) ω = 0 := by
    unfold blockAverage
    have hv : ∑ i ∈ split.fit n, traeIntegrand V h 0 (sample.Z i ω) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [traeIntegrand, (sampleZeroEvent_spec V P sample hZero i).2]
    rw [hv, mul_zero]
  unfold traeEmpiricalLoss
  by_cases hb : BddAbove (Set.range (fun f : V.F =>
      blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω))
  · exact hv ▸ le_ciSup hb (⟨0, hz⟩ : V.F)
  · rw [ciSup_of_not_bddAbove hb, Real.sSup_empty]

/-- Suppose [the minimum-norm solution belongs to the hypothesis class](hyp:hRealizable),
[the comparison constant is positive](hyp:hCevent), [the accuracy at n is
nonnegative](hyp:hd), and [the penalty lies in $(0,2]$](hyp:hlam).
If [loss and norm comparisons hold on E](hyp:hComparisons), [the sample outcome
belongs to E](hyp:hω), [h is an admissible hypothesis](hyp:hh), and [its penalized
empirical objective is no larger than that of the minimum-norm solution](hyp:hOpt),
then [its empirical loss plus the penalty times its squared error and twice its
inner product error with the minimum-norm solution is at most
three times the comparison constant plus four times its square, times squared
accuracy, plus one eighth of the penalty times squared error](goal). -/
-- @node: trae_empirical_optimality
lemma trae_empirical_optimality
    (hRealizable : H0MemHypothesisClass V)
    {δ : ℕ → ℝ} {n : ℕ} {E : Set Ω} {Cevent lam : ℝ} {ω : Ω}
    (hCevent : 0 < Cevent) (hd : 0 ≤ δ n) (hlam : lam ∈ Set.Ioc (0 : ℝ) 2)
    (hComparisons : TRAEComparisonsOn V P sample split δ n E Cevent) (hω : ω ∈ E)
    {h : V.Hbar.toSubmodule} (hh : h ∈ V.H)
    (hOpt : traeEmpiricalLoss V P sample split n ω h +
        lam * primalEmpSq V P sample split n ω h ≤
      traeEmpiricalLoss V P sample split n ω (minNormSolution V) +
        lam * primalEmpSq V P sample split n ω (minNormSolution V)) :
    traeEmpiricalLoss V P sample split n ω h +
        lam * (‖h - minNormSolution V‖ ^ 2 +
          2 * inner ℝ (minNormSolution V) (h - minNormSolution V)) ≤
      (3 * Cevent + 4 * Cevent ^ 2) * δ n ^ 2 +
        lam / 8 * ‖h - minNormSolution V‖ ^ 2 := by
  obtain ⟨_, hnorm, hzero, _⟩ := hComparisons ω hω
  have hn := (abs_le.mp (hnorm h hh)).1
  have he : ‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2 =
      ‖h - minNormSolution V‖ ^ 2 +
        2 * inner ℝ (minNormSolution V) (h - minNormSolution V) := by
    have hx : h = minNormSolution V + (h - minNormSolution V) := by abel
    conv_lhs => rw [hx, norm_add_sq_real]
    ring
  have hy : Cevent * δ n * ‖h - minNormSolution V‖ ≤
      ‖h - minNormSolution V‖ ^ 2 / 8 + 2 * Cevent ^ 2 * δ n ^ 2 := by
    nlinarith [sq_nonneg (‖h - minNormSolution V‖ - 4 * Cevent * δ n)]
  have hy' := mul_le_mul_of_nonneg_left hy hlam.1.le
  have hz := mul_le_mul_of_nonneg_right hlam.2
    (show 0 ≤ (Cevent + 2 * Cevent ^ 2) * δ n ^ 2 by positivity)
  rw [he] at hn
  have hm := mul_le_mul_of_nonneg_left hn hlam.1.le
  nlinarith

/-- Assume [the grid ratio lies in $[1/2,1)$](hyp:hρ), [the range condition
holds](hyp:hRange), [the solution satisfies the beta source condition with
source vector w₀](hyp:hSource), [the minimum-norm solution is admissible](hyp:hRealizable),
[projected residuals are admissible critics](hyp:hClose), [the candidate fits
attain the grid minima](hyp:hMinima), [the accuracy sequences satisfy the
deterministic calibration conditions](hyp:hDeterministic), and [the event
comparison constant is positive](hyp:hCevent). Then [one positive constant
bounds, on every measurable event of probability at least one minus the
confidence level carrying those comparisons, both the candidate's empirical
loss plus half the penalty times squared error by squared accuracy plus the
source bias, and its squared error by squared accuracy divided by the penalty
plus the interpolation power of empirical loss plus squared accuracy, uniformly
over positive sample sizes and grid penalties](goal). -/
-- @node: trae_strong_from_comparisons
lemma trae_strong_from_comparisons
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (hRealizable : H0MemHypothesisClass V) (hClose : ClosenessCondition V)
    (hMinima : TRAEMinimaAttained V P sample split ρ candidate)
    (hDeterministic : CalibrationDeterministic δ ν)
    (Cevent : ℝ) (hCevent : 0 < Cevent) :
      ∃ C > 0, ∀ ξ : ℝ, ∀ n : ℕ, 0 < n →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      TRAEComparisonsOn V P sample split δ n E Cevent → ∀ ω ∈ E,
      ∀ lam ∈ regGrid ρ n,
        traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + lam / 2 * ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤
          C * (δ n ^ 2 + ‖w₀‖ ^ 2 * lam ^ biasExponent β) ∧
        ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤ C * (δ n ^ 2 / lam +
          (traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + δ n ^ 2) ^ interpolationExponent β) := by
  obtain ⟨Cs, hCs, hs⟩ := (variational_source V β w₀ hSource).2
    (1 / 16) (by norm_num)
  let A := 3 * Cevent + 4 * Cevent ^ 2
  let D := 2 + 2 * Cevent
  let α := interpolationExponent β
  let K := Cs * ‖w₀‖ ^ (2 / (1 + truncatedSource β))
  let C := 2 * (A + Cevent + Cs) + 2 * A + 2 * K * D ^ α + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : 0 < truncatedSource β := lt_min hSource.1 zero_lt_one
  have hα : 0 < α := by
    dsimp [α, interpolationExponent]
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ξ n hn E hE hprob hComparisons ω hω lam hlam
  have hl : lam ∈ Set.Ioc (0 : ℝ) 2 := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hlam
    dsimp [gridValue]
    constructor
    · exact mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
    · have hp : ρ ^ k ≤ 1 := pow_le_one₀ (by linarith [hρ.1]) hρ.2.le
      linarith
  have hl0 : 0 < lam := hl.1
  obtain ⟨hh, hOpt⟩ := (hMinima n hn lam hlam).1 ω
  let h := candidate n lam ω
  let u := h - minNormSolution V
  let L := traeEmpiricalLoss V P sample split n ω h
  have hL : 0 ≤ L := traeEmpiricalLoss_nonneg V P sample split hRealizable hClose n ω h ((hComparisons ω hω).2.2.2)
  have hbase := trae_empirical_optimality V P sample split hRealizable hCevent
    (hDeterministic.1 n) hl hComparisons hω hh (hOpt _ hRealizable)
  change L + lam * (‖u‖ ^ 2 + 2 * inner ℝ (minNormSolution V) u) ≤
    A * δ n ^ 2 + lam / 8 * ‖u‖ ^ 2 at hbase
  have hw : ‖projCondExpOp V u‖ ^ 2 ≤ 2 * L + 2 * Cevent * δ n ^ 2 := by
    have hc := ((hComparisons ω hω).1 h hh).1
    rw [traePopulationLoss_eq V hRange hClose h hh] at hc
    change (1 / 2 : ℝ) * ‖projCondExpOp V u‖ ^ 2 - Cevent * δ n ^ 2 ≤ L at hc
    linarith
  have hinner : -|inner ℝ (minNormSolution V) u| ≤ inner ℝ (minNormSolution V) u :=
    neg_abs_le _
  have hneg := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 2 * lam)
  have henergy := (hs u).1 lam hl
  have hfirst : L + lam / 2 * ‖u‖ ^ 2 ≤
      2 * (A + Cevent + Cs) * (δ n ^ 2 + ‖w₀‖ ^ 2 * lam ^ biasExponent β) := by
    have hbias : 0 ≤ ‖w₀‖ ^ 2 * lam ^ biasExponent β := by positivity
    have ht : 0 ≤ lam * ‖u‖ ^ 2 := by positivity
    have hcross : 0 ≤ (A + Cevent) * (‖w₀‖ ^ 2 * lam ^ biasExponent β) := by positivity
    have hnoise : 0 ≤ Cs * δ n ^ 2 := by positivity
    nlinarith
  have hKD : 0 ≤ K * D ^ α := by positivity
  have hCfirst : 2 * (A + Cevent + Cs) ≤ C := by
    dsimp [C]
    linarith
  constructor
  · exact hfirst.trans (mul_le_mul_of_nonneg_right hCfirst (by positivity))
  · have hsecond := (hs u).2
    have hnorm : (13 / 16 : ℝ) * ‖u‖ ^ 2 ≤
        A * δ n ^ 2 / lam + K * ‖projCondExpOp V u‖ ^
          (2 * truncatedSource β / (1 + truncatedSource β)) := by
      apply (mul_le_mul_iff_right₀ hl0).mp
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hl0)]
      change lam * ((13 / 16 : ℝ) * ‖u‖ ^ 2) ≤ A * δ n ^ 2 +
        lam * (Cs * ‖w₀‖ ^ (2 / (1 + truncatedSource β)) *
          ‖projCondExpOp V u‖ ^ (2 * truncatedSource β / (1 + truncatedSource β)))
      have hpos := mul_le_mul_of_nonneg_left hsecond hl.1.le
      nlinarith only [hbase, hpos, hneg, hL]
    have hwD : ‖projCondExpOp V u‖ ^ 2 ≤ D * (L + δ n ^ 2) := by
      calc
        _ ≤ 2 * L + 2 * Cevent * δ n ^ 2 := hw
        _ ≤ _ := by
          dsimp [D]
          nlinarith only [mul_nonneg hCevent.le hL, sq_nonneg (δ n)]
    have hpow : ‖projCondExpOp V u‖ ^ (2 * truncatedSource β / (1 + truncatedSource β)) ≤
        D ^ α * (L + δ n ^ 2) ^ α := by
      calc
        _ = (‖projCondExpOp V u‖ ^ 2) ^ α := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
          congr 1
          dsimp [α, interpolationExponent]
          ring
        _ ≤ (D * (L + δ n ^ 2)) ^ α :=
          Real.rpow_le_rpow (sq_nonneg _) hwD hα.le
        _ = _ := Real.mul_rpow hD.le (by positivity)
    have hkpow := mul_le_mul_of_nonneg_left hpow hK
    have hx : 0 ≤ δ n ^ 2 / lam := by positivity
    have hp : 0 ≤ (L + δ n ^ 2) ^ α := by positivity
    have hcA : 2 * A ≤ C := by dsimp [C]; linarith
    have hcK : 2 * K * D ^ α ≤ C := by dsimp [C]; linarith
    have hca := mul_le_mul_of_nonneg_right hcA hx
    have hck := mul_le_mul_of_nonneg_right hcK hp
    change ‖u‖ ^ 2 ≤ C * (δ n ^ 2 / lam + (L + δ n ^ 2) ^ α)
    have hh2 : ‖u‖ ^ 2 ≤ 2 * (A * (δ n ^ 2 / lam) +
        K * D ^ α * (L + δ n ^ 2) ^ α) := by
      rw [mul_div_assoc] at hnorm
      nlinarith only [hnorm, hkpow, sq_nonneg ‖u‖]
    nlinarith only [hh2, hca, hck]


/-- Given [localized concentration for the adversarial loss](hyp:hBennett_of_gate),
[localized squared-norm comparisons](hyp:hNorm_of_gate), and [a grid ratio in
$[1/2,1)$](hyp:hρ), [each positive event comparison constant admits a positive
calibration threshold such that, under the range, source, realizability,
closeness, mean-square continuity, boundedness, complexity, attainment and
calibration conditions, one positive constant controls both the empirical loss
plus half the penalty times squared error by squared accuracy plus source bias,
and squared error by squared accuracy divided by the penalty plus the
interpolation power of empirical loss plus squared accuracy, throughout every
supplied common event and uniformly over sample sizes and grid penalties](goal).

The event comparison constant is fixed before the calibration threshold. -/
-- @node: lem:strong-convexity
lemma strong_convexity
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    : ∀ Cevent : ℝ, 0 < Cevent →
      ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hClose : ClosenessCondition V) →
      (hMSC : MeanSquareContinuity V) →
      (hBound : TRAEBoundedness V B) → (hCommon : TRAECommonNullSetBoundedness V B) →
      (hComplexity : TRAECriticalRadiusBound V tildeδ) →
      (hMinima : TRAEMinimaAttained V P sample split ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      ∃ C > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => gridConfidence ρ ξ n)) →
      ∀ n : ℕ, 0 < n →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      TRAEComparisonsOn V P sample split δ n E Cevent → ∀ ω ∈ E,
      ∀ lam ∈ regGrid ρ n,
        traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + lam / 2 * ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤
          C * (δ n ^ 2 + ‖w₀‖ ^ 2 * lam ^ biasExponent β) ∧
        ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤ C * (δ n ^ 2 / lam +
          (traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + δ n ^ 2) ^ interpolationExponent β) := by
  intro Cevent hCevent
  refine ⟨1, zero_lt_one, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro β w₀ δ ν hRange hSource hRealizable hClose hMSC hBound hCommon
    hComplexity hMinima hInflation hDeterministic
  obtain ⟨C, hC, hstrong⟩ := trae_strong_from_comparisons (V := V) (P := P) (sample := sample)
    (split := split) (ρ := ρ) (β := β) (w₀ := w₀) (δ := δ)
    (ν := ν) (candidate := candidate) hρ hRange hSource hRealizable hClose hMinima hDeterministic Cevent hCevent
  exact ⟨C, hC, fun ξ _ _ => hstrong ξ⟩

/-- Given [localized concentration for the adversarial loss](hyp:hBennett_of_gate),
[localized squared-norm comparisons](hyp:hNorm_of_gate), and [a grid ratio in
$[1/2,1)$](hyp:hρ), [each positive event comparison constant admits a positive
calibration threshold such that, under the range, source, realizability,
closeness, mean-square continuity, boundedness, complexity, attainment and
calibration conditions, a single positive constant bounds the candidate's
squared projected error by empirical loss plus squared accuracy and its squared
structural error by the stability term plus the interpolation power of empirical
loss plus squared accuracy, throughout every supplied common event and uniformly
over sample sizes and grid penalties](goal). -/
-- @node: lem:trae-accepted-bounds
lemma trae_accepted_bounds
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    : ∀ Cevent : ℝ, 0 < Cevent →
      ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hClose : ClosenessCondition V) →
      (hMSC : MeanSquareContinuity V) →
      (hBound : TRAEBoundedness V B) → (hCommon : TRAECommonNullSetBoundedness V B) →
      (hComplexity : TRAECriticalRadiusBound V tildeδ) →
      (hMinima : TRAEMinimaAttained V P sample split ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      ∃ C > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => gridConfidence ρ ξ n)) →
      ∀ n : ℕ, 0 < n →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      TRAEComparisonsOn V P sample split δ n E Cevent → ∀ ω ∈ E,
      ∀ lam ∈ regGrid ρ n,
        ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2 ≤ C * (traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + δ n ^ 2) ∧
        ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤ C * (traeStability (δ n) lam +
          (traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + δ n ^ 2) ^ interpolationExponent β) := by
  intro Cevent hCevent
  obtain ⟨required, hrequired, hstrong⟩ := strong_convexity
    (V := V) (P := P) (sample := sample) (split := split)
    (ρ := ρ) (B := B) (baseδ := baseδ) (baseν := baseν)
    (tildeδ := tildeδ) (c₀ := c₀) (CG := CG) (Cm := Cm)
    (candidate := candidate) hBennett_of_gate hNorm_of_gate hρ Cevent hCevent
  refine ⟨required, hrequired, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro β w₀ δ ν hRange hSource hRealizable hClose hMSC hBound hCommon
    hComplexity hMinima hInflation hDeterministic
  obtain ⟨Cs, hCs, hs⟩ := hstrong κ₀ β w₀ δ ν hRange hSource
    hRealizable hClose hMSC hBound hCommon hComplexity hMinima hInflation
    hDeterministic
  let C := Cs + 2 + 2 * Cevent
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hScale n hn E hE hprob hComparisons ω hω lam hlam
  have hh := ((hMinima n hn lam hlam).1 ω).1
  have hL := traeEmpiricalLoss_nonneg V P sample split hRealizable hClose n ω
    (candidate n lam ω) ((hComparisons ω hω).2.2.2)
  constructor
  · have hc := ((hComparisons ω hω).1 _ hh).1
    rw [traePopulationLoss_eq V hRange hClose _ hh] at hc
    have hCL : 0 ≤ (Cs + 2 * Cevent) *
        traeEmpiricalLoss V P sample split n ω (candidate n lam ω) := by positivity
    have hCd : 0 ≤ (Cs + 2) * δ n ^ 2 := by positivity
    have hweak : ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2 ≤
        C * (traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + δ n ^ 2) := by
      dsimp only [C]
      linarith only [hc, hCL, hCd]
    exact hweak
  · have hb := (hs ξ hξ hScale n hn E hE hprob hComparisons ω hω lam hlam).2
    have hbase : 0 ≤ traeStability (δ n) lam +
        (traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + δ n ^ 2) ^
          interpolationExponent β := (mul_nonneg_iff_of_pos_left hCs).mp
            ((sq_nonneg _).trans hb)
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hbase)


end Papers.TsAdaptiveEstimationInference
