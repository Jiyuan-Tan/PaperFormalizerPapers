module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAE
/-! TTraeDiscrepancyBound for adaptive inverse problems. -/
public section
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
-- @node: thm:trae-discrepancy-bound
/-- Given [localized TRAE concentration](hyp:hBennett_of_gate), [the squared-norm
comparison](hyp:hNorm_of_gate), [a grid factor between one-half inclusive and one
exclusive](hyp:hρ), and [a failure level strictly between zero and one](hyp:hξ),
[there is a positive calibration threshold, uniform over inflation rules, source
exponents and witnesses, and accuracy curves, such that the range condition,
the source condition, solution realizability, closeness, mean-square continuity,
boundedness, common-null-set boundedness, critical-radius control, scale
calibration at the grid confidence levels, attained fitting minima, adequate
calibration inflation, and deterministic accuracy curves imply the existence
of a positive constant and, at every positive sample size, a measurable event
of probability at least one minus the failure level on which both the TRAE
comparisons and discrepancy envelope hold with that constant](goal). -/
theorem trae_discrepancy_bound
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    : ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hClose : ClosenessCondition V) →
      (hMSC : MeanSquareContinuity V) →
      (hBound : TRAEBoundedness V B) → (hCommon : TRAECommonNullSetBoundedness V B) →
      (hComplexity : TRAECriticalRadiusBound V tildeδ) →
      (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => gridConfidence ρ ξ n)) →
      (hMinima : TRAEMinimaAttained V P sample split ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      TRAEComparisonsOn V P sample split δ n E C ∧ TRAEDiscrepancyEnvelope V P sample split ρ β δ w₀ candidate n E C := by
  classical
  -- Fix the comparison constant before introducing the source exponent and witness.
  by_cases hSetup : RangeCondition V ∧ H0MemHypothesisClass V ∧ ClosenessCondition V ∧
      MeanSquareContinuity V ∧ TRAEBoundedness V B ∧ TRAECommonNullSetBoundedness V B ∧ TRAECriticalRadiusBound V tildeδ ∧
      TRAEScaleCalibration baseδ tildeδ (fun n => gridConfidence ρ ξ n)
  · obtain ⟨hr, hh0, hcl, hm, hb, hcb, hcx, hsc⟩ := hSetup
    obtain ⟨Ce, hCe, hevent⟩ := traeCommonEvent_constructed (hBennett_of_gate := hBennett_of_gate) V P sample split ρ ξ B baseδ tildeδ
      hNorm_of_gate hρ hξ hr hh0 hcl hm hb hcb hcx hsc
    let A := 3 * Ce + 4 * Ce ^ 2
    let D := 2 * (A + Ce)
    -- This inflation absorbs both the reference loss and the noise part of optimality.
    let R := D + Ce + 1
    have hA : 0 < A := by dsimp [A]; positivity
    have hD : 0 < D := by dsimp [D]; positivity
    have hR : 0 < R := by dsimp [R]; positivity
    refine ⟨R, hR, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hClose hMSC hBound hCommon
      hComplexity hScale hMinima hInflation hDeterministic
    obtain ⟨Cs, hCs, hs⟩ := (variational_source V β w₀ hSource).2
      (1 / 16) (by norm_num)
    let C := Ce + 2 * Cs + 1
    have hC : 0 < C := by dsimp [C]; positivity
    have hCeC : Ce ≤ C := by dsimp [C]; linarith
    have hCsC : 2 * Cs ≤ C := by dsimp [C]; linarith
    have hk : 1 ≤ κδ := hInflation.1
    have hRk : R ≤ κδ := hInflation.2.2.1
    have hDk : D ≤ κδ ^ 2 := by
      have hDle : D ≤ κδ := by dsimp [R] at hRk; linarith
      nlinarith
    have hCek : Ce ≤ κδ ^ 2 := by
      have hCele : Ce ≤ κδ := by dsimp [R] at hRk; linarith
      nlinarith
    refine ⟨C, hC, ?_⟩
    intro n hn
    obtain ⟨normEvent, hE, hp, hcomp⟩ := hevent n hn
    let E := traeCommonSampleEvent V P sample split ρ ξ B baseδ tildeδ hBennett_of_gate
      hr hcl hm hb hcb hcx hξ hsc n hn normEvent
    have hd0 : 0 ≤ baseδ n := by
      exact (show 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) by positivity).trans
        ((le_max_right _ _).trans (hsc.1 n hn))
    have hd : baseδ n ≤ δ n := by
      rw [hInflation.2.2.2.2.1 n]
      nlinarith
    have hd2 : baseδ n ^ 2 ≤ δ n ^ 2 := pow_le_pow_left₀ hd0 hd 2
    have hnoise : D * baseδ n ^ 2 ≤ δ n ^ 2 := by
      rw [hInflation.2.2.2.2.1 n]
      nlinarith [mul_le_mul_of_nonneg_right hDk (sq_nonneg (baseδ n))]
    have hzero : Ce * baseδ n ^ 2 ≤ δ n ^ 2 := by
      rw [hInflation.2.2.2.2.1 n]
      nlinarith [mul_le_mul_of_nonneg_right hCek (sq_nonneg (baseδ n))]
    have hcomp' : TRAEComparisonsOn V P sample split δ n E C := by
      intro ω hω
      obtain ⟨hloss, hnorm, hz, hZero⟩ := hcomp ω hω
      have hsq : Ce * baseδ n ^ 2 ≤ C * δ n ^ 2 :=
        (mul_le_mul_of_nonneg_left hd2 hCe.le).trans
          (mul_le_mul_of_nonneg_right hCeC (sq_nonneg _))
      refine ⟨?_, ?_, hz.trans hsq, hZero⟩
      · intro h hh
        obtain ⟨hl, hu⟩ := hloss h hh
        constructor <;> linarith
      · intro h hh
        refine (hnorm h hh).trans ?_
        apply (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hd (norm_nonneg _)) hd2) hCe.le).trans
        exact mul_le_mul_of_nonneg_right hCeC
          (add_nonneg (mul_nonneg (hDeterministic.1 n) (norm_nonneg _)) (sq_nonneg _))
    refine ⟨E, hE, hp, hcomp', hC, ?_⟩
    intro ω hω
    refine ⟨((hcomp ω hω).2.2.1).trans hzero, ?_⟩
    intro lam hlam
    have hl : lam ∈ Set.Ioc (0 : ℝ) 2 := by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hlam
      dsimp [gridValue]
      constructor
      · exact mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
      · have hp : ρ ^ k ≤ 1 := pow_le_one₀ (by linarith [hρ.1]) hρ.2.le
        linarith
    have hl0 : 0 < lam := hl.1
    obtain ⟨hh, hopt⟩ := (hMinima n hn lam hlam).1 ω
    let h := candidate n lam ω
    let u := h - minNormSolution V
    let L := traeEmpiricalLoss V P sample split n ω h
    have hbase := trae_empirical_optimality V P sample split hRealizable hCe hd0 hl
      hcomp hω hh (hopt _ hRealizable)
    change L + lam * (‖u‖ ^ 2 + 2 * inner ℝ (minNormSolution V) u) ≤
      A * baseδ n ^ 2 + lam / 8 * ‖u‖ ^ 2 at hbase
    have hw : ‖projCondExpOp V u‖ ^ 2 ≤ 2 * L + 2 * Ce * baseδ n ^ 2 := by
      have hc := ((hcomp ω hω).1 h hh).1
      rw [traePopulationLoss_eq V hRange hClose h hh] at hc
      change (1 / 2 : ℝ) * ‖projCondExpOp V u‖ ^ 2 - Ce * baseδ n ^ 2 ≤ L at hc
      linarith
    have hL : 0 ≤ L := traeEmpiricalLoss_nonneg V P sample split hRealizable hClose n ω h ((hcomp ω hω).2.2.2)
    have ht : 0 ≤ lam * ‖u‖ ^ 2 := by positivity
    have henergy := (hs u).1 lam hl
    have hneg := mul_le_mul_of_nonneg_left
      (neg_abs_le (inner ℝ (minNormSolution V) u)) (by positivity : 0 ≤ 2 * lam)
    -- Absorb the source cross term into population curvature; only bias retains Cs.
    have hfirst : L + lam / 2 * ‖u‖ ^ 2 ≤
        D * baseδ n ^ 2 + 2 * Cs * (‖w₀‖ ^ 2 * lam ^ biasExponent β) := by
      dsimp only [D]
      nlinarith only [hbase, hw, henergy, hneg, hL, ht,
        mul_nonneg hCe.le (sq_nonneg (baseδ n))]
    have hdrop : L ≤ D * baseδ n ^ 2 +
        2 * Cs * (‖w₀‖ ^ 2 * lam ^ biasExponent β) := by
      have ht : 0 ≤ lam / 2 * ‖u‖ ^ 2 := by positivity
      linarith
    change L ≤ _
    have hbc := mul_le_mul_of_nonneg_right hCsC
      (show 0 ≤ ‖w₀‖ ^ 2 * lam ^ biasExponent β by positivity)
    nlinarith only [hdrop, hnoise, hbc]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hClose hMSC hBound hCommon
      hComplexity hScale hMinima hInflation hDeterministic
    exact (hSetup ⟨hRange, hRealizable, hClose, hMSC, hBound, hCommon, hComplexity, hScale⟩).elim


end Papers.TsAdaptiveEstimationInference
