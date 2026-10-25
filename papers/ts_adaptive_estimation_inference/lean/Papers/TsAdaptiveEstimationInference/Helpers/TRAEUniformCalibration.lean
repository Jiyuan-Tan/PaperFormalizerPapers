module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAE
public import Papers.TsAdaptiveEstimationInference.Helpers.TikhonovOracle
/-! Calibration of TRAE comparisons with a source-only output constant. -/
public section
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 600000
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- For [a grid ratio at least one half and less than one](hyp:hρ), [there is
a positive calibration threshold for each positive event constant, chosen
before the source exponent and source element, such that under the range,
source, realizability, closeness, and attained-minima conditions there is a
positive comparison constant chosen before the event constant and accuracy
curves: whenever the base loss-accuracy curve is nonnegative and the accuracy
curves are inflated above that threshold and satisfy deterministic calibration, the base TRAE comparisons on
any event at a positive sample size imply both the calibrated TRAE comparisons
and the discrepancy bias envelope on the same event](goal). -/
-- @node: trae_discrepancy_uniform
lemma trae_discrepancy_uniform
    (ρ : ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    ∃ required : ℝ → ℝ, (∀ Ce > 0, 0 < required Ce) ∧ ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule),
      RangeCondition V → BetaSourceCondition V β w₀ →
      H0MemHypothesisClass V → ClosenessCondition V →
      TRAEMinimaAttained V P sample split ρ candidate →
      ∃ C > 0, ∀ Ce > 0, ∀ (baseδ baseν δ ν : ℕ → ℝ) (κδ κν : ℝ),
      (∀ n : ℕ, 0 < n → 0 ≤ baseδ n) →
      CalibratedValidBounds δ ν baseδ baseν κδ κν (required Ce) →
      CalibrationDeterministic δ ν →
      ∀ n : ℕ, 0 < n → ∀ E : Set Ω,
        TRAEComparisonsOn V P sample split baseδ n E Ce →
        TRAEComparisonsOn V P sample split δ n E C ∧
        TRAEDiscrepancyEnvelope V P sample split ρ β δ w₀ candidate n E C := by
  classical
  let required : ℝ → ℝ := fun Ce => 2 * ((3 * Ce + 4 * Ce ^ 2) + Ce) + Ce + 1
  refine ⟨required, ?_, ?_⟩
  · intro Ce hCe
    dsimp [required]
    positivity
  intro β w₀ hRange hSource hRealizable hClose hMinima
  obtain ⟨Cs, hCs, hs⟩ := (variational_source V β w₀ hSource).2
    (1 / 16) (by norm_num)
  let C := 2 * Cs + 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hCsC : 2 * Cs ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro Ce hCe baseδ baseν δ ν κδ κν hBase hInflation hDeterministic
  let A := 3 * Ce + 4 * Ce ^ 2
  let D := 2 * (A + Ce)
  let R := D + Ce + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hk : 1 ≤ κδ := hInflation.1
  have hRk : R ≤ κδ := hInflation.2.2.1
  have hDk : D ≤ κδ ^ 2 := by
    have hDle : D ≤ κδ := by dsimp [R] at hRk; linarith
    nlinarith
  have hCek : Ce ≤ κδ ^ 2 := by
    have hCele : Ce ≤ κδ := by dsimp [R] at hRk; linarith
    nlinarith
  intro n hn E hcomp
  have hd0 : 0 ≤ baseδ n := hBase n hn
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
  have hlinear : Ce * baseδ n ≤ δ n := by
    rw [hInflation.2.2.2.2.1 n]
    have hCeκ : Ce ≤ κδ := by dsimp [R] at hRk; linarith
    exact mul_le_mul_of_nonneg_right hCeκ hd0
  have honeC : 1 ≤ C := by dsimp [C]; linarith
  have hcomp' : TRAEComparisonsOn V P sample split δ n E C := by
    intro ω hω
    obtain ⟨hloss, hnorm, hz, hZero⟩ := hcomp ω hω
    have hsq : Ce * baseδ n ^ 2 ≤ C * δ n ^ 2 :=
      hzero.trans (le_mul_of_one_le_left (sq_nonneg _) honeC)
    refine ⟨?_, ?_, hz.trans hsq, hZero⟩
    · intro h hh
      obtain ⟨hl, hu⟩ := hloss h hh
      constructor <;> linarith
    · intro h hh
      have hl := mul_le_mul_of_nonneg_right hlinear (norm_nonneg (h - minNormSolution V))
      apply (hnorm h hh).trans
      calc
        Ce * (baseδ n * ‖h - minNormSolution V‖ + baseδ n ^ 2) ≤
            δ n * ‖h - minNormSolution V‖ + δ n ^ 2 := by nlinarith only [hl, hzero]
        _ ≤ C * (δ n * ‖h - minNormSolution V‖ + δ n ^ 2) :=
          le_mul_of_one_le_left (by positivity [hDeterministic.1 n]) honeC
  refine ⟨hcomp', hC, ?_⟩
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

end Papers.TsAdaptiveEstimationInference
