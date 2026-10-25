module
public import Papers.TsAdaptiveEstimationInference.Helpers.DRBiasRate
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEAdaptiveRates
/-! Joint adaptive nuisance rates at the prescribed shrinking confidence levels. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵)
variable (hTarget : Continuous V.targetFunctional)
variable (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

omit [IsProbabilityMeasure P] in
/-- If [every candidate on the regularization grid attains a measurable TRAE
minimum](hyp:hMinima) and [the sample size is positive](hyp:hn), then [the
candidate chosen by the discrepancy rule belongs to the primal hypothesis
class for every sample outcome](goal). -/
-- @node: trae_selected_mem_hypothesis
lemma trae_selected_mem_hypothesis (ρ : ℝ) (δ : ℕ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hMinima : TRAEMinimaAttained V P sample split ρ candidate)
    (n : ℕ) (hn : 0 < n) (ω : Ω) :
    candidate n (traeSelected V P sample split ρ δ candidate n ω) ω ∈ V.H := by
  have hi : discrepancyIndex ρ n
      (fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω))
      (traeNoiseLevel (δ n)) ≤ terminalIndex ρ n := by
    unfold discrepancyIndex
    split
    next he => exact (Nat.find_spec he).1
    next => exact le_rfl
  have hsel : traeSelected V P sample split ρ δ candidate n ω ∈ regGrid ρ n :=
    Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
  exact ((hMinima n hn _ hsel).1 ω).1

/-- For [a family of primal candidates indexed by sample size and penalty](hyp:hCandidate),
assume [primal localized concentration](hyp:hBennett), [dual localized
concentration](hyp:qBennett), [a primal localized comparison of squared
norms](hyp:hNorm), [a dual localized comparison of squared norms](hyp:qNorm),
and [a grid ratio between one-half inclusive and one exclusive](hyp:hρ).
Then [there is a positive calibration threshold, chosen before the source
parameters, such that the joint primal and dual TRAE assumptions, common
null-set envelopes, and a confidence sequence yield positive rate constants
and measurable events with failure probability at most twice that sequence;
eventually on these events both selected candidates belong to their hypothesis
classes, their squared strong errors obey the respective interpolation rates,
and their squared operator errors are bounded by the corresponding constants
times the accuracy scale squared](goal). -/
-- @node: dr_adaptive_joint_rate_events
lemma dr_adaptive_joint_rate_events
    (ρ B c₀ CG Cm : ℝ) (baseδ baseν ξseq : ℕ → ℝ)
    (tildeδh tildeδq : ℕ → ℝ → ℝ)
    (hCandidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (qCandidate : ℕ → ℝ → Ω → V.Qbar.toSubmodule)
    (hBennett : TRAELocalizedConcentration V)
    (qBennett : TRAELocalizedConcentration (dualWorld V hTarget))
    (hNorm : SquaredNormLocalizedComparison V P sample split)
    (qNorm : SquaredNormLocalizedComparison (dualWorld V hTarget) P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (βh βq : ℝ) (wh : V.Hbar.toSubmodule) (wq : V.Qbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      PrimalDualTRAEHypotheses V hTarget P sample split ρ B βh βq wh wq
        tildeδh tildeδq δ ν baseδ baseν ξseq required c₀ CG Cm κ₀
        hCandidate qCandidate → TRAECommonNullSetBoundedness V B →
      TRAECommonNullSetBoundedness (dualWorld V hTarget) B → ConfidenceSequence ξseq →
      let hhat := fun n ω => hCandidate n (traeSelected V P sample split ρ δ hCandidate n ω) ω
      let qhat := fun n ω => qCandidate n (traeSelected (dualWorld V hTarget) P sample split ρ δ qCandidate n ω) ω
      ∃ Ch > 0, ∃ Cq > 0, ∃ E : ℕ → Set Ω,
        (∀ n, MeasurableSet (E n)) ∧ (∀ n, 1 - 2 * ξseq n ≤ P.real (E n)) ∧
        ∀ᶠ n in atTop, ∀ ω ∈ E n,
          hhat n ω ∈ V.H ∧ qhat n ω ∈ V.Q ∧
          ‖hhat n ω - minNormSolution V‖ ^ 2 ≤ Ch * δ n ^ (2 * interpolationExponent βh) ∧
          ‖qhat n ω - dualMinNormSolution V hTarget‖ ^ 2 ≤ Cq * δ n ^ (2 * interpolationExponent βq) ∧
          ‖projCondExpOp V (hhat n ω - minNormSolution V)‖ ^ 2 ≤ Ch * δ n ^ 2 ∧
          ‖adjointOp V (qhat n ω - dualMinNormSolution V hTarget)‖ ^ 2 ≤ Cq * δ n ^ 2 := by
  classical
  let allocation := fun n => gridConfidence ρ (ξseq n / 2) n
  obtain ⟨Rh, hRh, hh⟩ := trae_rate_events_at_allocation V P sample split hBennett
    ρ B baseδ baseν tildeδh allocation hCandidate hNorm hρ
  obtain ⟨Rq, hRq, hq⟩ := trae_rate_events_at_allocation (dualWorld V hTarget) P sample split qBennett
    ρ B baseδ baseν tildeδq allocation qCandidate qNorm hρ
  refine ⟨max Rh Rq, hRh.trans_le (le_max_left _ _), ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro βh βq wh wq δ ν hBoth hCommon qCommon hConfidence
  obtain ⟨hRange, qRange, hSource, qSource, hReal, qReal, hClose, qClose,
    hMSC, qMSC, hBound, qBound, hComplex, qComplex, hMinima, qMinima,
    hScale, qScale, hInflation, hDet⟩ := hBoth
  have hinflate (R : ℝ) (hR : R ≤ max Rh Rq) :
      CalibratedValidBounds δ ν baseδ baseν κδ κν R :=
    ⟨hInflation.1, hInflation.2.1, hR.trans hInflation.2.2.1,
      hR.trans hInflation.2.2.2.1, hInflation.2.2.2.2⟩
  obtain ⟨Ch, hCh, hhRate⟩ := hh βh wh δ ν κδ κν hRange hSource hReal hClose
    hMSC hBound hCommon hComplex hScale hMinima (hinflate Rh (le_max_left _ _)) hDet
  obtain ⟨Cq, hCq, hqRate⟩ := hq βq wq δ ν κδ κν qRange qSource qReal qClose
    qMSC qBound qCommon qComplex qScale qMinima (hinflate Rq (le_max_right _ _)) hDet
  have halloc_le (n : ℕ) : 2 * allocation n ≤ ξseq n := by
    have hk : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hdiv : allocation n ≤ ξseq n / 2 := by
      dsimp [allocation, gridConfidence]
      exact div_le_self (by positivity [hConfidence.1 n]) hk
    linarith only [hdiv]
  have hvalid : ∀ᶠ n in atTop, allocation n ∈ Set.Ioo (0 : ℝ) 1 := by
    filter_upwards [hConfidence.2.2.eventually (gt_mem_nhds zero_lt_one)] with n hn
    constructor
    · dsimp [allocation, gridConfidence]
      positivity [hConfidence.1 n]
    · linarith [halloc_le n]
  let good := fun n => traeMinSampleSize B ≤ n ∧ allocation n ∈ Set.Ioo (0 : ℝ) 1
  have hev : ∀ n, ∃ Eh Eq : Set Ω,
      MeasurableSet Eh ∧ MeasurableSet Eq ∧
      1 - ξseq n ≤ P.real Eh ∧ 1 - ξseq n ≤ P.real Eq ∧
      (good n → ∀ ω ∈ Eh,
        ‖projCondExpOp V (hCandidate n (traeSelected V P sample split ρ δ hCandidate n ω) ω - minNormSolution V)‖ ^ 2 ≤ Ch * δ n ^ 2 ∧
        ‖hCandidate n (traeSelected V P sample split ρ δ hCandidate n ω) ω - minNormSolution V‖ ^ 2 ≤ Ch * δ n ^ (2 * interpolationExponent βh)) ∧
      (good n → ∀ ω ∈ Eq,
        ‖projCondExpOp (dualWorld V hTarget) (qCandidate n (traeSelected (dualWorld V hTarget) P sample split ρ δ qCandidate n ω) ω - (show V.Qbar.toSubmodule from minNormSolution (dualWorld V hTarget)))‖ ^ 2 ≤ Cq * δ n ^ 2 ∧
        ‖qCandidate n (traeSelected (dualWorld V hTarget) P sample split ρ δ qCandidate n ω) ω - (show V.Qbar.toSubmodule from minNormSolution (dualWorld V hTarget))‖ ^ 2 ≤ Cq * δ n ^ (2 * interpolationExponent βq)) := by
    intro n
    by_cases hn : good n
    · obtain ⟨Eh, hEh, hpEh, hrh⟩ := hhRate n hn.1 hn.2
      obtain ⟨Eq, hEq, hpEq, hrq⟩ := hqRate n hn.1 hn.2
      refine ⟨Eh, Eq, hEh, hEq, by linarith [halloc_le n], by linarith [halloc_le n], ?_, ?_⟩
      · intro _ ω hω
        simpa only [interpolationExponent, div_mul_eq_mul_div, mul_div_assoc] using hrh ω hω
      · intro _ ω hω
        convert hrq ω hω using 1 <;>
          simp only [interpolationExponent, mul_div_assoc] <;> rfl
    · refine ⟨Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ, ?_, ?_, ?_, ?_⟩
      · simpa using sub_le_self (1 : ℝ) (hConfidence.1 n).le
      · simpa using sub_le_self (1 : ℝ) (hConfidence.1 n).le
      · exact fun h => (hn h).elim
      · exact fun h => (hn h).elim
  choose Eh Eq hEh hEq hpEh hpEq hrh hrq using hev
  refine ⟨Ch, hCh, Cq, hCq, fun n => Eh n ∩ Eq n,
    fun n => (hEh n).inter (hEq n), ?_, ?_⟩
  · intro n
    have hu := measureReal_union_le (μ := P) (Eh n)ᶜ (Eq n)ᶜ
    rw [← Set.compl_inter] at hu
    linarith [probReal_add_probReal_compl (μ := P) (hEh n),
      probReal_add_probReal_compl (μ := P) (hEq n),
      probReal_add_probReal_compl (μ := P) ((hEh n).inter (hEq n)), hpEh n, hpEq n]
  · filter_upwards [hvalid, eventually_ge_atTop (traeMinSampleSize B), eventually_gt_atTop 0] with n hn hnN hn0
    intro ω hω
    have hhr := hrh n ⟨hnN, hn⟩ ω hω.1
    have hqr := hrq n ⟨hnN, hn⟩ ω hω.2
    rw [dualWorld_operator, dualWorld_solution V hTarget qRange] at hqr
    exact ⟨trae_selected_mem_hypothesis V P sample split ρ δ hCandidate hMinima n hn0 ω,
      trae_selected_mem_hypothesis (dualWorld V hTarget) P sample split ρ δ qCandidate qMinima n hn0 ω,
      hhr.2, hqr.2, hhr.1, hqr.1⟩

end Papers.TsAdaptiveEstimationInference
