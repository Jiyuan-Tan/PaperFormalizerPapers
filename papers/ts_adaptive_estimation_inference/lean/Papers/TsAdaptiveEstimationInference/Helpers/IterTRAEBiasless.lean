module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEComparisons
/-! The biasless excess-loss comparison on the calibrated iterative common event. -/
public section
set_option linter.style.longLine false

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped Topology

variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]

/-- Assume [the range condition](hyp:hRange), [feasibility of residual
critics](hyp:hClose), [a nonnegative event constant](hyp:hC), [a nonnegative
radius at this sample size](hyp:hr), [the terminal grid point is below the
source radius](hyp:hOracle), and [the common event supplies iterative TRAE
concentration](hyp:hEvent). For [an outcome in that event](hyp:hω), [a penalty
on the grid](hyp:hgrid) and [in the oracle segment](hyp:hsegment), and [an
iteration at least one](hyp:hj) and [no larger than the horizon](hyp:hjt), if
[the population iterate is in the hypothesis class](hyp:hStar) and [the fitted
sequence recursively minimizes the empirical TRAE objective](hyp:hEst), [its
population excess loss over the population iterate is at most the penalty times
the empirical center difference plus the squared event constant plus twice the
constant plus one, multiplied by the sum of the radius times strong variance
times critic supremum norm, the radius times weak variance, and the squared
radius](goal). -/
-- @node: iter_trae_biasless_comparison_on_common_event
lemma iter_trae_biasless_comparison_on_common_event
    (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
    (sample : AnalysisSample V P) (split : SampleSplit)
    (ρ c b β C : ℝ) (t n j : ℕ) (δ r : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (E : Set Ω)
    (hRange : RangeCondition V) (hClose : ClosenessCondition V)
    (hC : 0 ≤ C) (hr : 0 ≤ r n)
    (hOracle : gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))
    (hEvent : IterTRAEConcentrationOn V P sample split ρ c b β t δ r iter n E C)
    (ω : Ω) (hω : ω ∈ E) (lam : ℝ) (hgrid : lam ∈ regGrid ρ n)
    (hsegment : lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2)
    (hj : 1 ≤ j) (hjt : j ≤ t)
    (hStar : populationIterate V lam j ∈ V.H)
    (hEst : IsIterTRAEEstimator V P sample split n t lam (fun k => iter n k lam)) :
    traePopulationLoss V (iter n j lam ω) -
        traePopulationLoss V (populationIterate V lam j) ≤
      lam * iterEmpiricalCenterDifference V P sample split n j lam
        (fun k => iter n k lam) ω +
      (C ^ 2 + 2 * C + 1) *
        (r n * iterStrongVariance V j lam (iter n j lam ω) *
            iterCriticInfinityNorm V j lam +
          r n * iterWeakVariance V j lam (iter n j lam ω) + r n ^ 2) := by
  have hh := (hEst.2 j hj hjt ω).1
  obtain ⟨habs, hinc, _⟩ := hEvent.2 hOracle ω hω lam hgrid hsegment j hj hjt
  have hopt : traeEmpiricalLoss V P sample split n ω (iter n j lam ω) -
      traeEmpiricalLoss V P sample split n ω (populationIterate V lam j) ≤
      lam * iterEmpiricalCenterDifference V P sample split n j lam
        (fun k => iter n k lam) ω := by
    have ho := (hEst.2 j hj hjt ω).2 _ hStar
    unfold iterEmpiricalCenterDifference
    linarith only [ho]
  exact iter_trae_biasless_on_event V P sample split hRange hClose n ω C (r n) lam
    (iterEmpiricalCenterDifference V P sample split n j lam (fun k => iter n k lam) ω)
    hC hr _ _ hh hStar (habs _ hh)
    (fun a ha f hf => hinc a ha f hf) hopt

/-- Assume [localized TRAE concentration](hyp:hBennett), [anchored
concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss
concentration](hyp:hFixedSq_of_gate), [scalar Lipschitz concentration](hyp:hNorm_of_gate),
[a grid ratio from one half inclusive to one exclusive](hyp:hρ), [a positive
iteration horizon](hyp:ht), [a positive source multiplier](hyp:hc), [a source
scale at least two](hyp:hb), [mean-square continuity](hyp:hMSC), [iterative
mean-square continuity](hyp:hIterMSC), [TRAE boundedness](hyp:hBound), [a common
almost-sure envelope](hyp:hCommon), and [critical-radius bounds](hyp:hComplexity).
[There are positive event and comparison constants, chosen before confidence
and source parameters, such that calibrated scales, range and realizability
conditions, feasible residual critics, attained empirical minima, and measurable
localized processes yield measurable component events with their allocated
probability bounds; their common event has probability at least one minus the
failure budget, supplies iterative concentration, and bounds each fitted
iterate's population excess loss over its population comparator by the penalty
times the empirical center difference plus the comparison constant times the
sum of the base radius times strong variance times critic supremum norm, the
base radius times weak variance, and the squared base radius](goal). -/
-- @node: iter_trae_excess_loss_biasless
lemma iter_trae_excess_loss_biasless
    (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (hBennett : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : ScalarLipschitzLocalizedConcentration V P sample split)
    (ρ B c b : ℝ) (t : ℕ) (baseδ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (ht : 1 ≤ t) (hc : 0 < c) (hb : 2 ≤ b)
    (hMSC : MeanSquareContinuity V) (hIterMSC : IterMeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ Cevent > 0, ∃ C > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
      ∀ (β : ℝ) (δ : ℕ → ℝ),
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
        ∀ (_hOracle : gridValue ρ (terminalIndex ρ n) ≤
            c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))),
        ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
          lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
          ∀ j, 1 ≤ j → j ≤ t →
            traePopulationLoss V (iter n j lam ω) -
              traePopulationLoss V (populationIterate V lam j) ≤
            lam * iterEmpiricalCenterDifference V P sample split n j lam
              (fun k => iter n k lam) ω +
            C * (baseδ n * iterStrongVariance V j lam (iter n j lam ω) *
                iterCriticInfinityNorm V j lam +
              baseδ n * iterWeakVariance V j lam (iter n j lam ω) + baseδ n ^ 2) := by
  obtain ⟨D, hD, hevent⟩ := iter_trae_concentration_event_uniform_confidence
    V P sample split (ρ := ρ) (B := B) (baseδ := baseδ) (tildeδ := tildeδ)
    (candidate := candidate) (iter := iter) (b := b) (c := c) (t := t)
    hBennett hAnchored_of_gate hFixedSq_of_gate hNorm_of_gate
    hρ ht hc hb hMSC hIterMSC hBound hCommon hComplexity
  refine ⟨D, hD, D ^ 2 + 2 * D + 1, by positivity, ?_⟩
  intro ξ hξ hScale β δ hRange hRealizable hClose hIterRealizable
    hMinima hIterMinima hProcesses n hn
  obtain ⟨component, hcomponent, hE, hpE, hEvent⟩ :=
    hevent ξ hξ hScale β δ hRange hRealizable hClose hIterRealizable
      hMinima hIterMinima hProcesses n hn
  refine ⟨component, hcomponent, hE, hpE, hEvent, ?_⟩
  intro hOracle ω hω lam hlam hsegment j hj hjt
  have hStar := hIterRealizable n hOracle j hj hjt lam hlam hsegment
  have hEst := (hIterMinima n hn lam hlam).1
  have hr : 0 ≤ baseδ n :=
    (Real.rpow_nonneg (by positivity) _).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  exact iter_trae_biasless_comparison_on_common_event V P sample split
    ρ c b β D t n j δ baseδ iter _ hRange hClose hD.le hr hOracle hEvent
    ω hω lam hlam hsegment hj hjt hStar hEst

end Papers.TsAdaptiveEstimationInference
