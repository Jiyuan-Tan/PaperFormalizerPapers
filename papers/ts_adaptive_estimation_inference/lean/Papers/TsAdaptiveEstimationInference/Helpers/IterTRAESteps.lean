module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEBiasless
/-! One-step deterministic curvature estimates for iterative TRAE. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]

/-- Under [the range condition](hyp:hRange), [closeness](hyp:hClose),
[boundedness](hyp:hB), [a common almost-sure envelope](hyp:hCommonB),
[a nonnegative concentration constant](hyp:hC), [nonnegative accuracy](hyp:hr),
[an oracle above the grid floor](hyp:hOracle), and [the iterative concentration
comparisons on the event](hyp:hEvent), take [an observation in that event](hyp:hω),
[a grid penalty](hyp:hgrid) [on the oracle segment](hyp:hsegment) [that is positive](hyp:hlam),
and [an iteration at least one](hyp:hj) [within the horizon](hyp:hjt), with
[its population iterate in the hypothesis class](hyp:hStar) and
[empirical iterates minimizing the iterative objectives](hyp:hEst).
[The squared strong variance is bounded by its displayed coefficient times squared
accuracy divided by squared penalty plus the preceding strong variance; the squared
weak variance is bounded by its displayed coefficient times squared weak bias,
squared accuracy, and penalty times the preceding strong variance](goal). -/
-- @node: iter_trae_step_bounds
lemma iter_trae_step_bounds (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
    (sample : AnalysisSample V P) (split : SampleSplit)
    (ρ c b β B C : ℝ) (t n j : ℕ) (δ r : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (E : Set Ω)
    (hRange : RangeCondition V) (hClose : ClosenessCondition V)
    (hB : TRAEBoundedness V B) (hCommonB : TRAECommonNullSetBoundedness V B) (hC : 0 ≤ C) (hr : 0 ≤ r n)
    (hOracle : gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))
    (hEvent : IterTRAEConcentrationOn V P sample split ρ c b β t δ r iter n E C)
    (ω : Ω) (hω : ω ∈ E) (lam : ℝ) (hgrid : lam ∈ regGrid ρ n)
    (hsegment : lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2)
    (hlam : 0 < lam) (hj : 1 ≤ j) (hjt : j ≤ t)
    (hStar : populationIterate V lam j ∈ V.H)
    (hEst : IsIterTRAEEstimator V P sample split n t lam (fun k => iter n k lam)) :
    iterStrongVariance V j lam (iter n j lam ω) ^ 2 ≤
      (16 * ((C ^ 2 + 2 * C + 1) * (B + 1) + 2 * C + 1) ^ 2) *
        (r n ^ 2 / lam ^ 2 +
          iterStrongVariance V (j - 1) lam (iter n (j - 1) lam ω) ^ 2) ∧
    iterWeakVariance V j lam (iter n j lam ω) ^ 2 ≤
      (16 * ((C ^ 2 + 4 * C + 1) + C + 1) ^ 2) *
        (iterWeakBias V j lam ^ 2 + r n ^ 2 +
          lam * iterStrongVariance V (j - 1) lam (iter n (j - 1) lam ω) ^ 2) := by
  obtain ⟨habs, _, hcenter⟩ := hEvent.2 hOracle ω hω lam hgrid hsegment j hj hjt
  have hh := (hEst.2 j hj hjt ω).1
  have hopt : traeEmpiricalLoss V P sample split n ω (iter n j lam ω) -
      traeEmpiricalLoss V P sample split n ω (populationIterate V lam j) ≤
      lam * iterEmpiricalCenterDifference V P sample split n j lam (fun k => iter n k lam) ω := by
    have ho := (hEst.2 j hj hjt ω).2 _ hStar
    unfold iterEmpiricalCenterDifference
    linarith only [ho]
  have hcurv := iter_trae_population_curvature V hRange hClose j hj lam hlam hStar _ hh
  have hi := iter_trae_biasless_comparison_on_common_event V P sample split
    ρ c b β C t n j δ r iter E hRange hClose hC hr hOracle hEvent
    ω hω lam hgrid hsegment hj hjt hStar hEst
  have hi' := iter_trae_ordinary_on_event V P sample split hRange hClose n ω C (r n) lam
    (iterEmpiricalCenterDifference V P sample split n j lam (fun k => iter n k lam) ω)
    hC hr _ _ hh hStar (habs _ hh) ((hEvent.1 ω hω).1 _ hStar).2 hopt
  rw [hcurv] at hi hi'
  have hc := (abs_le.mp hcenter).2
  have hcl := mul_le_mul_of_nonneg_left hc hlam.le
  have hinf := trae_critic_infinity_le V B hB hCommonB _ (hClose _ hStar)
  have hmul := mul_le_mul_of_nonneg_left hinf
    (show 0 ≤ r n * ‖iter n j lam ω - populationIterate V lam j‖ by positivity)
  have hK : 0 ≤ C ^ 2 + 2 * C + 1 := by positivity
  have hmul' := mul_le_mul_of_nonneg_left hmul hK
  constructor
  · apply iter_trae_strong_absorb _ _ (iterWeakVariance V j lam (iter n j lam ω)) _ _ _ _ _
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hr hlam hsegment.2 hK hC hB.1
    dsimp only [iterStrongVariance, iterWeakVariance, iterCriticInfinityNorm] at hi ⊢
    nlinarith only [hi, hcl, hmul']
  · apply iter_trae_weak_absorb (iterStrongVariance V j lam (iter n j lam ω)) _ _ _ _ _ _ _
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hr hlam hsegment.2
      (by positivity) hC
    dsimp only [iterStrongVariance, iterWeakVariance, iterWeakBias] at hi' ⊢
    nlinarith only [hi', hcl]

end Papers.TsAdaptiveEstimationInference
