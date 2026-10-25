module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVFittingTransfer
/-! Calibrated RDIV fitting comparisons from the reviewed Foster source input.

The conditional specialization and actual-sample transport use the same raw
confidence curves and the separate coherent fitting-supremum convention.
-/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- Assume [the localized concentration bound for the two fitting coordinates](hyp:hVector),
[ρ is at least one half and less than one](hyp:hρ), [ξ is strictly between zero
and one](hyp:hξ), [the instrument space is the full instrument-measurable L²
space, the true density generates the joint input–instrument law, and the moment
representer gives the conditional outcome mean](hyp:hIV), [the moment representer
lies in the range of the projected conditional expectation operator](hyp:hRange),
and [the minimum-norm solution belongs to the hypothesis class](hyp:hRealizable).
Suppose also [the density class contains the true density and consists of measurable,
nonnegative conditional densities normalized almost everywhere](hyp:hDensity),
[the true density is bounded below by positive c₀ on the common support and class
densities are bounded above by positive CG there and vanish outside it](hyp:hBounds),
[the outcome is almost surely bounded in absolute value by nonnegative B](hyp:hOutcome),
[all hypotheses are bounded in absolute value by B on the common support](hyp:hHyp),
[the selected density maximizes preliminary-sample likelihood within the class](hyp:hMLE),
[localized processes for the hypothesis class and each fixed-density image class
have measurable versions](hyp:hMeas), [grid penalties are positive and at most two
and localized fitted-loss suprema have jointly measurable versions coherent on
fresh samples and the actual fitting block](hyp:hFittingVersion), [δH bounds the
critical radii of the hypothesis class and every density image class at grid
confidence levels](hyp:hRadius), and [δG and δH dominate a common positive multiple
of their respective confidence floors](hyp:hFloor). Then [there is a positive
constant C such that, at every positive sample size and every grid penalty, for
almost every fixed preliminary sample, the absolute difference between population
and empirical penalized-risk contrasts relative to the minimum-norm solution is
simultaneously at most C times the sum of δH times the Hilbert distance to that
solution and δH², with success probability at least one minus a quarter of the
grid confidence budget; δH is evaluated at that quarter budget](goal). -/
-- @node: rdiv_frozen_fitting_comparison_local
lemma rdiv_frozen_fitting_comparison_local
    (μ : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
    (B c₀ CG ρ ξ : ℝ) (δG δH : ℕ → ℝ → ℝ)
    (hVector : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V μ g₀) (hRange : RangeCondition V)
    (hRealizable : H0MemHypothesisClass V)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hOutcome : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split μ G g₀ gHat)
    (hFittingVersion : RDIVFittingSupremumVersion V P sample split μ gHat ρ)
    (hRadius : HypothesisCriticalRadiusBound V μ G δH ρ)
    (hFloor : RDIVRadiusFloor δG δH ρ) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ lam ∈ regGrid ρ n,
      ∀ᵐ preliminary ∂P,
        1 - gridConfidence ρ ξ n / 4 ≤ P.real {ω | ∀ h ∈ V.H,
          |(conditionalRisk V μ gHat n preliminary lam h -
              conditionalRisk V μ gHat n preliminary lam (minNormSolution V)) -
            (empiricalRisk V P sample split μ (fun _ _ => gHat n preliminary) n ω lam h -
              empiricalRisk V P sample split μ (fun _ _ => gHat n preliminary) n ω lam
                (minNormSolution V))| ≤
          C * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
            δH n (gridConfidence ρ ξ n / 4) ^ 2)} := by
  exact rdiv_frozen_fitting_comparison V P sample split μ G g₀ gHat support
    B c₀ CG ρ ξ δG δH hVector hρ hξ hIV hRange hRealizable hDensity hBounds
    hOutcome hHyp hMLE hMeas hFittingVersion hRadius hFloor

/-- Assume [the localized concentration bound for the two fitting coordinates](hyp:hVector),
[ρ is at least one half and less than one](hyp:hρ), [ξ is strictly between zero
and one](hyp:hξ), [the instrument space is the full instrument-measurable L²
space, the true density generates the joint input–instrument law, and the moment
representer gives the conditional outcome mean](hyp:hIV), [the moment representer
lies in the range of the projected conditional expectation operator](hyp:hRange),
and [the minimum-norm solution belongs to the hypothesis class](hyp:hRealizable).
Suppose also [the density class contains the true density and consists of measurable,
nonnegative conditional densities normalized almost everywhere](hyp:hDensity),
[the true density is bounded below by positive c₀ on the common support and class
densities are bounded above by positive CG there and vanish outside it](hyp:hBounds),
[the outcome is almost surely bounded in absolute value by nonnegative B](hyp:hOutcome),
[all hypotheses are bounded in absolute value by B on the common support](hyp:hHyp),
[the selected density maximizes preliminary-sample likelihood within the class](hyp:hMLE),
[localized processes for the hypothesis class and each fixed-density image class
have measurable versions](hyp:hConditionalMeas), [grid penalties are positive and
at most two and localized fitted-loss suprema have jointly measurable versions
coherent on fresh samples and the actual fitting block](hyp:hFittingVersion),
[δH bounds the critical radii of the hypothesis class and every density image
class at grid confidence levels](hyp:hRadius), and [δG and δH dominate a common
positive multiple of their respective confidence floors](hyp:hFloor). Then
[there is a positive constant C such that, at every positive sample size, a
measurable event of probability at least 1 − ξ/4 bounds the absolute difference
between population and empirical penalized-risk contrasts relative to the
minimum-norm solution, simultaneously for every grid penalty and hypothesis,
by C times the sum of δH times the Hilbert distance to that solution and δH²,
with the selected density evaluated on the observed sample and δH evaluated at
one quarter of the grid confidence budget](goal). -/
-- @node: rdiv_fitting_concentration_local
lemma rdiv_fitting_concentration_local
    (μ : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
    (B c₀ CG ρ ξ : ℝ) (δG δH : ℕ → ℝ → ℝ)
    (hVector : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V μ g₀) (hRange : RangeCondition V)
    (hRealizable : H0MemHypothesisClass V)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hOutcome : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hConditionalMeas : PinRDIVMeasurabilityReading V P sample split μ G g₀ gHat)
    (hFittingVersion : RDIVFittingSupremumVersion V P sample split μ gHat ρ)
    (hRadius : HypothesisCriticalRadiusBound V μ G δH ρ)
    (hFloor : RDIVRadiusFloor δG δH ρ) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ F : Set Ω,
      MeasurableSet F ∧ 1 - ξ / 4 ≤ P.real F ∧
      ∀ ω ∈ F, ∀ lam ∈ regGrid ρ n, ∀ h ∈ V.H,
        |(conditionalRisk V μ gHat n ω lam h -
            conditionalRisk V μ gHat n ω lam (minNormSolution V)) -
          (empiricalRisk V P sample split μ gHat n ω lam h -
            empiricalRisk V P sample split μ gHat n ω lam (minNormSolution V))| ≤
          C * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
            δH n (gridConfidence ρ ξ n / 4) ^ 2) := by
  obtain ⟨C, hC, hfrozen⟩ := rdiv_frozen_fitting_comparison_local V P sample split
    μ G g₀ gHat support B c₀ CG ρ ξ δG δH hVector hρ hξ hIV hRange
    hRealizable hDensity hBounds hOutcome hHyp hMLE hConditionalMeas hFittingVersion hRadius hFloor
  refine ⟨C, hC, ?_⟩
  exact rdiv_thaw_fitting_comparisons V P sample split μ G g₀ gHat support B c₀ CG
    ρ ξ δG δH hρ hξ hIV hRange hRealizable hDensity hBounds hOutcome
    hHyp hMLE hConditionalMeas hFittingVersion hRadius hFloor C hC hfrozen


end Papers.TsAdaptiveEstimationInference
