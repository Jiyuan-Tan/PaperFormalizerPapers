module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAESteps
/-! Strong variance propagation with an explicit, source-independent coefficient. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]

/-- Suppose [the grid ratio is admissible](hyp:hρ), [the range condition](hyp:hRange),
[closeness](hyp:hClose), [boundedness](hyp:hBound), and [a common almost-sure envelope](hyp:hCommon)
hold, [the concentration constant is positive](hyp:hCevent), [population iterates are realizable](hyp:hIterRealizable),
and [empirical iterative minima are attained](hyp:hIterMinima). For [a positive sample size](hyp:hn),
[nonnegative accuracy](hyp:hr), [an oracle above the grid floor](hyp:hOracle),
[an event satisfying the iterative concentration comparisons](hyp:hEvent),
[an observation in that event](hyp:hω), and [a grid penalty](hyp:hl)
[on the oracle segment](hyp:hs), [the squared strong variance at every iteration
up to the horizon is at most squared accuracy divided by squared penalty times
the iteration power of twice the explicit one-step coefficient plus one](goal). -/
-- @node: iter_trae_strong_variance_explicit
lemma iter_trae_strong_variance_explicit
    (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (ρ c b β B Cevent : ℝ) (t : ℕ) (δ r : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : GridDomain ρ) (hRange : RangeCondition V) (hClose : ClosenessCondition V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hCevent : 0 < Cevent)
    (hIterRealizable : IterRealizableTRAE V ρ c b β t δ)
    (hIterMinima : IterTRAEMinimaAttained V P sample split ρ t iter)
    (n : ℕ) (hn : 0 < n) (hr : 0 ≤ r n)
    (hOracle : gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))
    (E : Set Ω) (hEvent : IterTRAEConcentrationOn V P sample split
      ρ c b β t δ r iter n E Cevent) (ω : Ω) (hω : ω ∈ E)
    (lam : ℝ) (hl : lam ∈ regGrid ρ n)
    (hs : lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2) :
    let A := 16 * ((Cevent ^ 2 + 2 * Cevent + 1) * (B + 1) + 2 * Cevent + 1) ^ 2
    ∀ j, j ≤ t → iterStrongVariance V j lam (iter n j lam ω) ^ 2 ≤
      (2 * A + 1) ^ j * (r n ^ 2 / lam ^ 2) := by
  dsimp only
  let A := 16 * ((Cevent ^ 2 + 2 * Cevent + 1) * (B + 1) + 2 * Cevent + 1) ^ 2
  let D := 2 * A + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 1 ≤ D := by dsimp [D]; linarith only [hA]
  have hgridDomain (lam : ℝ) (hl : lam ∈ regGrid ρ n) : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    exact mul_pos (by norm_num) (pow_pos (by linarith only [hρ.1]) k)
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
      have hstep := (iter_trae_step_bounds V P sample split ρ c b β B Cevent
        t n (j + 1) δ r iter E hRange hClose hBound hCommon hCevent.le hr hOracle hEvent
        ω hω lam hl hs hlam hj hjt hStar hEst).1
      change iterStrongVariance V (j + 1) lam (iter n (j + 1) lam ω) ^ 2 ≤
        A * (r n ^ 2 / lam ^ 2 + iterStrongVariance V j lam (iter n j lam ω) ^ 2) at hstep
      have hi := ih (by omega)
      have hjPow : 1 ≤ D ^ j := one_le_pow₀ hD
      have hcoef : A * (1 + D ^ j) ≤ D ^ (j + 1) := by
        rw [pow_succ]
        change A * (1 + D ^ j) ≤ D ^ j * (2 * A + 1)
        nlinarith only [hA, hjPow, mul_nonneg hA (sub_nonneg.mpr hjPow)]
      calc
        _ ≤ A * (r n ^ 2 / lam ^ 2 + iterStrongVariance V j lam (iter n j lam ω) ^ 2) := hstep
        _ ≤ A * (r n ^ 2 / lam ^ 2 + D ^ j * (r n ^ 2 / lam ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hi) hA
        _ = (A * (1 + D ^ j)) * (r n ^ 2 / lam ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

end Papers.TsAdaptiveEstimationInference
