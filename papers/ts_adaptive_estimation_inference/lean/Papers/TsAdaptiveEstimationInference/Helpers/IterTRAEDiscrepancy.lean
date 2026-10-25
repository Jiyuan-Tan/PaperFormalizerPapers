module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAERefinedPropagation
/-! A discrepancy bias coefficient chosen before the oracle balancing constant. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]

/-- Assume [an admissible grid ratio](hyp:hρ), [horizon at least one](hyp:ht),
[multiplier at least two](hyp:hb), [the range condition](hyp:hRange), [the source condition
with the given exponent and witness](hyp:hSource), [closeness](hyp:hClose),
[boundedness](hyp:hBound), [boundedness outside a common null set](hyp:hCommon),
[a positive event constant](hyp:hCevent), [nonnegative base accuracy at positive sample
sizes](hyp:hbase), [accuracy equal to the inflation factor times base accuracy](hyp:hscale),
and [squared inflation at least five quarters of the noise constant plus the event
constant](hyp:hcoeff). Then [one positive bias coefficient works for every balancing
constant: whenever iterative realizability and measurable empirical minima hold, the
sample size is positive, the terminal grid reaches the oracle radius, the oracle point
exceeds the square root of the iterative scale, and an event carries the concentration
certificate, that event also carries the iterative TRAE discrepancy bound](goal). -/
-- @node: iter_trae_discrepancy_uniform
lemma iter_trae_discrepancy_uniform
    (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (ρ b β B Cevent : ℝ) (t : ℕ) (δ baseδ : ℕ → ℝ) (κδ : ℝ)
    (w₀ : V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : GridDomain ρ) (ht : 1 ≤ t) (hb : 2 ≤ b)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (hClose : ClosenessCondition V) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hCevent : 0 < Cevent)
    (hbase : ∀ n, 0 < n → 0 ≤ baseδ n)
    (hscale : ∀ n, δ n = κδ * baseδ n)
    (hcoeff : (5 / 4 : ℝ) * iterTraeNoiseConstant B Cevent t + Cevent ≤ κδ ^ 2) :
    ∃ C > 0, ∀ c : ℝ, IterRealizableTRAE V ρ c b β t δ →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      ∀ n, 0 < n →
      gridValue ρ (terminalIndex ρ n) ≤
        c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) →
      Real.sqrt (b * δ n ^ 2) ≤ iterTraeOraclePoint ρ c b β t δ n →
      ∀ E : Set Ω, IterTRAEConcentrationOn V P sample split
        ρ c b β t δ baseδ iter n E Cevent →
      IterTRAEDiscrepancyOn V P sample split ρ c b β t δ w₀ iter n E C := by
  let K := iterTraeNoiseConstant B Cevent t
  obtain ⟨Cb, hCb, hpop⟩ := iter_trae_preliminary_weak_bound_uniform V P sample split
    ρ b β B Cevent t δ baseδ w₀ iter hρ ht (by linarith) hRange hSource hClose
    hBound hCommon hCevent
  refine ⟨(5 / 4 : ℝ) * Cb + 1, by positivity, ?_⟩
  intro c hIterRealizable hIterMinima n hn0 hterminal hstable E hEvent
  refine ⟨by positivity, ?_⟩
  intro ω hω lam hl hs
  have hlam : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    exact mul_pos (by norm_num) (pow_pos (by linarith only [hρ.1]) k)
  have hweak := hpop c hIterRealizable hIterMinima n hn0 (hbase n hn0) hterminal E hEvent ω hω lam hl hs
  change traePopulationLoss V (iter n t lam ω) ≤
    K * (baseδ n ^ 2 + b * baseδ n ^ 2 / lam) +
      Cb * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t at hweak
  have hupper := ((hEvent.1 ω hω).1 _
    (((hIterMinima n hn0 lam hl).1.2 t ht le_rfl ω).1)).2
  have hnoise : ((5 / 4 : ℝ) * K + Cevent) * baseδ n ^ 2 ≤ δ n ^ 2 := by
    rw [hscale n, mul_pow]
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
  have hnoise' : (5 / 4 : ℝ) * K * (b * baseδ n ^ 2 / lam) ≤ b * δ n ^ 2 / lam := by
    have hc : (5 / 4 : ℝ) * K ≤ κδ ^ 2 := by linarith only [hcoeff, hCevent]
    have hi := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ b * baseδ n ^ 2 / lam by positivity)
    rw [hscale n, mul_pow]
    convert hi using 1 <;> first | rfl | ring
  have hbranch : min lam (b * δ n ^ 2 / lam) = b * δ n ^ 2 / lam := by
    apply min_eq_right
    apply (div_le_iff₀ hlam).2
    have hsq : b * δ n ^ 2 ≤ lam ^ 2 :=
      (Real.sqrt_le_iff).1 (hstable.trans hs.1) |>.2
    nlinarith only [hsq]
  change traeEmpiricalLoss V P sample split n ω (iter n t lam ω) ≤
    δ n ^ 2 + min lam (b * δ n ^ 2 / lam) +
      ((5 / 4 : ℝ) * Cb + 1) * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t
  rw [hbranch]
  have hbias : 0 ≤ ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t := by positivity
  nlinarith only [hweak, hupper, hnoise, hnoise', hbias]

end Papers.TsAdaptiveEstimationInference
