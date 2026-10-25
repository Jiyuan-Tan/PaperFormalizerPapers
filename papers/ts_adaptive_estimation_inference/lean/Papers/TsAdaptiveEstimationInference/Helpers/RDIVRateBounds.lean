module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVAccepted
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVLossBridge
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVAcceptance
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVRateAssembly
/-! Bounded hypotheses and finite-prefix constants for the RDIV rate assembly. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology

/-- If [M is nonnegative](hyp:_hM), [the baseline constant C₀ is nonnegative](hyp:hC₀), [the rate A is positive from index n₀ onward](hyp:hA), and [the rate D is positive from index n₀ onward](hyp:hD), then [there is a positive constant at least C₀ whose product with either rate is at least M at every index from n₀ up to, but excluding, N](goal). -/
-- @node: rdiv_finite_prefix_constant
lemma rdiv_finite_prefix_constant (A D : ℕ → ℝ) (M C₀ : ℝ) (N n₀ : ℕ)
    (_hM : 0 ≤ M) (hC₀ : 0 ≤ C₀)
    (hA : ∀ n, n₀ ≤ n → 0 < A n) (hD : ∀ n, n₀ ≤ n → 0 < D n) :
    ∃ C > 0, C₀ ≤ C ∧ ∀ n, n₀ ≤ n → n < N →
      M ≤ C * A n ∧ M ≤ C * D n := by
  classical
  let S := ∑ k ∈ Finset.range N, (|M / A k| + |M / D k|)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨C₀ + S + 1, by positivity, by linarith, ?_⟩
  intro n hn hnN
  have ht : |M / A n| + |M / D n| ≤ S :=
    Finset.single_le_sum (fun k _ => add_nonneg (abs_nonneg (M / A k)) (abs_nonneg (M / D k)))
      (Finset.mem_range.2 hnN)
  constructor
  · apply (div_le_iff₀ (hA n hn)).1
    linarith only [le_abs_self (M / A n), abs_nonneg (M / D n), ht, hC₀]
  · apply (div_le_iff₀ (hD n hn)).1
    linarith only [le_abs_self (M / D n), abs_nonneg (M / A n), ht, hC₀]

/-- If [ρ defines an admissible geometric grid](hyp:hρ) and [the confidence error ξ lies strictly between zero and one](hyp:hξ), then [the square of the public logarithmic scale is eventually at least the reciprocal sample size](goal). -/
-- @node: rdiv_public_log_eventual_square_floor
lemma rdiv_public_log_eventual_square_floor (ρ ξ : ℝ)
    (hρ : GridDomain ρ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) ≤ rdivPublicLogScale ρ ξ n ^ 2 := by
  have hr : 0 < ρ := by linarith [hρ.1]
  have hd : 0 < Real.log (1 / ρ) :=
    Real.log_pos ((lt_div_iff₀ hr).2 (by linarith [hρ.2]))
  have hlog := Real.tendsto_log_atTop.comp
    ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hevent := (tendsto_atTop.1 hlog) (2 * Real.log (1 / ρ) - Real.log 2)
  filter_upwards [hevent, eventually_gt_atTop 0] with n hn hn0
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hnlog : 2 ≤ (terminalIndex ρ n : ℝ) := by
    apply le_trans _ (Nat.le_ceil _)
    apply (le_div_iff₀ hd).2
    rw [Real.log_mul (by norm_num) (pow_pos hnpos 2).ne']
    change 2 * Real.log (1 / ρ) - Real.log 2 ≤ Real.log ((n : ℝ) ^ 2) at hn
    linarith
  have hratio : (3 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) / ξ := by
    apply (le_div_iff₀ hξ.1).2
    push_cast
    linarith [hξ.2]
  have hlog1 : 1 ≤ Real.log ((terminalIndex ρ n + 1 : ℕ) / ξ) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hratio
    have hl3 : 1 < Real.log 3 := by
      exact (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
    linarith
  unfold rdivPublicLogScale
  simp only [Nat.cast_add, Nat.cast_one] at hlog1 ⊢
  rw [Real.sq_sqrt (div_nonneg (by linarith) hnpos.le)]
  exact div_le_div_of_nonneg_right hlog1 hnpos.le

/-- If [δ and ν are calibrated valid inflations of the base scales d and v](hyp:hi), [δ and ν are nonnegative at every sample size](hyp:hn), and [the sum of d and v converges to zero](hyp:hl), then [δ and ν each converge to zero](goal). -/
-- @node: rdiv_inflated_scales_tendsto_zero
lemma rdiv_inflated_scales_tendsto_zero (δ ν d v : ℕ → ℝ)
    (kd kv required : ℝ)
    (hi : CalibratedValidBounds δ ν d v kd kv required)
    (hn : CalibrationDeterministic δ ν)
    (hl : Tendsto (fun n => d n + v n) atTop (𝓝 0)) :
    Tendsto δ atTop (𝓝 0) ∧ Tendsto ν atTop (𝓝 0) := by
  have hkd : 0 < kd := by linarith only [hi.1]
  have hkv : 0 < kv := by linarith only [hi.2.1]
  have hd (n : ℕ) : 0 ≤ d n := by
    have h := hn.1 n
    rw [hi.2.2.2.2.1 n] at h
    exact nonneg_of_mul_nonneg_right h hkd
  have hv (n : ℕ) : 0 ≤ v n := by
    have h := hn.2 n
    rw [hi.2.2.2.2.2 n] at h
    exact nonneg_of_mul_nonneg_right h hkv
  have hdl := squeeze_zero hd (fun n => le_add_of_nonneg_right (hv n)) hl
  have hvl := squeeze_zero hv (fun n => le_add_of_nonneg_left (hd n)) hl
  constructor
  · simpa only [mul_zero] using (hdl.const_mul kd).congr (fun n => (hi.2.2.2.2.1 n).symm)
  · simpa only [mul_zero] using (hvl.const_mul kv).congr (fun n => (hi.2.2.2.2.2 n).symm)

/-- Suppose [Ce is positive](hyp:hCe), [the instrumental-variable model has true conditional density g₀ relative to mu](hyp:hIV), [the range condition holds](hyp:hRange), [the minimum-norm solution belongs to the hypothesis class](hyp:hReal), [the outcome is bounded by B](hyp:hY), and [the candidates attain the empirical minima on the regularization grid](hyp:hMin). For [a positive sample size](hyp:hn), assume [the RDIV comparisons hold on E with constant Ce](hyp:hcomp), [the density complexity radius is nonnegative](hyp:hG), [the hypothesis complexity radius is nonnegative](hyp:hH), [the density radius is at most δ](hyp:hGδ), [the hypothesis radius is at most δ](hyp:hHδ), [the minimum-norm solution is zero](hyp:hz), and [the sample outcome lies in E](hyp:hω). Then [at penalty two both the squared projected error and the squared solution error are at most Ce squared plus twice Ce, multiplied by δ squared](goal). -/
-- @node: rdiv_zero_solution_initial_errors
lemma rdiv_zero_solution_initial_errors {W X Z Ω : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Ω]
    (V : IVWorld W X Z) (P : Measure Ω) (sample : AnalysisSample V P)
    (split : SampleSplit) (mu : Measure X) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (ρ ξ B Ce : ℝ) (δ ν : ℕ → ℝ) (dG dH dr : ℕ → ℝ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hCe : 0 < Ce) (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hReal : H0MemHypothesisClass V) (hY : OutcomeBounded V B)
    (hMin : RDIVMinimaAttained V P sample split mu gHat ρ candidate)
    (n : ℕ) (hn : 0 < n) (E : Set Ω)
    (hcomp : RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν
      dG dH dr candidate n E Ce)
    (hG : 0 ≤ dG n (ξ / 4)) (hH : 0 ≤ dH n (gridConfidence ρ ξ n / 4))
    (hGδ : dG n (ξ / 4) ≤ δ n) (hHδ : dH n (gridConfidence ρ ξ n / 4) ≤ δ n)
    (hz : ZeroSolutionCase V) (ω : Ω) (hω : ω ∈ E) :
    ‖projCondExpOp V (candidate n 2 ω - minNormSolution V)‖ ^ 2 ≤
      (Ce ^ 2 + 2 * Ce) * δ n ^ 2 ∧
    ‖candidate n 2 ω - minNormSolution V‖ ^ 2 ≤
      (Ce ^ 2 + 2 * Ce) * δ n ^ 2 := by
  have hgrid : (2 : ℝ) ∈ regGrid ρ n := by
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), by simp [gridValue]⟩
  have hh := ((hMin n hn 2 hgrid).1 ω).1
  have hopt := ((hMin n hn 2 hgrid).1 ω).2 (minNormSolution V) hReal
  have herr := (abs_le.mp (rdiv_population_empirical_comparison V P sample split
    mu g₀ gHat rHat ρ ξ Ce (δ n) ν dG dH dr candidate n E hCe hcomp hReal
    hG hH hGδ hHδ ω hω _ hh 2 hgrid)).2
  have hp : populationRisk V 2 (candidate n 2 ω) -
      populationRisk V 2 (minNormSolution V) =
      ‖projCondExpOp V (candidate n 2 ω - minNormSolution V)‖ ^ 2 +
        2 * ‖candidate n 2 ω - minNormSolution V‖ ^ 2 := by
    rw [populationRisk, populationRisk,
      rdivPopulationLoss_eq V mu g₀ hIV hRange B hY,
      rdivPopulationLoss_eq V mu g₀ hIV hRange B hY]
    change minNormSolution V = 0 at hz
    simp [hz]
    ring
  rw [hp] at herr
  have hbasic : ‖projCondExpOp V (candidate n 2 ω - minNormSolution V)‖ ^ 2 +
      2 * ‖candidate n 2 ω - minNormSolution V‖ ^ 2 ≤
      (2 * Ce) * (δ n * ‖candidate n 2 ω - minNormSolution V‖ + δ n ^ 2) := by
    linarith only [herr, hopt]
  have hyoung := sq_nonneg (‖candidate n 2 ω - minNormSolution V‖ - Ce * δ n)
  constructor <;> nlinarith only [hbasic, hyoung,
    sq_nonneg ‖candidate n 2 ω - minNormSolution V‖,
    sq_nonneg ‖projCondExpOp V (candidate n 2 ω - minNormSolution V)‖]

end Papers.TsAdaptiveEstimationInference
