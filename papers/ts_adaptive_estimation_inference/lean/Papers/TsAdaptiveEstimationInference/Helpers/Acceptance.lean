module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAE
/-! Bounded fitting samples and the terminal discrepancy test. -/
public section
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- Under [the TRAE boundedness conditions with envelope B](hyp:hb) and
[population envelope bounds holding outside one common null set](hyp:hCommon),
[there is a measurable event of probability one on which every primal hypothesis
is bounded in absolute value by B at every sampled observation](goal). -/
-- @node: trae_sample_bounded_event
lemma trae_sample_bounded_event (B : ℝ) (hb : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ᵐ ω ∂P, ω ∈ S) ∧
      ∀ ω ∈ S, ∀ i, ∀ h ∈ V.H,
        |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B := by
  have hi : ∀ i, ∀ᵐ ω ∂P, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B := by
    intro i
    exact ae_of_ae_map (μ := P)
      (p := fun w => ∀ h ∈ V.H, |primalVersion V h (V.xOf w)| ≤ B)
      (sample.meas i).aemeasurable (by rw [sample.map_eq i]; exact hCommon.mono (fun _ hw => hw.1))
  have hall := ae_all_iff.mpr hi
  let bad := {ω | ¬ ∀ i, ∀ h ∈ V.H,
    |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B}
  have hbad : P bad = 0 := by exact hall
  refine ⟨(toMeasurable P bad)ᶜ, (measurableSet_toMeasurable P bad).compl, ?_, ?_⟩
  · rw [ae_iff]
    simpa only [Set.mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable] using hbad
  · intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P bad h)

/-- If [B is nonnegative](hyp:hB), [the fitting sample size is positive](hyp:hn),
and [the first hypothesis is bounded in absolute value by B at every sampled
observation](hyp:hh) and [the second hypothesis has the same bound](hyp:hh'),
then [their empirical squared
fitting distance is at most four times B squared](goal). -/
-- @node: primalEmpDistanceSq_le_four
lemma primalEmpDistanceSq_le_four (B : ℝ) (hB : 0 ≤ B) (n : ℕ) (hn : 0 < n)
    (ω : Ω) (h h' : V.Hbar.toSubmodule)
    (hh : ∀ i, |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B)
    (hh' : ∀ i, |primalVersion V h' (V.xOf (sample.Z i ω))| ≤ B) :
    primalEmpDistanceSq V P sample split n ω h h' ≤ 4 * B ^ 2 := by
  unfold primalEmpDistanceSq blockAverage
  rw [split.card_fit]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (inv_mul_le_iff₀ hn').2
  calc
    _ ≤ ∑ _i ∈ split.fit n, (4 * B ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have ha := abs_le.mp (hh i)
      have hb := abs_le.mp (hh' i)
      nlinarith [sq_nonneg (2 * B -
        (primalVersion V h (V.xOf (sample.Z i ω)) -
          primalVersion V h' (V.xOf (sample.Z i ω)))),
        sq_nonneg (2 * B + (primalVersion V h (V.xOf (sample.Z i ω)) -
          primalVersion V h' (V.xOf (sample.Z i ω))))]
    _ = _ := by simp [split.card_fit]

/-- [The empirical squared fitting distance between any two primal hypotheses
is nonnegative](goal). -/
-- @node: primalEmpDistanceSq_nonneg
lemma primalEmpDistanceSq_nonneg (n : ℕ) (ω : Ω) (h h' : V.Hbar.toSubmodule) :
    0 ≤ primalEmpDistanceSq V P sample split n ω h h' := by
  unfold primalEmpDistanceSq blockAverage
  positivity

/-- If [the base accuracy scale dominates the allocated radius and the inverse
square-root sample-size floor and tends to zero](hyp:hscale), [the public bounds
are valid calibrated inflations of the base bounds](hyp:hinflate), and [the sample
size is positive](hyp:hn), then [the squared public accuracy scale is at least
the reciprocal sample size](goal). -/
-- @node: trae_calibrated_square_floor
lemma trae_calibrated_square_floor (baseδ δ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (allocation : ℕ → ℝ) (ν baseν : ℕ → ℝ) (κδ κν required : ℝ)
    (hscale : TRAEScaleCalibration baseδ tildeδ allocation)
    (hinflate : CalibratedValidBounds δ ν baseδ baseν κδ κν required)
    (n : ℕ) (hn : 0 < n) : 1 / (n : ℝ) ≤ δ n ^ 2 := by
  have hf := (le_max_right _ _).trans (hscale.1 n hn)
  have hb : 0 ≤ baseδ n := (Real.rpow_nonneg (by positivity) _).trans hf
  have hd : baseδ n ≤ δ n := by
    rw [hinflate.2.2.2.2.1 n]
    nlinarith [hinflate.1]
  have hs := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ))
    (-(1 / 2 : ℝ))) (hf.trans hd) 2
  have heq : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ))]
    norm_num [Real.rpow_neg_one]
  rwa [heq] at hs

/-- If [M is nonnegative](hyp:hM), [n is positive](hyp:hn), [n is at least twice
M](hyp:hsize), [the regularization penalty is at most the reciprocal of n
squared](hyp:hlam), and [d is at least the reciprocal of n](hyp:hd), then
[the penalty times M is at most half of d](goal). -/
-- @node: terminal_remainder_le_half
lemma terminal_remainder_le_half (M lam d : ℝ) (n : ℕ) (hM : 0 ≤ M)
    (hn : 0 < n) (hsize : 2 * M ≤ n) (hlam : lam ≤ 1 / (n : ℝ) ^ 2)
    (hd : 1 / (n : ℝ) ≤ d) : lam * M ≤ 1 / 2 * d := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hm : M / (n : ℝ) ^ 2 ≤ 1 / 2 * (1 / (n : ℝ)) := by
    apply (div_le_iff₀ (sq_pos_of_pos hn')).2
    field_simp
    nlinarith
  calc
    lam * M ≤ M / (n : ℝ) ^ 2 := by
      simpa [div_eq_mul_inv, mul_comm] using (mul_le_mul_of_nonneg_right hlam hM)
    _ ≤ 1 / 2 * d := hm.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
end Papers.TsAdaptiveEstimationInference
