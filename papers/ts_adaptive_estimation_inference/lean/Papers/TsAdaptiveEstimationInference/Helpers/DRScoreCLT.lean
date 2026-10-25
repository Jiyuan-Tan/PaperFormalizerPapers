module
public import Papers.TsAdaptiveEstimationInference.Helpers.DoublyRobust
public import Causalean.Stat.SampleSplit.PartialFoldCLT
/-! The central limit theorem for the evaluation-block population score. -/
public section
set_option linter.unusedSectionVars false

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵)
variable (hTarget : Continuous V.targetFunctional)
variable (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- [The centered population score is a measurable function of the
observation](goal). -/
-- @node: centeredScore_measurable
@[fun_prop] lemma centeredScore_measurable : Measurable (centeredScore V hTarget) := by
  unfold centeredScore
  exact (((V.measurable_mt _).add (V.measurable_m _)).sub
    (((V.primal_measurable _).comp V.measurable_x).mul
      ((V.dual_measurable _).comp V.measurable_z))).sub_const _

/-- [The evaluation-block average of any real-valued function, multiplied by
the square root of the block size, equals the sum of its evaluated values
divided by that square root](goal). -/
-- @node: dr_eval_normalized_sum
lemma dr_eval_normalized_sum (f : 𝒲 → ℝ) (n : ℕ) (ω : Ω) :
    Real.sqrt n * blockAverage V P sample (split.eval n) f ω =
      (Real.sqrt n)⁻¹ * ∑ i ∈ split.eval n, f (sample.Z i ω) := by
  unfold blockAverage
  rw [split.card_eval, ← mul_assoc]
  congr 1
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    apply (mul_right_cancel₀ hspos.ne')
    rw [inv_mul_cancel₀ hspos.ne']
    calc
      _ = (Real.sqrt n) ^ 2 * (n : ℝ)⁻¹ := by ring
      _ = 1 := by rw [Real.sq_sqrt hnpos.le, mul_inv_cancel₀ hnpos.ne']

/-- Under [the primal range condition](hyp:hRange) and [the dual range
condition](hyp:hDualRange),
if [the population score is square integrable with strictly positive
variance](hyp:hVariance), then [the evaluation-block average of the centered
population score, multiplied by the square root of sample size, converges in
distribution to a mean-zero Gaussian with the population score variance](goal). -/
-- @node: centeredScore_eval_clt
lemma centeredScore_eval_clt (hRange : RangeCondition V)
    (hDualRange : RangeCondition (dualWorld V hTarget))
    (hVariance : ScoreVariancePositive V hTarget) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n *
        blockAverage V P sample (split.eval n) (centeredScore V hTarget) ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (scoreVariance V hTarget))) := by
  let full := Causalean.Stat.IsAsymLinear.normalizedSum sample (centeredScore V hTarget)
    (fun n => Finset.range n)
  let evalSum := fun (n : ℕ) (ω : Ω) => Real.sqrt n *
    blockAverage V P sample (split.eval n) (centeredScore V hTarget) ω
  have hmeas : ∀ n, AEMeasurable (evalSum n) P := by
    intro n
    have heq : evalSum n = fun ω => (Real.sqrt n)⁻¹ *
        ∑ i ∈ split.eval n, centeredScore V hTarget (sample.Z i ω) := by
      funext ω
      exact dr_eval_normalized_sum V P sample split _ n ω
    rw [heq]
    exact ((Finset.measurable_sum _ (fun i _ =>
      (centeredScore_measurable V hTarget).comp (sample.meas i))).const_mul _).aemeasurable
  have hfull := sample.clt_normalized_sum (centeredScore_measurable V hTarget)
    (centeredScore_mean_zero V hTarget hRange hDualRange) hVariance.1.integrable_sq
  change TendstoInDistribution full atTop (id : ℝ → ℝ) (fun _ => P)
    (gaussianReal 0 (Real.toNNReal (scoreVariance V hTarget))) at hfull
  have hlaw : ∀ n, P.map (evalSum n) = P.map (full n) := by
    intro n
    let : IsProbabilityMeasure (P.map (evalSum n)) := Measure.isProbabilityMeasure_map (hmeas n)
    let : IsProbabilityMeasure (P.map (full n)) :=
      Measure.isProbabilityMeasure_map (hfull.forall_aemeasurable n)
    apply Measure.ext_of_charFun
    funext t
    have hcf := sample.charFun_normalizedSum_finset_eq_range_card
      (centeredScore_measurable V hTarget) (split.eval n) t
    have hfull_eq : full n = fun ω => (Real.sqrt n)⁻¹ *
        ∑ i ∈ Finset.range n, centeredScore V hTarget (sample.Z i ω) := by
      simp only [full, Causalean.Stat.IsAsymLinear.normalizedSum_def, Finset.card_range]
    rw [hfull_eq]
    simpa only [evalSum, split.card_eval, ← dr_eval_normalized_sum] using hcf
  refine ⟨hmeas, hfull.aemeasurable_limit, ?_⟩
  apply Filter.Tendsto.congr' ?_ hfull.tendsto
  exact Filter.Eventually.of_forall fun n => (Subtype.ext (hlaw n)).symm

end Papers.TsAdaptiveEstimationInference
