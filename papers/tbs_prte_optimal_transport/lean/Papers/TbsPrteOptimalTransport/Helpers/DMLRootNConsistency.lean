module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleNormality
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleSecondMoment
/-! Root-n consistency and consistency of DML estimates from their oracle
normal limit. The full-sample rate differs from the evaluation-half rate by
only the fixed factor sqrt two. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

-- @node: dml_half_sample_rate_identity
/-- [The inverse square root of the full sample size, multiplied by the square root of two, equals the inverse square root of the evaluation sample size](goal), when the evaluation sample contains one more observation than the indexing integer and the full sample is twice as large. -/
lemma dml_half_sample_rate_identity (n : ℕ) :
    Real.sqrt 2 * (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) =
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv_rev]
  field_simp

-- @node: dml_rootn_consistent_of_normal_limit
/-- If [the estimation error multiplied by the square root of the evaluation sample size converges in distribution to a probability law](hyp:hlaw), then [the estimation error is bounded in probability at the inverse-square-root full-sample rate](goal), where the full sample size is twice the evaluation sample size. -/
lemma dml_rootn_consistent_of_normal_limit
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (estimate : ℕ → A → ℝ) (theta : ℝ)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hlaw : Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) * (estimate n a - theta)) atTop Q) :
    Causalean.Stat.IsBigOp (fun n a => estimate n a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ := by
  have ht := hlaw.tightness
  intro δ hδ
  obtain ⟨B, hB, hb⟩ := ht δ hδ
  refine ⟨B * Real.sqrt 2, by positivity, hb.mono ?_⟩
  intro n hn
  apply le_trans (measure_mono ?_) hn
  intro a ha
  change B * 1 ≤ ‖Real.sqrt ((n + 1 : ℕ) : ℝ) * (estimate n a - theta)‖
  change B * Real.sqrt 2 * _ ≤ ‖estimate n a - theta‖ at ha
  rw [mul_assoc, dml_half_sample_rate_identity] at ha
  have hp : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hh := mul_le_mul_of_nonneg_left ha hp.le
  rw [← mul_assoc, mul_comm (Real.sqrt _) B, mul_assoc, mul_inv_cancel₀ hp.ne',
    mul_one] at hh
  simpa only [mul_one, norm_mul, Real.norm_eq_abs, abs_of_pos hp] using hh

-- @node: dml_estimate_consistent_of_normal_limit
/-- If [the estimation error multiplied by the square root of the evaluation sample size converges in distribution to a probability law](hyp:hlaw), then [the estimation error converges to zero in probability](goal). -/
lemma dml_estimate_consistent_of_normal_limit
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (estimate : ℕ → A → ℝ) (theta : ℝ)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hlaw : Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) * (estimate n a - theta)) atTop Q) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => estimate n a - theta) atTop (fun _ _ => 0) := by
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hr := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
  have ht := hlaw.tightness.const_mul_tendsto_zero hr
  have heq : (fun n a => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
      (Real.sqrt ((n + 1 : ℕ) : ℝ) * (estimate n a - theta))) =
      (fun n a => estimate n a - theta) := by
    funext n a
    rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne', one_mul]
  dsimp only [Function.comp_def] at ht
  rw [heq] at ht
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
  intro eps heps
  simpa only [mul_one, sub_zero] using ht eps heps

-- @node: bigOp_transfer_on_recovery
/-- If [the probability of leaving the recovery event tends to zero](hyp:hG), [two random sequences agree on that event at every sample size](hyp:heq), and [the second sequence is bounded in probability at a given rate](hyp:hg), then [the first sequence is bounded in probability at the same rate](goal). -/
lemma bigOp_transfer_on_recovery {A E : Type*} [MeasurableSpace A]
    [SeminormedAddCommGroup E] (μ : Measure A) (G : ℕ → Set A)
    (f g : ℕ → A → E) (rate : ℕ → ℝ)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → f n a = g n a)
    (hg : Causalean.Stat.IsBigOp g rate μ) :
    Causalean.Stat.IsBigOp f rate μ := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨B, hB, hb⟩ := hg (δ / 2) hhalf
  have hbad : ∀ᶠ n in atTop, μ (G n)ᶜ < δ / 2 :=
    (tendsto_order.mp hG).2 (δ / 2) hhalf
  refine ⟨B, hB, ?_⟩
  filter_upwards [hb, hbad] with n hn hGn
  calc
    μ {a | B * rate n ≤ ‖f n a‖} ≤
        μ ({a | B * rate n ≤ ‖g n a‖} ∪ (G n)ᶜ) := by
      apply measure_mono
      intro a ha
      by_cases hm : a ∈ G n
      · left
        change B * rate n ≤ ‖g n a‖
        change B * rate n ≤ ‖f n a‖ at ha
        rwa [heq n a hm] at ha
      · exact Or.inr hm
    _ ≤ μ {a | B * rate n ≤ ‖g n a‖} + μ (G n)ᶜ := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hn hGn.le
    _ = δ := ENNReal.add_halves δ

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_oracle_dml_conclusions
/-- For [fitted-score functions of the training view and one observation at each even sample size](hyp:f), under [an equal split into training and evaluation halves](hyp:hSplit), suppose [the fitted score is represented by a function of the training view and a new observation](hyp:hscore), [this representing function is measurable at each sample size](hyp:hf), and [the reference score is measurable](hyp:hg) and [almost surely bounded by the given constant](hyp:hB). If [each evaluation-row fitted-minus-reference score is square integrable](hyp:hfit), [the population integrated squared score error converges to zero in probability](hyp:hrate), [the reference score has mean equal to the target](hyp:hmean), and [the fitted-minus-reference DML estimate is negligible after multiplication by the square root of the evaluation sample size](hyp:hrem), then [the fitted estimate has the full-sample root-n rate, its evaluation-half-normalized error converges to a centered Gaussian with the reference score's population variance, and its variance estimate converges in probability to that variance](goal). -/
lemma equalHalfSplit_oracle_dml_conclusions
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o, score (2 * (n + 1)) a o =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (truth : Obs X Z → ℝ) (hg : Measurable truth)
    (B : ℝ) (hB : ∀ᵐ o ∂observationLaw M, ‖truth o‖ ≤ B)
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a) -
        truth (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (f n (trainingView M S I₁ (2 * (n + 1)) a, o) - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (hrem : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ o => truth o) (2 * (n + 1)) a))
      atTop (fun _ _ => 0)) :
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ ∧
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  haveI : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hLp : MemLp truth 2 (observationLaw M) :=
    MemLp.of_bound hg.aestronglyMeasurable B hB
  have hrow : ∀ n i, AEMeasurable (fun a => score (2 * (n + 1)) a
      (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) μ := by
    intro n i
    simp only [hscore]
    have ht := equalHalfSplit_measurable_trainingView M μ S I₁ I₂ hSplit
      (2 * (n + 1)) (by omega) ⟨n + 1, by omega⟩
    have he := (equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).2.2.1 i
    fun_prop
  have hlaw := equalHalfSplit_fitted_oracle_dmlRV_clt M μ S I₁ I₂ hSplit
    truth hLp theta hmean score hrow hrem
  have hb := dml_estimate_consistent_of_normal_limit μ
    (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a) theta _ hlaw
  refine ⟨dml_rootn_consistent_of_normal_limit μ _ theta _ hlaw, hlaw, ?_⟩
  exact equalHalfSplit_varianceRV_consistent_of_bounded_truth M μ S I₁ I₂ hSplit
    score f hscore hf truth hg B hB hfit hrate theta hb

-- Exact recovery transfers all three conclusions, even though the feasible
-- score may depend on evaluation covariates through its recovered labels.
-- @node: dml_conclusions_transfer_on_recovery
/-- Suppose [the recovery events have probabilities tending to one](hyp:hG), [the feasible and oracle scores agree on every evaluation observation on those events](hyp:heq), and [the normalized feasible estimation error is almost everywhere measurable](hyp:hf). If the oracle estimate [has the inverse-square-root full-sample rate](hyp:hr), [has an evaluation-half-normalized centered Gaussian limit with the specified variance](hyp:hlaw), and [has a variance estimate converging in probability to that variance](hyp:hvar), then [the feasible estimate and its variance estimate satisfy all three of these conclusions](goal). -/
lemma dml_conclusions_transfer_on_recovery
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (feasible oracle : ℕ → A → Obs X Z → ℝ)
    (G : ℕ → Set A) (theta sigmaSq : ℝ)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (2 * (n + 1)) a,
      feasible (2 * (n + 1)) a (S.Z i a) = oracle (2 * (n + 1)) a (S.Z i a))
    (hf : ∀ n, AEMeasurable
      (fun a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)) μ)
    (hr : Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ oracle (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ)
    (hlaw : Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ oracle (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal sigmaSq)))
    (hvar : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ oracle (2 * (n + 1)) a)
      atTop (fun _ _ => sigmaSq)) :
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ ∧
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal sigmaSq)) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ feasible (2 * (n + 1)) a)
      atTop (fun _ _ => sigmaSq) := by
  refine ⟨bigOp_transfer_on_recovery μ G _ _ _ hG ?_ hr, ?_⟩
  · intro n a ha
    rw [dmlRV_eq_of_score_eq_on_sample M S I₂ feasible oracle
      (2 * (n + 1)) a (heq n a ha)]
  · exact dml_statistics_transfer_on_recovery M S I₂ feasible oracle
      (fun n => 2 * (n + 1)) G (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ))
      theta sigmaSq _ hG heq hf hlaw hvar

-- The oracle CLT, remainder argument, and second-moment LLN are proved by
-- the oracle assembly; only equality on the recovery event is used here.
-- @node: equalHalfSplit_feasible_dml_conclusions
/-- For [oracle-score functions of the training view and one observation at each even sample size](hyp:f), under [an equal training/evaluation half split](hyp:hSplit), suppose [the oracle score is a function of the training view and a new observation](hyp:hscore), [that function is measurable](hyp:hf), and [the reference score is measurable](hyp:hg) and [almost surely bounded by the given constant](hyp:hB). Assume [square integrability of each evaluation-row oracle-minus-reference score](hyp:hfit), [population integrated squared score error tending to zero in probability](hyp:hrate), [reference score mean equal to the target](hyp:hmean), [a root-evaluation-sample negligible oracle-minus-reference DML remainder](hyp:hrem), [recovery events with probabilities tending to one](hyp:hG), [feasible and oracle scores agreeing on evaluation observations on recovery](hyp:heq), and [almost everywhere measurable feasible evaluation scores](hyp:hrow); then [the feasible estimate has the full-sample root-n rate and an evaluation-half-normalized centered Gaussian limit with the reference score's population variance, and its variance estimate is consistent for that variance](goal). -/
lemma equalHalfSplit_feasible_dml_conclusions
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o, score (2 * (n + 1)) a o =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (truth : Obs X Z → ℝ) (hg : Measurable truth)
    (B : ℝ) (hB : ∀ᵐ o ∂observationLaw M, ‖truth o‖ ≤ B)
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a) -
        truth (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (f n (trainingView M S I₁ (2 * (n + 1)) a, o) - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (hrem : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ o => truth o) (2 * (n + 1)) a))
      atTop (fun _ _ => 0))
    (feasible : ℕ → A → Obs X Z → ℝ) (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (2 * (n + 1)) a,
      feasible (2 * (n + 1)) a (S.Z i a) = score (2 * (n + 1)) a (S.Z i a))
    (hrow : ∀ n i, AEMeasurable (fun a => feasible (2 * (n + 1)) a
      (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) μ) :
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ ∧
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ feasible (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have ho := equalHalfSplit_oracle_dml_conclusions M μ S I₁ I₂ hSplit
    score f hscore hf truth hg B hB hfit hrate theta hmean hrem
  have hm := equalHalfSplit_dmlRV_aemeasurable_of_evaluation_rows M μ S I₁ I₂
    hSplit feasible hrow
  exact dml_conclusions_transfer_on_recovery M μ S I₂ feasible score G theta
    (populationVariance M truth theta) hG heq
    (fun n => ((hm n).sub_const theta).const_mul _) ho.1 ho.2.1 ho.2.2

end Papers.TbsPrteOptimalTransport
