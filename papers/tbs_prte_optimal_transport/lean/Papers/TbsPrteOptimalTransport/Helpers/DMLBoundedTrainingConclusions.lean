module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTrainingFactorization
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIntegrableEvaluationLLN
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTargetConclusions
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRootNConsistency
/-! Oracle and feasible DML conclusions from bounded training-dependent score
differences. The training factor and its integrability are constructed here;
population scores need only the measurable versions supplied by `MemLp`.
Variance consistency uses the integrable squared-score LLN independently of
normality, so no fourth moment of the population score is required. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_bounded_training_empirical_score_error
/-- With [equal training and evaluation halves](hyp:hSplit), suppose [the
fitted score error is measurable from training data and the observation](hyp:hm),
[its absolute bound is nonnegative](hyp:hb), [that bound holds at every observation
and training realization](hyp:hbound), and [its population mean squared error
tends to zero in probability along even sample sizes](hyp:hrate). Then [the
average squared score error on the evaluation half tends to zero in probability](goal). -/
lemma equalHalfSplit_bounded_training_empirical_score_error
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (bound : ℝ) (hb : 0 ≤ bound)
    (hbound : ∀ n a o, |score n a o - truth o| ≤ bound)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (score (2 * (n + 1)) a (S.Z i a) - truth (S.Z i a)) ^ 2)
      atTop (fun _ _ => 0) := by
  obtain ⟨f, heq, hf, hsection, hfit⟩ :=
    equalHalfSplit_bounded_training_score_factorization M μ S I₁ I₂ hSplit
      (fun n a o => score n a o - truth o) hm bound hb hbound
  have hrate' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [← heq] using hrate
  have hE := equalHalfSplit_empirical_fitted_score_energy M μ S I₁ I₂
    hSplit f hf hfit hrate'
  simpa only [← heq] using hE

-- @node: equalHalfSplit_bounded_training_oracle_mean_variance_consistent
/-- With [equal training and evaluation halves](hyp:hSplit), assume [the
population score has the target mean](hyp:hmean) and [a finite second moment](hyp:hLp),
while [the fitted score error is measurable from training data and the
observation](hyp:hm), [its absolute bound is nonnegative](hyp:hb), [the bound
holds everywhere](hyp:hbound), and [its population mean squared error vanishes
in probability along even sample sizes](hyp:hrate). Then [the held-out score
mean converges in probability to the target and its empirical variance converges
to the population score variance](goal). -/
lemma equalHalfSplit_bounded_training_oracle_mean_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (hLp : MemLp truth 2 (observationLaw M))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (bound : ℝ) (hb : 0 ≤ bound)
    (hbound : ∀ n a o, |score n a o - truth o| ≤ bound)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hE := equalHalfSplit_bounded_training_empirical_score_error M μ S I₁ I₂
    hSplit score truth hm bound hb hbound hrate
  exact ⟨equalHalfSplit_dmlRV_consistent_of_empirical_score_error M μ S I₁ I₂
      hSplit score truth (hLp.integrable (by norm_num)) theta hmean hE,
    equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp M μ S I₁ I₂
      hSplit score truth hLp theta hmean hE⟩

-- @node: equalHalfSplit_bounded_training_feasible_mean_variance_consistent
/-- Under [equal training and evaluation halves](hyp:hSplit), assume [the
population score has the target mean](hyp:hmean) and [a finite second moment](hyp:hLp),
and [the oracle score error is measurable from training data and the
observation](hyp:hm), [has a nonnegative absolute bound](hyp:hb), [obeys that
bound everywhere](hyp:hbound), and [vanishes in population mean square in
probability along even sample sizes](hyp:hrate). If [recovery events have
probability tending to one](hyp:hG) and [feasible and oracle scores agree on all
evaluation rows on these events](hyp:heq), [the feasible score mean and empirical
variance converge in probability to the target and population score variance,
respectively](goal). -/
lemma equalHalfSplit_bounded_training_feasible_mean_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (hLp : MemLp truth 2 (observationLaw M))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (bound : ℝ) (hb : 0 ≤ bound)
    (hbound : ∀ n a o, |score n a o - truth o| ≤ bound)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (feasible : ℕ → A → Obs X Z → ℝ) (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (2 * (n + 1)) a,
      feasible (2 * (n + 1)) a (S.Z i a) = score (2 * (n + 1)) a (S.Z i a)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ feasible (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have ho := equalHalfSplit_bounded_training_oracle_mean_variance_consistent
    M μ S I₁ I₂ hSplit score truth theta hmean hLp hm bound hb hbound hrate
  exact dml_mean_variance_transfer_on_recovery M S I₂ feasible score
    (fun n => 2 * (n + 1)) G theta (populationVariance M truth theta)
    hG heq ho.1 ho.2


-- @node: equalHalfSplit_bounded_training_oracle_dml_conclusions
/-- With [equal training and evaluation halves](hyp:hSplit), assume [the
population score has the target mean](hyp:hmean) and [a finite second moment](hyp:hLp),
and [the fitted score error is measurable from training data and the
observation](hyp:hm), [has a nonnegative absolute bound](hyp:hb), [satisfies that
bound everywhere](hyp:hbound), [has population mean squared error tending to
zero in probability along even sample sizes](hyp:hrate), and [has population
bias negligible after multiplication by the square root of the evaluation sample
size](hyp:hbias). Then [the held-out score estimator has error of order the
inverse square root of total sample size in probability, its error scaled by the
square root of evaluation sample size converges in distribution to a centered
normal with the population score variance, and its empirical variance is
consistent for that variance](goal). -/
lemma equalHalfSplit_bounded_training_oracle_dml_conclusions
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (hLp : MemLp truth 2 (observationLaw M))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (bound : ℝ) (hb : 0 ≤ bound)
    (hbound : ∀ n a o, |score n a o - truth o| ≤ bound)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (hbias : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ o, score (2 * (n + 1)) a o - truth o ∂observationLaw M))
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
  obtain ⟨f, heq, hf, hsection, hfit⟩ :=
    equalHalfSplit_bounded_training_score_factorization M μ S I₁ I₂ hSplit
      (fun n a o => score n a o - truth o) hm bound hb hbound
  have hrate' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [← heq] using hrate
  have hbias' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M))
      atTop (fun _ _ => 0) := by
    simpa only [← heq] using hbias
  have hrem := equalHalfSplit_oracle_score_remainder_negligible M μ S I₁ I₂
    hSplit score truth f heq hf hsection hfit hrate' hbias'
  have hrow : ∀ n i, AEMeasurable (fun a => score (2 * (n + 1)) a
      (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) μ := by
    intro n i
    have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n
    have hp : MemLp truth 2 (μ.map
        (fun a => S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) := by
      rw [(hl.2.2.2.1 i).2]
      exact hLp
    have ht := hp.comp_of_map (hl.2.2.1 i).aemeasurable
    have hr := (hfit n i).add ht
    convert hr.aestronglyMeasurable.aemeasurable using 1
    funext a
    rw [Pi.add_apply, ← heq]
    simp only [Function.comp_apply]
    ring
  have hlaw := equalHalfSplit_fitted_oracle_dmlRV_clt M μ S I₁ I₂ hSplit
    truth hLp theta hmean score hrow hrem
  refine ⟨dml_rootn_consistent_of_normal_limit μ _ theta _ hlaw, hlaw, ?_⟩
  exact (equalHalfSplit_bounded_training_oracle_mean_variance_consistent
    M μ S I₁ I₂ hSplit score truth theta hmean hLp hm bound hb hbound hrate).2

-- @node: equalHalfSplit_bounded_training_feasible_dml_conclusions
/-- With [equal training and evaluation halves](hyp:hSplit), assume [the
population score has the target mean](hyp:hmean) and [a finite second moment](hyp:hLp),
and [the oracle score error is measurable from training data and the
observation](hyp:hm), [has a nonnegative absolute bound](hyp:hb), [obeys that
bound everywhere](hyp:hbound), [has population mean squared error vanishing in
probability along even sample sizes](hyp:hrate), and [has bias negligible at
the square root of evaluation sample size scale](hyp:hbias). If [recovery
events have probability tending to one](hyp:hG), [feasible and oracle scores
agree on evaluation rows on those events](hyp:heq), and [each feasible
evaluation-row score is almost everywhere measurable](hyp:hrow), [the feasible
estimator has error of inverse square root order in total sample size in
probability, its error scaled by the square root of evaluation sample size has
a centered normal limit with population score variance, and its empirical
variance consistently estimates that variance](goal). -/
lemma equalHalfSplit_bounded_training_feasible_dml_conclusions
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (hLp : MemLp truth 2 (observationLaw M))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (bound : ℝ) (hb : 0 ≤ bound)
    (hbound : ∀ n a o, |score n a o - truth o| ≤ bound)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (hbias : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ o, score (2 * (n + 1)) a o - truth o ∂observationLaw M))
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
  have ho := equalHalfSplit_bounded_training_oracle_dml_conclusions M μ S I₁ I₂
    hSplit score truth theta hmean hLp hm bound hb hbound hrate hbias
  have hmstat := equalHalfSplit_dmlRV_aemeasurable_of_evaluation_rows M μ S I₁ I₂
    hSplit feasible hrow
  exact dml_conclusions_transfer_on_recovery M μ S I₂ feasible score G theta
    (populationVariance M truth theta) hG heq
    (fun n => ((hmstat n).sub_const theta).const_mul _) ho.1 ho.2.1 ho.2.2

end Papers.TbsPrteOptimalTransport
