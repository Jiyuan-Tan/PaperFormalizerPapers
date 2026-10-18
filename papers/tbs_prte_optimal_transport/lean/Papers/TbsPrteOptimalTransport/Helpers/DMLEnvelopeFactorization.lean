module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTrainingFactorization
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIntegrableEvaluationLLN
/-! Training-score factorization with an observation-dependent L² envelope.
The fitted scores need only grow within one square-integrable envelope. Clipping
the measurable factor off the training image preserves the actual scores and
supplies both population-section and random evaluation-row second moments.
This avoids requiring bounded scores at observations outside the outcome support. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Topology

-- @node: envelope_training_predictor_factorization
/-- If [a score is jointly measurable using only the training view and the observation](hyp:hm),
[its envelope is measurable](hyp:he), [nonnegative](hyp:hepos), and
[bounds the absolute score everywhere](hyp:hbound), then [the score factors through a
jointly measurable function of the training view and observation that obeys the same
envelope bound at every possible training view](goal). -/
lemma envelope_training_predictor_factorization
    {A T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
    (view : A → T) (score : A → B → ℝ)
    (hm : Measurable[(MeasurableSpace.comap view inferInstance).prod inferInstance]
      (Function.uncurry score))
    (envelope : B → ℝ) (he : Measurable envelope)
    (hepos : ∀ b, 0 ≤ envelope b)
    (hbound : ∀ a b, |score a b| ≤ envelope b) :
    ∃ f : T × B → ℝ, Measurable f ∧
      (∀ t b, |f (t, b)| ≤ envelope b) ∧
      ∀ a b, score a b = f (view a, b) := by
  obtain ⟨g, hg, heq⟩ := measurable_training_predictor_factorization view score hm
  refine ⟨fun tb => max (-envelope tb.2) (min (envelope tb.2) (g tb.1 tb.2)),
    ?_, ?_, ?_⟩
  · fun_prop
  · intro t b
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith [hepos b]) (min_le_left _ _)⟩
  · intro a b
    dsimp only
    rw [← heq a b]
    have hab := abs_le.mp (hbound a b)
    rw [min_eq_right hab.2, max_eq_right hab.1]

-- @node: envelope_training_factor_sections_and_rows_memLp
/-- If [a function of the training view and observation is jointly measurable](hyp:hm),
[the training view is measurable](hyp:hv), [the evaluation row has the observation
law](hyp:hr), and [a square-integrable envelope](hyp:hLp) [bounds the function at
every training view and observation](hyp:hbound), then [every population section
and the random evaluation row are square-integrable](goal). -/
lemma envelope_training_factor_sections_and_rows_memLp
    {A T B : Type*} [MeasurableSpace A] [MeasurableSpace T] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B)
    (view : A → T) (row : A → B) (f : T × B → ℝ)
    (hm : Measurable f) (hv : Measurable view)
    (hr : MeasurePreserving row μ ν)
    (envelope : B → ℝ) (hLp : MemLp envelope 2 ν)
    (hbound : ∀ t b, |f (t, b)| ≤ envelope b) :
    (∀ t, MemLp (fun b => f (t, b)) 2 ν) ∧
      MemLp (fun a => f (view a, row a)) 2 μ := by
  constructor
  · intro t
    have hs : Measurable (fun b => f (t, b)) := by fun_prop
    exact hLp.mono' hs.aestronglyMeasurable
      (Eventually.of_forall fun b => by
        simpa only [Real.norm_eq_abs] using hbound t b)
  · have hs : Measurable (fun a => f (view a, row a)) := by
      have hrow := hr.measurable
      fun_prop
    exact (hLp.comp_measurePreserving hr).mono' hs.aestronglyMeasurable
      (Eventually.of_forall fun a => by
        simpa only [Real.norm_eq_abs, Function.comp_apply] using hbound (view a) (row a))

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_envelope_training_score_factorization
/-- Under [an equal half split](hyp:hSplit), if [the scores are jointly measurable
from training information and the observation](hyp:hm) and [a measurable](hyp:he),
[nonnegative](hyp:hepos), [square-integrable envelope](hyp:hLp)
[bounds every fitted score in absolute value](hyp:hbound), then [at each even sample
size the score factors through a measurable function of the training view and
observation, with square-integrable population sections and evaluation rows](goal). -/
lemma equalHalfSplit_envelope_training_score_factorization
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ)
    (hm : TrainingPredictorMeasurable M S I₁ score)
    (envelope : Obs X Z → ℝ) (he : Measurable envelope)
    (hepos : ∀ o, 0 ≤ envelope o)
    (hLp : MemLp envelope 2 (observationLaw M))
    (hbound : ∀ n a o, |score n a o| ≤ envelope o) :
    ∃ f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) ×
        Obs X Z → ℝ,
      (∀ n a o, score (2 * (n + 1)) a o =
        f n (trainingView M S I₁ (2 * (n + 1)) a, o)) ∧
      (∀ n, Measurable (f n)) ∧
      (∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M)) ∧
      (∀ n i, MemLp (fun a => f n
        (trainingView M S I₁ (2 * (n + 1)) a,
          S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) := by
  have hex (n : ℕ) := envelope_training_predictor_factorization
    (trainingView M S I₁ (2 * (n + 1))) (score (2 * (n + 1)))
    (hm (2 * (n + 1))) envelope he hepos (hbound (2 * (n + 1)))
  choose f hf hb heq using hex
  refine ⟨f, heq, hf, ?_, ?_⟩
  · intro n t
    have hs : Measurable (fun o => f n (t, o)) := by fun_prop
    exact hLp.mono' hs.aestronglyMeasurable
      (Eventually.of_forall fun o => by
        simpa only [Real.norm_eq_abs] using hb n t o)
  · intro n i
    have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n
    exact (envelope_training_factor_sections_and_rows_memLp μ (observationLaw M)
      _ _ (f n) (hf n) hl.2.1
      ⟨hl.2.2.1 i, (hl.2.2.2.1 i).2⟩ envelope hLp (hb n)).2

-- @node: equalHalfSplit_envelope_training_oracle_mean_variance_consistent
/-- Under [an equal half split](hyp:hSplit), suppose [the oracle score has mean
theta](hyp:hmean) and [a finite second moment](hyp:htruth), and [the fitted score
error is measurable from training information and the observation](hyp:hm).
If [a measurable](hyp:he), [nonnegative](hyp:hepos), [square-integrable
envelope](hyp:hLp) [bounds that error everywhere](hyp:hbound) and [its population
mean squared error converges to zero in probability along even sample sizes](hyp:hrate),
then [the evaluation-half score mean converges in probability to theta and its
variance estimate converges in probability to the oracle population variance](goal). -/
lemma equalHalfSplit_envelope_training_oracle_mean_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (htruth : MemLp truth 2 (observationLaw M))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (envelope : Obs X Z → ℝ) (he : Measurable envelope)
    (hepos : ∀ o, 0 ≤ envelope o)
    (hLp : MemLp envelope 2 (observationLaw M))
    (hbound : ∀ n a o, |score n a o - truth o| ≤ envelope o)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  let : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  obtain ⟨f, heq, hf, hsection, hfit⟩ :=
    equalHalfSplit_envelope_training_score_factorization M μ S I₁ I₂ hSplit
      (fun n a o => score n a o - truth o) hm envelope he hepos hLp hbound
  have hrate' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [← heq] using hrate
  have hE := equalHalfSplit_empirical_fitted_score_energy M μ S I₁ I₂
    hSplit f hf hfit hrate'
  simp only [← heq] at hE
  exact ⟨equalHalfSplit_dmlRV_consistent_of_empirical_score_error M μ S I₁ I₂
      hSplit score truth (htruth.integrable (by norm_num)) theta hmean hE,
    equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp M μ S I₁ I₂
      hSplit score truth htruth theta hmean hE⟩

-- @node: equalHalfSplit_envelope_training_oracle_remainder_negligible
/-- Under [an equal half split](hyp:hSplit), suppose [the fitted score error is
measurable from training information and the observation](hyp:hm) and
[a measurable](hyp:he), [nonnegative](hyp:hepos), [square-integrable envelope](hyp:hLp)
[bounds it everywhere](hyp:hbound). If [its population mean squared error tends
to zero in probability](hyp:hrate) and [its population mean multiplied by the
square root of the evaluation-half size tends to zero in probability](hyp:hbias),
then [the difference between fitted and oracle evaluation-half score averages,
multiplied by the same square root, tends to zero in probability](goal). -/
lemma equalHalfSplit_envelope_training_oracle_remainder_negligible
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (envelope : Obs X Z → ℝ) (he : Measurable envelope)
    (hepos : ∀ o, 0 ≤ envelope o)
    (hLp : MemLp envelope 2 (observationLaw M))
    (hbound : ∀ n a o, |score n a o - truth o| ≤ envelope o)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (hbias : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ o, score (2 * (n + 1)) a o - truth o ∂observationLaw M))
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a))
      atTop (fun _ _ => 0) := by
  obtain ⟨f, heq, hf, hsection, hfit⟩ :=
    equalHalfSplit_envelope_training_score_factorization M μ S I₁ I₂ hSplit
      (fun n a o => score n a o - truth o) hm envelope he hepos hLp hbound
  apply equalHalfSplit_oracle_score_remainder_negligible M μ S I₁ I₂ hSplit
    score truth f heq hf hsection hfit
  · simpa only [← heq] using hrate
  · simpa only [← heq] using hbias

end Papers.TbsPrteOptimalTransport
