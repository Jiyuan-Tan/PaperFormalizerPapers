module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleRemainder
public import Papers.TbsPrteOptimalTransport.Helpers.PluginSplitMoment
/-! Measurable factorization of bounded training-dependent score functions.
Clipping the factor off the image of the training view gives bounded sections
without changing any score on that image. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Topology

-- @node: bounded_training_factor_sections_and_rows_memLp
/-- If [a training-and-observation score factor is measurable](hyp:hm), [the training view is measurable](hyp:hv), [the selected observation is measurable](hyp:hr), and [the factor is uniformly bounded in absolute value](hyp:hb), [every fixed-training section has a finite second moment under the finite observation measure, and the score evaluated at the training view and selected observation has a finite second moment under the finite sample measure](goal). -/
lemma bounded_training_factor_sections_and_rows_memLp
    {A T B : Type*} [MeasurableSpace A] [MeasurableSpace T] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (view : A → T) (row : A → B) (f : T × B → ℝ)
    (hm : Measurable f) (hv : Measurable view) (hr : Measurable row)
    (bound : ℝ) (hb : ∀ t b, |f (t, b)| ≤ bound) :
    (∀ t, MemLp (fun b => f (t, b)) 2 ν) ∧
      MemLp (fun a => f (view a, row a)) 2 μ := by
  constructor
  · intro t
    have hs : Measurable (fun b => f (t, b)) := by
      fun_prop
    exact MemLp.of_bound hs.aestronglyMeasurable bound
      (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hb t b)
  · have hs : Measurable (fun a => f (view a, row a)) := by
      fun_prop
    exact MemLp.of_bound hs.aestronglyMeasurable bound
      (Eventually.of_forall fun a => by
        simpa only [Real.norm_eq_abs] using hb (view a) (row a))

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_bounded_training_score_factorization
/-- Given [an equal half split](hyp:hSplit), [a score measurable with respect to the training information and a new observation](hyp:hm), [a nonnegative bound](hyp:hb), and [a uniform absolute score bound by that constant](hyp:hbound), [there exists a factor through the training view that reproduces the score at every even sample size, is measurable, has square-integrable sections for every training view, and is square-integrable when evaluated at each evaluation observation](goal). -/
lemma equalHalfSplit_bounded_training_score_factorization
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ)
    (hm : TrainingPredictorMeasurable M S I₁ score)
    (bound : ℝ) (hb : 0 ≤ bound)
    (hbound : ∀ n a o, |score n a o| ≤ bound) :
    ∃ f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) ×
        Obs X Z → ℝ,
      (∀ n a o, score (2 * (n + 1)) a o =
        f n (trainingView M S I₁ (2 * (n + 1)) a, o)) ∧
      (∀ n, Measurable (f n)) ∧
      (∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M)) ∧
      (∀ n i, MemLp (fun a => f n
        (trainingView M S I₁ (2 * (n + 1)) a,
          S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) := by
  have hex (n : ℕ) := bounded_training_predictor_factorization
    (trainingView M S I₁ (2 * (n + 1))) (score (2 * (n + 1)))
    (hm (2 * (n + 1))) bound hb (hbound (2 * (n + 1)))
  choose g hf hfb heq using hex
  let f := fun n => Function.uncurry (g n)
  refine ⟨f, heq, hf, ?_, ?_⟩
  · intro n t
    have hs : Measurable (fun o => f n (t, o)) := by fun_prop
    let : IsProbabilityMeasure (observationLaw M) := by
      rw [← S.map_eq 0]
      exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
    exact MemLp.of_bound hs.aestronglyMeasurable bound
      (Eventually.of_forall fun o => by
        simpa only [Real.norm_eq_abs, f, Function.uncurry_apply_pair] using hfb n t o)
  · intro n i
    have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n
    let : IsProbabilityMeasure (observationLaw M) := by
      rw [← S.map_eq 0]
      exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
    exact (bounded_training_factor_sections_and_rows_memLp μ (observationLaw M)
      _ _ (f n) (hf n) hl.2.1 (hl.2.2.1 i) bound (hfb n)).2

-- @node: equalHalfSplit_bounded_training_oracle_remainder_negligible
/-- Suppose [the sample has an equal half split](hyp:hSplit), [the fitted-minus-oracle score is measurable from the training information and a new observation](hyp:hm), [the bounding constant is nonnegative](hyp:hb), and [the absolute score difference is uniformly bounded by it](hyp:hbound). If [its integrated squared error at even sample sizes converges to zero in probability](hyp:hrate) and [its population mean multiplied by the square root of the evaluation sample size converges to zero in probability](hyp:hbias), [the difference between fitted and oracle evaluation averages, multiplied by that same square root, converges to zero in probability](goal). -/
lemma equalHalfSplit_bounded_training_oracle_remainder_negligible
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
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
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a))
      atTop (fun _ _ => 0) := by
  obtain ⟨f, heq, hf, hsection, hfit⟩ :=
    equalHalfSplit_bounded_training_score_factorization M μ S I₁ I₂ hSplit
      (fun n a o => score n a o - truth o) hm bound hb hbound
  apply equalHalfSplit_oracle_score_remainder_negligible M μ S I₁ I₂ hSplit
    score truth f heq hf hsection hfit
  · simpa only [← heq] using hrate
  · simpa only [← heq] using hbias

end Papers.TbsPrteOptimalTransport
