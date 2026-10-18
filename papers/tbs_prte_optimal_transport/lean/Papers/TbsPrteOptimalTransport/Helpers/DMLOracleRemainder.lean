module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomEvaluationMoments
/-! The oracle evaluation remainder is the sum of its population bias and
the centered evaluation fluctuation, with the actual random half-sample. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_scaled_score_difference_decomposition
/-- For [score-difference functions of training data and one observation at each even sample size](hyp:f), under [the equal-half sample-splitting laws](hyp:hSplit), if [the fitted-minus-oracle score is a function of the training data and the evaluated observation](hyp:hscore), then [the difference of the DML estimates multiplied by the square root of the evaluation size equals, almost surely, the population mean score difference multiplied by that square root plus the centered evaluation sum divided by that square root](goal). -/
lemma equalHalfSplit_scaled_score_difference_decomposition
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o, score (2 * (n + 1)) a o - truth o =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o)) (n : ℕ) :
    (fun a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (dmlRV M S I₂ score (2 * (n + 1)) a -
        dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a)) =ᵐ[μ]
    (fun a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M) +
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ I₂ (2 * (n + 1)) a,
        (f n (trainingView M S I₁ (2 * (n + 1)) a, S.Z i a) -
          ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M)) := by
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ =
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
    have hp := Real.sqrt_pos.2 hn
    have hsq := Real.sq_sqrt hn.le
    field_simp
    nlinarith
  filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1]
    with a ha
  have hcard : (I₂ (2 * (n + 1)) a).card = n + 1 := by
    rw [← ha.2, Finset.card_image_of_injective _ ha.1, Finset.card_univ,
      Fintype.card_fin]
  have hne : (I₂ (2 * (n + 1)) a).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; omega)
  simp only [dmlRV, dif_pos hne, scoreAverage, splitMean,
    ← Finset.sum_sub_distrib, hscore, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, hcard]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp only [hscore, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, hcard]
  have hc : ((n + 1 : ℕ) : ℝ) ≠ 0 := hn.ne'
  rw [← mul_assoc, hs]
  have hs' : (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * ((n + 1 : ℕ) : ℝ) =
      Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    rw [← hs, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [mul_sub, ← mul_assoc, hs']
  ring

-- @node: equalHalfSplit_oracle_score_remainder_negligible
/-- For [score-difference functions of training data and one observation at each even sample size](hyp:f), under [the equal-half sample-splitting laws](hyp:hSplit), suppose [the fitted-minus-oracle score factors through training data and a single observation](hyp:hscore), [this function is measurable](hyp:hf), [each fixed-training section is square-integrable under the observation law](hyp:hsection), and [each evaluation row is square-integrable under the sampling law](hyp:hfit). If [the population squared score difference converges in probability to zero](hyp:hrate) and [its population mean multiplied by the square root of the evaluation size converges in probability to zero](hyp:hbias), then [the fitted-minus-oracle DML estimate multiplied by that square root converges in probability to zero](goal). -/
lemma equalHalfSplit_oracle_score_remainder_negligible
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o, score (2 * (n + 1)) a o - truth o =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hsection : ∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (hbias : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M))
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a))
      atTop (fun _ _ => 0) := by
  have hfluct := equalHalfSplit_centered_fitted_score_fluctuation M μ S I₁ I₂
    hSplit f hf hsection hfit hrate
  have hneg := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt hfluct
  simp only [neg_zero] at hneg
  have hsum := hbias.sub hneg
  simp only [sub_zero, sub_neg_eq_add] at hsum
  exact TendstoInMeasure.congr
    (fun n => (equalHalfSplit_scaled_score_difference_decomposition M μ S I₁ I₂
      hSplit score truth f hscore n).symm)
    (Eventually.of_forall (fun _ => rfl)) hsum

end Papers.TbsPrteOptimalTransport
