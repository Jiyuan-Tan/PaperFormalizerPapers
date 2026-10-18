module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTailConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryTrainingVariance
/-! Evaluation consistency for the continuous terminal score.
The shared terminal coordinates give a uniform almost-everywhere bound.
Training factorization transfers population score convergence to the random
evaluation half, and the oracle LLNs give mean and variance consistency. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_tail_abs_bound
/-- For [a valid policy](hyp:hphi), suppose [the derivative bound is nonnegative](hyp:hB)
and [bounds the absolute policy derivative throughout the unit interval](hyp:hb).
If [the continuous nuisance functions are admissible](hyp:he), [the clipping threshold is positive](hyp:hc),
and [positive-level assignment probabilities exceed that threshold almost everywhere](hyp:hpi), then
[the absolute terminal score is almost everywhere bounded by the absolute lower outcome endpoint multiplied by the sum of two, the derivative bound, and the reciprocal clipping threshold](goal). -/
lemma fitted_continuous_tail_abs_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    ∀ᵐ o ∂observationLaw M,
      |commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o| ≤
        |M.yMin| * (2 + B + 1 / c) := by
  exact fitted_binary_tail_abs_bound M phi dphi hphi B hB hb L
    (continuousTailCoordinates L e) (continuousTailCoordinates_admissible M L e he)
    c hc hpi

-- @node: nuisanceRates_training_continuous_tail_empirical_score_error
/-- Under [an equal training/evaluation split](hyp:hSplit), let [the policy be valid](hyp:hphi),
[have the specified derivative](hyp:hd), and [have a bounded, Lipschitz derivative](hyp:hDerivative).
Suppose [the reference nuisances are admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh),
[the clipping threshold is positive](hyp:hc), and [reference and fitted level assignment probabilities exceed it almost everywhere](hyp:hclip).
If [propensities](hyp:hrp), [level probabilities](hyp:hrlev), [level assignment probabilities](hyp:hrpi),
and [terminal weights](hyp:hrg) satisfy the finite-coordinate rate conditions, and
[the fitted-minus-reference terminal score is measurable using only the training sample and a new observation](hyp:hm), then
[the evaluation-half average squared terminal-score error converges in probability to zero along even sample sizes](goal). -/
lemma nuisanceRates_training_continuous_tail_empirical_score_error
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o =>
      commonTailScore M phi dphi L (eh n a).prop (eh n a).pLev
        (eh n a).piLev (eh n a).gammaTail o -
      commonTailScore M phi dphi L e0.prop e0.pLev e0.piLev e0.gammaTail o)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (commonTailScore M phi dphi L (eh (2 * (n + 1)) a).prop
            (eh (2 * (n + 1)) a).pLev (eh (2 * (n + 1)) a).piLev
            (eh (2 * (n + 1)) a).gammaTail (S.Z i a) -
          commonTailScore M phi dphi L e0.prop e0.pLev e0.piLev e0.gammaTail
            (S.Z i a)) ^ 2) atTop (fun _ _ => 0) := by
  obtain ⟨B, D, hB, hD, hder⟩ := hDerivative
  have hDerivative : PolicyDerivativeBoundedLipschitz dphi := ⟨B, D, hB, hD, hder⟩
  have hbder z x p (hp : p ∈ Icc (0 : ℝ) 1) : |dphi z x p| ≤ B :=
    (hder z x p p hp hp).1
  let C := |M.yMin| * (2 + B + 1 / c)
  have hb n a : ∀ᵐ o ∂observationLaw M,
      |commonTailScore M phi dphi L (eh n a).prop (eh n a).pLev
        (eh n a).piLev (eh n a).gammaTail o -
      commonTailScore M phi dphi L e0.prop e0.pLev e0.piLev e0.gammaTail o| ≤
        C + C := by
    filter_upwards [fitted_continuous_tail_abs_bound M phi dphi hphi B hB hbder
      L (eh n a) (heh n a) c hc (fun i => (hclip n a i).mono (fun _ h => h.2)),
      fitted_continuous_tail_abs_bound M phi dphi hphi B hB hbder L e0 he0
        c hc (fun i => (hclip n a i).mono (fun _ h => h.1))] with o hfit htruth
    exact (abs_sub _ _).trans (add_le_add hfit htruth)
  obtain ⟨f, heq, hf, hfit⟩ :=
    equalHalfSplit_ae_bounded_training_score_factorization M μ S I₁ I₂ hSplit _ hm
      (C + C) hb
  have hr := nuisanceRates_continuous_commonTailScore_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip hrp hrlev hrpi hrg
  have hr' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [← heq] using hr
  have hE := equalHalfSplit_empirical_fitted_score_energy M μ S I₁ I₂ hSplit
    f hf hfit hr'
  simpa only [← heq] using hE

-- @node: nuisanceRates_training_continuous_tail_mean_variance_consistent
/-- Under [an equal training/evaluation split](hyp:hSplit), assume [a valid policy](hyp:hphi)
[with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative),
[admissible reference nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh),
[a positive clipping threshold](hyp:hc), and [reference and fitted level assignment probabilities bounded below by it almost everywhere](hyp:hclip).
If [propensities](hyp:hrp), [level probabilities](hyp:hrlev), [level assignment probabilities](hyp:hrpi),
and [terminal weights](hyp:hrg) satisfy the finite-coordinate rate conditions, and
[the terminal-score error is measurable from the training sample and a new observation](hyp:hm), then
[the fitted terminal-score average converges to the reference score's population mean and its empirical variance converges to the reference score's population variance along even sample sizes](goal). -/
lemma nuisanceRates_training_continuous_tail_mean_variance_consistent
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o =>
      commonTailScore M phi dphi L (eh n a).prop (eh n a).pLev
        (eh n a).piLev (eh n a).gammaTail o -
      commonTailScore M phi dphi L e0.prop e0.pLev e0.piLev e0.gammaTail o)) :
    let score := fun n a => commonTailScore M phi dphi L (eh n a).prop
      (eh n a).pLev (eh n a).piLev (eh n a).gammaTail
    let truth := commonTailScore M phi dphi L e0.prop e0.pLev e0.piLev e0.gammaTail
    let theta := ∫ o, truth o ∂observationLaw M
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  let : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hE := nuisanceRates_training_continuous_tail_empirical_score_error M μ S I₁ I₂
    hSplit phi dphi hphi hd hDerivative L e0 eh he0 heh c hc hclip hrp hrlev hrpi hrg hm
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure μ
  have hLp := fitted_continuous_commonTailScore_memLp M phi dphi hphi hd hDerivative
    L e0 he0 c hc
    (fun i => (hclip 0 (Classical.choice inferInstance) i).mono (fun _ h => h.1))
  dsimp only
  exact ⟨equalHalfSplit_dmlRV_consistent_of_empirical_score_error M μ S I₁ I₂
      hSplit _ _ (hLp.integrable (by norm_num)) _ rfl hE,
    equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp M μ S I₁ I₂
      hSplit _ _ hLp _ rfl hE⟩

end Papers.TbsPrteOptimalTransport
