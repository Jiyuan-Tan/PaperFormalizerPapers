module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousScoreConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomEvaluationMoments
/-! Continuous oracle score moments and evaluation-sample squared error.
Clipping and the simplex restriction supply second moments of the encoded score.
The proved population score convergence then controls the empirical squared error
on the actual random evaluation half through conditional Markov's inequality. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

set_option linter.style.longLine false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z]

-- @node: encoded_continuous_total_score_memLp
/-- If [the policy map is valid](hyp:hphi), [its derivative is correct](hyp:hd)
and [bounded and Lipschitz](hyp:hDerivative), [the level count is positive](hyp:hK),
[the encoded nuisance fit satisfies clipping](hyp:hclip), [its fitted shares lie in
the simplex](hyp:hshares), and [all encoded components are measurable](hyp:hm), then,
under [potential outcomes in the outcome domain almost surely](hyp:hp), [consistency](hyp:hcons), [known outcome
endpoints](hyp:hend), [a positive overlap constant](hyp:hcpi), and [denominators
clipped at that constant](hyp:hden), [the fitted continuous total score has a finite
second moment under the observation distribution](goal). -/
lemma encoded_continuous_total_score_memLp (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e : NuisanceCont L) (hclip : ContClipping M L e)
    (hshares : ContFittedSharesSimplex L e)
    (hm : ∀ d, Measurable (contComponent M L e d))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (cpi : ℝ) (hcpi : 0 < cpi) (hden : ContDenominatorsClipped L e cpi) :
    MemLp (fun o => psiCont M phi dphi L hK o e) 2 (observationLaw M) := by
  let er := restrictContShares L e
  have her : ContAdmissible M L er :=
    restrictContShares_admissible_of_encoded_clipping M L e hclip hshares hm
  have hc : 0 < cpi / 2 := by linarith
  have hpi (i : PositiveIndex L.K) : ∀ᵐ x ∂xLaw M, cpi / 2 ≤ er.piLev i x :=
    Eventually.of_forall (fun x => (hden.1 i x).1)
  have htau (r : RegularIndex L) : ∀ᵐ x ∂xLaw M, cpi / 2 ≤ er.tauLev r x :=
    Eventually.of_forall (fun x => (hden.2 r x
      (contFittedSharesSimplex_policy_nonempty L e hshares r)).1)
  have hs := fitted_continuous_total_score_memLp M phi dphi hphi hd hDerivative
    L hK er her hp hcons hend (cpi / 2) hc hpi htau
  simpa only [er, psiCont_restrictContShares] using hs

-- @node: true_continuous_total_score_memLp_of_overlap
/-- Under [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
that is [bounded and Lipschitz](hyp:hDerivative), [a positive level count](hyp:hK),
[admissible true nuisances](hyp:he0), [potential outcomes in the outcome domain almost surely](hyp:hp),
[consistency](hyp:hcons), [known outcome endpoints](hyp:hend), [baseline
overlap](hyp:hov), and [policy overlap](hyp:hpol), [the true continuous total score
has a finite second moment under the observation distribution](goal). -/
lemma true_continuous_total_score_memLp_of_overlap (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi) :
    MemLp (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      2 (observationLaw M) := by
  have hpi (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).piLev i x :=
    Eventually.of_forall (fun x => hov.2 x i.val i.property.1 i.property.2)
  have htau (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).tauLev r x :=
    Eventually.of_forall (fun x => hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (continuous_admissible_policy_nonempty M L _ he0 r))
  exact fitted_continuous_total_score_memLp M phi dphi hphi hd hDerivative
    L hK _ he0 hp hcons hend cpi hov.1 hpi htau

-- @node: encoded_continuous_total_score_difference_memLp
/-- Under [a valid policy map](hyp:hphi), [the specified policy derivative](hyp:hd)
that is [bounded and Lipschitz](hyp:hDerivative), [a positive level count](hyp:hK),
[admissible true nuisances](hyp:he0), [clipped fitted nuisances](hyp:hclip),
[simplex-valued fitted shares](hyp:hshares), [measurable encoded components](hyp:hm),
[potential outcomes in the outcome domain almost surely](hyp:hp), [consistency](hyp:hcons), [known outcome
endpoints](hyp:hend), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol), and
[clipped fitted denominators](hyp:hden), [the difference between the fitted and
true continuous total scores has a finite second moment](goal). -/
lemma encoded_continuous_total_score_difference_memLp
    (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (e : NuisanceCont L) (hclip : ContClipping M L e)
    (hshares : ContFittedSharesSimplex L e)
    (hm : ∀ d, Measurable (contComponent M L e d))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : ContDenominatorsClipped L e cpi) :
    MemLp (fun o => psiCont M phi dphi L hK o e -
      psiCont M phi dphi L hK o (trueNuisance M L)) 2 (observationLaw M) := by
  have hfit := encoded_continuous_total_score_memLp M phi dphi hphi hd hDerivative
    L hK e hclip hshares hm hp hcons hend cpi hov.1 hden
  have htruth := true_continuous_total_score_memLp_of_overlap M phi dphi hphi hd
    hDerivative L hK he0 hp hcons hend cpi hov hpol
  exact hfit.sub htruth

-- @node: encoded_continuous_total_score_difference_integrable_sq
/-- If [the policy map is valid](hyp:hphi), [its derivative is correct](hyp:hd)
and [bounded and Lipschitz](hyp:hDerivative), [the level count is positive](hyp:hK),
[the true nuisances are admissible](hyp:he0), [the fitted nuisances are
clipped](hyp:hclip), [their shares lie in the simplex](hyp:hshares), and [their
encoded components are measurable](hyp:hm), then [potential outcomes in the outcome domain almost surely](hyp:hp),
[consistency](hyp:hcons), [known outcome endpoints](hyp:hend), [baseline
overlap](hyp:hov), [policy overlap](hyp:hpol), and [clipped fitted
denominators](hyp:hden) imply that [the squared difference between fitted and true
continuous total scores is integrable under the observation distribution](goal). -/
lemma encoded_continuous_total_score_difference_integrable_sq
    (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (e : NuisanceCont L) (hclip : ContClipping M L e)
    (hshares : ContFittedSharesSimplex L e)
    (hm : ∀ d, Measurable (contComponent M L e d))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : ContDenominatorsClipped L e cpi) :
    Integrable (fun o => (psiCont M phi dphi L hK o e -
      psiCont M phi dphi L hK o (trueNuisance M L)) ^ 2) (observationLaw M) := by
  exact (encoded_continuous_total_score_difference_memLp M phi dphi hphi hd
    hDerivative L hK he0 e hclip hshares hm hp hcons hend cpi hov hpol hden).integrable_sq

-- The representation and evaluation moment hypotheses describe the measurable
-- training fit. Population score convergence is derived from nuisance rates.
-- @node: equalHalfSplit_encoded_continuous_empirical_score_error
/-- For [an equal training and evaluation split](hyp:hSplit) in [a threshold-crossing
model](hyp:h), assume [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd)
that is [bounded and Lipschitz](hyp:hDerivative), [a positive level count](hyp:hK),
[invariant level ordering](hyp:hOrder), [potential outcomes in the outcome domain almost surely](hyp:hp),
[consistency](hyp:hcons), and [known outcome endpoints](hyp:hend). If [the true
nuisances are admissible](hyp:he0), [all fitted nuisances satisfy clipping](hyp:hclip),
[their shares lie in the simplex](hyp:hshares), [their encoded components are
measurable](hyp:hm), [their componentwise nuisance rates hold](hyp:hr), [boundary
densities are bounded](hyp:hDensity), [baseline overlap](hyp:hov) and [policy
overlap](hyp:hpol) hold, [fitted denominators are clipped](hyp:hden), [the score
error factors through the training summary via the given function](hyp:hscore),
[a score-error function of sample size, training summary, and observation is given](hyp:f),
[that function is measurable](hyp:hf), and [its evaluation observations have finite
second moments](hyp:hfit), then [the evaluation-half average squared error between
fitted and true total scores converges in probability to zero](goal). -/
lemma equalHalfSplit_encoded_continuous_empirical_score_error
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a d, Measurable (contComponent M L (eh n a) d))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (hDensity : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n a, ContDenominatorsClipped L (eh n a) cpi)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiCont M phi dphi L hK o (eh (2 * (n + 1)) a) -
        psiCont M phi dphi L hK o (trueNuisance M L) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (psiCont M phi dphi L hK (S.Z i a) (eh (2 * (n + 1)) a) -
            psiCont M phi dphi L hK (S.Z i a) (trueNuisance M L)) ^ 2)
      atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_total_score_sq_tendsto_probability_zero
    M μ h phi dphi hphi hd hDerivative L hK hOrder hp hcons hend he0
    eh hclip hshares hm hr hDensity cpi hov hpol hden
  have hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [← hscore] using hs
  have henergy := equalHalfSplit_empirical_fitted_score_energy M μ S I₁ I₂
    hSplit f hf hfit hrate
  simpa only [← hscore] using henergy

-- Here a nuisance fit is given on the training summary itself. This lets the
-- section moments needed by conditional Chebyshev follow from clipping, rather
-- than being an extra population-score moment assumption.
-- @node: equalHalfSplit_encoded_continuous_centered_score_fluctuation
/-- For [an equal training and evaluation split](hyp:hSplit) in [a threshold-crossing
model](hyp:h), assume [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd)
that is [bounded and Lipschitz](hyp:hDerivative), [a positive level count](hyp:hK),
[invariant level ordering](hyp:hOrder), [potential outcomes in the outcome domain almost surely](hyp:hp),
[consistency](hyp:hcons), [known outcome endpoints](hyp:hend), and [admissible true
nuisances](hyp:he0). For [continuous-outcome nuisance fits indexed by sample size and training summary](hyp:eh), if [each fit from a training summary satisfies clipping](hyp:hclip),
[its shares lie in the simplex](hyp:hshares), [its encoded components are
measurable](hyp:hm), [the training fits satisfy the componentwise nuisance
rates](hyp:hr), [boundary densities are bounded](hyp:hDensity), [baseline
overlap](hyp:hov) and [policy overlap](hyp:hpol) hold, [fitted denominators are
clipped](hyp:hden), [the score error is jointly measurable in the training summary
and observation](hyp:hf), and [each evaluation score error has a finite second
moment](hyp:hfit), then [the sum of the evaluation-half score errors, centered by
their population means and divided by the square root of the half-sample size,
converges in probability to zero](goal). -/
lemma equalHalfSplit_encoded_continuous_centered_score_fluctuation
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ∀ n, (Finset ℕ × (Fin n → Unit ⊕ Obs X Z)) → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ
      (fun n a => contComponent M L (eh n (trainingView M S I₁ n a)))
      (contComponent M L (trueNuisance M L)))
    (hDensity : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (hf : ∀ n, Measurable (fun tb :
      (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z =>
        psiCont M phi dphi L hK tb.2 (eh (2 * (n + 1)) tb.1) -
          psiCont M phi dphi L hK tb.2 (trueNuisance M L)))
    (hfit : ∀ n i, MemLp (fun a =>
      psiCont M phi dphi L hK
          (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)
          (eh (2 * (n + 1)) (trainingView M S I₁ (2 * (n + 1)) a)) -
        psiCont M phi dphi L hK
          (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)
          (trueNuisance M L)) 2 μ) :
    let D := fun n a o => psiCont M phi dphi L hK o
      (eh (2 * (n + 1)) (trainingView M S I₁ (2 * (n + 1)) a)) -
        psiCont M phi dphi L hK o (trueNuisance M L)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (D n a (S.Z i a) - ∫ o, D n a o ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  let f := fun (n : ℕ)
    (tb : (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z) =>
      psiCont M phi dphi L hK tb.2 (eh (2 * (n + 1)) tb.1) -
        psiCont M phi dphi L hK tb.2 (trueNuisance M L)
  have hsection (n : ℕ) (t : Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) :
      MemLp (fun o => f n (t, o)) 2 (observationLaw M) :=
    encoded_continuous_total_score_difference_memLp M phi dphi hphi hd hDerivative
      L hK he0 (eh _ t) (hclip _ t) (hshares _ t) (hm _ t)
      hp hcons hend cpi hov hpol (hden _ t)
  have hrate := encoded_continuous_total_score_sq_tendsto_probability_zero
    M μ h phi dphi hphi hd hDerivative L hK hOrder hp hcons hend he0
    (fun n a => eh n (trainingView M S I₁ n a))
    (fun n a => hclip n _) (fun n a => hshares n _) (fun n a => hm n _)
    hr hDensity cpi hov hpol (fun n a => hden n _)
  exact equalHalfSplit_centered_fitted_score_fluctuation M μ S I₁ I₂ hSplit
    f hf hsection hfit hrate

end Papers.TbsPrteOptimalTransport
