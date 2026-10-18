module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryPopulationNormality
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousScoreBounds
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousLabelTransport
/-! The centered evaluation remainder for continuous scores.
The population bias is subtracted explicitly, so this file proves the empirical
part of the DML remainder without presupposing the second-order bias bound. -/
public section

set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: equalHalfSplit_ae_bounded_training_centered_oracle_remainder
/-- For [an equal training and evaluation half split](hyp:hSplit), suppose [the
fitted-minus-population score is measurable from the training data and the
prediction observation](hyp:hm), [its absolute value is uniformly bounded almost
everywhere](hyp:hb), and [its observation-integrated squared error converges to
zero in probability along sample sizes twice one plus the index](hyp:hrate).
Then [the difference between fitted and population evaluation means, after
subtracting its population expectation and multiplying by the square root of the
evaluation half's size, converges to zero in probability](goal). -/
lemma equalHalfSplit_ae_bounded_training_centered_oracle_remainder
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (C : ℝ) (hb : ∀ n a, ∀ᵐ o ∂observationLaw M, |score n a o - truth o| ≤ C)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a -
          ∫ o, score (2 * (n + 1)) a o - truth o ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  obtain ⟨f, heq, hf, hsection, hfit⟩ :=
    equalHalfSplit_ae_bounded_training_l2_factorization M μ S I₁ I₂ hSplit
      (fun n a o => score n a o - truth o) hm C hb
  have hfluct := equalHalfSplit_centered_fitted_score_fluctuation M μ S I₁ I₂
    hSplit f hf hsection hfit (by simpa only [← heq] using hrate)
  apply TendstoInMeasure.congr _ (Eventually.of_forall (fun _ => rfl)) hfluct
  intro n
  filter_upwards [equalHalfSplit_scaled_score_difference_decomposition
    M μ S I₁ I₂ hSplit score truth f heq n] with a ha
  simp only [← heq] at ha ⊢
  linarith only [ha]


-- @node: encoded_continuous_centered_oracle_remainder_negligible
/-- Assume [an equal training and evaluation half split](hyp:hSplit), [a valid
policy map](hyp:hphi), [correct policy differentiation](hyp:hd), [a bounded
Lipschitz policy derivative](hyp:hDerivative), [the structural model
assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend), [a positive number
of treatment levels](hyp:hK), [policy-invariant level ordering](hyp:hOrder),
[an admissible population nuisance](hyp:he0), [baseline overlap](hyp:hov), and
[policy overlap](hyp:hpol). If [the oracle fit's encoded components are measurable
from the training split and prediction covariates](hyp:hm), [its fits satisfy
clipping, simplex-share, and denominator restrictions](hyp:hc), [are
admissible](hyp:ha), [have componentwise L² errors that vanish faster in probability
than the inverse fourth root of sample size](hyp:hrate), and [boundary
densities are bounded](hyp:hDensity), [the fitted-minus-population continuous-score
evaluation mean, centered by its population expectation and scaled by the square
root of the evaluation half's size, converges to zero in probability along
sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_centered_oracle_remainder_negligible
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (oracle : ℕ → A → NuisanceCont L)
    (hm : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun n a => contComponent M L (oracle n a) c))
    (hc : ∀ n a, ContClipping M L (oracle n a) ∧
      ContFittedSharesSimplex L (oracle n a) ∧ ContDenominatorsClipped L (oracle n a) cpi)
    (ha : ∀ n a, ContAdmissible M L (oracle n a))
    (hrate : FiniteNuisanceRates M μ (fun n a => contComponent M L (oracle n a))
      (contComponent M L (trueNuisance M L)))
    (hDensity : BoundaryDensitiesBounded M L) :
    let score := fun n a o => psiCont M phi dphi L hK o (oracle n a)
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a -
          ∫ o, score (2 * (n + 1)) a o - truth o ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hscore := training_measurable_continuous_score_of_components M S I₁
    phi dphi hphi hd L hK oracle hm (fun n a => (hc n a).1.1)
  have hdiff := training_measurable_continuous_score_difference M S I₁
    phi dphi hphi hd L hK he0 _ hscore
  have hsection (n : ℕ) (a : A) (c) :
      Measurable (contComponent M L (oracle n a) c) := by
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    exact (hm c n).comp (measurable_const.prodMk measurable_id)
  have hconv := encoded_continuous_total_score_sq_tendsto_probability_zero
    M μ hStruct.2.2.2.1 phi dphi hphi hd hDerivative L hK hOrder
    hStruct.1 hStruct.2.1 hend he0 oracle (fun n a => (hc n a).1)
    (fun n a => (hc n a).2.1) hsection hrate hDensity cpi hov hpol
    (fun n a => (hc n a).2.2)
  have hpos : 0 < cpi / 2 := by linarith [hov.1]
  have hp0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have ht0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hpol.1]
  have hpf n a (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (oracle n a).piLev i x :=
    Eventually.of_forall (fun x => (hc n a).2.2.1 i x |>.1)
  have htf n a (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (oracle n a).tauLev r x :=
    Eventually.of_forall (fun x => ((hc n a).2.2.2 r x
      (contFittedSharesSimplex_policy_nonempty L _ (hc n a).2.1 r)).1)
  obtain ⟨C, hbound⟩ := fitted_continuous_total_score_uniform_bound M phi dphi hphi
    hDerivative L hK hStruct.1 hStruct.2.1 hend (cpi / 2) hpos
  have hb n a : ∀ᵐ o ∂observationLaw M,
      |psiCont M phi dphi L hK o (oracle n a) -
        psiCont M phi dphi L hK o (trueNuisance M L)| ≤ C + C := by
    filter_upwards [hbound _ (ha n a) (hpf n a) (htf n a),
      hbound _ he0 hp0 ht0] with o hf ht
    exact (abs_sub _ _).trans (add_le_add hf ht)
  exact equalHalfSplit_ae_bounded_training_centered_oracle_remainder
    M μ S I₁ I₂ hSplit _ _ hdiff (C+C) hb hconv

-- The oracle retains its component rates for the subsequent bias proof.
-- Recovery transfers the centered fluctuation even though classification used I₂.
-- @node: contDMLRegime_centered_remainder_on_recovery_of_labels_eq
/-- Assume [an equal training and evaluation half split](hyp:hSplit), [a valid
policy map](hyp:hphi), [correct policy differentiation](hyp:hd), [a bounded
Lipschitz derivative](hyp:hDerivative), [the structural model assumptions](hyp:hStruct),
[known outcome endpoints](hyp:hend), [a positive level count](hyp:hK),
[policy-invariant level ordering](hyp:hOrder), [measurable level propensities](hyp:hlev),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
[continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), [the finite continuous
DML regime conditions](hyp:hr), [recovery events whose complement probabilities
vanish](hyp:hG), and [equality of recovered and population labels on those events
at sample sizes twice one plus the index](hyp:hLabels). Then [there exists a
nuisance sequence on the population levels with training-measurable components,
clipping, simplex shares, clipped denominators, admissibility, and componentwise
L² errors vanishing faster in probability than the inverse fourth root of sample
size, whose scores equal the recovered fitted scores on the recovery events;
the recovered-minus-population evaluation mean, centered by this sequence's
population score difference and scaled by the square root of the evaluation
half's size, converges to zero in probability](goal). -/
lemma contDMLRegime_centered_remainder_on_recovery_of_labels_eq
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        recoveryLabels L) :
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ c, TrainingPredictorMeasurable M S I₁
        (fun n a => contComponent M L (oracle n a) c)) ∧
      (∀ n a, ContClipping M L (oracle n a) ∧
        ContFittedSharesSimplex L (oracle n a) ∧
        ContDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, ContAdmissible M L (oracle n a)) ∧
      FiniteNuisanceRates M μ (fun n a => contComponent M L (oracle n a))
        (contComponent M L (trueNuisance M L)) ∧
      (∀ n a, a ∈ G n → ∀ o,
        fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat (2 * (n + 1)) a o =
          psiCont M phi dphi L hK o (oracle (2 * (n + 1)) a)) ∧
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
          (dmlRV M S I₂ (fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat)
              (2 * (n + 1)) a -
            dmlRV M S I₂ (fun _ _ o => psiCont M phi dphi L hK o (trueNuisance M L))
              (2 * (n + 1)) a -
            ∫ o, psiCont M phi dphi L hK o (oracle (2 * (n + 1)) a) -
              psiCont M phi dphi L hK o (trueNuisance M L) ∂observationLaw M))
        atTop (fun _ _ => 0) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hq := population_policyProp_measurable M hStruct.2.2.2.1 phi hphi
  have he0 := population_continuous_nuisance_admissible M hStruct hend
    (policyProp phi M.prop) hq L hOrder hlev cpi hov hpol
  obtain ⟨oracle, hm, hc, ha, heq, hrate⟩ :=
    contDMLRegime_regular_oracle_nuisance_records_of_labels_eq
      M μ S I₁ I₂ pHat phi rho gap cpi L ch hK hend eHat hr G hG hLabels
  have hscore n a (hna : a ∈ G n) o :=
    fittedContScore_eq_oracle_of_labels_eq M S I₁ I₂ pHat phi dphi
      rho gap L hK eHat oracle _ a (hLabels n a hna) (heq n a hna) o
  refine ⟨oracle, hm, hc, ha, hrate, hscore, ?_⟩
  have hfluct := encoded_continuous_centered_oracle_remainder_negligible
    M μ S I₁ I₂ hSplit phi dphi hphi hd hDerivative hStruct hend L hK hOrder
    he0 cpi hov hpol oracle hm hc ha hrate hr.2.2.1
  dsimp only at hfluct
  apply probability_limit_transfer_on_recovery μ G _ _ 0 hG _ hfluct
  intro n a hna
  rw [dmlRV_eq_of_score_eq_on_sample M S I₂ _
    (fun n a o => psiCont M phi dphi L hK o (oracle n a))
    (2 * (n + 1)) a (fun i hi => hscore n a hna (S.Z i a))]

end Papers.TbsPrteOptimalTransport
