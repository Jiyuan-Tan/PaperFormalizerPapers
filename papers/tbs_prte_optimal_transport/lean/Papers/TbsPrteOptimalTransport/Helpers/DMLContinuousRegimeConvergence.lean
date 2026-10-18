module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLScoreMeasurability
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousOracleClipping
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousEvaluation
/-! Continuous oracle score convergence directly from the fitted regime.
The measurable, clipped oracle is constructed from training coordinates. Its
score agrees with the feasible score on exact recovery, while the component
rates imply population L₂ score convergence. -/
public section
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
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

-- @node: contAdmissible_component_measurable
/-- If [the continuous nuisance record is admissible](hyp:he), then [every encoded nuisance coordinate is measurable](goal). -/
@[fun_prop] lemma contAdmissible_component_measurable
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℕ × ℕ × ℕ × Z) :
    Measurable (contComponent M L e c) := by
  try fun_prop
  rcases he with ⟨_, hp, _, hl, _, hpi, _, ht, _, hs, _, hf, _, hg,
    _, htail, _, hn, _, hmp, _, hmm, _, hjp, _, hjm, _, hjfp, _, hjfm, _⟩
  rcases c with ⟨code, k, j, z⟩
  unfold contComponent
  dsimp only
  split <;> try dsimp only
  all_goals try simp only [positiveValue, regularValue, shareValue, fullValue,
    nuValue, boundaryValue, minusBoundaryValue, meanValue, minusMeanValue, minusFullValue]
  all_goals repeat' first
    | fun_prop
    | split
    | exact hp _
    | exact hl _
    | exact hpi _
    | exact ht _
    | exact hs _ _
    | exact hf _
    | exact hg _
    | exact htail
    | exact hn _
    | exact hmp _
    | exact hmm _
    | exact hjp _
    | exact hjm _
    | exact hjfp _
    | exact hjfm _

-- @node: training_measurable_continuous_score_difference
/-- If [the policy is a valid policy map](hyp:hphi), [its derivative is the specified derivative map](hyp:hd), [there is a positive number of levels](hyp:hK), [the true nuisance record is admissible](hyp:he0), and [the fitted score is measurable using the training sample and the observation](hyp:hm), then [subtracting the true continuous score preserves that training measurability](goal). -/
lemma training_measurable_continuous_score_difference
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ : SampleSplit A) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (score : ℕ → A → Obs X Z → ℝ)
    (hm : TrainingPredictorMeasurable M S I₁ score) :
    TrainingPredictorMeasurable M S I₁ (fun n a o =>
      score n a o - psiCont M phi dphi L hK o (trueNuisance M L)) := by
  have hconst : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun (_ : ℕ) (_ : A) => contComponent M L (trueNuisance M L) c) := by
    intro c n
    let : MeasurableSpace A :=
      MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    exact (contAdmissible_component_measurable M L _ he0 c).comp measurable_snd
  have htruth := training_measurable_continuous_score_of_components M S I₁
    phi dphi hphi hd L hK (fun _ _ => trueNuisance M L) hconst
    (fun _ _ => M.rangeProp)
  intro n
  exact (hm n).sub (htruth n)

-- @node: contDMLRegime_oracle_score_convergence_on_recovery
/-- Suppose [the policy is valid](hyp:hphi), [the specified derivative differentiates it](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative), [the structural model assumptions hold](hyp:hStruct), [outcome endpoints are known](hyp:hend), [the level count is positive](hyp:hK), [level ordering is invariant under the policy](hyp:hOrder), [the true nuisance record is admissible](hyp:he0), [baseline overlap has the specified witness](hyp:hov), and [policy overlap holds at the same bound](hyp:hpol). For [continuous-outcome nuisance estimates on the recovered levels](hyp:eHat), under [the finite continuous DML regime](hyp:hr), [recovery events whose complement probabilities tend to zero](hyp:hG), and [exact recovery of the fixed level data on those events at even sample sizes](hyp:hLevels), [there exists an everywhere clipped, simplex-valued, denominator-clipped and admissible oracle nuisance sequence whose score difference is training measurable, whose population squared score error converges in probability to zero, and whose score equals the fitted score on the recovery events](goal). -/
lemma contDMLRegime_oracle_score_convergence_on_recovery
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLevels : ∀ n a, a ∈ G n →
      recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a = L) :
    ∃ oracle : ℕ → A → NuisanceCont L,
      (∀ n a, ContClipping M L (oracle n a) ∧
        ContFittedSharesSimplex L (oracle n a) ∧
        ContDenominatorsClipped L (oracle n a) cpi) ∧
      (∀ n a, ContAdmissible M L (oracle n a)) ∧
      TrainingPredictorMeasurable M S I₁ (fun n a o =>
        psiCont M phi dphi L hK o (oracle n a) -
          psiCont M phi dphi L hK o (trueNuisance M L)) ∧
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n a => ∫ o,
          (psiCont M phi dphi L hK o (oracle (2 * (n + 1)) a) -
            psiCont M phi dphi L hK o (trueNuisance M L)) ^ 2 ∂observationLaw M)
        atTop (fun _ _ => 0) ∧
      (∀ n a, a ∈ G n → ∀ o,
        fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat (2 * (n + 1)) a o =
          psiCont M phi dphi L hK o (oracle (2 * (n + 1)) a)) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  obtain ⟨oracle, hm, hc, ha, heq, hrate⟩ :=
    contDMLRegime_regular_oracle_nuisance_records M μ S I₁ I₂ pHat phi
      rho gap cpi L ch hK hend eHat hr G hG hLevels
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
    (fun n a => (hc n a).2.1) hsection hrate hr.2.2.1 cpi hov hpol
    (fun n a => (hc n a).2.2)
  refine ⟨oracle, hc, ha, hdiff, hconv, ?_⟩
  intro n a hna o
  exact fittedContScore_eq_oracle_of_component_eq M S I₁ I₂ pHat phi dphi
    rho gap L hK eHat oracle _ a (hLevels n a hna) (heq n a hna) o

end Papers.TbsPrteOptimalTransport
