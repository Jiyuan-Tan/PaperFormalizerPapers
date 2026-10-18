module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIntegrableEvaluationLLN
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleNormality
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRootNConsistency
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousTarget
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBoundaries
/-! Target-centered continuous oracle variance consistency and true-score normality.
The population score identity supplies the centering in the evaluation LLNs and
IID oracle CLT. The fitted-score variance conclusion uses nuisance convergence,
without assuming a score-bias rate or a normal limit. -/
public section
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z]

-- @node: equalHalfSplit_encoded_continuous_target_mean_variance_consistent
/-- Under [an equal training/evaluation split](hyp:hSplit), assume [a valid policy](hyp:hphi)
[with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative),
[at least one positive level](hyp:hK), [policy-invariant level order](hyp:hOrder),
[the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
and [admissible true nuisances](hyp:he0).
Suppose [fitted nuisances obey clipping restrictions](hyp:hclip), [fitted shares form a simplex](hyp:hshares),
[all fitted coordinates are measurable in covariates](hyp:hm), [encoded coordinates satisfy the finite-coordinate nuisance rate conditions](hyp:hr),
[baseline levels are measurable](hyp:hlev), [band boundaries are measurable](hyp:hb),
[there is no atom at the lower outcome endpoint](hyp:h0), [boundary densities are bounded](hyp:hDensity),
[baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold, and [fitted denominators obey the overlap clipping threshold](hyp:hden).
For [a representation of score error as a function of the training view and a new observation](hyp:f), assume
[this representation equals the fitted-minus-true score](hyp:hscore), [is measurable](hyp:hf),
and [has finite second moments at indexed evaluation observations](hyp:hfit).
Then [the evaluation-half fitted-score average converges in probability to the discrete policy target, and its empirical variance converges to the true score's population variance centered at that target, along even sample sizes](goal). -/
lemma equalHalfSplit_encoded_continuous_target_mean_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a d, Measurable (contComponent M L (eh n a) d))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (hlev : ∀ k, Measurable (L.pLev k))
    (hb : ∀ k < L.K, ∀ j ≤ L.l k, Measurable (bandBoundary M L k j))
    (h0 : NoAtomAtLowerEndpoint M L)
    (hDensity : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
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
    let score := fun n a o => psiCont M phi dphi L hK o (eh n a)
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_continuous_score_mean_eq_target M hStruct hend
    phi dphi hphi hdphi hDerivative L hK hOrder hlev cpi hov hpol hb hDensity h0).2
  have hc := equalHalfSplit_encoded_continuous_mean_variance_consistent
    M μ S I₁ I₂ hSplit hStruct.2.2.2.1 phi dphi hphi hd hDerivative L hK hOrder
    hStruct.1 hStruct.2.1 hend he0 eh hclip hshares hm hr hDensity cpi hov hpol
    hden f hscore hf hfit
  dsimp only at hc ⊢
  rwa [hmean] at hc

-- @node: equalHalfSplit_true_continuous_target_clt
/-- Under [an equal training/evaluation split](hyp:hSplit), assume [a valid policy](hyp:hphi)
[with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative),
[the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[at least one positive level](hyp:hK), [policy-invariant level order](hyp:hOrder),
[measurable baseline levels](hyp:hlev), and [admissible true nuisances](hyp:he0).
If [baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold, [band boundaries are measurable](hyp:hb),
[boundary densities are bounded](hyp:hDensity), and [there is no atom at the lower outcome endpoint](hyp:h0), then
[the true-score evaluation average minus the discrete policy target, multiplied by the square root of the evaluation-half size, converges in law to a centered Gaussian with variance equal to the true score's population variance](goal). -/
lemma equalHalfSplit_true_continuous_target_clt
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
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hb : ∀ k < L.K, ∀ j ≤ L.l k, Measurable (bandBoundary M L k j))
    (hDensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L) :
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_continuous_score_mean_eq_target M hStruct hend
    phi dphi hphi hdphi hDerivative L hK hOrder hlev cpi hov hpol hb hDensity h0).2
  have hLp := true_continuous_total_score_memLp_of_overlap M phi dphi hphi hd
    hDerivative L hK he0 hStruct.1 hStruct.2.1 hend cpi hov hpol
  exact equalHalfSplit_oracle_dmlRV_clt_of_memLp M μ S I₁ I₂ hSplit
    _ hLp _ hmean

-- @node: equalHalfSplit_true_continuous_target_rootn
/-- Under [an equal training/evaluation split](hyp:hSplit), suppose [the policy is valid](hyp:hphi),
[has the specified derivative](hyp:hd), and [has a bounded, Lipschitz derivative](hyp:hDerivative).
Assume [the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[at least one positive level](hyp:hK), [policy-invariant level order](hyp:hOrder),
[measurable baseline levels](hyp:hlev), [admissible true nuisances](hyp:he0),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [measurable band boundaries](hyp:hb),
[bounded boundary densities](hyp:hDensity), and [no atom at the lower outcome endpoint](hyp:h0).
Then [the true-score evaluation average estimates the discrete policy target with an error of order the inverse square root of the full sample size in probability along even sample sizes](goal). -/
lemma equalHalfSplit_true_continuous_target_rootn
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
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hb : ∀ k < L.K, ∀ j ≤ L.l k, Measurable (bandBoundary M L k j))
    (hDensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L) :
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ := by
  have hlaw := equalHalfSplit_true_continuous_target_clt M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend L hK hOrder hlev he0 cpi hov hpol
    hb hDensity h0
  exact dml_rootn_consistent_of_normal_limit μ _ _ _ hlaw

-- The canonical level structure supplies measurable levels and boundaries.
-- Finite-instrument identification converts the oracle centering to thetaLower1.
-- @node: equalHalfSplit_true_continuous_lower_bound_clt
/-- Under [an equal training/evaluation split](hyp:hSplit), assume [a valid policy](hyp:hphi)
[with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative),
[the structural model assumptions](hyp:hStruct), and [known outcome endpoints](hyp:hend).
For the canonical level structure at the reference covariate, suppose [propensity gaps are separated](hyp:hGap),
[level order is policy invariant](hyp:hOrder), [the instrument admits finite reduction](hyp:hFinite),
[there is at least one positive level](hyp:hK), [true nuisances are admissible](hyp:he0),
[baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold,
[boundary densities are bounded](hyp:hDensity), and [there is no atom at the lower outcome endpoint](hyp:h0).
Then [the true-score evaluation average centered at the identified lower bound, multiplied by the square root of the evaluation-half size, converges in law to a centered Gaussian with variance equal to the true score's population variance about that bound](goal). -/
lemma equalHalfSplit_true_continuous_lower_bound_clt
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (he0 : ContAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0)
      (trueNuisance M (LevelStructure M.prop (policyProp phi M.prop) x0)))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M
      (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hDensity : BoundaryDensitiesBounded M
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (h0 : NoAtomAtLowerEndpoint M (LevelStructure M.prop (policyProp phi M.prop) x0)) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have hq := population_policyProp_measurable M hStruct.2.2.2.1 phi hphi
  have hb := population_bandBoundary_measurable M (policyProp phi M.prop) hq
    _ hOrder hlev
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hend hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact equalHalfSplit_true_continuous_target_clt M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend _ hK hOrder hlev he0 cpi hov hpol
    (fun k hk j hj => hb k j hk hj) hDensity h0

-- Point and variance consistency transfer separately; neither needs a CLT.
omit [Fintype Z] in
-- @node: dml_mean_variance_transfer_on_recovery
/-- If [the probability of failure of the recovery events tends to zero](hyp:hG),
[feasible and oracle scores agree at every evaluation observation on each recovery event](hyp:heq),
[the oracle evaluation average converges in probability to the target](hyp:hmean), and
[the oracle empirical variance converges in probability to the specified variance](hyp:hvar), then
[the feasible evaluation average and empirical variance converge in probability to the same target and variance along the chosen sample-size sequence](goal). -/
lemma dml_mean_variance_transfer_on_recovery
    (M : LatentIVModel Ω X Z) {μ : Measure A} (S : ObservedSample M μ)
    (I₂ : SampleSplit A) (feasible oracle : ℕ → A → Obs X Z → ℝ)
    (N : ℕ → ℕ) (G : ℕ → Set A) (theta sigmaSq : ℝ)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (N n) a,
      feasible (N n) a (S.Z i a) = oracle (N n) a (S.Z i a))
    (hmean : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ oracle (N n) a - theta) atTop (fun _ _ => 0))
    (hvar : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ oracle (N n) a) atTop (fun _ _ => sigmaSq)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ feasible (N n) a - theta) atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ feasible (N n) a) atTop (fun _ _ => sigmaSq) := by
  constructor
  · apply probability_limit_transfer_on_recovery μ G _ _ 0 hG _ hmean
    intro n a ha
    rw [dmlRV_eq_of_score_eq_on_sample M S I₂ feasible oracle (N n) a (heq n a ha)]
  · apply probability_limit_transfer_on_recovery μ G _ _ sigmaSq hG _ hvar
    intro n a ha
    exact varianceRV_eq_of_score_eq_on_sample M S I₂ feasible oracle (N n) a (heq n a ha)

-- @node: equalHalfSplit_encoded_continuous_lower_bound_mean_variance_consistent
/-- Under [an equal training/evaluation split](hyp:hSplit), assume [a valid policy](hyp:hphi)
[with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative).
For the canonical level structure at the reference covariate, suppose [propensity gaps are separated](hyp:hGap),
[the instrument admits finite reduction](hyp:hFinite), [there is at least one positive level](hyp:hK),
[level order is policy invariant](hyp:hOrder), [the structural model assumptions hold](hyp:hStruct),
[outcome endpoints are known](hyp:hend), and [true nuisances are admissible](hyp:he0).
Assume [fitted nuisances obey clipping restrictions](hyp:hclip), [fitted shares form a simplex](hyp:hshares),
[fitted coordinates are measurable in covariates](hyp:hm), [encoded nuisance coordinates satisfy the finite-coordinate rate conditions](hyp:hr),
[there is no atom at the lower outcome endpoint](hyp:h0), [boundary densities are bounded](hyp:hDensity),
[baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold, and [fitted denominators obey the overlap clipping threshold](hyp:hden).
For [a representation of score error using the training view and a new observation](hyp:f), suppose
[it equals the fitted-minus-true score](hyp:hscore), [is measurable](hyp:hf), and
[has finite second moments at indexed evaluation observations](hyp:hfit).
Then [the fitted-score evaluation average converges in probability to the identified lower bound and its empirical variance converges to the true score's population variance about that bound along even sample sizes](goal). -/
lemma equalHalfSplit_encoded_continuous_lower_bound_mean_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (he0 : ContAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0)
      (trueNuisance M (LevelStructure M.prop (policyProp phi M.prop) x0)))
    (eh : ℕ → A → NuisanceCont (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hclip : ∀ n a, ContClipping M (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a))
    (hm : ∀ n a d, Measurable (contComponent M
      (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a) d))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M
      (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a))
      (contComponent M
      (LevelStructure M.prop (policyProp phi M.prop) x0)
      (trueNuisance M (LevelStructure M.prop (policyProp phi M.prop) x0))))
    (h0 : NoAtomAtLowerEndpoint M (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hDensity : BoundaryDensitiesBounded M (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ) (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hden : ∀ n a, ContDenominatorsClipped (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a) cpi)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiCont M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0)
        hK o (eh (2 * (n + 1)) a) -
        psiCont M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0)
        hK o
          (trueNuisance M (LevelStructure M.prop (policyProp phi M.prop) x0)) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fun n a o => psiCont M phi dphi L hK o (eh n a)
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have hq := population_policyProp_measurable M hStruct.2.2.2.1 phi hphi
  have hb := population_bandBoundary_measurable M (policyProp phi M.prop) hq
    _ hOrder hlev
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hend hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact equalHalfSplit_encoded_continuous_target_mean_variance_consistent
    M μ S I₁ I₂ hSplit phi dphi hphi hd hDerivative _ hK hOrder hStruct hend
    he0 eh hclip hshares hm hr hlev (fun k hk j hj => hb k j hk hj)
    h0 hDensity cpi hov hpol hden
    f hscore hf hfit

-- @node: equalHalfSplit_continuous_lower_bound_mean_variance_on_recovery
/-- Under [an equal training/evaluation split](hyp:hSplit), assume [a valid policy](hyp:hphi)
[with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative).
For the canonical level structure at the reference covariate, suppose [propensity gaps are separated](hyp:hGap),
[the instrument admits finite reduction](hyp:hFinite), [there is at least one positive level](hyp:hK),
[level order is policy invariant](hyp:hOrder), [the structural model assumptions hold](hyp:hStruct),
[outcome endpoints are known](hyp:hend), and [true nuisances are admissible](hyp:he0).
Assume [fitted nuisances obey clipping restrictions](hyp:hclip), [fitted shares form a simplex](hyp:hshares),
[fitted coordinates are measurable in covariates](hyp:hm), [encoded coordinates satisfy the finite-coordinate nuisance rate conditions](hyp:hr),
[there is no atom at the lower outcome endpoint](hyp:h0), [boundary densities are bounded](hyp:hDensity),
[baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold, and [fitted denominators obey the overlap clipping threshold](hyp:hden).
For [a representation of score error using the training view and a new observation](hyp:f), suppose
[it equals the fitted-minus-true score](hyp:hscore), [is measurable](hyp:hf), and
[has finite second moments at indexed evaluation observations](hyp:hfit).
If [recovery failure probability tends to zero](hyp:hG) and [the feasible score equals the fitted canonical score at every evaluation observation on recovery](hyp:heq), then
[the feasible evaluation average converges in probability to the identified lower bound and its empirical variance converges to the true score's population variance about that bound along even sample sizes](goal). -/
lemma equalHalfSplit_continuous_lower_bound_mean_variance_on_recovery
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (he0 : ContAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0)
      (trueNuisance M (LevelStructure M.prop (policyProp phi M.prop) x0)))
    (eh : ℕ → A → NuisanceCont (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hclip : ∀ n a, ContClipping M (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a))
    (hm : ∀ n a d, Measurable (contComponent M
      (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a) d))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M
      (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a))
      (contComponent M
      (LevelStructure M.prop (policyProp phi M.prop) x0)
      (trueNuisance M (LevelStructure M.prop (policyProp phi M.prop) x0))))
    (h0 : NoAtomAtLowerEndpoint M (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hDensity : BoundaryDensitiesBounded M (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ) (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hden : ∀ n a, ContDenominatorsClipped (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eh n a) cpi)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiCont M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0)
        hK o (eh (2 * (n + 1)) a) -
        psiCont M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0)
        hK o
          (trueNuisance M (LevelStructure M.prop (policyProp phi M.prop) x0)) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (feasible : ℕ → A → Obs X Z → ℝ) (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (2 * (n + 1)) a,
      feasible (2 * (n + 1)) a (S.Z i a) =
        psiCont M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0)
          hK (S.Z i a) (eh (2 * (n + 1)) a)) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ feasible (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have ho := equalHalfSplit_encoded_continuous_lower_bound_mean_variance_consistent
    M μ S I₁ I₂ hSplit phi dphi hphi hd hDerivative x0 hGap hFinite hK hOrder
    hStruct hend he0 eh hclip hshares hm hr
    h0 hDensity cpi hov hpol hden
    f hscore hf hfit
  dsimp only at ho ⊢
  exact dml_mean_variance_transfer_on_recovery M S I₂ feasible
    (fun n a o => psiCont M phi dphi _ hK o (eh n a))
    (fun n => 2 * (n + 1)) G _ _ hG heq ho.1 ho.2

end Papers.TbsPrteOptimalTransport
