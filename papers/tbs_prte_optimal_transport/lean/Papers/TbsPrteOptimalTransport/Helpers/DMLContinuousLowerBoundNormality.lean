module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTargetConclusions
/-! True continuous-score oracle variance consistency and lower-bound root-n rate.
The evaluation LLN and the population score identity establish variance consistency;
the oracle CLT yields the rate by tightness. Finite-instrument identification
centers both conclusions at the paper's lower-bound target. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z]

-- @node: equalHalfSplit_true_continuous_target_variance_consistent
/-- Under [an equal half-sample split](hyp:hSplit), [a valid policy map](hyp:hphi),
[the specified policy derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[a positive level count](hyp:hK), [invariant level ordering](hyp:hOrder),
[measurable baseline levels](hyp:hlev), [admissibility of the true nuisance](hyp:he0),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [measurable band boundaries](hyp:hb),
[bounded boundary densities](hyp:hDensity), and [no atom at the lower endpoint](hyp:h0),
[the empirical variance of the true continuous score converges in probability,
along even sample sizes, to its population variance centered at the discrete
lower target](goal). -/
lemma equalHalfSplit_true_continuous_target_variance_consistent
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
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_continuous_score_mean_eq_target M hStruct hend
    phi dphi hphi hdphi hDerivative L hK hOrder hlev cpi hov hpol hb hDensity h0).2
  have hLp := true_continuous_total_score_memLp_of_overlap M phi dphi hphi hd
    hDerivative L hK he0 hStruct.1 hStruct.2.1 hend cpi hov hpol
  apply equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp
    M μ S I₁ I₂ hSplit _ _ hLp _ hmean
  -- The empirical error is identically zero for the true-score oracle.
  simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, mul_zero]
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
  intro eps heps
  simpa only [sub_zero, norm_zero, not_le.mpr heps, Set.ofPred_false, measure_empty]
    using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))

-- @node: equalHalfSplit_true_continuous_lower_bound_variance_consistent
/-- Assume [an equal half-sample split](hyp:hSplit), [a valid policy map](hyp:hphi),
[the specified policy derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[separated propensity gaps](hyp:hGap), [invariant level ordering](hyp:hOrder),
[finite-instrument reduction](hyp:hFinite), [a positive level count](hyp:hK),
[admissibility of the true nuisance](hyp:he0), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [bounded boundary densities](hyp:hDensity), and
[no atom at the lower endpoint](hyp:h0) for the structure at the reference covariate.
Then [the empirical variance of the true continuous score converges in probability,
along even sample sizes, to its population variance centered at the transport
lower bound](goal). -/
lemma equalHalfSplit_true_continuous_lower_bound_variance_consistent
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
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a) atTop
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
  exact equalHalfSplit_true_continuous_target_variance_consistent M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend _ hK hOrder hlev he0 cpi hov hpol
    (fun k hk j hj => hb k j hk hj) hDensity h0

-- @node: equalHalfSplit_true_continuous_lower_bound_rootn
/-- Under [an equal half-sample split](hyp:hSplit), [a valid policy map](hyp:hphi),
[the specified policy derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[separated propensity gaps](hyp:hGap), [invariant level ordering](hyp:hOrder),
[finite-instrument reduction](hyp:hFinite), [a positive level count](hyp:hK),
[admissibility of the true nuisance](hyp:he0), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [bounded boundary densities](hyp:hDensity), and
[no atom at the lower endpoint](hyp:h0), [the true-score sample mean minus the
transport lower bound is of order in probability the inverse square root of the
total sample size, along even sample sizes](goal). -/
lemma equalHalfSplit_true_continuous_lower_bound_rootn
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
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ := by
  have hlaw := equalHalfSplit_true_continuous_lower_bound_clt M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend x0 hGap hOrder hFinite hK
    he0 cpi hov hpol hDensity h0
  exact dml_rootn_consistent_of_normal_limit μ _ _ _ hlaw

end Papers.TbsPrteOptimalTransport
