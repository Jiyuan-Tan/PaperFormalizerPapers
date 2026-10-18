module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryOracleConclusions
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryScoreMean
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTargetConclusions
/-! True binary-score oracle variance consistency, normality and root-n rate.
Overlap supplies finite second moments; the evaluation LLN and population
score identity give variance consistency before the oracle CLT and tightness. -/
public section
set_option linter.style.openClassical false

set_option linter.style.longLine false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: equalHalfSplit_true_binary_target_variance_consistent
/-- Assume [an equal half split](hyp:hSplit), [a measurable probability-valued policy](hyp:hphi), [its correct derivative](hyp:hd), [a uniformly bounded propensity-Lipschitz derivative](hyp:hDerivative), [the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend), [outcomes supported almost surely on those two endpoints](hyp:hy), and [a finite instrument reduction](hyp:hFinite). With [a positive level count](hyp:hK), [a covariate-invariant ordering of baseline and policy propensity levels](hyp:hOrder), [measurable baseline level propensities](hyp:hlev), [admissible true binary nuisances](hyp:he0), [baseline overlap at the chosen constant](hyp:hov), and [policy overlap at that constant](hyp:hpol), [the empirical variance of the true binary score on the evaluation half converges in probability to its population second moment centered at the discrete target](goal). -/
lemma equalHalfSplit_true_binary_target_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hy : OutcomeBinaryAE M)
    (hFinite : InstrumentFiniteReduction Z)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (he0 : BinAdmissible M L (eta0Bin M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi) :
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_binary_score_mean_eq_target M hStruct hend hFinite
    phi dphi hphi hdphi hDerivative L hK hOrder hlev cpi hov hpol hy he0).2
  have hpi (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).piLev i x :=
    Eventually.of_forall (fun x => hov.2 x i i.property.1 i.property.2)
  have htau (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev r x :=
    Eventually.of_forall (fun x => hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have hLp := fitted_binary_score_memLp M phi dphi hphi hd hDerivative L hK
    (eta0Bin M L) he0 hy cpi hov.1 hpi htau
  apply equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp
    M μ S I₁ I₂ hSplit _ _ hLp _ hmean
  -- The empirical error is identically zero for the true-score oracle.
  simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, mul_zero]
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
  intro eps heps
  simpa only [sub_zero, norm_zero, not_le.mpr heps, Set.ofPred_false, measure_empty]
    using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))

-- @node: equalHalfSplit_true_binary_target_clt
/-- Assume [an equal half split](hyp:hSplit), [a measurable probability-valued policy](hyp:hphi), [its correct derivative](hyp:hd), [a uniformly bounded propensity-Lipschitz derivative](hyp:hDerivative), [the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend), [binary outcomes almost surely](hyp:hy), and [a finite instrument reduction](hyp:hFinite). Under [a positive level count](hyp:hK), [a covariate-invariant ordering of baseline and policy propensity levels](hyp:hOrder), [measurable baseline level propensities](hyp:hlev), [admissible true binary nuisances](hyp:he0), [baseline overlap](hyp:hov), and [policy overlap at the same constant](hyp:hpol), [the oracle evaluation average minus the discrete target, multiplied by the square root of the evaluation sample size, converges in distribution to a centered Gaussian with the population score variance](goal). -/
lemma equalHalfSplit_true_binary_target_clt
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hy : OutcomeBinaryAE M)
    (hFinite : InstrumentFiniteReduction Z)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (he0 : BinAdmissible M L (eta0Bin M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi) :
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_binary_score_mean_eq_target M hStruct hend hFinite
    phi dphi hphi hdphi hDerivative L hK hOrder hlev cpi hov hpol hy he0).2
  have hpi (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).piLev i x :=
    Eventually.of_forall (fun x => hov.2 x i i.property.1 i.property.2)
  have htau (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev r x :=
    Eventually.of_forall (fun x => hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have hLp := fitted_binary_score_memLp M phi dphi hphi hd hDerivative L hK
    (eta0Bin M L) he0 hy cpi hov.1 hpi htau
  exact equalHalfSplit_oracle_dmlRV_clt_of_memLp M μ S I₁ I₂ hSplit
    _ hLp _ hmean

-- @node: equalHalfSplit_true_binary_lower_bound_clt
/-- Assume [an equal half split](hyp:hSplit), [a measurable probability-valued policy](hyp:hphi), [its correct derivative](hyp:hd), [a uniformly bounded propensity-Lipschitz derivative](hyp:hDerivative), [the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend), and [binary outcomes almost surely](hyp:hy). If [baseline and policy propensity gaps are separated](hyp:hGap), [their level ordering from the reference covariate is covariate-invariant](hyp:hOrder), [the instrument admits a finite reduction](hyp:hFinite), [the resulting level count is positive](hyp:hK), [the true binary nuisances are admissible](hyp:he0), and [baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold at the chosen constant, [the true-score evaluation average centered at the transport lower bound and multiplied by the square root of the evaluation sample size converges in distribution to a centered Gaussian with the population score variance](goal). -/
lemma equalHalfSplit_true_binary_lower_bound_clt
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hy : OutcomeBinaryAE M)
    (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (he0 : BinAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M
      (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hend hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact equalHalfSplit_true_binary_target_clt M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend hy hFinite _ hK hOrder hlev he0 cpi hov hpol

-- @node: equalHalfSplit_true_binary_lower_bound_variance_consistent
/-- Assume [an equal half split](hyp:hSplit), [a measurable probability-valued policy](hyp:hphi), [its correct derivative](hyp:hd), [a uniformly bounded propensity-Lipschitz derivative](hyp:hDerivative), [the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend), and [binary outcomes almost surely](hyp:hy). If [baseline and policy propensity gaps are separated](hyp:hGap), [the level ordering determined at the reference covariate is covariate-invariant](hyp:hOrder), [the instrument admits a finite reduction](hyp:hFinite), [the level count is positive](hyp:hK), [the true binary nuisances are admissible](hyp:he0), and [baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold at the chosen constant, [the empirical variance of the oracle evaluation scores converges in probability to their population second moment centered at the transport lower bound](goal). -/
lemma equalHalfSplit_true_binary_lower_bound_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hy : OutcomeBinaryAE M)
    (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (he0 : BinAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M
      (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hend hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact equalHalfSplit_true_binary_target_variance_consistent M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend hy hFinite _ hK hOrder hlev he0 cpi hov hpol

-- @node: equalHalfSplit_true_binary_lower_bound_rootn
/-- Assume [an equal half split](hyp:hSplit), [a measurable probability-valued policy](hyp:hphi), [its correct derivative](hyp:hd), [a uniformly bounded propensity-Lipschitz derivative](hyp:hDerivative), [the structural model assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend), and [binary outcomes almost surely](hyp:hy). With [separated baseline and policy propensity gaps](hyp:hGap), [a covariate-invariant level ordering determined at the reference covariate](hyp:hOrder), [a finite instrument reduction](hyp:hFinite), [a positive level count](hyp:hK), [admissible true binary nuisances](hyp:he0), [baseline overlap](hyp:hov), and [policy overlap](hyp:hpol), [the oracle evaluation average estimates the transport lower bound with error bounded in probability at the inverse-square-root total-sample-size rate](goal). -/
lemma equalHalfSplit_true_binary_lower_bound_rootn
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hy : OutcomeBinaryAE M)
    (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (he0 : BinAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0)
      (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M
      (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ := by
  have hlaw := equalHalfSplit_true_binary_lower_bound_clt M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend hy x0 hGap hOrder hFinite hK
    he0 cpi hov hpol
  exact dml_rootn_consistent_of_normal_limit μ _ _ _ hlaw

end Papers.TbsPrteOptimalTransport
