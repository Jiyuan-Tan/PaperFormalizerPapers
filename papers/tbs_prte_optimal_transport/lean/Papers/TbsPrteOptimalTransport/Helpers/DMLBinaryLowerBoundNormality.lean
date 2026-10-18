module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryTargetConclusions
/-! Binary lower-bound normality from the oracle remainder and population identification.
The root-n rate follows from the normal limit. These conclusions use the same
component rates and training factorization as the variance consistency theorem. -/
public section
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: equalHalfSplit_binary_lower_bound_clt
/-- Under [equal half-split sampling](hyp:hSplit), [a valid policy map](hyp:hphi),
[its specified derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural assumptions](hyp:hStruct), [known outcome endpoints](hyp:hEndpoints),
[finite instrument reduction](hyp:hFinite), and [almost surely binary outcomes](hyp:hy),
suppose [distinct baseline and policy propensities are separated by a positive gap](hyp:hGap),
[the canonical level count is positive](hyp:hK), [canonical level ordering is covariate invariant](hyp:hOrder),
[policy overlap](hyp:hov) and [baseline overlap](hyp:hbase) hold, and
[the true record](hyp:he0) and [all fitted records](hyp:heh) are admissible.
Assume [a positive fitted denominator bound](hyp:hc), [a positive branch-separation bound](hyp:hsep),
almost sure lower bounds on fitted [baseline masses](hyp:hpi) and [regular group masses](hyp:htau),
and finite nuisance rates for [propensities](hyp:hrp), [baseline level propensities](hyp:hrlev),
[treated-success regressions](hyp:hrP), [baseline masses](hyp:hrpi), [each group's shares](hyp:hrs),
[regular masses](hyp:hrt), [regular policy-union probability weights](hyp:hrg), [higher-policy minus higher-baseline probability weights](hyp:hrfull),
and [the tail policy probability](hyp:hrtail). If [adjacent true pooled policy levels are separated,
and both endpoints stay separated from the adjusted next baseline level](hyp:hgap), and
[the fitted-minus-true score factors through training data and an observation](hyp:hscore)
via [a sample-size-indexed function of the training view and a new observation](hyp:f)
with [a measurable factor](hyp:hf), [square-integrable sections](hyp:hsection), and
[square-integrable evaluation rows](hyp:hfit), then
[the estimator's error relative to the population transport lower bound, scaled by the square root
of the evaluation-sample size, converges in distribution to a centered normal law
with the true score's population variance around that bound](goal). -/
lemma equalHalfSplit_binary_lower_bound_clt
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hEndpoints : OutcomeEndpointsKnown M)
    (hFinite : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ) (hov : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hbase : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (he0 : BinAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0))) (eh : ℕ → A → NuisanceBin (LevelStructure M.prop (policyProp phi M.prop) x0))
    (heh : ∀ n a, BinAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0) (eh n a))
    (c sep : ℝ) (hc : 0 < c) (hsep : 0 < sep)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).piLev)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).tauLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).gammaTail))
    (hgap : ∀ k ∈ Finset.range (LevelStructure M.prop (policyProp phi M.prop) x0).K, ∀ j ∈ Finset.Icc 1 ((LevelStructure M.prop (policyProp phi M.prop) x0).l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k j x -
        pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).pLev (k + 1) x -
        binFullJ (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k x -
        pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).pLev (k + 1) x -
        binFullJ (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k x -
        pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k j x|)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiBin M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0) hK o (eh (2 * (n + 1)) a) -
        psiBin M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0) hK o (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hsection : ∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fun n a o => psiBin M phi dphi L hK o (eh n a)
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hEndpoints hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact nuisanceRates_binary_oracle_dmlRV_clt M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy _ hK hlev hOrder
    cpi hov hbase he0 eh heh c sep hc hsep hpi htau hrp hrlev hrP hrpi hrs hrt
    hrg hrfull hrtail hgap f hscore hf hsection hfit

-- @node: equalHalfSplit_binary_lower_bound_rootn
/-- Suppose [sampling uses equal halves](hyp:hSplit), [the policy map is valid](hyp:hphi),
[its derivative is correctly specified](hyp:hd) and [bounded and Lipschitz](hyp:hDerivative),
[the structural assumptions hold](hyp:hStruct), [outcome endpoints are known](hyp:hEndpoints),
[the instrument admits finite reduction](hyp:hFinite), and [outcomes are almost surely binary](hyp:hy).
Assume [positive separation of distinct baseline and policy propensities](hyp:hGap),
[a positive canonical level count](hyp:hK), [covariate-invariant canonical level ordering](hyp:hOrder),
[policy overlap](hyp:hov), [baseline overlap](hyp:hbase), [an admissible true record](hyp:he0),
[admissible fitted records](hyp:heh), [a positive denominator bound](hyp:hc),
[a positive branch-separation bound](hyp:hsep), and almost sure lower bounds on fitted
[baseline masses](hyp:hpi) and [regular masses](hyp:htau).
Require finite nuisance rates for [instrument propensities](hyp:hrp), [baseline level propensities](hyp:hrlev),
[treated-success regressions](hyp:hrP), [baseline masses](hyp:hrpi), [shares in each group](hyp:hrs),
[regular masses](hyp:hrt), [regular policy-union probability weights](hyp:hrg), [higher-policy minus higher-baseline probability weights](hyp:hrfull),
and [the tail policy probability](hyp:hrtail), together with [separated adjacent true pooled policy levels
and separation of their endpoints from the adjusted next baseline level](hyp:hgap).
If [the score error factors through training data and an observation](hyp:hscore) via
[a sample-size-indexed function of the training view and a new observation](hyp:f) with
[a measurable factor](hyp:hf), [square-integrable sections](hyp:hsection), and
[square-integrable evaluation rows](hyp:hfit), then
[the estimator's error relative to the population transport lower bound is bounded
in probability at the inverse square root of the total sample size](goal). -/
lemma equalHalfSplit_binary_lower_bound_rootn
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hEndpoints : OutcomeEndpointsKnown M)
    (hFinite : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ) (hov : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hbase : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (he0 : BinAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0))) (eh : ℕ → A → NuisanceBin (LevelStructure M.prop (policyProp phi M.prop) x0))
    (heh : ∀ n a, BinAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0) (eh n a))
    (c sep : ℝ) (hc : 0 < c) (hsep : 0 < sep)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).piLev)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).tauLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).gammaTail))
    (hgap : ∀ k ∈ Finset.range (LevelStructure M.prop (policyProp phi M.prop) x0).K, ∀ j ∈ Finset.Icc 1 ((LevelStructure M.prop (policyProp phi M.prop) x0).l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k j x -
        pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).pLev (k + 1) x -
        binFullJ (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k x -
        pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).pLev (k + 1) x -
        binFullJ (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k x -
        pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k j x|)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiBin M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0) hK o (eh (2 * (n + 1)) a) -
        psiBin M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0) hK o (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hsection : ∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fun n a o => psiBin M phi dphi L hK o (eh n a)
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ := by
  have hlaw := equalHalfSplit_binary_lower_bound_clt M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy x0 hGap hK
    hOrder cpi hov hbase he0 eh heh c sep hc hsep hpi htau hrp hrlev hrP hrpi
    hrs hrt hrg hrfull hrtail hgap f hscore hf hsection hfit
  exact dml_rootn_consistent_of_normal_limit μ _ _ _ hlaw

-- @node: equalHalfSplit_binary_lower_bound_conclusions_on_recovery
/-- Assume [equal half-split sampling](hyp:hSplit), [a valid policy map](hyp:hphi),
[its specified derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural assumptions](hyp:hStruct), [known outcome endpoints](hyp:hEndpoints),
[finite instrument reduction](hyp:hFinite), and [almost surely binary outcomes](hyp:hy).
Suppose [distinct baseline and policy propensities have a positive separation gap](hyp:hGap),
[the canonical level count is positive](hyp:hK), [canonical level ordering is covariate invariant](hyp:hOrder),
[policy overlap](hyp:hov) and [baseline overlap](hyp:hbase) hold,
[the true record](hyp:he0) and [every fitted record](hyp:heh) are admissible,
[the fitted denominator bound](hyp:hc) and [the branch-separation bound](hyp:hsep) are positive,
and fitted [baseline masses](hyp:hpi) and [regular masses](hyp:htau) exceed the denominator bound almost surely.
Assume finite nuisance rates for [propensities](hyp:hrp), [baseline level propensities](hyp:hrlev),
[treated-success regressions](hyp:hrP), [baseline masses](hyp:hrpi), [each group's shares](hyp:hrs),
[regular masses](hyp:hrt), [regular policy-union probability weights](hyp:hrg), [higher-policy minus higher-baseline probability weights](hyp:hrfull),
and [the tail policy probability](hyp:hrtail), with [adjacent true pooled policy levels separated
and both endpoints separated from the adjusted next baseline level](hyp:hgap).
Require [a sample-size-indexed function of the training view and a new observation](hyp:f)
[that represents the fitted-minus-true score exactly](hyp:hscore),
[measurability of its factor](hyp:hf), [square-integrable sections](hyp:hsection), and
[square-integrable evaluation rows](hyp:hfit). If [the recovery-event complements have
probability tending to zero](hyp:hG), [the feasible and oracle scores agree on all evaluation
observations on those events](hyp:heq), and [each feasible evaluation row is almost everywhere measurable](hyp:hrow),
then [the feasible estimator is root-total-sample-size consistent for the population transport
lower bound, its error scaled by the square root of the evaluation-sample size has a centered
normal limit with the true score's population variance, and its empirical variance converges
in probability to that same population variance](goal). -/
lemma equalHalfSplit_binary_lower_bound_conclusions_on_recovery
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hEndpoints : OutcomeEndpointsKnown M)
    (hFinite : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ) (hov : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hbase : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (he0 : BinAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0))) (eh : ℕ → A → NuisanceBin (LevelStructure M.prop (policyProp phi M.prop) x0))
    (heh : ∀ n a, BinAdmissible M (LevelStructure M.prop (policyProp phi M.prop) x0) (eh n a))
    (c sep : ℝ) (hc : 0 < c) (hsep : 0 < sep)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).piLev)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).tauLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).gammaTail))
    (hgap : ∀ k ∈ Finset.range (LevelStructure M.prop (policyProp phi M.prop) x0).K, ∀ j ∈ Finset.Icc 1 ((LevelStructure M.prop (policyProp phi M.prop) x0).l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k j x -
        pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).pLev (k + 1) x -
        binFullJ (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k x -
        pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)).pLev (k + 1) x -
        binFullJ (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k x -
        pooledQBin phi (LevelStructure M.prop (policyProp phi M.prop) x0) (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) k j x|)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiBin M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0) hK o (eh (2 * (n + 1)) a) -
        psiBin M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0) hK o (eta0Bin M (LevelStructure M.prop (policyProp phi M.prop) x0)) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hsection : ∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (feasible : ℕ → A → Obs X Z → ℝ) (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (2 * (n + 1)) a,
      feasible (2 * (n + 1)) a (S.Z i a) =
        psiBin M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0)
          hK (S.Z i a) (eh (2 * (n + 1)) a))
    (hrow : ∀ n i, AEMeasurable (fun a => feasible (2 * (n + 1)) a
      (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) μ) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ ∧
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ feasible (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have hlaw := equalHalfSplit_binary_lower_bound_clt M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy x0 hGap hK
    hOrder cpi hov hbase he0 eh heh c sep hc hsep hpi htau hrp hrlev hrP hrpi
    hrs hrt hrg hrfull hrtail hgap f hscore hf hsection hfit
  have hv := equalHalfSplit_binary_lower_bound_mean_variance_consistent M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy x0 hGap hK
    hOrder cpi hov hbase he0 eh heh c sep hc hsep hpi htau hrp hrlev hrP hrpi
    hrs hrt hrg hrfull hrtail hgap f hscore hf hfit
  have hm := equalHalfSplit_dmlRV_aemeasurable_of_evaluation_rows M μ S I₁ I₂
    hSplit feasible hrow
  dsimp only at hlaw hv ⊢
  exact dml_conclusions_transfer_on_recovery M μ S I₂ feasible
    (fun n a o => psiBin M phi dphi _ hK o (eh n a)) G _ _ hG heq
    (fun n => ((hm n).sub_const _).const_mul _)
    (dml_rootn_consistent_of_normal_limit μ _ _ _ hlaw) hlaw hv.2

end Papers.TbsPrteOptimalTransport
