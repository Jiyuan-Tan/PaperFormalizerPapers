module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryVarianceConsistency
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTargetConclusions
/-! Binary mean and variance consistency centered at the identified lower bound.
Canonical levels supply their measurability, finite-instrument identification
supplies the target, and equality on the recovery event transfers consistency. -/
public section
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

-- @node: equalHalfSplit_binary_lower_bound_mean_variance_consistent
/-- Suppose [the sample is split into equal halves](hyp:hSplit), [the policy
is valid](hyp:hphi) with [the specified derivative](hyp:hd) that is [bounded and
Lipschitz](hyp:hDerivative), [the structural assumptions hold](hyp:hStruct),
[outcome endpoints are known](hyp:hEndpoints), [the instrument admits finite
reduction](hyp:hFinite), [outcomes are binary almost surely](hyp:hy), and
[propensities satisfy gap separation](hyp:hGap). If the canonical levels at
the reference covariate have [positive count](hyp:hK), [invariant order](hyp:hOrder),
[policy overlap](hyp:hov), and [baseline overlap](hyp:hbase), [population nuisances](hyp:he0)
and [all fitted nuisances](hyp:heh) are admissible, [c is positive](hyp:hc),
[the branch separation threshold is positive](hyp:hsep), [fitted level probabilities](hyp:hpi)
and [regular-cell probabilities](hyp:htau) are at least c almost everywhere,
the finite nuisance rate conditions hold for [propensities](hyp:hrp), [baseline
levels](hyp:hrlev), [success regressions](hyp:hrP), [level probabilities](hyp:hrpi),
[shares](hyp:hrs), [cell probabilities](hyp:hrt), [regular weights](hyp:hrg),
[full weights](hyp:hrfull), and [tail weights](hyp:hrtail), [each adjacent pooled
success increment and both distances from the residual success mass to the
adjacent pooled values are at least the separation threshold almost everywhere](hyp:hgap),
[a sample-size-indexed function of the training view and a new observation](hyp:f)
[represents the fitted-minus-population score exactly](hyp:hscore), [that function is measurable
at each sample size](hyp:hf), and [its held-out evaluations are square-integrable](hyp:hfit),
[the binary evaluation average converges in probability to the identified lower
bound and its empirical variance converges in probability to the population
score variance centered at that bound along even sample sizes](goal). -/
lemma equalHalfSplit_binary_lower_bound_mean_variance_consistent
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
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fun n a o => psiBin M phi dphi L hK o (eh n a)
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hEndpoints hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact nuisanceRates_binary_oracle_mean_variance_consistent M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy _ hK hlev hOrder
    cpi hov hbase he0 eh heh c sep hc hsep hpi htau hrp hrlev hrP hrpi hrs hrt
    hrg hrfull hrtail hgap f hscore hf hfit

-- @node: equalHalfSplit_binary_lower_bound_mean_variance_on_recovery
/-- Suppose [the split has equal halves](hyp:hSplit), [the policy is valid](hyp:hphi)
with [the specified derivative](hyp:hd) that is [bounded and Lipschitz](hyp:hDerivative),
[the structural assumptions hold](hyp:hStruct), [outcome endpoints are known](hyp:hEndpoints),
[the instrument admits finite reduction](hyp:hFinite), [outcomes are binary
almost surely](hyp:hy), and [propensities satisfy gap separation](hyp:hGap).
Assume the canonical levels at the reference covariate have [positive count](hyp:hK),
[invariant order](hyp:hOrder), [policy overlap](hyp:hov), and [baseline overlap](hyp:hbase),
[population nuisances](hyp:he0) and [all fitted nuisances](hyp:heh) are admissible,
[c is positive](hyp:hc), [the branch separation threshold is positive](hyp:hsep),
[fitted level probabilities](hyp:hpi) and [regular-cell probabilities](hyp:htau)
are at least c almost everywhere, and the finite nuisance rate conditions hold
for [propensities](hyp:hrp), [baseline levels](hyp:hrlev), [success regressions](hyp:hrP),
[level probabilities](hyp:hrpi), [shares](hyp:hrs), [cell probabilities](hyp:hrt),
[regular weights](hyp:hrg), [full weights](hyp:hrfull), and [tail weights](hyp:hrtail).
If [each adjacent pooled success increment and both distances from the residual
success mass to the adjacent pooled values are at least the separation threshold
almost everywhere](hyp:hgap), [a sample-size-indexed function of the training view
and a new observation](hyp:f) [represents the fitted-minus-population score exactly](hyp:hscore), [the factor is
measurable](hyp:hf) and [has square-integrable held-out evaluations](hyp:hfit),
[recovery events have probability tending to one](hyp:hG), and [the feasible
score agrees with the fitted canonical score at every evaluation observation
on those events](hyp:heq), [the feasible evaluation average converges in probability
to the identified lower bound and its empirical variance converges in probability
to the population score variance centered at that bound along even sample sizes](goal). -/
lemma equalHalfSplit_binary_lower_bound_mean_variance_on_recovery
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
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (feasible : ℕ → A → Obs X Z → ℝ) (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (2 * (n + 1)) a,
      feasible (2 * (n + 1)) a (S.Z i a) =
        psiBin M phi dphi (LevelStructure M.prop (policyProp phi M.prop) x0)
          hK (S.Z i a) (eh (2 * (n + 1)) a)) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ feasible (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have ho := equalHalfSplit_binary_lower_bound_mean_variance_consistent M μ S I₁ I₂
    hSplit phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy x0 hGap hK
    hOrder cpi hov hbase he0 eh heh c sep hc hsep hpi htau hrp hrlev hrP hrpi
    hrs hrt hrg hrfull hrtail hgap f hscore hf hfit
  dsimp only at ho ⊢
  exact dml_mean_variance_transfer_on_recovery M S I₂ feasible
    (fun n a o => psiBin M phi dphi _ hK o (eh n a))
    (fun n => 2 * (n + 1)) G _ _ hG heq ho.1 ho.2

end Papers.TbsPrteOptimalTransport
