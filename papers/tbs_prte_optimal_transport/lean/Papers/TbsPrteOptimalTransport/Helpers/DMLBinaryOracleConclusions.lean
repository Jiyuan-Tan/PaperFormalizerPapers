module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRootNConsistency
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryOracleMoments
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryVarianceConsistency
/-! Binary oracle DML conclusions from componentwise nuisance rates.
The population score convergence and conditional empirical-energy argument
supply variance consistency, alongside the proved oracle normal limit. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_binary_oracle_dml_conclusions
/-- Suppose [the sample is split into equal halves](hyp:hSplit),
[the policy map is valid](hyp:hphi), [its derivative is correctly specified](hyp:hd)
and [bounded and Lipschitz](hyp:hDerivative), [the structural assumptions hold](hyp:hStruct),
[outcome endpoints are known](hyp:hEndpoints), [the instrument admits finite reduction](hyp:hFinite),
and [outcomes are almost surely binary](hyp:hy). Assume [a positive level count](hyp:hK),
[measurable baseline level propensities](hyp:hlev), [covariate-invariant level ordering](hyp:hOrder),
[policy overlap](hyp:hov), [baseline overlap](hyp:hbase), [admissibility of the true record](hyp:he0)
and [of every fitted record](hyp:heh), [a positive denominator bound](hyp:hc),
[a positive separation bound](hyp:hsep), and almost sure lower bounds on fitted
[baseline masses](hyp:hpi) and [regular group masses](hyp:htau).
Require finite nuisance rates for [propensities](hyp:hrp), [baseline level propensities](hyp:hrlev),
[treated-success regressions](hyp:hrP), [baseline masses](hyp:hrpi),
[shares in every group](hyp:hrs), [regular masses](hyp:hrt), [regular policy-union probability weights](hyp:hrg),
[higher-policy minus higher-baseline probability weights](hyp:hrfull), and [the tail policy probability](hyp:hrtail), and
[separation of adjacent true pooled policy levels and of both endpoints from the adjusted next baseline level](hyp:hgap).
If [the score error factors through the training data and an observation](hyp:hscore),
via [a sample-size-indexed function of the training view and a new observation](hyp:f)
with [a measurable factor](hyp:hf), [square-integrable sections at each training realization](hyp:hsection),
and [square-integrable evaluation rows](hyp:hfit), then
[the score-average estimator is root-total-sample-size consistent for the discrete lower target,
its error scaled by the square root of the evaluation-sample size converges to a centered
normal law with the true score's population variance, and the empirical variance consistently estimates that variance](goal). -/
lemma nuisanceRates_binary_oracle_dml_conclusions
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hEndpoints : OutcomeEndpointsKnown M)
    (hFinite : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c sep : ℝ) (hc : 0 < c) (hsep : 0 < sep)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M L).piLev)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M L).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) (eta0Bin M L).gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (eta0Bin M L).gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (eta0Bin M L).gammaTail))
    (hgap : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiBin M phi dphi L hK o (eh (2 * (n + 1)) a) -
        psiBin M phi dphi L hK o (eta0Bin M L) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hsection : ∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) :
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ (fun n a o => psiBin M phi dphi L hK o (eh n a))
        (2 * (n + 1)) a - discreteTarget M false L (policyProp phi M.prop))
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ ∧
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ (fun n a o => psiBin M phi dphi L hK o (eh n a))
          (2 * (n + 1)) a - discreteTarget M false L (policyProp phi M.prop))) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M
        (fun o => psiBin M phi dphi L hK o (eta0Bin M L))
        (discreteTarget M false L (policyProp phi M.prop))))) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ (fun n a o => psiBin M phi dphi L hK o (eh n a))
        (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M (fun o => psiBin M phi dphi L hK o (eta0Bin M L))
        (discreteTarget M false L (policyProp phi M.prop))) := by
  have hlaw := nuisanceRates_binary_oracle_dmlRV_clt M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy L hK hlev hOrder
    cpi hov hbase he0 eh heh c sep hc hsep hpi htau hrp hrlev hrP hrpi hrs hrt
    hrg hrfull hrtail hgap f hscore hf hsection hfit
  have hv := nuisanceRates_binary_oracle_mean_variance_consistent M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy L hK hlev hOrder
    cpi hov hbase he0 eh heh c sep hc hsep hpi htau hrp hrlev hrP hrpi hrs hrt
    hrg hrfull hrtail hgap f hscore hf hfit
  exact ⟨dml_rootn_consistent_of_normal_limit μ _ _ _ hlaw, hlaw, hv.2⟩

end Papers.TbsPrteOptimalTransport
