module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomEvaluationLaw
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryOracleRemainder
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryScoreMean
/-! Oracle normality for measurable versions of true scores and fitted scores.
The IID oracle CLT combines with the vanishing root-n score remainder by Slutsky.
Measurability of fitted statistics is derived from their evaluation rows. -/
public section

set_option linter.style.longLine false
set_option linter.style.openClassical false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_oracle_dmlRV_clt_of_memLp
/-- Under [the equal-half sample-splitting laws](hyp:hSplit), if [the oracle score is square-integrable under the observation law](hyp:hLp) and [its population mean equals the target](hyp:hmean), then [the oracle DML estimate centered at the target and multiplied by the square root of the evaluation size converges in distribution to a centered Gaussian with the oracle population variance](goal). -/
lemma equalHalfSplit_oracle_dmlRV_clt_of_memLp
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (truth : Obs X Z → ℝ) (hLp : MemLp truth 2 (observationLaw M))
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta) :
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ (fun _ _ o => truth o) (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  let hm := hLp.aestronglyMeasurable.aemeasurable
  let g := hm.mk truth
  have heq : truth =ᵐ[observationLaw M] g := hm.ae_eq_mk
  have hmg : Measurable g := hm.measurable_mk
  have hvg : populationVariance M g theta = populationVariance M truth theta := by
    apply integral_congr_ae
    filter_upwards [heq] with o ho
    rw [ho]
  have hclt := equalHalfSplit_oracle_dmlRV_clt M μ S I₁ I₂ hSplit g hmg
    (hLp.ae_eq heq) theta ((integral_congr_ae heq).symm.trans hmean)
  rw [hvg] at hclt
  apply TendstoInDistribution.congr _ (Eventually.of_forall fun _ => rfl) hclt
  intro n
  have hs : ∀ᵐ a ∂μ, ∀ i : ℕ, truth (S.Z i a) = g (S.Z i a) := by
    apply ae_all_iff.mpr
    intro i
    have hp : MeasurePreserving (S.Z i) μ (observationLaw M) := ⟨S.meas i, S.map_eq i⟩
    exact hp.quasiMeasurePreserving.ae_eq heq
  filter_upwards [hs] with a ha
  rw [dmlRV_eq_of_score_eq_on_sample M S I₂ (fun _ _ o => g o)
    (fun _ _ o => truth o) _ a (fun i _ => (ha i).symm)]

-- @node: equalHalfSplit_dmlRV_aemeasurable_of_evaluation_rows
/-- Under [the equal-half sample-splitting laws](hyp:hSplit), if [every fitted score evaluated at an enumerated evaluation observation is almost everywhere measurable](hyp:hrow), then [the DML estimate at every even sample size is almost everywhere measurable](goal). -/
lemma equalHalfSplit_dmlRV_aemeasurable_of_evaluation_rows
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ)
    (hrow : ∀ n i, AEMeasurable (fun a => score (2 * (n + 1)) a
      (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) μ) :
    ∀ n, AEMeasurable (fun a => dmlRV M S I₂ score (2 * (n + 1)) a) μ := by
  intro n
  have hm : AEMeasurable (fun a => ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∑ i : Fin (n + 1), score (2 * (n + 1)) a
        (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) μ := by
    simpa only [Finset.sum_apply] using
      (Finset.aemeasurable_sum Finset.univ (fun i _ => hrow n i)).const_mul
        (((n + 1 : ℕ) : ℝ)⁻¹)
  apply hm.congr
  filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1,
    (hSplit (2 * (n + 1)) (by omega) ⟨n + 1, by omega⟩).1] with a he ha
  have hc : (I₂ (2 * (n + 1)) a).card = n + 1 := by simpa using ha.2.2.2
  have hne : (I₂ (2 * (n + 1)) a).Nonempty := by
    apply Finset.card_pos.mp
    rw [hc]
    omega
  simp only [dmlRV, dif_pos hne, scoreAverage, splitMean, hc]
  congr 1
  calc
    _ = ∑ i ∈ Finset.univ.image (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a)),
        score (2 * (n + 1)) a (S.Z i a) :=
      (Finset.sum_image (fun i hi j hj hij => he.1 hij)).symm
    _ = _ := by rw [he.2]

-- @node: equalHalfSplit_fitted_oracle_dmlRV_clt
/-- Under [the equal-half sample-splitting laws](hyp:hSplit), suppose [the oracle score is square-integrable](hyp:hLp), [its mean equals the target](hyp:hmean), and [every fitted evaluation row is almost everywhere measurable](hyp:hrow). If [the fitted-minus-oracle estimate multiplied by the square root of the evaluation size converges in probability to zero](hyp:hrem), then [the fitted DML estimate centered at the target and multiplied by that square root converges in distribution to a centered Gaussian with the oracle population variance](goal). -/
lemma equalHalfSplit_fitted_oracle_dmlRV_clt
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (truth : Obs X Z → ℝ) (hLp : MemLp truth 2 (observationLaw M))
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (score : ℕ → A → Obs X Z → ℝ)
    (hrow : ∀ n i, AEMeasurable (fun a => score (2 * (n + 1)) a
      (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) μ)
    (hrem : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ o => truth o) (2 * (n + 1)) a))
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  have hclt := equalHalfSplit_oracle_dmlRV_clt_of_memLp M μ S I₁ I₂ hSplit
    truth hLp theta hmean
  have hm := equalHalfSplit_dmlRV_aemeasurable_of_evaluation_rows M μ S I₁ I₂
    hSplit score hrow
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hclt _
    (fun n => ((hm n).sub_const theta).const_mul _)
  change TendstoInMeasure μ
    (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (dmlRV M S I₂ score (2 * (n + 1)) a -
        dmlRV M S I₂ (fun _ _ o => truth o) (2 * (n + 1)) a)) atTop 0 at hrem
  convert hrem using 1
  funext n a
  simp only [Pi.sub_apply]
  ring

variable [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_binary_oracle_dmlRV_clt
/-- For [binary score-error functions of the training view and one observation at each even sample size](hyp:f), suppose [the equal-half sample-splitting laws hold](hyp:hSplit), [the policy is a policy map](hyp:hphi), [its specified derivative is valid](hyp:hd), and [that derivative is bounded and Lipschitz](hyp:hDerivative). Assume [the structural model conditions](hyp:hStruct), [known outcome endpoints](hyp:hEndpoints), [finite instrument reduction](hyp:hFinite), [almost surely binary outcomes](hyp:hy), [a positive number of levels](hyp:hK), [measurable level propensities](hyp:hlev), [policy-invariant level ordering](hyp:hOrder), [policy overlap](hyp:hov), and [a baseline overlap witness](hyp:hbase). Suppose [the true binary nuisance is admissible](hyp:he0), [all fitted binary nuisances are admissible](hyp:heh), [the clipping and separation constants are positive](hyp:hc,hsep), [fitted assignment probabilities are bounded below by the clipping constant](hyp:hpi), and [fitted policy denominators have the same lower bound](hyp:htau). Assume the finite nuisance rates for [instrument propensities](hyp:hrp), [level treatment probabilities](hyp:hrlev), [treated-success probabilities](hyp:hrP), [level assignment probabilities](hyp:hrpi), [shares for every type](hyp:hrs), [policy denominators](hyp:hrt), [regular outcome coefficients](hyp:hrg), [full-block coefficients](hyp:hrfull), and [tail coefficients](hyp:hrtail), together with [uniform separation of adjacent pooled thresholds and of both thresholds from the residual treatment mass](hyp:hgap). If [the score difference factors through the training data and one observation](hyp:hscore), [the representing function is measurable](hyp:hf), [its fixed-training sections are square-integrable](hyp:hsection), and [its evaluation rows are square-integrable](hyp:hfit), then [the fitted binary DML estimate centered at the discrete policy target and multiplied by the square root of the evaluation size converges in distribution to a centered Gaussian with the true-score population variance](goal). -/
lemma nuisanceRates_binary_oracle_dmlRV_clt
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
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ (fun n a o => psiBin M phi dphi L hK o (eh n a))
          (2 * (n + 1)) a - discreteTarget M false L (policyProp phi M.prop))) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M
        (fun o => psiBin M phi dphi L hK o (eta0Bin M L))
        (discreteTarget M false L (policyProp phi M.prop))))) := by
  have h : ThresholdCrossing M := hStruct.2.2.2.1
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop h.2.1 M.rangeProp
  have hmean := (population_binary_score_mean_eq_target M hStruct hEndpoints hFinite
    phi dphi hphi hdphi hDerivative L hK hOrder hlev cpi hbase hov hy he0).2
  have hpi0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).piLev i x :=
    Eventually.of_forall (fun x => hbase.2 x i i.property.1 i.property.2)
  have htau0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev r x :=
    Eventually.of_forall (fun x => hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have hLp := fitted_binary_score_memLp M phi dphi hphi hd hDerivative L hK
    (eta0Bin M L) he0 hy cpi hbase.1 hpi0 htau0
  have hrem := nuisanceRates_binary_oracle_remainder_negligible M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative h hy L hK hlev hOrder cpi hov hbase he0 eh heh
    c sep hc hsep hpi htau hrp hrlev hrP hrpi hrs hrt hrg hrfull hrtail hgap
    f hscore hf hsection hfit
  apply equalHalfSplit_fitted_oracle_dmlRV_clt M μ S I₁ I₂ hSplit
    (fun o => psiBin M phi dphi L hK o (eta0Bin M L)) hLp
    (discreteTarget M false L (policyProp phi M.prop)) hmean
    (fun n a o => psiBin M phi dphi L hK o (eh n a)) _ hrem
  intro n i
  have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n
  have hp : MemLp (fun o => psiBin M phi dphi L hK o (eta0Bin M L)) 2
      (μ.map (fun a => S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) := by
    rw [(hl.2.2.2.1 i).2]
    exact hLp
  have ht := hp.comp_of_map (hl.2.2.1 i).aemeasurable
  have hm := (hfit n i).add ht
  convert hm.aestronglyMeasurable.aemeasurable using 1
  funext a
  rw [Pi.add_apply, ← hscore]
  simp only [Function.comp_apply]
  ring

end Papers.TbsPrteOptimalTransport
