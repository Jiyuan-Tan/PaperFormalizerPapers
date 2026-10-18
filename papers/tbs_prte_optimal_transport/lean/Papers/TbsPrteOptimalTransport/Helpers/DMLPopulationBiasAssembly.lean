module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPopulationProductBias
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryBiasAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularScoreConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryScoreMean
/-! Assembly of the complete binary score bias under the paper margins from the original
componentwise nuisance rates, retaining every fitted residual correction. -/
public section

set_option linter.style.haveILetI false
set_option linter.style.longLine false
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

-- @node: nuisanceRates_population_binary_score_bias_root_n_negligible
/-- Assume [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), [the structural model
assumptions](hyp:h), [binary outcomes almost surely](hyp:hy), [known outcome
endpoints](hyp:hEndpoints), [finite instrument reduction](hyp:hf), [a positive
number of treatment levels](hyp:hK), [measurable treatment-level propensities](hyp:hlev),
and [invariant level ordering under the policy](hyp:hOrder). Suppose [policy](hyp:hov)
and [baseline](hyp:hbase) overlap hold, [population nuisances](hyp:he0) and
[all fits](hyp:heh) are admissible, [policy levels avoid the boundary](hyp:hOff),
[propensity gaps are separated](hyp:hGap), [outcome gaps are separated](hyp:hOutcome),
[c is positive](hyp:hc), and [fitted baseline assignment masses](hyp:hpi) and
[policy masses](hyp:htau) are almost surely at least c. If quarter-rate conditions
hold for [propensities](hyp:hrp), [treatment-level propensities](hyp:hrlev),
[treated-success probabilities](hyp:hrP), [baseline assignment masses](hyp:hrpi),
[pooling shares](hyp:hrs), [policy masses](hyp:hrt), [regular regression weights](hyp:hrg),
[full-level regression weights](hyp:hrfull), and [the tail regression weight](hyp:hrtail),
then [the fitted binary score's population mean minus its population-nuisance
mean, evaluated at sample sizes twice n plus two and multiplied by the square
root of n plus one, converges to zero in probability](goal). -/
lemma nuisanceRates_population_binary_score_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (h : StructuralAssumptions M) (hy : OutcomeBinaryAE M)
    (hEndpoints : OutcomeEndpointsKnown M) (hf : InstrumentFiniteReduction Z)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (ch : ℝ) (hOutcome : DiscreteOutcomeGapWitness M L ch)
    (c : ℝ) (hc : 0 < c)
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
    :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, psiBin M phi dphi L hK o (eh (2*(n+1)) a) ∂observationLaw M) -
          (∫ o, psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hdBound := hDerivative
  obtain ⟨B, Lip, hB, hLip, hbound⟩ := hdBound
  have hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b| :=
    fun z x a b ha hb => (hbound z x a b ha hb).2
  have hfull := nuisanceRates_full_block_root_n_bias_negligible M μ L eh cpi c
    hbase hc hy he0 heh hpi hrP hrpi hrfull
  have hfrac := nuisanceRates_population_fractional_product_block_bias_root_n_negligible M μ
    phi dphi hphi hd hDerivative h hEndpoints hf hy L hOrder cpi hov hbase he0 eh heh
    hOff gap hGap ch hOutcome c hc hpi htau hrp hrlev hrP hrpi hrs hrt hrg
  have htailClip (n : ℕ) (a : A) :
      ∀ᵐ x ∂xLaw M, c ≤ positiveValue (eh n a).piLev L.K x := by
    simpa only [positiveValue, dif_pos (show 1 ≤ L.K ∧ L.K ≤ L.K from ⟨hK, le_rfl⟩)]
      using hpi n a ⟨L.K, hK, le_rfl⟩
  have htail := nuisanceRates_tail_root_n_bias_negligible M μ h.2.2.2.1 phi dphi hphi hd
    hDerivative Lip hLip hlip L hK hOrder eh heh he0 cpi c hbase hc htailClip
    hrp hrlev hrpi hrtail
  have hnfrac := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt hfrac
  have hntail := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt htail
  simp only [neg_zero] at hnfrac hntail
  have hs := (hfull.sub hnfrac).sub hntail
  simp only [sub_zero, sub_neg_eq_add] at hs
  have hpi0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).piLev i x :=
    Eventually.of_forall (fun x => hbase.2 x i i.property.1 i.property.2)
  have htau0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev r x :=
    Eventually.of_forall (fun x => hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)) := by
    first
    | fun_prop
    | exact policy_derivative_graph_measurable phi dphi hphi hd M.prop h.2.2.2.1.2.1 M.rangeProp
  have hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B := fun z x =>
    (hbound z x _ _ (M.rangeProp z x) (M.rangeProp z x)).1
  have hfull0 :
      (∑ k : Fin L.K, ∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M) =
      ∑ k : Fin L.K, ∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x
        ∂xLaw M := by
    apply Finset.sum_congr rfl
    intro k _
    exact population_binary_full_product_mean_of_overlap M L cpi hbase hy he0 k
  let T := fun k j (x : X) => gamma M L k j x * hMinus phi L (eta0Bin M L) k j x
  have mT (k j : ℕ) (hk : k ∈ Finset.range L.K)
      (hj : j ∈ Finset.Icc 1 (L.l k)) : Measurable (T k j) := by
    let r : RegularIndex L := ⟨(k,j), (Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
    have hg : Measurable (gamma M L k j) := (he0.2.2.2.2.2.1 r).2
    have hh := population_hMinus_measurable M h.2.2.2.1 phi hphi L hlev k j
    dsimp only [T]
    fun_prop
  have iT (k j : ℕ) (hk : k ∈ Finset.range L.K)
      (hj : j ∈ Finset.Icc 1 (L.l k)) :
      Integrable (fun o : Obs X Z => T k j o.1) (observationLaw M) := by
    let r : RegularIndex L := ⟨(k,j), (Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
    have hg : Measurable (gamma M L k j) := (he0.2.2.2.2.2.1 r).2
    have hgb : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x‖ ≤ 1 := by
      filter_upwards [he0.2.2.2.2.1 r] with x hx
      have hxg : gamma M L k j x ∈ Icc (0 : ℝ) 1 := hx.2
      rw [Real.norm_eq_abs, abs_of_nonneg hxg.1]
      exact hxg.2
    exact binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
      he0 k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj) _ hg 1 hgb
  have iR0 (k j : ℕ) (hk : k ∈ Finset.range L.K)
      (hj : j ∈ Finset.Icc 1 (L.l k)) :
      Integrable (psiProdBin phi dphi L (eta0Bin M L) k j) (observationLaw M) :=
    (population_binary_regular_product_mean_of_overlap M h.2.2.2.1 phi dphi hphi hdphi
      B hB hb L hOrder hlev cpi hbase hov hy he0 k j
      (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)).1
  have hfrac0 :
      (∫ o, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        psiProdBin phi dphi L (eta0Bin M L) k j o ∂observationLaw M) =
      (∫ o : Obs X Z, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        T k j o.1 ∂observationLaw M) := by
    rw [integral_finsetSum _ (fun k hk =>
      integrable_finsetSum _ (fun j hj => iR0 k j hk hj)),
      integral_finsetSum _ (fun k hk =>
        integrable_finsetSum _ (fun j hj => iT k j hk hj))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum _ (fun j hj => iR0 k j hk hj),
      integral_finsetSum _ (fun j hj => iT k j hk hj)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(population_binary_regular_product_mean_of_overlap M h.2.2.2.1 phi dphi hphi hdphi
      B hB hb L hOrder hlev cpi hbase hov hy he0 k j
      (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)).2,
      observationLaw_covariate_integral M (T k j) (mT k j hk hj)]
  convert hs using 1
  funext n a
  rw [fitted_binary_score_integral_decomposition M phi dphi hphi hd hDerivative
    L hK _ (heh _ a) hy c hc (hpi _ a) (htau _ a),
    fitted_binary_score_integral_decomposition M phi dphi hphi hd hDerivative
      L hK _ he0 hy cpi hbase.1 hpi0 htau0, hfull0, hfrac0]
  rw [integral_finsetSum Finset.univ (fun k _ =>
    (fitted_full_product_memLp M L _ (heh _ a) hy c hc (hpi _ a) k).integrable
      (by norm_num))]
  dsimp only [T]
  ring

-- @node: nuisanceRates_population_binary_target_bias_root_n_negligible
/-- Suppose [the policy is valid](hyp:hphi), [its derivative is as specified](hyp:hd)
and [uniformly bounded and Lipschitz](hyp:hDerivative), [the structural assumptions
hold](hyp:h), [outcomes are binary almost surely](hyp:hy), [their endpoints are
known](hyp:hEndpoints), [instruments admit finite reduction](hyp:hf), [the number
of treatment levels is positive](hyp:hK), [level propensities are measurable](hyp:hlev),
and [level ordering is invariant under the policy](hyp:hOrder). With [policy](hyp:hov)
and [baseline](hyp:hbase) overlap, [admissible population nuisances](hyp:he0)
and [fits](hyp:heh), [policy levels off the boundary](hyp:hOff), [separated
propensity gaps](hyp:hGap), [separated outcome gaps](hyp:hOutcome), [positive c](hyp:hc),
and [fitted baseline assignment masses](hyp:hpi) and [policy masses](hyp:htau)
almost surely at least c, assume quarter-rate conditions for [propensities](hyp:hrp),
[treatment-level propensities](hyp:hrlev), [treated-success probabilities](hyp:hrP),
[baseline assignment masses](hyp:hrpi), [pooling shares](hyp:hrs), [policy masses](hyp:hrt),
[regular regression weights](hyp:hrg), [full-level regression weights](hyp:hrfull),
and [the tail regression weight](hyp:hrtail). Then [the fitted binary score's
population mean minus the discrete lower target under the policy, evaluated
at sample sizes twice n plus two and multiplied by the square root of n plus
one, converges to zero in probability](goal). -/
lemma nuisanceRates_population_binary_target_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (h : StructuralAssumptions M) (hy : OutcomeBinaryAE M)
    (hEndpoints : OutcomeEndpointsKnown M) (hf : InstrumentFiniteReduction Z)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (ch : ℝ) (hOutcome : DiscreteOutcomeGapWitness M L ch)
    (c : ℝ) (hc : 0 < c)
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
    :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, psiBin M phi dphi L hK o (eh (2*(n+1)) a) ∂observationLaw M) -
          discreteTarget M false L (policyProp phi M.prop)))
      atTop (fun _ _ => 0) := by
  have hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)) := by
    first
    | fun_prop
    | exact policy_derivative_graph_measurable phi dphi hphi hd M.prop h.2.2.2.1.2.1
        M.rangeProp
  have hm := (population_binary_score_mean_eq_target M h hEndpoints hf phi dphi
    hphi hdphi hDerivative L hK hOrder hlev cpi hbase hov hy he0).2
  have hb := nuisanceRates_population_binary_score_bias_root_n_negligible M μ phi dphi hphi hd
    hDerivative h hy hEndpoints hf L hK hlev hOrder cpi hov hbase he0 eh heh
    hOff gap hGap ch hOutcome c hc hpi htau hrp hrlev hrP hrpi hrs hrt hrg hrfull hrtail
  simpa only [hm] using hb

end Papers.TbsPrteOptimalTransport
