module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalProductBias
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularScoreConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryScoreMean
/-! Assembly of the complete binary score population bias from the original
componentwise nuisance rates, retaining every fitted residual correction. -/
public section

set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_binary_score_integral_decomposition
/-- Under [a valid policy map](hyp:hphi), [policy differentiability](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative), [a positive number of levels](hyp:hK), [an admissible fitted nuisance](hyp:he), and [almost surely binary outcomes](hyp:hy), suppose [the clipping constant is positive](hyp:hc) and the fitted [baseline assignment probabilities](hyp:hpi) and [regular policy probabilities](hyp:htau) are almost surely at least that constant. Then [the population mean of the total binary score equals the sum of the means of all full-interval product scores, the mean of the sum of all regular-band product scores, and the mean of the common tail score](goal). -/
lemma fitted_binary_score_integral_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e : NuisanceBin L) (he : BinAdmissible M L e)
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    (∫ o, psiBin M phi dphi L hK o e ∂observationLaw M) =
      (∑ k : Fin L.K, ∫ o, psiFullProdBin L e k o ∂observationLaw M) +
      (∫ o, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        psiProdBin phi dphi L e k j o ∂observationLaw M) +
      (∫ o, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
        ∂observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have iF := (fitted_full_score_block_memLp M L e he hy c hc hpi).integrable
    (by norm_num)
  have iR := (fitted_regular_score_block_memLp M phi dphi hphi hd hDerivative
    L e he hy c hc hpi htau).integrable (by norm_num)
  have iT := (fitted_commonTailScore_memLp M phi dphi hphi hd hDerivative
    L e he c hc hpi).integrable (by norm_num)
  simp only [psiBin, Finset.sum_add_distrib]
  rw [integral_add (iF.fun_add iR) iT, integral_add iF iR,
    integral_finsetSum _ (fun k hk =>
      (fitted_full_product_memLp M L e he hy c hc hpi ⟨k, Finset.mem_range.mp hk⟩).integrable (by norm_num))]
  rw [← Fin.sum_univ_eq_sum_range]

-- @node: nuisanceRates_binary_score_bias_root_n_negligible
/-- Assume [a valid policy map](hyp:hphi), [policy differentiability](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative), [threshold crossing](hyp:h), [almost surely binary outcomes](hyp:hy), [a positive number of levels](hyp:hK), [measurable baseline levels](hyp:hlev), [policy-invariant level ordering](hyp:hOrder), [policy overlap](hyp:hov), [baseline overlap](hyp:hbase), [an admissible true nuisance](hyp:he0), and [admissible fitted nuisances](hyp:heh). Suppose [the clipping constant is positive](hyp:hc), [the separation constant is positive](hyp:hsep), the fitted [baseline assignment probabilities](hyp:hpi) and [policy probabilities](hyp:htau) are almost surely at least the clipping constant, the componentwise L² errors in [propensities](hyp:hrp), [baseline treatment levels](hyp:hrlev), [treated-success regressions](hyp:hrP), [baseline assignment probabilities](hyp:hrpi), [within-band instrument shares](hyp:hrs), [policy probabilities](hyp:hrt), [regular weights](hyp:hrg), [full-interval weights](hyp:hrfull), and [tail weights](hyp:hrtail) are negligible relative to inverse fourth-root sample size, and [each regular reference band has width and distances from the full-interval threshold to both endpoints almost surely at least the separation constant](hyp:hgap). Then [the difference between the fitted and true population means of the total binary score, evaluated at sample sizes twice the iteration index plus two and multiplied by the square root of that index plus one, converges to zero in probability](goal). -/
lemma nuisanceRates_binary_score_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (h : ThresholdCrossing M) (hy : OutcomeBinaryAE M)
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
        pooledQBin phi L (eta0Bin M L) k j x|) :
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
  have hfrac := nuisanceRates_fractional_product_block_bias_root_n_negligible M μ
    phi dphi hphi hd hDerivative h hy L hOrder cpi hov hbase he0 eh heh c sep
    hc hsep hpi htau hrp hrlev hrP hrpi hrs hrt hrg hgap
  have htailClip (n : ℕ) (a : A) :
      ∀ᵐ x ∂xLaw M, c ≤ positiveValue (eh n a).piLev L.K x := by
    simpa only [positiveValue, dif_pos (show 1 ≤ L.K ∧ L.K ≤ L.K from ⟨hK, le_rfl⟩)]
      using hpi n a ⟨L.K, hK, le_rfl⟩
  have htail := nuisanceRates_tail_root_n_bias_negligible M μ h phi dphi hphi hd
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
    | exact policy_derivative_graph_measurable phi dphi hphi hd M.prop h.2.1 M.rangeProp
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
    have hh := population_hMinus_measurable M h phi hphi L hlev k j
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
    (population_binary_regular_product_mean_of_overlap M h phi dphi hphi hdphi
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
    rw [(population_binary_regular_product_mean_of_overlap M h phi dphi hphi hdphi
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

-- @node: nuisanceRates_binary_target_bias_root_n_negligible
/-- Assume [a valid policy map](hyp:hphi), [policy differentiability](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative), [the structural model conditions](hyp:h), [almost surely binary outcomes](hyp:hy), [known outcome endpoints](hyp:hEndpoints), [a finite instrument space with discrete topology](hyp:hf), [a positive number of levels](hyp:hK), [measurable baseline levels](hyp:hlev), [policy-invariant level ordering](hyp:hOrder), [policy overlap](hyp:hov), [baseline overlap](hyp:hbase), [an admissible true nuisance](hyp:he0), and [admissible fitted nuisances](hyp:heh). Suppose [the clipping constant is positive](hyp:hc), [the separation constant is positive](hyp:hsep), fitted [baseline assignment probabilities](hyp:hpi) and [policy probabilities](hyp:htau) are almost surely at least the clipping constant, the componentwise L² errors in [propensities](hyp:hrp), [baseline treatment levels](hyp:hrlev), [treated-success regressions](hyp:hrP), [baseline assignment probabilities](hyp:hrpi), [within-band instrument shares](hyp:hrs), [policy probabilities](hyp:hrt), [regular weights](hyp:hrg), [full-interval weights](hyp:hrfull), and [tail weights](hyp:hrtail) are negligible relative to inverse fourth-root sample size, and [each regular reference band's width and distances from the full-interval threshold to both endpoints are almost surely at least the separation constant](hyp:hgap). Then [the fitted population mean of the total binary score minus the lower discrete policy target, evaluated at sample sizes twice the iteration index plus two and multiplied by the square root of that index plus one, converges to zero in probability](goal). -/
lemma nuisanceRates_binary_target_bias_root_n_negligible
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
        pooledQBin phi L (eta0Bin M L) k j x|) :
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
  have hb := nuisanceRates_binary_score_bias_root_n_negligible M μ phi dphi hphi hd
    hDerivative h.2.2.2.1 hy L hK hlev hOrder cpi hov hbase he0 eh heh c sep hc hsep
    hpi htau hrp hrlev hrP hrpi hrs hrt hrg hrfull hrtail hgap
  simpa only [hm] using hb

end Papers.TbsPrteOptimalTransport
