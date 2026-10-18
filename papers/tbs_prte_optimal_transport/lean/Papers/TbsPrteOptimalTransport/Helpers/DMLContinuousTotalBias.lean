module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousSmoothPropensity
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousScoreConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousPolicyBounds
/-! Assembly of the continuous oracle's root-n conditional score bias.
The full, finite band, and terminal remainders are combined relative to the
true score mean. All component rates and denominator bounds remain explicit. -/
public section

set_option linter.deprecated false
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

-- @node: true_continuous_band_product_covariate_mean
/-- Assume [the structural model conditions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[a valid policy map](hyp:hphi), [its differentiability with the given derivative](hyp:hd),
[a bounded Lipschitz policy derivative](hyp:hDerivative), and [preservation of the
level ordering by the policy](hyp:hL). Under [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [admissibility of the true continuous nuisances](hyp:he0),
[bounded boundary densities](hyp:hdensity), and [no atom at the lower endpoint](hyp:h0),
for [a level below the terminal level](hyp:hk) and [a band index between one and
that level's band count](hyp:hj), [the population mean of the true band product
score equals the covariate mean of the band weight times the preceding continuous
band integral](goal). -/
lemma true_continuous_band_product_covariate_mean
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    (∫ o, psiProd M phi dphi L (trueNuisance M L) k j o ∂observationLaw M) =
      ∫ x, gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x ∂xLaw M := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hb b (hb : b ≤ L.l k) : Measurable (bandBoundary M L k b) := by
    have hm : Measurable (nuValue M (trueNuisance M L) k b) := by fun_prop
    have heq : nuValue M (trueNuisance M L) k b = bandBoundary M L k b := by
      funext x
      exact population_nuValue_eq_bandBoundary M L k b hk hb x
    rwa [heq] at hm
  have hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)) := by
    first | fun_prop | exact (policy_derivative_graph_measurable phi dphi hphi hd M.prop
      hStruct.2.2.2.1.2.1 M.rangeProp)
  have hm := (population_continuous_band_product_mean_from_overlap M hStruct hend
    phi dphi hdphi hDerivative L hL cpi hov hpol k j hk hj.1 hj.2
    (hb (j-1) (by omega)) (hb j hj.2) hdensity h0 (fun _ => 1)
    measurable_const (integrable_const 1)).2
  simp only [one_mul] at hm
  rw [hm]
  have hg : regularValue (trueNuisance M L).gamma k j = gamma M L k j := by
    funext x
    simp only [regularValue, trueNuisance, dif_pos (show
      k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le, hj⟩)]
  rw [← hg]
  rw [← (observationLaw_fst_measurePreserving M).map_eq]
  exact (integral_map (μ := observationLaw M) measurable_fst.aemeasurable (by
    rw [(observationLaw_fst_measurePreserving M).map_eq]
    exact ((fitted_continuous_regular_gamma_memLp M L _ he0 k j).integrable_mul
      (fitted_contJ_memLp M L _ he0 k (j-1))).aestronglyMeasurable)).symm

-- @node: encoded_continuous_nested_band_bias_root_n_negligible
/-- Assume [the structural conditions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[a valid policy map](hyp:hphi), [its differentiability](hyp:hd), [a bounded Lipschitz
derivative](hyp:hDerivative), [invariant level ordering](hyp:hL), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), and [separation of distinct baseline and policy
propensity levels](hyp:hg). For [a sequence of fitted continuous nuisances](hyp:eh),
suppose [the true nuisances are admissible](hyp:he0), [all fitted nuisances are
admissible](hyp:heh), [boundary densities are bounded](hyp:hdensity), [there is no
atom at the lower endpoint](hyp:h0), and [the encoded nuisance components satisfy
the finite nuisance rate conditions](hyp:hr). If [the clipping constant is positive](hyp:hc)
and [all fitted baseline assignment probabilities](hyp:hpi) and [all fitted policy
assignment probabilities](hyp:htau) are almost surely at least that constant,
then [the difference between fitted and true population means of the sum of all
nonterminal band product scores, multiplied by the square root of one plus the
sequence index, converges in probability to zero when fits use sample sizes twice
one plus that index](goal). -/
lemma encoded_continuous_nested_band_bias_root_n_negligible
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi gap : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hg : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a r, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            psiProd M phi dphi L (eh (2*(n+1)) a) k j o ∂observationLaw M) -
          (∫ o, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            psiProd M phi dphi L (trueNuisance M L) k j o ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let F := fun k n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
    ((∫ o, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L
        (eh (2*(n+1)) a) k j o ∂observationLaw M) -
      (∫ o, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L
        (trueNuisance M L) k j o ∂observationLaw M))
  have hp0 i : ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).piLev i x :=
    Eventually.of_forall (fun x => hov.2 x i i.property.1 i.property.2)
  have ht0 r : ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).tauLev r x :=
    Eventually.of_forall (fun x => hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (continuous_admissible_policy_nonempty M L _ he0 r))
  have ip n a k j (hk : k < L.K) (hj : j ∈ Finset.Icc 1 (L.l k)) :=
    (fitted_continuous_band_product_mean_decomposition M phi dphi L
      (eh n a) (heh n a) k j hk.le (Finset.mem_Icc.mp hj)
      ((fitted_continuous_weighted_band_component_memLp M phi dphi hphi hd hDerivative L
        (eh n a) (heh n a) c hc (hpi n a) (htau n a) k j hk
        (Finset.mem_Icc.mp hj)).integrable (by norm_num))).1
  have ip0 k j (hk : k < L.K) (hj : j ∈ Finset.Icc 1 (L.l k)) :=
    (fitted_continuous_band_product_mean_decomposition M phi dphi L
      (trueNuisance M L) he0 k j hk.le (Finset.mem_Icc.mp hj)
      ((fitted_continuous_weighted_band_component_memLp M phi dphi hphi hd hDerivative L
        _ he0 cpi hov.1 hp0 ht0 k j hk (Finset.mem_Icc.mp hj)).integrable (by norm_num))).1
  have hF k (hk : k < L.K) : TendstoInMeasure μ (F k) atTop (fun _ => (0 : ℝ)) := by
    let t := (Finset.Icc 1 (L.l k)).image (fun j => (k,j))
    have hi : ∀ i ∈ t, i.1 < L.K ∧ 1 ≤ i.2 ∧ i.2 ≤ L.l i.1 := by
      intro i hit
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hit
      exact ⟨hk, Finset.mem_Icc.mp hj⟩
    have h := encoded_continuous_band_product_block_bias_root_n_negligible
      M hStruct hend μ phi dphi hphi hd hDerivative L hL cpi gap hov hpol hg
      eh he0 heh hdensity h0 hr t hi c hc hpi htau
    have hinj : Set.InjOn (fun j : ℕ => (k,j)) (Finset.Icc 1 (L.l k)) := by
      intro a _ b _ hab
      exact Prod.mk.inj hab |>.2
    simp only [t, Finset.sum_image hinj] at h
    have it j (hj : j ∈ Finset.Icc 1 (L.l k)) : Integrable
        (fun x => gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x) (xLaw M) := by
      have heq : regularValue (trueNuisance M L).gamma k j = gamma M L k j := by
        funext x
        simp only [regularValue, trueNuisance, dif_pos (show
          k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le, Finset.mem_Icc.mp hj⟩)]
      rw [← heq]
      exact (fitted_continuous_regular_gamma_memLp M L _ he0 k j).integrable_mul
        (fitted_contJ_memLp M L _ he0 k (j-1))
    have hm : (∫ o, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L
        (trueNuisance M L) k j o ∂observationLaw M) =
        ∫ x, ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x *
          contJ L (trueNuisance M L) k (j-1) x ∂xLaw M := by
      rw [integral_finsetSum _ (fun j hj => ip0 k j hk hj), integral_finsetSum _ it]
      exact Finset.sum_congr rfl (fun j hj => true_continuous_band_product_covariate_mean
        M hStruct hend phi dphi hphi hd hDerivative L hL cpi hov hpol he0
        hdensity h0 k j hk (Finset.mem_Icc.mp hj))
    change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) at h
    simpa only [F, hm] using h
  have hs (s : Finset ℕ) (hk : ∀ k ∈ s, k < L.K) :
      TendstoInMeasure μ (fun n a => ∑ k ∈ s, F k n a) atTop (fun _ => (0 : ℝ)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    | @insert k s hks ih =>
      simpa only [Finset.sum_insert hks] using
        (hF k (hk k (Finset.mem_insert_self _ _))).add_zero
          (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs (Finset.range L.K) (fun k hk => Finset.mem_range.mp hk) using 1
  funext n a
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _
      (fun j hj => ip _ a k j (Finset.mem_range.mp hk) hj)),
    integral_finsetSum _ (fun k hk => integrable_finsetSum _
      (fun j hj => ip0 k j (Finset.mem_range.mp hk) hj))]
  simp only [F, ← Finset.sum_sub_distrib, Finset.mul_sum]

-- @node: encoded_continuous_total_score_bias_root_n_negligible
/-- Under [the structural conditions](hyp:hStruct), [known outcome endpoints](hyp:hend),
[a valid policy map](hyp:hphi), [its differentiability](hyp:hd), [a bounded Lipschitz
derivative](hyp:hDerivative), [a positive number of levels](hyp:hK), [invariant level
ordering](hyp:hL), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol), and
[separation of distinct baseline and policy propensity levels](hyp:hg), consider
[a sequence of fitted continuous nuisances](hyp:eh). If [the true nuisances are
admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh), [boundary
densities are bounded](hyp:hdensity), [there is no atom at the lower endpoint](hyp:h0),
[the encoded nuisance components satisfy the finite nuisance rate conditions](hyp:hr),
[the clipping constant is positive](hyp:hc), and [fitted baseline assignment
probabilities](hyp:hpi) and [fitted policy assignment probabilities](hyp:htau) are
almost surely bounded below by it, then [the fitted-minus-true population mean
of the complete continuous score, multiplied by the square root of one plus the
sequence index, converges in probability to zero using fits at sample sizes twice
one plus that index](goal). -/
lemma encoded_continuous_total_score_bias_root_n_negligible
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi gap : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hg : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a r, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, psiCont M phi dphi L hK o (eh (2*(n+1)) a) ∂observationLaw M) -
          (∫ o, psiCont M phi dphi L hK o (trueNuisance M L) ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  obtain ⟨hrp, hrlev, hrpi, _, _, hrg, _, hrtail, _, _, _, _, _, hrplus, hrminus⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hfull := nuisanceRates_continuous_full_score_block_bias_root_n_negligible
    M μ hStruct.2.2.2.1 (policyProp phi M.prop) L hL eh he0 heh
    hStruct.1 hStruct.2.1 hend c hc hpi hrpi hrlev hrplus hrminus hrg
  have htrue := (true_continuous_full_block_mean M hStruct.2.2.2.1
    (policyProp phi M.prop) L hL he0 hStruct.1 hStruct.2.1 hend cpi hov).2
  rw [← htrue] at hfull
  have hband := encoded_continuous_nested_band_bias_root_n_negligible
    M hStruct hend μ phi dphi hphi hd hDerivative L hL cpi gap hov hpol hg
    eh he0 heh hdensity h0 hr c hc hpi htau
  obtain ⟨B, Lip, hB, hLip, hb⟩ := hDerivative
  have hder : PolicyDerivativeBoundedLipschitz dphi := ⟨B, Lip, hB, hLip, hb⟩
  have hterminal n a : ∀ᵐ x ∂xLaw M, c ≤ positiveValue (eh n a).piLev L.K x := by
    simpa only [positiveValue, dif_pos (show 1 ≤ L.K ∧ L.K ≤ L.K from ⟨hK, le_rfl⟩)]
      using hpi n a ⟨L.K, ⟨hK, le_rfl⟩⟩
  have htail := nuisanceRates_continuous_tail_root_n_bias_negligible
    M μ hStruct.2.2.2.1 phi dphi hphi hd hder Lip hLip
    (fun z x a b ha hb' => (hb z x a b ha hb').2) L hK hL eh heh he0
    cpi c hov hc hterminal hrp hrlev hrpi hrtail
  have hs := ((show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hfull).add_zero
    (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hband)).add_zero
    (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from htail)
  have hp0 i : ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).piLev i x :=
    Eventually.of_forall (fun x => hov.2 x i i.property.1 i.property.2)
  have ht0 r : ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).tauLev r x :=
    Eventually.of_forall (fun x => hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (continuous_admissible_policy_nonempty M L _ he0 r))
  have hmean (e : NuisanceCont L) (he : ContAdmissible M L e)
      (c' : ℝ) (hc' : 0 < c')
      (hpi' : ∀ i, ∀ᵐ x ∂xLaw M, c' ≤ e.piLev i x)
      (htau' : ∀ r, ∀ᵐ x ∂xLaw M, c' ≤ e.tauLev r x) :
      (∫ o, psiCont M phi dphi L hK o e ∂observationLaw M) =
        (∫ o, ∑ k : Fin L.K, psiFullProd L e k o ∂observationLaw M) +
        (∫ o, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          psiProd M phi dphi L e k j o ∂observationLaw M) +
        (∫ o, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
          ∂observationLaw M) := by
    have ifull := (fitted_continuous_full_score_block_memLp M L e he hStruct.1
      hStruct.2.1 hend c' hc' hpi').integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have iband := (fitted_continuous_fractional_product_score_memLp
      M phi dphi hphi hd hder L e he c' hc' hpi' htau').integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
    have itail := (fitted_continuous_commonTailScore_memLp
      M phi dphi hphi hd hder L e he c' hc' hpi').integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
    simp only [psiCont, Finset.sum_add_distrib]
    rw [integral_add (ifull.fun_add iband) itail, integral_add ifull iband]
    have hf (o : Obs X Z) := Fin.sum_univ_eq_sum_range (fun k => psiFullProd L e k o) L.K
    simp_rw [hf]
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  rw [hmean _ (heh _ a) c hc (hpi _ a) (htau _ a), hmean _ he0 cpi hov.1 hp0 ht0]
  ring

end Papers.TbsPrteOptimalTransport
