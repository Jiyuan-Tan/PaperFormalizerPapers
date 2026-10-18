module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFiniteLabelClipping
/-! Continuous feasible variance consistency using only the recovered finite label domains. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedVariables false

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: policyUnion_eq_of_scoreLabels_eq
/-- If [two level systems have identical score labels](hyp:hLabels) and
[the baseline index is no greater than the population level count](hyp:hk),
[their policy unions at the specified baseline and policy indices are equal](goal). -/
lemma policyUnion_eq_of_scoreLabels_eq (H L : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (k j : ℕ) (hk : k ≤ L.K) : policyUnion H k j = policyUnion L k j := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  unfold policyUnion
  rw [(hdom k hk).1]
  apply Finset.biUnion_congr rfl
  intro i hi
  by_cases hj : j ≤ i
  · simp only [if_pos hj]
    exact (hdom k hk).2.2 i (by have := Finset.mem_range.mp hi; omega)
  · simp only [if_neg hj]

-- @node: higherPolicy_eq_of_scoreLabels_eq
/-- If [two level systems have identical score labels](hyp:hLabels),
[their unions of higher policy levels are equal at every baseline index](goal). -/
lemma higherPolicy_eq_of_scoreLabels_eq (H L : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (k : ℕ) : higherPolicy H k = higherPolicy L k := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  unfold higherPolicy
  rw [hK]
  apply Finset.biUnion_congr rfl
  intro i hi
  have hiK : i ≤ L.K := by have := Finset.mem_range.mp hi; omega
  by_cases hki : k < i
  · simp only [if_pos hki]
    rw [(hdom i hiK).1]
    apply Finset.biUnion_congr rfl
    intro j hj
    exact (hdom i hiK).2.2 j (by have := Finset.mem_range.mp hj; omega)
  · simp only [if_neg hki]

-- @node: higherBaseline_eq_of_scoreLabels_eq
/-- If [two level systems have identical score labels](hyp:hLabels),
[their unions of higher baseline levels are equal at every baseline index](goal). -/
lemma higherBaseline_eq_of_scoreLabels_eq (H L : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (k : ℕ) : higherBaseline H k = higherBaseline L k := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  unfold higherBaseline
  rw [hK]
  apply Finset.biUnion_congr rfl
  intro i hi
  have hiK : i ≤ L.K := by have := Finset.mem_range.mp hi; omega
  simp only [(hdom i hiK).2.1]

-- @node: psiCont_decode_eq_of_scoreLabels_eq
/-- If [two level systems have identical score labels](hyp:hLabels) and
[both have positive level counts](hyp:hH,hL),
[decoding the same component predictor in either system gives the same continuous score
at the specified observation](goal). -/
lemma psiCont_decode_eq_of_scoreLabels_eq (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (H L : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (hH : LevelCountPos H.K) (hL : LevelCountPos L.K)
    (F : (ℕ × ℕ × ℕ × Z) → X → ℝ) (o : Obs X Z) :
    psiCont M phi dphi H hH o (decodeContComponents H F) =
      psiCont M phi dphi L hL o (decodeContComponents L F) := by
  obtain ⟨hK, hdom⟩ := (scoreRecoveryLabels_eq_iff H L).mp hLabels
  simp only [psiCont]
  apply congrArg₂ (· + ·)
  · rw [hK]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt := Finset.mem_range.mp hk
    have hl := (hdom k (Nat.le_of_lt hklt)).1
    have hs := (hdom k (Nat.le_of_lt hklt)).2.1
    have hs1 := (hdom (k+1) hklt).2.1
    apply congrArg₂ (· + ·)
    · simp only [psiFullProd, psiFullJ, contFullJ, RpCont,
        higherPolicy_eq_of_scoreLabels_eq H L hLabels,
        higherBaseline_eq_of_scoreLabels_eq H L hLabels]
      simp [decodeContComponents, fullValue, minusFullValue, positiveValue, hK, hs, hs1]
    · rw [hl]
      apply Finset.sum_congr rfl
      intro j hj
      have hu := policyUnion_eq_of_scoreLabels_eq H L hLabels k j (Nat.le_of_lt hklt)
      have ht0 := (hdom k (Nat.le_of_lt hklt)).2.2 (j-1)
        (by have := (Finset.mem_Icc.mp hj).2; omega)
      have ht1 := (hdom k (Nat.le_of_lt hklt)).2.2 (j-1+1)
        (by have := Finset.mem_Icc.mp hj; omega)
      simp only [psiProd, contScoreComponents, contJ, IFJ, IFM, alphaLow, alphaHigh,
        RpCont, RqCont, pooledQ, hu]
      simp [decodeContComponents, positiveValue, regularValue, shareValue, nuValue,
        meanValue, minusMeanValue, boundaryValue, minusBoundaryValue,
        hK, hl, hs, hs1, ht0, ht1]
  · have hu := policyUnion_eq_of_scoreLabels_eq H L hLabels L.K 1 le_rfl
    have hs := (hdom L.K le_rfl).2.1
    simp [commonTailScore, decodeContComponents, positiveValue, hK, hu, hs]

-- @node: psiCont_eq_of_contComponent_eq_of_scoreLabels_eq
/-- If [two level systems have identical score labels](hyp:hLabels),
[both have positive level counts](hyp:hH,hL), and
[their nuisance records agree component by component at every covariate value](hyp:heq),
[their continuous scores agree at the specified observation](goal). -/
lemma psiCont_eq_of_contComponent_eq_of_scoreLabels_eq (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (H L : LevelData Z X)
    (hLabels : scoreRecoveryLabels H = scoreRecoveryLabels L)
    (hH : LevelCountPos H.K) (hL : LevelCountPos L.K)
    (e : NuisanceCont H) (f : NuisanceCont L)
    (heq : ∀ c x, contComponent M H e c x = contComponent M L f c x)
    (o : Obs X Z) : psiCont M phi dphi H hH o e = psiCont M phi dphi L hL o f := by
  have hfun : contComponent M H e = contComponent M L f :=
    funext fun c => funext (heq c)
  rw [← psiCont_decodeContComponents_contComponent M phi dphi H hH o e,
    hfun, psiCont_decode_eq_of_scoreLabels_eq M phi dphi H L hLabels hH hL,
    psiCont_decodeContComponents_contComponent]

-- @node: fittedContScore_eq_oracle_of_scoreLabels_eq
/-- For [continuous nuisance records fitted on the recovered levels](hyp:eHat), if [the population level count is positive](hyp:hK),
[the recovered and population score labels agree at the specified sample size and realization](hyp:hLabels),
and [the oracle and fitted nuisance components agree everywhere there](hyp:heq),
[the fitted continuous score equals the population-level score evaluated at the oracle
nuisance record for the specified observation](goal). -/
lemma fittedContScore_eq_oracle_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap : ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (oracle : ℕ → A → NuisanceCont L) (n : ℕ) (a : A)
    (hLabels : scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a) =
      scoreRecoveryLabels L)
    (heq : ∀ c x, contComponent M L (oracle n a) c x =
      contComponent M _ (eHat n a) c x) (o : Obs X Z) :
    fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat n a o =
      psiCont M phi dphi L hK o (oracle n a) := by
  have hk := (scoreRecoveryLabels_eq_iff _ _).mp hLabels |>.1
  have hK' : LevelCountPos (recoveredData M S I₁ I₂ pHat phi rho gap n a).K :=
    hk.symm ▸ hK
  simp only [fittedContScore, dif_pos hK']
  exact psiCont_eq_of_contComponent_eq_of_scoreLabels_eq M phi dphi _ L hLabels
    hK' hK (eHat n a) (oracle n a) (fun c x => (heq c x).symm) o

-- @node: contDMLRegime_mean_variance_consistent_on_recovery_of_scoreLabels_eq
/-- For [continuous nuisance records fitted on the recovered levels](hyp:eHat), assume [an equal half sample split](hyp:hSplit), [a valid policy map](hyp:hphi),
[the specified policy derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural model assumptions](hyp:hStruct), and [known outcome endpoints](hyp:hend).
If [the level count is positive](hyp:hK), [level order is invariant](hyp:hOrder),
[baseline levels are measurable](hyp:hlev), [all relevant band boundaries are measurable](hyp:hb),
[baseline overlap](hyp:hov) and [policy overlap](hyp:hpol) hold at the specified constant,
[the finite continuous double machine learning regime holds](hyp:hr),
[recovery-event failure probabilities tend to zero](hyp:hG), and
[score labels are recovered on those events at even sample sizes](hyp:hLabels),
[the fitted score mean converges in probability to the discrete target and its empirical
variance converges in probability to the true score's population variance about that target](goal). -/
lemma contDMLRegime_mean_variance_consistent_on_recovery_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hb : ∀ k < L.K, ∀ j ≤ L.l k, Measurable (bandBoundary M L k j))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L) :
    let score := fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hq := population_policyProp_measurable M hStruct.2.2.2.1 phi hphi
  have he0 := population_continuous_nuisance_admissible M hStruct hend
    (policyProp phi M.prop) hq L hOrder hlev cpi hov hpol
  obtain ⟨oracle, hc, ha, hm, hrate, heq⟩ :=
    contDMLRegime_oracle_score_convergence_of_scoreLabels_eq M μ S I₁ I₂ phi dphi hphi hd
      hDerivative hStruct hend L hK hOrder he0 cpi hov hpol pHat rho gap ch eHat hr G hG hLabels
  have hscoreeq (n : ℕ) (a : A) (haG : a ∈ G n) (o : Obs X Z) :=
    fittedContScore_eq_oracle_of_scoreLabels_eq M S I₁ I₂ pHat phi dphi rho gap L hK
      eHat oracle (2 * (n + 1)) a (hLabels n a haG) (heq n a haG) o
  have hpos : 0 < cpi / 2 := by linarith [hov.1]
  have hp0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have ht0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hpol.1]
  have hpf n a (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (oracle n a).piLev i x :=
    Eventually.of_forall (fun x => (hc n a).2.2.1 i x |>.1)
  have htf n a (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (oracle n a).tauLev r x :=
    Eventually.of_forall (fun x => ((hc n a).2.2.2 r x
      (contFittedSharesSimplex_policy_nonempty L _ (hc n a).2.1 r)).1)
  obtain ⟨C, hbound⟩ := fitted_continuous_total_score_uniform_bound M phi dphi hphi
    hDerivative L hK hStruct.1 hStruct.2.1 hend (cpi / 2) hpos
  have hdiff n a : ∀ᵐ o ∂observationLaw M,
      |psiCont M phi dphi L hK o (oracle n a) -
        psiCont M phi dphi L hK o (trueNuisance M L)| ≤ C + C := by
    filter_upwards [hbound _ (ha n a) (hpf n a) (htf n a),
      hbound _ he0 hp0 ht0] with o hf ht
    exact (abs_sub _ _).trans (add_le_add hf ht)
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_continuous_score_mean_eq_target M hStruct hend phi dphi
    hphi hdphi hDerivative L hK hOrder hlev cpi hov hpol hb hr.2.2.1 hr.2.2.2).2
  have hLp := true_continuous_total_score_memLp_of_overlap M phi dphi hphi hd hDerivative
    L hK he0 hStruct.1 hStruct.2.1 hend cpi hov hpol
  dsimp only
  exact equalHalfSplit_ae_bounded_training_feasible_mean_variance_consistent M μ S I₁ I₂
    hSplit (fun n a o => psiCont M phi dphi L hK o (oracle n a)) _ _ hmean hLp hm
    (C+C) hdiff hrate _ G hG (fun n a hna i hi => hscoreeq n a hna (S.Z i a))

-- @node: contDMLRegime_lower_bound_variance_consistent_on_recovery_of_scoreLabels_eq
/-- For [continuous nuisance records fitted on the recovered levels](hyp:eHat), assume [an equal half sample split](hyp:hSplit), [a valid policy map](hyp:hphi),
[the specified policy derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural model assumptions](hyp:hStruct), and [known outcome endpoints](hyp:hend).
Under [propensity gap separation](hyp:hGap), [finite instrument reduction](hyp:hFinite),
[a positive canonical level count](hyp:hK), [invariant canonical level order](hyp:hOrder),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol), and
[the finite continuous double machine learning regime](hyp:hr), if
[recovery-event failure probabilities tend to zero](hyp:hG) and
[canonical score labels are recovered on those events at even sample sizes](hyp:hLabels),
[the fitted empirical variance converges in probability to the true continuous score's
population variance centered at the sharp lower bound](goal). -/
lemma contDMLRegime_lower_bound_variance_consistent_on_recovery_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (x0 : X) (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n → scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap
      (2 * (n + 1)) a) = scoreRecoveryLabels (LevelStructure M.prop (policyProp phi M.prop) x0)) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
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
  exact (contDMLRegime_mean_variance_consistent_on_recovery_of_scoreLabels_eq M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend _ hK hOrder hlev
    (fun k hk j hj => hb k j hk hj) cpi hov hpol pHat rho gap ch eHat hr
    G hG hLabels).2

-- @node: contDMLRegime_variance_consistent
/-- For [continuous nuisance records fitted on the recovered levels](hyp:eHat), assume [an equal half sample split](hyp:hSplit), [a valid policy map](hyp:hphi),
[the specified policy derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[the structural model assumptions](hyp:hStruct), and [known outcome endpoints](hyp:hend).
Under [propensity gap separation](hyp:hGap), [finite instrument reduction](hyp:hFinite),
[a positive canonical level count](hyp:hK), [invariant canonical level order](hyp:hOrder),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
[the finite first-stage rate condition](hyp:hRate),
[policy levels avoiding the boundary](hyp:hOff),
[separation witnessed by the specified recovery gap](hyp:hgap), and
[the finite continuous double machine learning regime](hyp:hr),
[the fitted empirical variance at even sample sizes converges in probability to the true
continuous score's population variance centered at the sharp lower bound](goal). -/
lemma contDMLRegime_variance_consistent
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (x0 : X) (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (pHat : ℕ → A → Z → X → ℝ) (hRate : FiniteFirstStageRate M μ pHat)
    (rho : ℕ → ℝ) (gap ch : ℝ)
    (hOff : PolicyLevelOffBoundary (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  have hG := contDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ hStruct.2.2.2.1
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hOrder hOff hgap hK ch eHat hr
  exact contDMLRegime_lower_bound_variance_consistent_on_recovery_of_scoreLabels_eq
    M μ S I₁ I₂ hSplit phi dphi hphi hd hDerivative hStruct hend x0 hGap hFinite hK
    hOrder cpi hov hpol pHat rho gap ch eHat hr
    (fun n => recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1))) hG
    (fun n a ha => (mem_recoveryEvent_iff_scoreRecoveryLabels_eq
      M S I₁ I₂ pHat phi rho gap _ _ a).mp ha)

end Papers.TbsPrteOptimalTransport
