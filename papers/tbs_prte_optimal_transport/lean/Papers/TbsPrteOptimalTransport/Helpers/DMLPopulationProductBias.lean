module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLStructuralZeroHinge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalBiasBlocks
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularBiasAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLObservedResidualConvergence
/-! Population-margin root-n negligibility of fractional binary product-score bias.
The fitted event correction leaves a product of errors, and the conditional
component bias retains all fitted regression and policy residual corrections. -/
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

-- @node: nuisanceRates_population_fractional_product_score_bias_root_n_negligible
/-- Assume [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), [the model's structural
assumptions](hyp:hStruct), [known outcome endpoints](hyp:hend), [finite instrument
reduction](hyp:hf), [an almost surely binary outcome](hyp:hy), [invariant ordering
of baseline and policy levels](hyp:hOrder), [policy overlap](hyp:hov), and
[baseline overlap](hyp:hbase). Suppose [population nuisances](hyp:he0) and
[all fits](hyp:heh) are admissible, [policy levels avoid the boundary](hyp:hOff),
[propensity gaps satisfy the specified separation](hyp:hGap), [outcome gaps
satisfy the specified separation](hyp:hOutcome), [c is positive](hyp:hc), and
[fitted baseline assignment masses](hyp:hpi) and [fitted policy masses](hyp:htau)
are almost surely at least c. If the componentwise quarter-rate conditions
hold for [propensities](hyp:hrp), [treatment-level propensities](hyp:hrlev),
[treated-success probabilities](hyp:hrP), [baseline assignment masses](hyp:hrpi),
[pooling shares](hyp:hrs), [policy masses](hyp:hrt), and [regular regression
weights](hyp:hrg), then at [a regular level below the maximum treatment level](hyp:hk),
[the fitted fractional product score's population mean minus the population
regression-weighted negative hinge, evaluated at sample sizes twice n plus two
and multiplied by the square root of n plus one, converges to zero in probability](goal). -/
lemma nuisanceRates_population_fractional_product_score_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (ch : ℝ) (hOutcome : DiscreteOutcomeGapWitness M L ch)
    (r : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M L).piLev)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M L).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) (eta0Bin M L).gamma)
    (hk : r.val.1 < L.K)
    :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, psiProdBin phi dphi L (eh (2*(n+1)) a) r.val.1 r.val.2 o
            ∂observationLaw M) -
          (∫ o : Obs X Z, gamma M L r.val.1 r.val.2 o.1 *
            hMinus phi L (eta0Bin M L) r.val.1 r.val.2 o.1 ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  have hComp := nuisanceRates_population_fractional_component_conditional_bias_root_n_negligible
    M μ phi dphi hphi hd hDerivative hStruct hend hf hy L hOrder cpi hov he0 eh heh
    hOff gap hGap ch hOutcome r hk c hc hpi htau hrp hrlev hrP hrpi hrs hrt
  have hCross := nuisanceRates_regular_product_cross_root_n_negligible M μ phi dphi
    hphi hd hDerivative L (eta0Bin M L) eh he0 heh hrp hrlev hrP hrs hrg
    r.val.1 r.val.2 hk r.property.2
  have hs := hComp.sub hCross
  simp only [sub_zero] at hs
  let H := fun n a x => regularValue (eh n a).gamma r.val.1 r.val.2 x *
    binaryFittedHingeRemainder
      (pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x)
      (pooledQBin phi L (eta0Bin M L) r.val.1 (r.val.2 - 1) x)
      (positiveValue (eta0Bin M L).pLev (r.val.1 + 1) x -
        binFullJ L (eta0Bin M L) r.val.1 x)
      (pooledQBin phi L (eh n a) r.val.1 r.val.2 x)
      (pooledQBin phi L (eh n a) r.val.1 (r.val.2 - 1) x)
      (positiveValue (eh n a).pLev (r.val.1 + 1) x - binFullJ L (eh n a) r.val.1 x)
  let R := fun n a x => regularValue (eh n a).gamma r.val.1 r.val.2 x *
    (binaryRegularRegressionMean phi L (eta0Bin M L) (eh n a) r.val.1 r.val.2 x -
      Dbd phi L (eh n a) r.val.1 r.val.2 x *
        ((positiveValue (eh n a).pLev (r.val.1 + 1) x - binFullJ L (eh n a) r.val.1 x) -
          (positiveValue (eta0Bin M L).pLev (r.val.1 + 1) x -
            binFullJ L (eta0Bin M L) r.val.1 x)) -
      (if r.val.2 = 1 then Edom phi L (eh n a) r.val.1 r.val.2 x *
        Iact phi L (eh n a) r.val.1 r.val.2 x *
        (positiveValue (eh n a).pLev r.val.1 x - positiveValue (eta0Bin M L).pLev r.val.1 x)
      else 0))
  let U := fun n a x =>
    (regularValue (eh n a).gamma r.val.1 r.val.2 x * Iact phi L (eh n a) r.val.1 r.val.2 x) *
    (pooledQBin phi L (eh n a) r.val.1 r.val.2 x +
      (∑ z, instProb M z x * RqBin dphi L (eh n a) r.val.1 r.val.2 (x,z,M.prop z x,0)) -
      pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x)
  let V := fun n a x => if r.val.2 = 1 then 0 else
    (regularValue (eh n a).gamma r.val.1 r.val.2 x * Edom phi L (eh n a) r.val.1 r.val.2 x *
      Iact phi L (eh n a) r.val.1 r.val.2 x) *
    (pooledQBin phi L (eh n a) r.val.1 (r.val.2 - 1) x +
      (∑ z, instProb M z x * RqBin dphi L (eh n a) r.val.1 (r.val.2 - 1) (x,z,M.prop z x,0)) -
      pooledQBin phi L (eta0Bin M L) r.val.1 (r.val.2 - 1) x)
  have iH (n : ℕ) (a : A) : Integrable (H n a) (xLaw M) :=
    fitted_population_binary_hinge_bias_integrable M phi hphi hStruct hend hf hy
      L hOrder hOff gap hGap cpi hov ch hOutcome he0 (eh n a) (heh n a)
      r.val.1 r.val.2 hk r.property.2
  have iR (n : ℕ) (a : A) : Integrable (R n a) (xLaw M) :=
    fitted_fractional_regression_centering_integrable M phi hphi L (eta0Bin M L)
      (eh n a) he0 (heh n a) c hc r.val.1 r.val.2 (hpi n a)
  have iU (n : ℕ) (a : A) : Integrable (U n a) (xLaw M) := by
    have hw := fitted_fractional_upper_weight_memLp_bound M phi hphi L (eh n a)
      (heh n a) r.val.1 r.val.2
    exact fitted_binary_conditional_policy_weighted_integrable M phi dphi hphi hd hDerivative
      L hOrder cpi hov he0 (eh n a) (heh n a) r c 1 hc zero_le_one (htau n a r)
      _ hw.1.1 hw.2
  have iV (n : ℕ) (a : A) : Integrable (V n a) (xLaw M) := by
    dsimp only [V]
    by_cases hj : r.val.2 = 1
    · simp only [if_pos hj]
      exact integrable_zero _ _ _
    · simp only [if_neg hj]
      have hprev : r.val.1 ≤ L.K ∧ 1 ≤ r.val.2-1 ∧ r.val.2-1 ≤ L.l r.val.1 := by
        have := r.property
        omega
      let t : RegularIndex L := ⟨(r.val.1, r.val.2-1), hprev⟩
      have hw := fitted_fractional_lower_weight_memLp_bound M phi hphi L (eh n a)
        (heh n a) r.val.1 r.val.2
      exact fitted_binary_conditional_policy_weighted_integrable M phi dphi hphi hd hDerivative
        L hOrder cpi hov he0 (eh n a) (heh n a) t c 1 hc zero_le_one (htau n a t)
        _ hw.1.1 hw.2
  let C := fun n a x => regularValue (eh n a).gamma r.val.1 r.val.2 x *
    (hMinus phi L (eh n a) r.val.1 r.val.2 x +
      binaryRegularRegressionMean phi L (eta0Bin M L) (eh n a) r.val.1 r.val.2 x +
      binaryRegularPolicyMean M phi dphi L (eh n a) r.val.1 r.val.2 x -
      hMinus phi L (eta0Bin M L) r.val.1 r.val.2 x)
  have iC (n : ℕ) (a : A) : Integrable (C n a) (xLaw M) := by
    apply (((iH n a).fun_add (iR n a)).fun_add (iU n a) |>.sub' (iV n a)).congr
    exact Eventually.of_forall (fun x => by
      dsimp only [Pi.sub_apply, C]
      rw [fitted_fractional_component_centered_bias_eq M phi dphi L (eta0Bin M L)
        (eh n a) r.val.1 r.val.2 x]
      dsimp only [H, R, U, V]
      by_cases hj : r.val.2 = 1
      · simp only [if_pos hj]; ring
      · simp only [if_neg hj]; ring)
  let D := fun n a x =>
    (regularValue (eh n a).gamma r.val.1 r.val.2 x -
      regularValue (eta0Bin M L).gamma r.val.1 r.val.2 x) *
    (hMinus phi L (eh n a) r.val.1 r.val.2 x -
      hMinus phi L (eta0Bin M L) r.val.1 r.val.2 x)
  have iD (n : ℕ) (a : A) : Integrable (D n a) (xLaw M) :=
    (fitted_regular_product_cross_L2_bound M phi hphi L (eta0Bin M L) (eh n a)
      he0 (heh n a) r.val.1 r.val.2 hk r.property.2).1
  convert hs using 1
  funext n a
  rw [← mul_sub]
  congr 1
  rw [(fitted_regular_product_exact_bias M hStruct.2.2.2.1 phi dphi hphi hd hDerivative L hOrder
    cpi hbase hy he0 (eh (2*(n+1)) a) (heh _ a) c hc (hpi _ a) (htau _ a)
    r.val.1 r.val.2 hk r.property.2).2]
  have hg0 (x : X) : regularValue (eta0Bin M L).gamma r.val.1 r.val.2 x =
      gamma M L r.val.1 r.val.2 x := by
    simp only [regularValue, eta0Bin, dif_pos r.property]
  simp_rw [← hg0]
  change (∫ o : Obs X Z, C (2*(n+1)) a o.1 - D (2*(n+1)) a o.1
    ∂observationLaw M) = (∫ x, C (2*(n+1)) a x ∂xLaw M) -
      ∫ x, D (2*(n+1)) a x ∂xLaw M
  have hmap := (observationLaw_fst_measurePreserving M).map_eq
  have im : Integrable (fun x => C (2*(n+1)) a x - D (2*(n+1)) a x)
      ((observationLaw M).map Prod.fst) := by
    rw [hmap]
    exact (iC _ a).sub' (iD _ a)
  rw [← integral_map measurable_fst.aemeasurable im.aestronglyMeasurable, hmap,
    integral_sub (iC _ a) (iD _ a)]


-- @node: nuisanceRates_population_fractional_product_block_bias_root_n_negligible
/-- Suppose [the policy is valid](hyp:hphi), [its derivative is as specified](hyp:hd)
and [uniformly bounded and Lipschitz](hyp:hDerivative), [the structural model
assumptions hold](hyp:hStruct), [outcome endpoints are known](hyp:hend),
[instruments admit finite reduction](hyp:hf), [outcomes are binary almost surely](hyp:hy),
[level ordering is invariant under the policy](hyp:hOrder), and [policy](hyp:hov)
and [baseline](hyp:hbase) overlap hold. Assume [admissible population nuisances](hyp:he0)
and [fits](hyp:heh), [policy levels off the boundary](hyp:hOff), [separated
propensity gaps](hyp:hGap), [separated outcome gaps](hyp:hOutcome), [positive c](hyp:hc),
and [fitted baseline assignment masses](hyp:hpi) and [policy masses](hyp:htau)
almost surely at least c. Under quarter-rate conditions for [propensities](hyp:hrp),
[treatment-level propensities](hyp:hrlev), [treated-success probabilities](hyp:hrP),
[baseline assignment masses](hyp:hrpi), [pooling shares](hyp:hrs), [policy masses](hyp:hrt),
and [regular regression weights](hyp:hrg), [the population mean of the entire
fitted fractional product block minus the mean of the corresponding population
regression-weighted negative hinges, evaluated at sample sizes twice n plus two
and multiplied by the square root of n plus one, tends to zero in probability](goal). -/
lemma nuisanceRates_population_fractional_product_block_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X)
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
    :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            psiProdBin phi dphi L (eh (2*(n+1)) a) k j o ∂observationLaw M) -
          (∫ o : Obs X Z, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            gamma M L k j o.1 * hMinus phi L (eta0Bin M L) k j o.1
            ∂observationLaw M))) atTop (fun _ _ => 0) := by
  let T := fun k j (o : Obs X Z) =>
    gamma M L k j o.1 * hMinus phi L (eta0Bin M L) k j o.1
  have iT (k j : ℕ) (hk : k ∈ Finset.range L.K) (hj : j ∈ Finset.Icc 1 (L.l k)) :
      Integrable (T k j) (observationLaw M) := by
    let r : RegularIndex L := ⟨(k,j), (Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
    have hm : Measurable (gamma M L k j) := (he0.2.2.2.2.2.1 r).2
    have hb : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x‖ ≤ 1 := by
      filter_upwards [he0.2.2.2.2.1 r] with x hx
      have hxg : gamma M L k j x ∈ Icc (0 : ℝ) 1 := hx.2
      rw [Real.norm_eq_abs, abs_of_nonneg hxg.1]
      exact hxg.2
    exact binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
      he0 k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj) _ hm 1 hb
  have iS (k j n : ℕ) (a : A) (hk : k ∈ Finset.range L.K)
      (hj : j ∈ Finset.Icc 1 (L.l k)) :
      Integrable (psiProdBin phi dphi L (eh (2*(n+1)) a) k j) (observationLaw M) :=
    (fitted_regular_product_exact_bias M hStruct.2.2.2.1 phi dphi hphi hd hDerivative L hOrder
      cpi hbase hy he0 _ (heh _ a) c hc (hpi _ a) (htau _ a)
      k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)).1
  let F := fun k j n a o => psiProdBin phi dphi L (eh (2*(n+1)) a) k j o - T k j o
  have iF (k j n : ℕ) (a : A) (hk : k ∈ Finset.range L.K)
      (hj : j ∈ Finset.Icc 1 (L.l k)) : Integrable (F k j n a) (observationLaw M) :=
    (iS k j n a hk hj).sub' (iT k j hk hj)
  have hs : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o,
        ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), F k j n a o
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    apply dml_finite_integral_root_n_negligible μ (observationLaw M) (Finset.range L.K)
      (fun k n a o => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n a o)
    · intro k hk n a
      exact integrable_finsetSum _ (fun j hj => iF k j n a hk hj)
    · intro k hk
      apply dml_finite_integral_root_n_negligible μ (observationLaw M)
        (Finset.Icc 1 (L.l k)) (F k)
      · intro j hj n a
        exact iF k j n a hk hj
      · intro j hj
        let r : RegularIndex L := ⟨(k,j), (Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
        have ht := nuisanceRates_population_fractional_product_score_bias_root_n_negligible M μ
          phi dphi hphi hd hDerivative hStruct hend hf hy L hOrder cpi hov hbase he0 eh heh
          hOff gap hGap ch hOutcome r c hc hpi htau hrp hrlev hrP hrpi hrs hrt hrg
          (Finset.mem_range.mp hk)
        simpa only [F, T, integral_sub (iS k j _ _ hk hj) (iT k j hk hj)] using ht
  convert hs using 1
  funext n a
  have hid (o : Obs X Z) :
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), F k j n a o) =
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        psiProdBin phi dphi L (eh (2*(n+1)) a) k j o) -
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), T k j o) := by
    simp only [F, Finset.sum_sub_distrib]
  simp_rw [hid]
  rw [integral_sub
    (integrable_finsetSum _ (fun k hk => integrable_finsetSum _ (fun j hj =>
      iS k j n a hk hj)))
    (integrable_finsetSum _ (fun k hk => integrable_finsetSum _ (fun j hj =>
      iT k j hk hj)))]

end Papers.TbsPrteOptimalTransport
