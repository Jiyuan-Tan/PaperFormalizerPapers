module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalPolicyBias
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalBiasBlocks
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularBiasAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLObservedResidualConvergence
/-! Root-n negligibility of the actual fractional binary product-score bias.
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

-- @node: nuisanceRates_fractional_product_score_bias_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [threshold crossing](hyp:h),
[an almost surely binary outcome](hyp:hy), [invariant baseline and policy level
ordering](hyp:hOrder), [policy overlap](hyp:hov), [baseline overlap](hyp:hbase),
and admissible [true](hyp:he0) and [fitted nuisances at every sample size](hyp:heh).
Suppose [the clipping constant](hyp:hc) and [the separation constant](hyp:hsep) are
positive, all fitted [level masses](hyp:hpi) and [policy masses](hyp:htau) are
almost surely at least the clipping constant, componentwise L2 errors are of
smaller order in probability than the inverse fourth root of sample size for
[propensities](hyp:hrp), [level propensities](hyp:hrlev), [treated-outcome masses](hyp:hrP),
[level masses](hyp:hrpi), [every component's instrument shares](hyp:hrs),
[policy masses](hyp:hrt), and [component weights](hyp:hrg), [the component's level
is below the terminal level](hyp:hk), and [the true pooled-policy interval width
and the boundary's distances from both endpoints are almost surely at least the
separation constant](hyp:hgap). Then [the population mean of the fitted product
score minus the mean true component weight times the true fractional hinge, at
sample sizes twice one more than the index and scaled by the square root of one
more than the index, converges in probability to zero](goal). -/
lemma nuisanceRates_fractional_product_score_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (h : ThresholdCrossing M) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (r : RegularIndex L) (c sep : ℝ) (hc : 0 < c) (hsep : 0 < sep)
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
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x -
        pooledQBin phi L (eta0Bin M L) r.val.1 (r.val.2 - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (r.val.1 + 1) x -
        binFullJ L (eta0Bin M L) r.val.1 x -
        pooledQBin phi L (eta0Bin M L) r.val.1 (r.val.2 - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (r.val.1 + 1) x -
        binFullJ L (eta0Bin M L) r.val.1 x -
        pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, psiProdBin phi dphi L (eh (2*(n+1)) a) r.val.1 r.val.2 o
            ∂observationLaw M) -
          (∫ o : Obs X Z, gamma M L r.val.1 r.val.2 o.1 *
            hMinus phi L (eta0Bin M L) r.val.1 r.val.2 o.1 ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  have hComp := nuisanceRates_fractional_component_conditional_bias_root_n_negligible
    M μ phi dphi hphi hd hDerivative L hOrder cpi hov he0 eh heh r c sep hc hsep
    hpi htau hrp hrlev hrP hrpi hrs hrt hgap
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
    (fitted_fractional_hinge_bias_energy_bound M phi hphi L (eta0Bin M L) (eh n a)
      he0 (heh n a) r.val.1 r.val.2 sep hsep hgap).1
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
  rw [(fitted_regular_product_exact_bias M h phi dphi hphi hd hDerivative L hOrder
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


-- @node: nuisanceRates_fractional_product_block_bias_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [threshold crossing](hyp:h),
[an almost surely binary outcome](hyp:hy), [invariant baseline and policy level
ordering](hyp:hOrder), [policy overlap](hyp:hov), [baseline overlap](hyp:hbase),
and admissible [true](hyp:he0) and [fitted nuisances at every sample size](hyp:heh).
Suppose [the clipping constant](hyp:hc) and [the separation constant](hyp:hsep) are
positive, all fitted [level masses](hyp:hpi) and [policy masses](hyp:htau) are
almost surely at least the clipping constant, componentwise L2 errors are of
smaller order in probability than the inverse fourth root of sample size for
[propensities](hyp:hrp), [level propensities](hyp:hrlev), [treated-outcome masses](hyp:hrP),
[level masses](hyp:hrpi), [every component's instrument shares](hyp:hrs),
[policy masses](hyp:hrt), and [component weights](hyp:hrg), and [every regular
component's true pooled-policy interval width and boundary distances from both
endpoints are almost surely at least the separation constant](hyp:hgap). Then
[the population mean of the sum of fitted product scores over all regular
components minus the mean sum of true component weights times true fractional
hinges, at sample sizes twice one more than the index and scaled by the square
root of one more than the index, converges in probability to zero](goal). -/
lemma nuisanceRates_fractional_product_block_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (h : ThresholdCrossing M) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X)
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
    (fitted_regular_product_exact_bias M h phi dphi hphi hd hDerivative L hOrder
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
        have ht := nuisanceRates_fractional_product_score_bias_root_n_negligible M μ
          phi dphi hphi hd hDerivative h hy L hOrder cpi hov hbase he0 eh heh r c sep
          hc hsep hpi htau hrp hrlev hrP hrpi hrs hrt hrg
          (Finset.mem_range.mp hk) (hgap k hk j hj)
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
