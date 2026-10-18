module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryPoolingBias
public import Papers.TbsPrteOptimalTransport.Helpers.DMLWeightedBaselineCancellation
/-! Conditional policy residual cancellation for the fractional binary score.
The actual finite conditional RqBin mean inherits the pooling remainder bound;
fitted active-branch weights are derived from clipped score nuisances. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_regular_policy_conditional_mean_eq
/-- [The true-instrument average of a fitted regular policy residual evaluated
at the true treatment mean equals the inverse fitted policy mass times the sum
over that component's instruments of the true instrument probability times the
policy derivative at the fitted propensity times the true-minus-fitted propensity](goal). -/
lemma fitted_regular_policy_conditional_mean_eq
    (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (r : RegularIndex L) (x : X) :
    (∑ z, instProb M z x * RqBin dphi L e r.val.1 r.val.2 (x,z,M.prop z x,0)) =
      (e.tauLev r x)⁻¹ * (∑ z ∈ L.T r.val.1 r.val.2,
        instProb M z x * dphi z x (e.prop z x) * (M.prop z x - e.prop z x)) := by
  have hj : ¬ (r.val.2 = 0 ∨ L.l r.val.1 < r.val.2) := by
    have := r.property
    omega
  rw [RqBin_finite_conditional_mean, if_neg hj]
  simp only [regularValue, dif_pos r.property]

-- @node: fitted_binary_conditional_policy_weighted_quadratic_bound
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd),
assume nonnegative [derivative](hyp:hB), [Lipschitz](hyp:hLip), [weight](hyp:hW),
[propensity-error](hyp:hreg), and [share-and-mass-error](hyp:hwt) bounds, and
[a positive clipping constant](hyp:hc). If [the derivative is bounded on the unit
interval](hyp:hbound) and [Lipschitz there](hyp:hlip), [baseline and policy level
ordering is invariant](hyp:hOrder), [policy overlap holds](hyp:hov), [the true](hyp:he0)
and [fitted](hyp:he) nuisances are admissible, [the fitted component policy mass
is almost surely at least the clipping constant](hyp:hden), the weight is
[almost everywhere strongly measurable](hyp:hw) and [almost surely bounded by the
weight bound](hyp:hwb), and the L2 errors in [component propensities](hyp:hpNorm),
[instrument shares](hyp:haNorm), and [policy mass](hyp:htNorm) obey their respective
bounds, then [the weighted, conditionally corrected pooled-policy error is
integrable and its absolute integral is at most the weight bound times the number
of component instruments times the sum of the Lipschitz bound times the squared
propensity-error bound and the derivative bound times one plus the reciprocal
clipping constant times the product of the two error bounds](goal). -/
lemma fitted_binary_conditional_policy_weighted_quadratic_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (B Lip c W reg wt : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip)
    (hc : 0 < c) (hW : 0 ≤ W) (hreg : 0 ≤ reg) (hwt : 0 ≤ wt)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p t, p ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x t| ≤ Lip * |p - t|)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (r : RegularIndex L)
    (hden : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (w : X → ℝ) (hw : AEStronglyMeasurable w (xLaw M))
    (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W)
    (hpNorm : ∀ z ∈ L.T r.val.1 r.val.2, finiteL2Error M (e.prop z) (M.prop z) ≤ reg)
    (haNorm : ∀ z ∈ L.T r.val.1 r.val.2,
      finiteL2Error M (e.share r z) ((eta0Bin M L).share r z) ≤ wt)
    (htNorm : finiteL2Error M (e.tauLev r) ((eta0Bin M L).tauLev r) ≤ wt) :
    let R := fun x => pooledQBin phi L e r.val.1 r.val.2 x +
      (∑ z, instProb M z x * RqBin dphi L e r.val.1 r.val.2 (x,z,M.prop z x,0)) -
      pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x
    Integrable (fun x => w x * R x) (xLaw M) ∧
      |∫ x, w x * R x ∂xLaw M| ≤ W * ((L.T r.val.1 r.val.2).card : ℝ) *
        (Lip * reg ^ 2 + (B + B / c) * (reg * wt)) := by
  dsimp only
  simp_rw [fitted_regular_policy_conditional_mean_eq M dphi L e r]
  exact fitted_binary_pooling_weighted_quadratic_bound M phi dphi hphi hd
    B Lip c W reg wt hB hLip hc hW hreg hwt hbound hlip
    L hOrder cpi hov he0 e he r hden w hw hwb hpNorm haNorm htNorm

-- @node: nuisanceRates_binary_conditional_policy_weighted_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [invariant baseline
and policy level ordering](hyp:hOrder), [policy overlap](hyp:hov), and admissible
[true](hyp:he0) and [fitted nuisances at every sample size](hyp:heh). With
[a positive clipping constant](hyp:hc), [a nonnegative weight bound](hyp:hW),
[fitted component policy masses almost surely bounded below by the clipping
constant](hyp:hden), [almost everywhere strongly measurable weights](hyp:hw)
[uniformly almost surely bounded by the weight bound](hyp:hwb), and componentwise
L2 errors of smaller order in probability than the inverse fourth root of sample
size for [propensities](hyp:hrp), [component instrument shares](hyp:hrs),
and [policy masses](hyp:hrt), [the integrated weighted, conditionally corrected
pooled-policy error at sample sizes twice one more than the index, scaled by the
square root of one more than the index, converges in probability to zero](goal). -/
lemma nuisanceRates_binary_conditional_policy_weighted_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (r : RegularIndex L) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hden : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x)
    (w : ℕ → A → X → ℝ) (hw : ∀ n a, AEStronglyMeasurable (w n a) (xLaw M))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, ‖w n a x‖ ≤ W)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrs : FiniteNuisanceRates M μ (fun n a => (eh n a).share r) ((eta0Bin M L).share r))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        w (2*(n+1)) a x * (pooledQBin phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x +
          (∑ z, instProb M z x * RqBin dphi L (eh (2*(n+1)) a)
            r.val.1 r.val.2 (x,z,M.prop z x,0)) -
          pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  simp_rw [fitted_regular_policy_conditional_mean_eq M dphi L _ r]
  exact nuisanceRates_binary_pooling_weighted_root_n_negligible M μ phi dphi hphi hd
    hDerivative L hOrder cpi hov he0 eh heh r c W hc hW hden w hw hwb hrp hrs hrt

-- @node: fitted_fractional_upper_weight_memLp_bound
/-- For [a valid policy map](hyp:hphi) and [admissible fitted binary nuisances](hyp:he),
[the fitted component weight multiplied by the active-branch indicator is square
integrable under the covariate law and almost surely bounded in absolute value
by one](goal). -/
lemma fitted_fractional_upper_weight_memLp_bound
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) (k j : ℕ) :
    MemLp (fun x => regularValue e.gamma k j x * Iact phi L e k j x) 2 (xLaw M) ∧
      (∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x * Iact phi L e k j x‖ ≤ 1) := by
  have hg := fitted_regular_gamma_memLp M L e he k j
  have hi := (fitted_fractional_branches_memLp M phi hphi L e he k j).1
  have hm : AEStronglyMeasurable (fun x => regularValue e.gamma k j x *
      Iact phi L e k j x) (xLaw M) := by
    first | fun_prop | exact hg.1.mul hi.1
  have hb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x * Iact phi L e k j x‖ ≤ 1 := by
    unfold regularValue
    split_ifs with hidx
    · filter_upwards [he.2.2.2.2.1 ⟨(k,j), hidx⟩] with x hx
      have hgamma : ‖e.gamma ⟨(k,j), hidx⟩ x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
        exact hx.2.2
      have hI : ‖Iact phi L e k j x‖ ≤ 1 := by
        unfold Iact indicator
        split_ifs <;> norm_num
      rw [norm_mul]
      exact (mul_le_mul hgamma hI (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · simp
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  exact ⟨MemLp.of_bound hm 1 hb, hb⟩

-- @node: nuisanceRates_fractional_upper_policy_correction_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [invariant baseline
and policy level ordering](hyp:hOrder), [policy overlap](hyp:hov), and admissible
[true](hyp:he0) and [fitted nuisances at every sample size](hyp:heh). If [the
clipping constant is positive](hyp:hc), [the fitted component policy mass is
almost surely at least that constant at every sample size](hyp:hden), and componentwise
L2 errors are of smaller order in probability than the inverse fourth root of
sample size for [propensities](hyp:hrp), [component instrument shares](hyp:hrs),
and [policy masses](hyp:hrt), then [the integrated upper pooled-policy error plus
its conditional residual correction, weighted by the fitted component weight
and active indicator, at sample sizes twice one more than the index and scaled
by the square root of one more than the index, converges in probability to zero](goal). -/
lemma nuisanceRates_fractional_upper_policy_correction_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (r : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hden : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrs : FiniteNuisanceRates M μ (fun n a => (eh n a).share r) ((eta0Bin M L).share r))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        (regularValue (eh (2*(n+1)) a).gamma r.val.1 r.val.2 x *
          Iact phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x) *
        (pooledQBin phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x +
          (∑ z, instProb M z x * RqBin dphi L (eh (2*(n+1)) a)
            r.val.1 r.val.2 (x,z,M.prop z x,0)) -
          pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  apply nuisanceRates_binary_conditional_policy_weighted_root_n_negligible M μ
    phi dphi hphi hd hDerivative L hOrder cpi hov he0 eh heh r c 1 hc zero_le_one hden
    (fun n a x => regularValue (eh n a).gamma r.val.1 r.val.2 x *
      Iact phi L (eh n a) r.val.1 r.val.2 x)
  · intro n a
    first | fun_prop | exact (fitted_fractional_upper_weight_memLp_bound M phi hphi
      L (eh n a) (heh n a) r.val.1 r.val.2).1.1
  · exact fun n a => (fitted_fractional_upper_weight_memLp_bound M phi hphi
      L (eh n a) (heh n a) r.val.1 r.val.2).2
  · exact hrp
  · exact hrs
  · exact hrt

-- At j=1 the policy residual is structurally zero; its baseline treatment
-- correction is handled by the separate regression-centering lemma.
-- @node: nuisanceRates_fractional_lower_policy_correction_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [invariant baseline
and policy level ordering](hyp:hOrder), [policy overlap](hyp:hov), and admissible
[true](hyp:he0) and [fitted nuisances at every sample size](hyp:heh). If [the
clipping constant is positive](hyp:hc), [all fitted component policy masses are
almost surely at least that constant at every sample size](hyp:hden), and componentwise
L2 errors are of smaller order in probability than the inverse fourth root of
sample size for [propensities](hyp:hrp), [every component's instrument
shares](hyp:hrs), and [policy masses](hyp:hrt), then [the integrated lower
pooled-policy error plus its conditional residual correction, weighted by the
fitted component weight and the dominance and active indicators and set to zero
for the first sublevel, at sample sizes twice one more than the index and scaled
by the square root of one more than the index, converges in probability to zero](goal). -/
lemma nuisanceRates_fractional_lower_policy_correction_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (r : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hden : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M L).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        (if r.val.2 = 1 then 0 else
          (regularValue (eh (2*(n+1)) a).gamma r.val.1 r.val.2 x *
            Edom phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x *
            Iact phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x) *
          (pooledQBin phi L (eh (2*(n+1)) a) r.val.1 (r.val.2-1) x +
            (∑ z, instProb M z x * RqBin dphi L (eh (2*(n+1)) a)
              r.val.1 (r.val.2-1) (x,z,M.prop z x,0)) -
            pooledQBin phi L (eta0Bin M L) r.val.1 (r.val.2-1) x)) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  by_cases hj : r.val.2 = 1
  · simp only [if_pos hj, integral_zero, mul_zero]
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  · simp only [if_neg hj]
    have hprev : r.val.1 ≤ L.K ∧ 1 ≤ r.val.2-1 ∧ r.val.2-1 ≤ L.l r.val.1 := by
      have := r.property
      omega
    let t : RegularIndex L := ⟨(r.val.1, r.val.2-1), hprev⟩
    apply nuisanceRates_binary_conditional_policy_weighted_root_n_negligible M μ
      phi dphi hphi hd hDerivative L hOrder cpi hov he0 eh heh t c 1 hc zero_le_one
      (fun n a => hden n a t)
      (fun n a x => regularValue (eh n a).gamma r.val.1 r.val.2 x *
        Edom phi L (eh n a) r.val.1 r.val.2 x * Iact phi L (eh n a) r.val.1 r.val.2 x)
    · intro n a
      first | fun_prop | exact (fitted_fractional_lower_weight_memLp_bound M phi hphi
        L (eh n a) (heh n a) r.val.1 r.val.2).1.1
    · exact fun n a => (fitted_fractional_lower_weight_memLp_bound M phi hphi
        L (eh n a) (heh n a) r.val.1 r.val.2).2
    · exact hrp
    · exact hrs t
    · exact hrt

-- @node: fitted_binary_conditional_policy_weighted_integrable
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [invariant baseline
and policy level ordering](hyp:hOrder), [policy overlap](hyp:hov), admissible
[true](hyp:he0) and [fitted](hyp:he) nuisances, [a positive clipping constant](hyp:hc),
and [a nonnegative weight bound](hyp:hW). If [the fitted component policy mass is
almost surely at least the clipping constant](hyp:hden) and the weight is
[almost everywhere strongly measurable](hyp:hw) and [almost surely bounded by
the weight bound](hyp:hwb), then [the weighted fitted pooled-policy value plus
its conditional policy-residual correction minus the true pooled-policy value
is integrable under the covariate law](goal). -/
lemma fitted_binary_conditional_policy_weighted_integrable
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (r : RegularIndex L)
    (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hden : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (w : X → ℝ) (hw : AEStronglyMeasurable w (xLaw M))
    (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun x => w x *
      (pooledQBin phi L e r.val.1 r.val.2 x +
        (∑ z, instProb M z x * RqBin dphi L e r.val.1 r.val.2 (x,z,M.prop z x,0)) -
        pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x)) (xLaw M) := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  let zs := (L.T r.val.1 r.val.2).toList
  let dp := fun z => finiteL2Error M (e.prop z) (M.prop z)
  let da := fun z => finiteL2Error M (e.share r z) ((eta0Bin M L).share r z)
  let reg := maxErrors (zs.map dp)
  let wt := maxErrors (zs.map da) + finiteL2Error M (e.tauLev r) ((eta0Bin M L).tauLev r)
  exact (fitted_binary_conditional_policy_weighted_quadratic_bound M phi dphi hphi hd
    B Lip c W reg wt hB hLip hc hW (maxErrors_nonneg _)
    (add_nonneg (maxErrors_nonneg _) (Real.sqrt_nonneg _))
    (fun z x p hp => (hder z x p p hp hp).1)
    (fun z x p q hp hq => (hder z x p q hp hq).2)
    L hOrder cpi hov he0 e he r hden w hw hwb
    (fun z hz => le_maxErrors_of_mem (List.mem_map.mpr
      ⟨z, by simpa only [zs, Finset.mem_toList] using hz, rfl⟩))
    (fun z hz => (show da z ≤ maxErrors (zs.map da) from
      le_maxErrors_of_mem (List.mem_map.mpr
        ⟨z, by simpa only [zs, Finset.mem_toList] using hz, rfl⟩)).trans
          (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    (le_add_of_nonneg_left (maxErrors_nonneg _))).1

-- @node: fitted_fractional_regression_centering_integrable
/-- For [a valid policy map](hyp:hphi) and admissible [reference](hyp:he0) and
[fitted](hyp:he) nuisances, suppose [the clipping constant is positive](hyp:hc)
and [each fitted level mass is almost surely at least that constant](hyp:hclip).
Then [the fitted component weight times its regression conditional mean, after
subtracting the boundary indicator times the boundary error and, for the first
sublevel, the dominance and active indicators times the level-propensity error,
is integrable under the covariate law](goal). -/
lemma fitted_fractional_regression_centering_integrable
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c) (k j : ℕ)
    (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    Integrable (fun x => regularValue e.gamma k j x *
      (binaryRegularRegressionMean phi L e0 e k j x -
        Dbd phi L e k j x *
          ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
            (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)) -
        (if j = 1 then Edom phi L e k j x * Iact phi L e k j x *
          (positiveValue e.pLev k x - positiveValue e0.pLev k x) else 0)))
      (xLaw M) := by
  let B := fun x => regularValue e.gamma k j x *
    Dbd phi L e k j x * binaryBoundaryCenteredResidual L e0 e k x
  let T := fun x => if j = 1 then regularValue e.gamma k j x *
    Edom phi L e k j x * Iact phi L e k j x *
    (positiveValue e0.piLev k x *
      (positiveValue e0.pLev k x - positiveValue e.pLev k x) /
        positiveValue e.piLev k x +
      (positiveValue e.pLev k x - positiveValue e0.pLev k x)) else 0
  have iB : Integrable (B) (xLaw M) := by
    have hgam := fitted_regular_gamma_memLp M L e he k j
    have hD := (fitted_fractional_branches_memLp M phi hphi L e he k j).2.1
    have hw : AEStronglyMeasurable (fun x => regularValue e.gamma k j x *
        Dbd phi L e k j x) (xLaw M) := by
      first | fun_prop | exact hgam.1.mul hD.1
    have hb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x *
        Dbd phi L e k j x‖ ≤ 1 := by
      unfold regularValue
      split_ifs with hi
      · filter_upwards [he.2.2.2.2.1 ⟨(k,j), hi⟩] with x hx
        have hg : ‖e.gamma ⟨(k,j), hi⟩ x‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]; exact hx.2.2
        have hd : ‖Dbd phi L e k j x‖ ≤ 1 := by
          unfold Dbd indicator; split_ifs <;> norm_num
        rw [norm_mul]
        exact (mul_le_mul hg hd (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      · simp
    exact (fitted_boundary_centered_residual_weighted_integral_bound M L e0 e
      he0 he c 1 hc zero_le_one k hclip _ hw hb).1
  have iT : Integrable (T) (xLaw M) := by
    dsimp only [T]
    by_cases hj : j = 1
    · simp only [if_pos hj]
      have hw := fitted_fractional_lower_weight_memLp_bound M phi hphi L e he k j
      exact (fitted_positive_treatment_centering_ae_weighted_L2_bound M L e0 e
        he0 he k c 1 hc zero_le_one hclip _ hw.1.1 hw.2).1
    · simp only [if_neg hj]
      exact integrable_zero _ _ _
  apply (iB.sub iT).congr
  exact Eventually.of_forall (fun x => by
    dsimp only [Pi.sub_apply]
    rw [fitted_fractional_regression_centering_identity phi L e0 e k j x]
    dsimp only [B, T]
    by_cases hj : j = 1
    · simp only [if_pos hj]; ring
    · simp only [if_neg hj]; ring)

-- At j=1, the structural policy residual is zero and the lower fitted level
-- is the baseline regression; its error belongs to the regression block.
-- @node: fitted_fractional_component_centered_bias_eq
/-- [The fitted fractional hinge plus its regression and policy conditional-mean
corrections minus the reference hinge equals the hinge remainder plus the centered
regression term plus the active indicator times the corrected upper pooled-policy
error, minus the dominance and active indicators times the corrected lower
pooled-policy error; the lower term is zero at the first sublevel, where the
centered regression term instead subtracts those indicators times the
level-propensity error](goal). -/
lemma fitted_fractional_component_centered_bias_eq
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 e : NuisanceBin L) (k j : ℕ) (x : X) :
    let Q := fun i => ∑ z, instProb M z x * RqBin dphi L e k i (x,z,M.prop z x,0)
    hMinus phi L e k j x + binaryRegularRegressionMean phi L e0 e k j x +
      binaryRegularPolicyMean M phi dphi L e k j x - hMinus phi L e0 k j x =
    binaryFittedHingeRemainder
      (pooledQBin phi L e0 k j x) (pooledQBin phi L e0 k (j-1) x)
      (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
      (pooledQBin phi L e k j x) (pooledQBin phi L e k (j-1) x)
      (positiveValue e.pLev (k+1) x - binFullJ L e k x) +
    (binaryRegularRegressionMean phi L e0 e k j x - Dbd phi L e k j x *
      ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
        (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)) -
      (if j = 1 then Edom phi L e k j x * Iact phi L e k j x *
        (positiveValue e.pLev k x - positiveValue e0.pLev k x) else 0)) +
    Iact phi L e k j x * (pooledQBin phi L e k j x + Q j - pooledQBin phi L e0 k j x) -
    (if j = 1 then 0 else Edom phi L e k j x * Iact phi L e k j x *
      (pooledQBin phi L e k (j-1) x + Q (j-1) - pooledQBin phi L e0 k (j-1) x)) := by
  dsimp only
  rw [hMinus_binaryFittedHingeRemainder_eq]
  dsimp only [binaryRegularPolicyMean]
  by_cases hj : j = 1
  · subst j
    simp only [Nat.sub_self, pooledQBin, RqBin, true_or, ite_true,
      mul_zero, Finset.sum_const_zero]
    ring
  · simp only [if_neg hj]
    ring

-- @node: nuisanceRates_fractional_component_conditional_bias_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), assume [invariant baseline
and policy level ordering](hyp:hOrder), [policy overlap](hyp:hov), and admissible
[true](hyp:he0) and [fitted nuisances at every sample size](hyp:heh). Suppose
[the clipping constant](hyp:hc) and [the separation constant](hyp:hsep) are positive,
all fitted [level masses](hyp:hpi) and [policy masses](hyp:htau) are almost surely
at least the clipping constant, componentwise L2 errors are of smaller order in
probability than the inverse fourth root of sample size for [propensities](hyp:hrp),
[level propensities](hyp:hrlev), [treated-outcome masses](hyp:hrP), [level masses](hyp:hrpi),
[every component's instrument shares](hyp:hrs), and [policy masses](hyp:hrt), and
[the true pooled-policy interval width and the boundary's distances from both
endpoints are almost surely at least the separation constant](hyp:hgap). Then
[the integrated conditional fractional-component bias, including the regression
and policy corrections and multiplied by the fitted component weight, at sample
sizes twice one more than the index and scaled by the square root of one more
than the index, converges in probability to zero](goal). -/
lemma nuisanceRates_fractional_component_conditional_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
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
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        regularValue (eh (2*(n+1)) a).gamma r.val.1 r.val.2 x *
          (hMinus phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x +
            binaryRegularRegressionMean phi L (eta0Bin M L) (eh (2*(n+1)) a)
              r.val.1 r.val.2 x +
            binaryRegularPolicyMean M phi dphi L (eh (2*(n+1)) a) r.val.1 r.val.2 x -
            hMinus phi L (eta0Bin M L) r.val.1 r.val.2 x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
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
  have hH := nuisanceRates_fractional_hinge_bias_root_n_negligible M μ phi dphi hphi hd
    hDerivative L (eta0Bin M L) eh he0 heh hrp hrlev hrP hrs r.val.1 r.val.2 sep hsep hgap
  have hR := nuisanceRates_fractional_regression_centering_root_n_negligible M μ phi hphi
    L (eta0Bin M L) eh he0 heh c hc r.val.1 r.val.2 hpi hrP hrlev hrpi
  have hU := nuisanceRates_fractional_upper_policy_correction_root_n_negligible M μ
    phi dphi hphi hd hDerivative L hOrder cpi hov he0 eh heh r c hc
    (fun n a => htau n a r) hrp (hrs r) hrt
  have hV := nuisanceRates_fractional_lower_policy_correction_root_n_negligible M μ
    phi dphi hphi hd hDerivative L hOrder cpi hov he0 eh heh r c hc htau hrp hrs hrt
  have hRneg := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt hR
  have hUneg := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt hU
  have hs := ((hH.sub hRneg).sub hUneg).sub hV
  simp only [neg_zero, sub_zero, sub_neg_eq_add] at hs
  convert hs using 1
  funext n a
  have hid : (fun x => regularValue (eh (2*(n+1)) a).gamma r.val.1 r.val.2 x *
      (hMinus phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x +
        binaryRegularRegressionMean phi L (eta0Bin M L) (eh (2*(n+1)) a) r.val.1 r.val.2 x +
        binaryRegularPolicyMean M phi dphi L (eh (2*(n+1)) a) r.val.1 r.val.2 x -
        hMinus phi L (eta0Bin M L) r.val.1 r.val.2 x)) =
      (fun x => H (2*(n+1)) a x + R (2*(n+1)) a x + U (2*(n+1)) a x - V (2*(n+1)) a x) := by
    funext x
    rw [fitted_fractional_component_centered_bias_eq M phi dphi L (eta0Bin M L)
      (eh (2*(n+1)) a) r.val.1 r.val.2 x]
    dsimp only [H, R, U, V]
    by_cases hj : r.val.2 = 1
    · simp only [if_pos hj]; ring
    · simp only [if_neg hj]; ring
  rw [hid, integral_sub ((iH _ a).fun_add (iR _ a) |>.fun_add (iU _ a)) (iV _ a),
    integral_add ((iH _ a).fun_add (iR _ a)) (iU _ a),
    integral_add (iH _ a) (iR _ a), mul_sub, mul_add, mul_add]

end Papers.TbsPrteOptimalTransport
