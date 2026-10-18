module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousPolicyResidual
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalPolicyBias
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousPooledJoint
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousPoolingRates
/-! Quadratic pooling cancellation for continuous score nuisances.
The shared-coordinate carrier transfers the simplex and policy Taylor bounds
without any binary restriction on the outcome. -/
public section

set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedTactic false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_pooling_weighted_quadratic_bound
/-- Suppose [the policy map is valid](hyp:hphi) [with the specified derivative](hyp:hd),
[the derivative bound is nonnegative](hyp:hB), [the Lipschitz constant is nonnegative](hyp:hLip),
[the denominator floor is positive](hyp:hc), and [the weight and error bounds are
nonnegative](hyp:hW,hreg,hwt). Assume [the derivative is bounded by the derivative
bound](hyp:hbound) and [is Lipschitz with the specified constant on the unit interval](hyp:hlip),
[policy and baseline propensities preserve the level ordering](hyp:hOrder), [policy
overlap holds](hyp:hov), [true and fitted nuisances are admissible](hyp:he0,he), and
[the fitted policy mass exceeds the denominator floor almost surely](hyp:hden).
For [an almost surely strongly measurable weight](hyp:hw) [bounded in norm by the
weight bound](hyp:hwb), if [each policy-set propensity L² error is at most the propensity
error bound](hyp:hpNorm), [each share L² error is at most the share error bound](hyp:haNorm),
and [the policy-mass L² error is at most the same share error bound](hyp:htNorm),
[the weighted, first-order-corrected pooling error is integrable and its absolute mean
is at most the weight bound times the policy-set cardinality times the sum of the
Lipschitz constant times the squared propensity error bound and the derivative bound
times one plus the reciprocal denominator floor times the product of the two error bounds](goal). -/
lemma fitted_continuous_pooling_weighted_quadratic_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (B Lip c W reg wt : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip)
    (hc : 0 < c) (hW : 0 ≤ W) (hreg : 0 ≤ reg) (hwt : 0 ≤ wt)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p - r|)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : ContAdmissible M L (trueNuisance M L)) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (r : RegularIndex L)
    (hden : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (w : X → ℝ) (hw : AEStronglyMeasurable w (xLaw M))
    (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W)
    (hpNorm : ∀ z ∈ L.T r.val.1 r.val.2,
      finiteL2Error M (e.prop z) (M.prop z) ≤ reg)
    (haNorm : ∀ z ∈ L.T r.val.1 r.val.2,
      finiteL2Error M (e.share r z) ((trueNuisance M L).share r z) ≤ wt)
    (htNorm : finiteL2Error M (e.tauLev r) ((trueNuisance M L).tauLev r) ≤ wt) :
    let R := fun x => pooledQ phi L e r.val.1 r.val.2 x +
      (e.tauLev r x)⁻¹ * (∑ z ∈ L.T r.val.1 r.val.2,
        instProb M z x * dphi z x (e.prop z x) * (M.prop z x - e.prop z x)) -
      pooledQ phi L (trueNuisance M L) r.val.1 r.val.2 x
    Integrable (fun x => w x * R x) (xLaw M) ∧
      |∫ x, w x * R x ∂xLaw M| ≤
        W * ((L.T r.val.1 r.val.2).card : ℝ) *
          (Lip * reg ^ 2 + (B + B / c) * (reg * wt)) := by
  have heb := continuousTailCoordinates_admissible M L e he
  have he0b := continuousTailCoordinates_admissible M L (trueNuisance M L) he0
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hs0 := he0b.2.2.2.2.2.2.2.2.1 r
  have hsh := heb.2.2.2.2.2.2.2.2.1 r
  dsimp only [continuousTailCoordinates] at hs0 hsh
  have ht (x : X) : 0 < (levelSetProb M L).2 r.val.1 r.val.2 x :=
    hov.1.trans_le (hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have hj0 : r.val.2 ≠ 0 := by have := r.property; omega
  have hj : ¬ L.l r.val.1 < r.val.2 := not_lt.mpr r.property.2.2
  have hq : ∀ᵐ x ∂xLaw M,
      pooledQ phi L (trueNuisance M L) r.val.1 r.val.2 x = L.qLev r.val.1 r.val.2 x := by
    filter_upwards [hs0] with x hx
    simp only [pooledQ, shareValue, if_neg hj0, if_neg hj, dif_pos r.property]
    calc
      _ = ∑ z ∈ L.T r.val.1 r.val.2,
          (trueNuisance M L).share r z x * L.qLev r.val.1 r.val.2 x := by
        apply Finset.sum_congr rfl
        intro z hz
        have hc := (hOrder.2.2.2.2.2.2.1 x r.val.1 r.val.2 z r.property.1
          r.property.2.1 r.property.2.2).mp hz
        simpa only [trueNuisance, policyProp] using congrArg ((trueNuisance M L).share r z x * ·) hc
      _ = _ := by rw [← Finset.sum_mul, hx.1, one_mul]
  have hp z : MemLp (fun x => e.prop z x - M.prop z x) 2 (xLaw M) :=
    ((fitted_prop_gammaTail_memLp M L (continuousTailCoordinates L e) heb).1 z).sub
      ((fitted_prop_gammaTail_memLp M L (continuousTailCoordinates L (trueNuisance M L)) he0b).1 z)
  have hshare (e' : NuisanceBin L) (he' : BinAdmissible M L e') (z : Z) :
      MemLp (e'.share r z) 2 (xLaw M) := by
    apply MemLp.of_bound (he'.2.2.2.2.2.2.2.1 r z).aestronglyMeasurable 1
    filter_upwards [he'.2.2.2.2.2.2.1 r z] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have ha z : MemLp (fun x => e.share r z x - (trueNuisance M L).share r z x) 2 (xLaw M) := (hshare (continuousTailCoordinates L e) heb z).sub (hshare (continuousTailCoordinates L (trueNuisance M L)) he0b z)
  have htauMem (e' : NuisanceBin L) (he' : BinAdmissible M L e') :
      MemLp (e'.tauLev r) 2 (xLaw M) := by
    apply MemLp.of_bound (he'.2.2.2.2.2.1 r).1.aestronglyMeasurable 1
    filter_upwards [he'.2.2.2.2.1 r] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1.1]
    exact hx.1.2
  have htau : MemLp (fun x => e.tauLev r x - (trueNuisance M L).tauLev r x) 2 (xLaw M) := by
    convert (htauMem (continuousTailCoordinates L e) heb).sub (htauMem (continuousTailCoordinates L (trueNuisance M L)) he0b) using 1
    funext x
    rfl
  have hm : AEStronglyMeasurable (fun x =>
      (∑ z ∈ L.T r.val.1 r.val.2, e.share r z x * phi z x (e.prop z x)) +
        (e.tauLev r x)⁻¹ * (∑ z ∈ L.T r.val.1 r.val.2,
          instProb M z x * dphi z x (e.prop z x) * (M.prop z x - e.prop z x)) -
        pooledQ phi L (trueNuisance M L) r.val.1 r.val.2 x) (xLaw M) := by
    first | fun_prop | skip
    apply AEStronglyMeasurable.sub
    · apply AEStronglyMeasurable.add
      · exact (fitted_pooledQBin_memLp M phi hphi L (continuousTailCoordinates L e) heb r.val.1 r.val.2).1
          |>.congr (Eventually.of_forall (fun x => by
            simp only [pooledQBin, continuousTailCoordinates, if_neg hj0, if_neg hj, dif_pos r.property]))
      · apply (heb.2.2.2.2.2.1 r).1.inv.aestronglyMeasurable.mul
        convert
          (Finset.aestronglyMeasurable_sum (L.T r.val.1 r.val.2) (fun z hz => by
            have hmass : Measurable (instProb M z) :=
              (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal
            exact (hmass.aestronglyMeasurable.mul
              (fitted_policy_derivative_aestronglyMeasurable M phi dphi hphi hd L (continuousTailCoordinates L e) heb z)).mul
              ((hp z).1.neg))) using 1
        funext x
        simp only [Finset.sum_apply, Pi.mul_apply, Pi.neg_apply, neg_sub, continuousTailCoordinates]
    · exact (fitted_pooledQBin_memLp M phi hphi L (continuousTailCoordinates L (trueNuisance M L)) he0b r.val.1 r.val.2).1
  have hb := fitted_pooled_policy_ae_weighted_quadratic_bound
    (xLaw M) phi dphi hd B Lip c hB hLip hc hbound hlip (L.T r.val.1 r.val.2)
    M.prop e.prop ((trueNuisance M L).share r) (e.share r) (instProb M)
    (pooledQ phi L (trueNuisance M L) r.val.1 r.val.2)
    ((trueNuisance M L).tauLev r) (e.tauLev r) hden
    (Eventually.of_forall (fun x z hz => by
      simp only [trueNuisance, levelShares, if_pos hz, div_mul_cancel₀ _ (ht x).ne']))
    (Eventually.of_forall (fun x z hz => M.rangeProp z x))
    (by filter_upwards [ae_all_iff.mpr heb.1] with x hx; exact fun z _ => hx z)
    (by
      filter_upwards [hq] with x hx
      intro z hz
      rw [hx]
      exact (hOrder.2.2.2.2.2.2.1 x r.val.1 r.val.2 z r.property.1
        r.property.2.1 r.property.2.2).mp hz)
    (hs0.mono fun x hx => hx.1) (hsh.mono fun x hx => hx.1)
    (by
      filter_upwards [ae_all_iff.mpr (he0b.2.2.2.2.2.2.1 r)] with x hx
      intro z hz
      change ∀ z, (trueNuisance M L).share r z x ∈ Icc (0 : ℝ) 1 at hx
      rw [abs_of_nonneg (hx z).1]
      exact (hx z).2)
    (fun z _ => hp z) (fun z _ => ha z)
    (by simpa only [regularValue, dif_pos r.property] using htau) hm w W reg wt
    hW hreg hwt hw hwb
    (fun z hz => by simpa only [← l2Error_eq_eLpNorm M _ _ (hp z)] using hpNorm z hz)
    (fun z hz => by simpa only [← l2Error_eq_eLpNorm M _ _ (ha z)] using haNorm z hz)
    (by
      have htt : MemLp (fun x => e.tauLev r x - (trueNuisance M L).tauLev r x) 2 (xLaw M) := by
        simpa only [regularValue, dif_pos r.property] using htau
      simpa only [← l2Error_eq_eLpNorm M _ _ htt] using htNorm)
  simpa only [pooledQ, shareValue, if_neg hj0, if_neg hj, dif_pos r.property] using hb

-- All envelopes are constructed from the original propensity, share and
-- denominator errors. Fitted branch weights may vary with the training data.
-- @node: nuisanceRates_continuous_pooling_weighted_root_n_negligible
/-- Assume [a valid policy map](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [preservation of level ordering by
policy and baseline propensities](hyp:hOrder), [policy overlap](hyp:hov), and
[admissible true and fitted nuisances](hyp:he0,heh). If [the denominator floor is
positive](hyp:hc), [the weight bound is nonnegative](hyp:hW), [all fitted policy masses
at the regular index exceed the floor almost surely](hyp:hden), [the weights are almost
surely strongly measurable](hyp:hw) [and uniformly bounded in norm by the weight
bound](hyp:hwb), [propensity L² errors toward truth are smaller in probability than the
inverse fourth root of sample size](hyp:hrp), [share L² errors have that same rate](hyp:hrs),
and [policy-mass L² errors have that same rate](hyp:hrt),
[the mean weighted pooling error with its
first-order propensity correction, multiplied by the square root of one plus the index,
converges in probability to zero when fits and weights use sample sizes twice one plus
the index](goal). -/
lemma nuisanceRates_continuous_pooling_weighted_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : ContAdmissible M L (trueNuisance M L)) (eh : ℕ → A → NuisanceCont L)
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (r : RegularIndex L) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hden : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x)
    (w : ℕ → A → X → ℝ)
    (hw : ∀ n a, AEStronglyMeasurable (w n a) (xLaw M))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, ‖w n a x‖ ≤ W)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrs : FiniteNuisanceRates M μ (fun n a => (eh n a).share r) ((trueNuisance M L).share r))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (trueNuisance M L).tauLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        w (2*(n+1)) a x *
          (pooledQ phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x +
            ((eh (2*(n+1)) a).tauLev r x)⁻¹ *
              (∑ z ∈ L.T r.val.1 r.val.2, instProb M z x *
                dphi z x ((eh (2*(n+1)) a).prop z x) *
                (M.prop z x - (eh (2*(n+1)) a).prop z x)) -
            pooledQ phi L (trueNuisance M L) r.val.1 r.val.2 x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  let zs := (L.T r.val.1 r.val.2).toList
  let dp := fun n a z => finiteL2Error M ((eh (2*(n+1)) a).prop z) (M.prop z)
  let ds := fun n a z => finiteL2Error M ((eh (2*(n+1)) a).share r z)
    ((trueNuisance M L).share r z)
  let reg := fun n a => maxErrors (zs.map (dp n a))
  let wt := fun n a => maxErrors (zs.map (ds n a)) +
    finiteL2Error M ((eh (2*(n+1)) a).tauLev r) ((trueNuisance M L).tauLev r)
  have hr := nuisanceRates_finite_maxErrors M μ (fun n a => (eh n a).prop)
    M.prop zs hrp
  have ht := (nuisanceRates_finite_maxErrors M μ (fun n a => (eh n a).share r)
    ((trueNuisance M L).share r) zs hrs).add_eventually_nonneg_rate
      (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hrt r)
  let C := W * ((L.T r.val.1 r.val.2).card : ℝ) * (Lip + B + B / c) + 1
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt C
    (by dsimp only [C]; positivity) hr ht
  intro n a
  have hreg : 0 ≤ reg n a := maxErrors_nonneg _
  have hwt : 0 ≤ wt n a := add_nonneg (maxErrors_nonneg _) (Real.sqrt_nonneg _)
  have hb := (fitted_continuous_pooling_weighted_quadratic_bound M phi dphi hphi hd
    B Lip c W (reg n a) (wt n a) hB hLip hc hW hreg hwt
    (fun z x p hp => (hder z x p p hp hp).1)
    (fun z x p q hp hq => (hder z x p q hp hq).2)
    L hOrder cpi hov he0 (eh (2*(n+1)) a) (heh _ a) r (hden _ a)
    (w (2*(n+1)) a) (hw _ a) (hwb _ a)
    (fun z hz => le_maxErrors_of_mem (List.mem_map.mpr
      ⟨z, by simpa only [zs, Finset.mem_toList] using hz, rfl⟩))
    (fun z hz => (show ds n a z ≤ maxErrors (zs.map (ds n a)) from
      le_maxErrors_of_mem (List.mem_map.mpr
        ⟨z, by simpa only [zs, Finset.mem_toList] using hz, rfl⟩)).trans
        (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    (le_add_of_nonneg_left (maxErrors_nonneg _))).2
  apply hb.trans
  have hn : 0 ≤ reg n a * wt n a := mul_nonneg hreg hwt
  calc
    _ ≤ W * ((L.T r.val.1 r.val.2).card : ℝ) *
        ((Lip + B + B / c) * (reg n a ^ 2 + reg n a * wt n a)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg (by positivity : 0 ≤ B + B / c) (sq_nonneg (reg n a)),
        mul_nonneg hLip hn]
    _ = (C - 1) * (reg n a ^ 2 + reg n a * wt n a) := by dsimp only [C]; ring
    _ ≤ C * (reg n a ^ 2 + reg n a * wt n a) :=
      mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (sq_nonneg _) hn)


-- @node: continuous_regular_policy_conditional_mean_eq
/-- [Averaging the fitted continuous policy residual over instruments at fixed covariates,
with treatment replaced by its true propensity and outcome set to zero, equals the
instrument-probability-weighted sum of policy derivatives times true-minus-fitted
propensities over the regular policy set, divided by the fitted policy mass](goal). -/
lemma continuous_regular_policy_conditional_mean_eq
    (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L)
    (r : RegularIndex L) (x : X) :
    (∑ z, instProb M z x * RqCont dphi L e r.val.1 r.val.2 (x,z,M.prop z x,0)) =
      (e.tauLev r x)⁻¹ * (∑ z ∈ L.T r.val.1 r.val.2,
        instProb M z x * dphi z x (e.prop z x) * (M.prop z x - e.prop z x)) := by
  exact fitted_regular_policy_conditional_mean_eq M dphi L
    (continuousTailCoordinates L e) r x

-- The tower identity moves the derived pooling remainder to the actual score,
-- so this statement includes the estimated residual rather than only a plug-in.
-- @node: nuisanceRates_continuous_observed_policy_weighted_root_n_negligible
/-- Assume [the threshold-crossing model](hyp:h), [a valid policy map](hyp:hphi)
[with the specified derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[preserved level ordering](hyp:hOrder), [policy overlap](hyp:hov), and [admissible true
and fitted nuisances](hyp:he0,heh). If [the denominator floor is positive](hyp:hc),
[the weight bound is nonnegative](hyp:hW), [fitted policy masses exceed the floor almost
surely](hyp:hden), [the weights are measurable](hyp:hw) [and uniformly bounded in norm
by the weight bound](hyp:hwb), [propensity L² errors toward truth are smaller in
probability than the inverse fourth root of sample size](hyp:hrp), [share L² errors have
that same rate](hyp:hrs), and [policy-mass L² errors have that same rate](hyp:hrt),
[the observation-law mean
of the weighted fitted pooled endpoint plus fitted policy residual minus true pooled
endpoint, multiplied by the square root of one plus the index, converges in probability
to zero when fits and weights use sample sizes twice one plus the index](goal). -/
lemma nuisanceRates_continuous_observed_policy_weighted_root_n_negligible
    (h : ThresholdCrossing M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : ContAdmissible M L (trueNuisance M L)) (eh : ℕ → A → NuisanceCont L)
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (r : RegularIndex L) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hden : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x)
    (w : ℕ → A → X → ℝ) (hw : ∀ n a, Measurable (w n a))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, ‖w n a x‖ ≤ W)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrs : FiniteNuisanceRates M μ (fun n a => (eh n a).share r) ((trueNuisance M L).share r))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (trueNuisance M L).tauLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        w (2*(n+1)) a o.1 *
          (pooledQ phi L (eh (2*(n+1)) a) r.val.1 r.val.2 o.1 +
            RqCont dphi L (eh (2*(n+1)) a) r.val.1 r.val.2 o -
            pooledQ phi L (trueNuisance M L) r.val.1 r.val.2 o.1) ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_continuous_pooling_weighted_root_n_negligible M μ
    phi dphi hphi hd hDerivative L hOrder cpi hov he0 eh heh r c W hc hW hden
    w (fun n a => (hw n a).aestronglyMeasurable) hwb hrp hrs hrt
  simp_rw [← continuous_regular_policy_conditional_mean_eq M dphi L _ r] at hs
  convert hs using 1
  funext n a
  congr 1
  have htower := population_continuous_weighted_pooled_fitted_mean M h phi dphi hphi hd
    hDerivative L (eh (2*(n+1)) a) (heh _ a) r c hc (hden _ a)
    (w (2*(n+1)) a) (hw _ a) W (hwb _ a)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have iw : MemLp (w (2*(n+1)) a) 2 (xLaw M) :=
    MemLp.of_bound (hw _ a).aestronglyMeasurable W (hwb _ a)
  have iq := iw.integrable_mul
    (fitted_continuous_pooledQ_memLp M phi hphi L _ he0 r.val.1 r.val.2)
  change Integrable (fun x => w (2*(n+1)) a x *
    pooledQ phi L (trueNuisance M L) r.val.1 r.val.2 x) (xLaw M) at iq
  have iqobs : Integrable (fun o : Obs X Z => w (2*(n+1)) a o.1 *
      pooledQ phi L (trueNuisance M L) r.val.1 r.val.2 o.1) (observationLaw M) :=
    (observationLaw_fst_measurePreserving M).integrable_comp_of_integrable iq
  simp_rw [mul_sub]
  rw [integral_sub htower.1 iqobs, integral_sub htower.2.1 iq, htower.2.2]
  congr 1
  have hmp := observationLaw_fst_measurePreserving M
  rw [← hmp.map_eq] at iq ⊢
  exact (integral_map hmp.aemeasurable iq.1).symm

-- Both gamma and the moving quantile are estimated; clipping alone bounds
-- their product, so no convergence rate for this multiplier is assumed.
-- @node: encoded_continuous_observed_quantile_policy_bias_root_n_negligible
/-- Assume [the threshold-crossing model](hyp:h), [a valid policy map](hyp:hphi)
[with the specified derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[preserved level ordering](hyp:hOrder), [policy overlap](hyp:hov), [admissible true
and fitted nuisances](hyp:he0,heh), and [encoded componentwise L² errors toward truth
smaller in probability than the inverse fourth root of sample size](hyp:hr).
If [the denominator floor is positive](hyp:hc) and [fitted policy masses at the selected
regular index exceed it almost surely](hyp:hden), [the observation-law mean of the
fitted pooled endpoint plus fitted policy residual minus true pooled endpoint, weighted
by the fitted regular effect coefficient times the selected fitted quantile and
multiplied by the square root of one plus the index, converges in probability to zero
along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_observed_quantile_policy_bias_root_n_negligible
    (h : ThresholdCrossing M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (g r : RegularIndex L) (k b : ℕ) (c : ℝ) (hc : 0 < c)
    (hden : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ o : Obs X Z,
        ((eh (2*(n+1)) a).gamma g o.1 * nuValue M (eh (2*(n+1)) a) k b o.1) *
          (pooledQ phi L (eh (2*(n+1)) a) r.val.1 r.val.2 o.1 +
            RqCont dphi L (eh (2*(n+1)) a) r.val.1 r.val.2 o -
            pooledQ phi L (trueNuisance M L) r.val.1 r.val.2 o.1) ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  obtain ⟨hrp, _, _, hrt, hrs, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrs' : FiniteNuisanceRates M μ (fun n a => (eh n a).share r)
      ((trueNuisance M L).share r) := by
    intro z
    have heq n a : finiteL2Error M ((restrictContShares L (eh n a)).share r z)
        ((restrictContShares L (trueNuisance M L)).share r z) =
        finiteL2Error M ((eh n a).share r z) ((trueNuisance M L).share r z) := by
      unfold finiteL2Error
      congr 1
      apply integral_congr_ae
      filter_upwards [restrictContShares_eq_of_admissible M L _ (heh n a),
        restrictContShares_eq_of_admissible M L _ he0] with x hx hy
      rw [hx r z, hy r z]
    simpa only [heq] using hrs r z
  let w := fun n a x => (eh n a).gamma g x * nuValue M (eh n a) k b x
  have hw n a : Measurable (w n a) := by
    first | fun_prop | skip
    have hg := (continuousTailCoordinates_admissible M L _ (heh n a)).2.2.2.2.2.1 g
    exact hg.2.mul (continuous_admissible_nuValue_measurable M L _ (heh n a) k b)
  have hwb n a : ∀ᵐ x ∂xLaw M, ‖w n a x‖ ≤ |M.yMin| + |M.yMax| := by
    have hg := (continuousTailCoordinates_admissible M L _ (heh n a)).2.2.2.2.1 g
    filter_upwards [hg, continuous_admissible_nuValue_abs_bound M L _ (heh n a) k b]
      with x hx hn
    change _ ∈ Icc (0 : ℝ) 1 ∧ (eh n a).gamma g x ∈ Icc (0 : ℝ) 1 at hx
    dsimp only [w]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.2.1]
    exact (mul_le_mul hx.2.2 hn (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  exact nuisanceRates_continuous_observed_policy_weighted_root_n_negligible M h μ
    phi dphi hphi hd hDerivative L hOrder cpi hov he0 eh heh r c
    (|M.yMin| + |M.yMax|) hc (by positivity) hden w hw hwb hrp hrs' hrt

end Papers.TbsPrteOptimalTransport
