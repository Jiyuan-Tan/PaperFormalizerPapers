module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLWeightedPooling
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPooledPolicyConvergence
/-! Second-order pooling bias for the actual binary score nuisances.
The population instrument masses and fitted simplex shares supply the inputs
to the weighted pooling bound; no residual-bias assumption is used. -/
public section

set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
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

-- fun_prop rejects registration of this dependent derivative graph rule.
-- @node: fitted_policy_derivative_aestronglyMeasurable
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) and
[an admissible binary nuisance record](hyp:he),
[the policy derivative evaluated at the fitted propensity for any fixed instrument
is almost everywhere strongly measurable under the covariate distribution](goal). -/
lemma fitted_policy_derivative_aestronglyMeasurable
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (L : LevelData Z X)
    (e : NuisanceBin L) (he : BinAdmissible M L e) (z : Z) :
    AEStronglyMeasurable (fun x => dphi z x (e.prop z x)) (xLaw M) := by
  first | fun_prop | skip
  let pc : Z → X → ℝ := fun z x => max 0 (min 1 (e.prop z x))
  have hm : Measurable (fun zx : Z × X => pc zx.1 zx.2) := by
    apply measurable_from_prod_countable_right
    intro z
    have hp := he.2.1 z
    dsimp only [pc]
    fun_prop
  have hr : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hdm := (policy_derivative_graph_measurable phi dphi hphi hd pc hm hr).comp
    ((measurable_const : Measurable (fun _ : X => z)).prodMk measurable_id)
  apply hdm.aestronglyMeasurable.congr
  filter_upwards [he.1 z] with x hx
  simp only [Function.comp_apply, id_eq, pc, min_eq_right hx.2, max_eq_right hx.1]

-- @node: fitted_binary_pooling_weighted_quadratic_bound
/-- Suppose [the policy map is valid](hyp:hphi) with [the specified derivative](hyp:hd),
[the derivative envelope](hyp:hB), [its Lipschitz constant](hyp:hLip),
[the weight envelope](hyp:hW), and [the propensity and mass-error bounds](hyp:hreg,hwt)
are nonnegative, and [the denominator lower bound is positive](hyp:hc).
Assume [the derivative is bounded by its envelope on the unit interval](hyp:hbound)
and [is Lipschitz there with the chosen constant](hyp:hlip),
[level ordering is covariate invariant](hyp:hOrder), [policy overlap holds](hyp:hov),
[the true record](hyp:he0) and [the fitted record](hyp:he) are admissible,
[the fitted mass of the selected regular group exceeds the denominator bound almost surely](hyp:hden),
[the weight is almost everywhere strongly measurable](hyp:hw) and
[bounded in norm by its envelope](hyp:hwb), and the selected group's
[propensity errors](hyp:hpNorm), [share errors](hyp:haNorm), and [mass error](hyp:htNorm)
satisfy their respective L2 bounds. Then [the weighted pooled-policy error plus its
inverse-mass derivative correction is integrable, and its absolute mean is at most
the weight envelope times group size times the sum of the Lipschitz constant times
the squared propensity-error bound and the derivative envelope times one plus the
reciprocal denominator bound times the product of the propensity and mass-error bounds](goal). -/
lemma fitted_binary_pooling_weighted_quadratic_bound
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
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (r : RegularIndex L)
    (hden : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (w : X → ℝ) (hw : AEStronglyMeasurable w (xLaw M))
    (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W)
    (hpNorm : ∀ z ∈ L.T r.val.1 r.val.2,
      finiteL2Error M (e.prop z) (M.prop z) ≤ reg)
    (haNorm : ∀ z ∈ L.T r.val.1 r.val.2,
      finiteL2Error M (e.share r z) ((eta0Bin M L).share r z) ≤ wt)
    (htNorm : finiteL2Error M (e.tauLev r) ((eta0Bin M L).tauLev r) ≤ wt) :
    let R := fun x => pooledQBin phi L e r.val.1 r.val.2 x +
      (e.tauLev r x)⁻¹ * (∑ z ∈ L.T r.val.1 r.val.2,
        instProb M z x * dphi z x (e.prop z x) * (M.prop z x - e.prop z x)) -
      pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x
    Integrable (fun x => w x * R x) (xLaw M) ∧
      |∫ x, w x * R x ∂xLaw M| ≤
        W * ((L.T r.val.1 r.val.2).card : ℝ) *
          (Lip * reg ^ 2 + (B + B / c) * (reg * wt)) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hs0 := he0.2.2.2.2.2.2.2.2.1 r
  have hsh := he.2.2.2.2.2.2.2.2.1 r
  have ht (x : X) : 0 < (levelSetProb M L).2 r.val.1 r.val.2 x :=
    hov.1.trans_le (hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have hj0 : r.val.2 ≠ 0 := by have := r.property; omega
  have hj : ¬ L.l r.val.1 < r.val.2 := not_lt.mpr r.property.2.2
  have hq : ∀ᵐ x ∂xLaw M,
      pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x = L.qLev r.val.1 r.val.2 x := by
    filter_upwards [hs0] with x hx
    simp only [pooledQBin, if_neg hj0, if_neg hj, dif_pos r.property]
    calc
      _ = ∑ z ∈ L.T r.val.1 r.val.2,
          (eta0Bin M L).share r z x * L.qLev r.val.1 r.val.2 x := by
        apply Finset.sum_congr rfl
        intro z hz
        have hc := (hOrder.2.2.2.2.2.2.1 x r.val.1 r.val.2 z r.property.1
          r.property.2.1 r.property.2.2).mp hz
        simpa only [eta0Bin, policyProp] using congrArg ((eta0Bin M L).share r z x * ·) hc
      _ = _ := by rw [← Finset.sum_mul, hx.1, one_mul]
  have hp z : MemLp (fun x => e.prop z x - M.prop z x) 2 (xLaw M) :=
    ((fitted_prop_gammaTail_memLp M L e he).1 z).sub
      ((fitted_prop_gammaTail_memLp M L (eta0Bin M L) he0).1 z)
  have hshare (e' : NuisanceBin L) (he' : BinAdmissible M L e') (z : Z) :
      MemLp (e'.share r z) 2 (xLaw M) := by
    apply MemLp.of_bound (he'.2.2.2.2.2.2.2.1 r z).aestronglyMeasurable 1
    filter_upwards [he'.2.2.2.2.2.2.1 r z] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have ha z := (hshare e he z).sub (hshare (eta0Bin M L) he0 z)
  have htauMem (e' : NuisanceBin L) (he' : BinAdmissible M L e') :
      MemLp (e'.tauLev r) 2 (xLaw M) := by
    apply MemLp.of_bound (he'.2.2.2.2.2.1 r).1.aestronglyMeasurable 1
    filter_upwards [he'.2.2.2.2.1 r] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1.1]
    exact hx.1.2
  have htau : MemLp (fun x => e.tauLev r x - (eta0Bin M L).tauLev r x) 2 (xLaw M) := by
    convert (htauMem e he).sub (htauMem (eta0Bin M L) he0) using 1
    funext x
    rfl
  have hm : AEStronglyMeasurable (fun x =>
      (∑ z ∈ L.T r.val.1 r.val.2, e.share r z x * phi z x (e.prop z x)) +
        (e.tauLev r x)⁻¹ * (∑ z ∈ L.T r.val.1 r.val.2,
          instProb M z x * dphi z x (e.prop z x) * (M.prop z x - e.prop z x)) -
        pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x) (xLaw M) := by
    first | fun_prop | skip
    apply AEStronglyMeasurable.sub
    · apply AEStronglyMeasurable.add
      · exact (fitted_pooledQBin_memLp M phi hphi L e he r.val.1 r.val.2).1
          |>.congr (Eventually.of_forall (fun x => by
            simp only [pooledQBin, if_neg hj0, if_neg hj, dif_pos r.property]))
      · apply (he.2.2.2.2.2.1 r).1.inv.aestronglyMeasurable.mul
        convert
          (Finset.aestronglyMeasurable_sum (L.T r.val.1 r.val.2) (fun z hz => by
            have hmass : Measurable (instProb M z) :=
              (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal
            exact (hmass.aestronglyMeasurable.mul
              (fitted_policy_derivative_aestronglyMeasurable M phi dphi hphi hd L e he z)).mul
              ((hp z).1.neg))) using 1
        funext x
        simp only [Finset.sum_apply, Pi.mul_apply, Pi.neg_apply, neg_sub]
    · exact (fitted_pooledQBin_memLp M phi hphi L (eta0Bin M L) he0 r.val.1 r.val.2).1
  have hb := fitted_pooled_policy_ae_weighted_quadratic_bound
    (xLaw M) phi dphi hd B Lip c hB hLip hc hbound hlip (L.T r.val.1 r.val.2)
    M.prop e.prop ((eta0Bin M L).share r) (e.share r) (instProb M)
    (pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2)
    ((eta0Bin M L).tauLev r) (e.tauLev r) hden
    (Eventually.of_forall (fun x z hz => by
      simp only [eta0Bin, levelShares, if_pos hz, div_mul_cancel₀ _ (ht x).ne']))
    (Eventually.of_forall (fun x z hz => M.rangeProp z x))
    (by filter_upwards [ae_all_iff.mpr he.1] with x hx; exact fun z _ => hx z)
    (by
      filter_upwards [hq] with x hx
      intro z hz
      rw [hx]
      exact (hOrder.2.2.2.2.2.2.1 x r.val.1 r.val.2 z r.property.1
        r.property.2.1 r.property.2.2).mp hz)
    (hs0.mono fun x hx => hx.1) (hsh.mono fun x hx => hx.1)
    (by
      filter_upwards [ae_all_iff.mpr (he0.2.2.2.2.2.2.1 r)] with x hx
      intro z hz
      rw [abs_of_nonneg (hx z).1]
      exact (hx z).2)
    (fun z _ => hp z) (fun z _ => ha z)
    (by simpa only [regularValue, dif_pos r.property] using htau) hm w W reg wt
    hW hreg hwt hw hwb
    (fun z hz => by simpa only [← l2Error_eq_eLpNorm M _ _ (hp z)] using hpNorm z hz)
    (fun z hz => by simpa only [← l2Error_eq_eLpNorm M _ _ (ha z)] using haNorm z hz)
    (by
      have htt : MemLp (fun x => e.tauLev r x - (eta0Bin M L).tauLev r x) 2 (xLaw M) := by
        simpa only [regularValue, dif_pos r.property] using htau
      simpa only [← l2Error_eq_eLpNorm M _ _ htt] using htNorm)
  simpa only [pooledQBin, if_neg hj0, if_neg hj, dif_pos r.property] using hb

-- All envelopes are constructed from the original propensity, share and
-- denominator errors. Fitted branch weights may vary with the training data.
-- @node: nuisanceRates_binary_pooling_weighted_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) and
[a bounded Lipschitz derivative](hyp:hDerivative), suppose
[level ordering is covariate invariant](hyp:hOrder), [policy overlap holds](hyp:hov),
[the true nuisance record is admissible](hyp:he0), and [every fitted record is admissible](hyp:heh).
Assume [a positive denominator lower bound](hyp:hc), [a nonnegative weight envelope](hyp:hW),
[fitted masses in the selected regular group almost surely exceed the lower bound](hyp:hden),
[the training-dependent weights are almost everywhere strongly measurable](hyp:hw) and
[uniformly bounded in norm by the envelope](hyp:hwb), and finite nuisance rates hold for
[propensities](hyp:hrp), [shares in the selected group](hyp:hrs), and [regular group masses](hyp:hrt).
Then [the weighted population pooled-policy error, corrected by the inverse fitted mass
times the instrument-mass-weighted derivative and propensity error, converges in probability
to zero after multiplication by the square root of the evaluation-sample size](goal). -/
lemma nuisanceRates_binary_pooling_weighted_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (r : RegularIndex L) (c W : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hden : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x)
    (w : ℕ → A → X → ℝ)
    (hw : ∀ n a, AEStronglyMeasurable (w n a) (xLaw M))
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, ‖w n a x‖ ≤ W)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrs : FiniteNuisanceRates M μ (fun n a => (eh n a).share r) ((eta0Bin M L).share r))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        w (2*(n+1)) a x *
          (pooledQBin phi L (eh (2*(n+1)) a) r.val.1 r.val.2 x +
            ((eh (2*(n+1)) a).tauLev r x)⁻¹ *
              (∑ z ∈ L.T r.val.1 r.val.2, instProb M z x *
                dphi z x ((eh (2*(n+1)) a).prop z x) *
                (M.prop z x - (eh (2*(n+1)) a).prop z x)) -
            pooledQBin phi L (eta0Bin M L) r.val.1 r.val.2 x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  let zs := (L.T r.val.1 r.val.2).toList
  let dp := fun n a z => finiteL2Error M ((eh (2*(n+1)) a).prop z) (M.prop z)
  let ds := fun n a z => finiteL2Error M ((eh (2*(n+1)) a).share r z)
    ((eta0Bin M L).share r z)
  let reg := fun n a => maxErrors (zs.map (dp n a))
  let wt := fun n a => maxErrors (zs.map (ds n a)) +
    finiteL2Error M ((eh (2*(n+1)) a).tauLev r) ((eta0Bin M L).tauLev r)
  have hr := nuisanceRates_finite_maxErrors M μ (fun n a => (eh n a).prop)
    M.prop zs hrp
  have ht := (nuisanceRates_finite_maxErrors M μ (fun n a => (eh n a).share r)
    ((eta0Bin M L).share r) zs hrs).add_eventually_nonneg_rate
      (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hrt r)
  let C := W * ((L.T r.val.1 r.val.2).card : ℝ) * (Lip + B + B / c) + 1
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt C
    (by dsimp only [C]; positivity) hr ht
  intro n a
  have hreg : 0 ≤ reg n a := maxErrors_nonneg _
  have hwt : 0 ≤ wt n a := add_nonneg (maxErrors_nonneg _) (Real.sqrt_nonneg _)
  have hb := (fitted_binary_pooling_weighted_quadratic_bound M phi dphi hphi hd
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

end Papers.TbsPrteOptimalTransport
