module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationInstrumentMoments
public import Papers.TbsPrteOptimalTransport.Helpers.JointPooledRemainder
public import Papers.TbsPrteOptimalTransport.Helpers.ProductScoreMoments
/-! Fitted policy residual means from treatment centering and the instrument kernel. -/
public section

set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- A bounded fitted instrument-specific coefficient needs no additional
-- integrability premise: both treatment regressions lie in the unit interval.
-- @node: fitted_instrument_residual_integrable
/-- If [the instrument-specific weight](hyp:hw) and [the fitted treatment regression](hyp:he)
are measurable, [the weight is almost surely bounded in absolute value uniformly over
instruments](hyp:hb), and [the fitted treatment regression lies between zero and one almost
surely for every instrument](hyp:hr), [the weight times observed treatment minus its fitted
regression is integrable under the observation law](goal). -/
lemma fitted_instrument_residual_integrable (w e : Z × X → ℝ) (B : ℝ)
    (hw : Measurable w) (he : Measurable e)
    (hb : ∀ᵐ x ∂xLaw M, ∀ z, ‖w (z, x)‖ ≤ B)
    (hr : ∀ᵐ x ∂xLaw M, ∀ z, e (z, x) ∈ Icc (0 : ℝ) 1) :
    Integrable (fun o : Obs X Z => w (o.2.1, o.1) *
      (o.2.2.1 - e (o.2.1, o.1))) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have ht : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
    have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    apply (ae_map_iff hobs.aemeasurable
      (measurableSet_Icc.preimage measurable_snd.snd.fst)).2
    exact Filter.Eventually.of_forall (fun s => by
      rcases M.rangeW s with hs | hs <;> simp [hs])
  apply Integrable.of_bound (by fun_prop) B
  filter_upwards [ht, observationLaw_covariate_ae M _ hb,
    observationLaw_covariate_ae M _ hr] with o ho hbo hro
  have hd : |o.2.2.1 - e (o.2.1, o.1)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [(hro o.2.1).1, (hro o.2.1).2, ho.1, ho.2]
  rw [norm_mul, Real.norm_eq_abs (o.2.2.1 - e (o.2.1, o.1))]
  exact (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans
    (by simpa only [mul_one] using hbo o.2.1)

-- This computes the fitted residual mean; the mean is not assumed as a gate.
-- @node: fitted_instrument_residual_mean_of_bound
/-- Under [threshold crossing](hyp:h), if [the instrument-specific weight](hyp:hw) and
[the fitted treatment regression](hyp:he) are measurable,
[the weight is almost surely bounded in absolute value uniformly over instruments](hyp:hb), and
[the fitted treatment regression lies between zero and one almost surely for every instrument](hyp:hr),
[the weighted fitted treatment residual is integrable and its mean equals the covariate
integral of the sum over instruments of true instrument probability times the weight times
true propensity minus fitted regression](goal). -/
lemma fitted_instrument_residual_mean_of_bound (h : ThresholdCrossing M)
    (w e : Z × X → ℝ) (B : ℝ) (hw : Measurable w) (he : Measurable e)
    (hb : ∀ᵐ x ∂xLaw M, ∀ z, ‖w (z, x)‖ ≤ B)
    (hr : ∀ᵐ x ∂xLaw M, ∀ z, e (z, x) ∈ Icc (0 : ℝ) 1) :
    Integrable (fun o : Obs X Z => w (o.2.1, o.1) *
      (o.2.2.1 - e (o.2.1, o.1))) (observationLaw M) ∧
    (∫ o : Obs X Z, w (o.2.1, o.1) * (o.2.2.1 - e (o.2.1, o.1))
      ∂observationLaw M) =
      ∫ x, ∑ z, instProb M z x * w (z, x) *
        (M.prop z x - e (z, x)) ∂xLaw M := by
  have hi := fitted_instrument_residual_integrable M w e B hw he hb hr
  have hi0 := fitted_instrument_residual_integrable M w
    (fun zx => M.prop zx.1 zx.2) B hw h.2.1 hb
    (Filter.Eventually.of_forall fun x z => M.rangeProp z x)
  have hd : Integrable (fun o : Obs X Z => w (o.2.1, o.1) *
      (M.prop o.2.1 o.1 - e (o.2.1, o.1))) (observationLaw M) := by
    convert hi.sub' hi0 using 1
    ext o
    ring
  have hz := population_treatment_weighted_integral_zero M h w hw hi0
  have hp := h.2.1
  have hm := population_instrument_integral M
    (fun zx => w zx * (M.prop zx.1 zx.2 - e zx)) (by fun_prop) hd
  have hid (o : Obs X Z) : w (o.2.1, o.1) * (o.2.2.1 - e (o.2.1, o.1)) =
      w (o.2.1, o.1) * (o.2.2.1 - M.prop o.2.1 o.1) +
      w (o.2.1, o.1) * (M.prop o.2.1 o.1 - e (o.2.1, o.1)) := by ring
  refine ⟨hi, ?_⟩
  simp_rw [hid]
  rw [integral_add hi0 hd, hz, zero_add, hm]
  simp only [mul_assoc]

-- Only the realized instrument survives in the finite policy sum.
-- @node: fitted_RqBin_residual_factorization
/-- [The fitted binary policy residual equals observed treatment minus fitted propensity at the
realized instrument, multiplied by zero for an invalid policy index and otherwise by the
inverse fitted policy-set probability, the realized instrument's policy-set indicator,
and the policy derivative evaluated at fitted propensity](goal). -/
lemma fitted_RqBin_residual_factorization (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) (k j : ℕ) (o : Obs X Z) :
    RqBin dphi L e k j o =
      (if j = 0 ∨ L.l k < j then 0 else
        (regularValue e.tauLev k j o.1)⁻¹ * indicator (o.2.1 ∈ L.T k j) *
          dphi o.2.1 o.1 (e.prop o.2.1 o.1)) *
        (o.2.2.1 - e.prop o.2.1 o.1) := by
  unfold RqBin
  split_ifs with hj
  · simp
  · have hs : (∑ z ∈ L.T k j, dphi z o.1 (e.prop z o.1) *
        indicator (o.2.1 = z) * (o.2.2.1 - e.prop z o.1)) =
        indicator (o.2.1 ∈ L.T k j) * dphi o.2.1 o.1 (e.prop o.2.1 o.1) *
          (o.2.2.1 - e.prop o.2.1 o.1) := by
      have hid (z : Z) : dphi z o.1 (e.prop z o.1) * indicator (o.2.1 = z) *
          (o.2.2.1 - e.prop z o.1) =
          if o.2.1 = z then dphi o.2.1 o.1 (e.prop o.2.1 o.1) *
            (o.2.2.1 - e.prop o.2.1 o.1) else 0 := by
        by_cases hz : o.2.1 = z
        · subst z
          simp [indicator]
        · simp [indicator, hz]
      simp_rw [hid]
      simp [indicator]
    rw [hs]
    ring

-- Clipped denominators and bounded fitted derivatives supply the analytic
-- inputs. The remaining mean is the true instrument mass times propensity error.
-- @node: fitted_RqBin_weighted_integral_of_clipping
/-- Under [threshold crossing](hyp:h), suppose [the clipping threshold is positive](hyp:hc),
[the weight and derivative bounds are nonnegative](hyp:hW,hB), and
[the fitted binary nuisance record is admissible](hyp:he).
If [the policy derivative evaluated at fitted propensity is measurable](hyp:hd),
[its absolute value is almost surely bounded uniformly over instruments](hyp:hdb),
[the fitted policy-set probability is almost surely at least the clipping threshold](hyp:hclip),
[the covariate weight is measurable](hyp:hw), and [its absolute value is almost surely at most
the weight bound](hyp:hwb), [the weighted policy residual is integrable and its mean equals
the covariate integral of the weight divided by fitted policy-set probability times the
policy-set sum of true instrument probability, fitted policy derivative, and true-minus-fitted
propensity](goal). -/
lemma fitted_RqBin_weighted_integral_of_clipping (h : ThresholdCrossing M)
    (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (r : RegularIndex L) (c W B : ℝ) (hc : 0 < c) (hW : 0 ≤ W) (hB : 0 ≤ B)
    (he : BinAdmissible M L e)
    (hd : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (e.prop zx.1 zx.2)))
    (hdb : ∀ᵐ x ∂xLaw M, ∀ z, |dphi z x (e.prop z x)| ≤ B)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (w : X → ℝ) (hw : Measurable w) (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L e r.val.1 r.val.2 o)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * RqBin dphi L e r.val.1 r.val.2 o
      ∂observationLaw M) =
      ∫ x, w x * (e.tauLev r x)⁻¹ *
        ∑ z ∈ L.T r.val.1 r.val.2, instProb M z x *
          dphi z x (e.prop z x) * (M.prop z x - e.prop z x) ∂xLaw M := by
  have ht : Measurable (e.tauLev r) := (he.2.2.2.2.2.1 r).1
  have hp : Measurable (fun zx : Z × X => e.prop zx.1 zx.2) := by
    first | fun_prop | exact measurable_from_prod_countable_right he.2.1
  let weight : Z × X → ℝ := fun zx => w zx.2 * (e.tauLev r zx.2)⁻¹ *
    indicator (zx.1 ∈ L.T r.val.1 r.val.2) * dphi zx.1 zx.2 (e.prop zx.1 zx.2)
  have hi : Measurable (fun zx : Z × X =>
      indicator (zx.1 ∈ L.T r.val.1 r.val.2)) := by
    unfold indicator
    exact Measurable.ite ((L.T r.val.1 r.val.2).finite_toSet.measurableSet.preimage
      measurable_fst) measurable_const measurable_const
  have hm : Measurable weight := by
    first | fun_prop | skip
    exact (((hw.comp measurable_snd).mul (ht.comp measurable_snd).inv).mul hi).mul hd
  have hb : ∀ᵐ x ∂xLaw M, ∀ z, ‖weight (z, x)‖ ≤ W / c * B := by
    filter_upwards [hwb, hclip, hdb] with x hx hcx hdx
    intro z
    have ht0 : 0 < e.tauLev r x := hc.trans_le hcx
    have hind : |indicator (z ∈ L.T r.val.1 r.val.2)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    dsimp only [weight]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_inv, abs_of_pos ht0]
    calc
      _ ≤ W * (1 / c) * 1 * B := by
        gcongr
        · simpa only [Real.norm_eq_abs] using hx
        · rw [← one_div]
          exact div_le_div_of_nonneg_left (by norm_num) hc hcx
        · exact hdx z
      _ = _ := by ring
  have hmean := fitted_instrument_residual_mean_of_bound M h weight
    (fun zx => e.prop zx.1 zx.2) (W / c * B) hm hp hb (ae_all_iff.mpr he.1)
  have hj : ¬ (r.val.2 = 0 ∨ L.l r.val.1 < r.val.2) := by
    have := r.property
    omega
  have hid (o : Obs X Z) : w o.1 * RqBin dphi L e r.val.1 r.val.2 o =
      weight (o.2.1, o.1) * (o.2.2.1 - e.prop o.2.1 o.1) := by
    rw [fitted_RqBin_residual_factorization]
    simp only [if_neg hj, regularValue, dif_pos r.property, weight]
    ring
  have hs (x : X) : (∑ z, instProb M z x * weight (z, x) *
      (M.prop z x - e.prop z x)) =
      w x * (e.tauLev r x)⁻¹ * ∑ z ∈ L.T r.val.1 r.val.2,
        instProb M z x * dphi z x (e.prop z x) * (M.prop z x - e.prop z x) := by
    simp only [weight, indicator, mul_ite, mul_one, mul_zero, zero_mul, ite_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  simp_rw [hid]
  exact ⟨hmean.1, by simpa only [hs] using hmean.2⟩

-- Specialize the existing joint-path bound at t = 1, using the actual
-- fitted-minus-true errors. No admissible affine path is required by DML.
-- @node: fitted_pooled_policy_remainder_bound
/-- Suppose [the policy has the specified derivative](hyp:hd),
[the derivative bound and Lipschitz constant are nonnegative](hyp:hB,hLip), and
[the derivative is bounded](hyp:hbound) and [Lipschitz](hyp:hlip) on the unit interval.
If [the clipping threshold is positive](hyp:hc), [the fitted policy-set probability exceeds
or equals that threshold](hyp:hden), [instrument masses equal true shares times true set
probability](hyp:ha), [true](hyp:hp) and [fitted](hyp:hph) propensities lie in the unit interval
on the instrument set, [true policy values all equal the reference level](hyp:hcommon), and
[true](hyp:hs) and [fitted](hyp:hsh) shares each sum to one, [the absolute error of the fitted
share-weighted policy value plus its derivative residual correction is bounded by the sum of
true absolute shares times the Lipschitz constant times squared propensity errors, absolute
share errors times the derivative bound times absolute propensity errors, and the absolute
set-probability error divided by the clipping threshold times the true-absolute-share-weighted
derivative bound and absolute propensity errors](goal). -/
lemma fitted_pooled_policy_remainder_bound
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (B Lip : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p-r|)
    (s : Finset Z) (x : X) (p ph a ah mass : Z → ℝ) (q tau th c : ℝ)
    (hc : 0 < c) (hden : c ≤ th)
    (ha : ∀ z ∈ s, mass z = a z * tau)
    (hp : ∀ z ∈ s, p z ∈ Icc (0 : ℝ) 1)
    (hph : ∀ z ∈ s, ph z ∈ Icc (0 : ℝ) 1)
    (hcommon : ∀ z ∈ s, phi z x (p z) = q)
    (hs : ∑ z ∈ s, a z = 1) (hsh : ∑ z ∈ s, ah z = 1) :
    |(∑ z ∈ s, ah z * phi z x (ph z)) +
        th⁻¹ * (∑ z ∈ s, mass z * dphi z x (ph z) * (p z - ph z)) - q| ≤
      (∑ z ∈ s, |a z| * (Lip * (ph z - p z)^2)) +
        (∑ z ∈ s, |ah z - a z| * (B * |ph z - p z|)) +
        |th - tau| / c * (∑ z ∈ s, |a z| * B * |ph z - p z|) := by
  have hsimplex : ∑ z ∈ s, (ah z - a z) = 0 := by
    rw [Finset.sum_sub_distrib, hsh, hs, sub_self]
  have hb := pooled_policy_debiased_joint_remainder_bound phi dphi hd B Lip hB hLip
    hbound hlip s x p (fun z => ph z - p z) a (fun z => ah z - a z)
    mass q tau (th - tau) 1 c hc (by simpa using hden) ha hp
    (by simpa using hph) hcommon hsimplex
  simp only [one_mul, add_sub_cancel, one_pow, mul_one] at hb
  have hq : (∑ z ∈ s, a z * phi z x (p z)) = q := by
    calc
      _ = ∑ z ∈ s, a z * q := Finset.sum_congr rfl (fun z hz => by rw [hcommon z hz])
      _ = q := by rw [← Finset.sum_mul, hs, one_mul]
  have hneg : (∑ z ∈ s, mass z * dphi z x (ph z) * (p z - ph z)) =
      -(∑ z ∈ s, mass z * dphi z x (ph z) * (ph z - p z)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hq] at hb
  rw [hneg]
  simpa only [mul_neg, sub_eq_add_neg] using hb

-- The true shares and their unit sum follow from the population mass and
-- policy overlap. The fitted simplex removes every first-order share term.
-- @node: fitted_pooledQBin_conditional_remainder_bound
/-- Suppose [the policy has the specified derivative](hyp:hd),
[the derivative bound and Lipschitz constant are nonnegative](hyp:hB,hLip), and
[the derivative is bounded](hyp:hbound) and [Lipschitz](hyp:hlip) on the unit interval.
Under [invariant level order](hyp:hOrder) and [policy overlap](hyp:hov), if
[the clipping threshold is positive](hyp:hc), [the fitted policy-set probability at the specified
covariate is at least that threshold](hyp:hden), [fitted propensities on the policy set lie
between zero and one](hyp:hph), and [fitted shares on that set sum to one](hyp:hsh),
[the absolute error of the fitted pooled policy level plus its conditional derivative residual
correction is bounded by three sums: true absolute shares times the Lipschitz constant times
squared propensity errors; absolute share errors times the derivative bound times absolute
propensity errors; and the absolute policy-set probability error divided by the clipping
threshold times the true-absolute-share-weighted derivative bound and absolute propensity errors](goal). -/
lemma fitted_pooledQBin_conditional_remainder_bound
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (B Lip : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p-r|)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (e : NuisanceBin L) (r : RegularIndex L) (x : X) (cpi c : ℝ)
    (hov : PolicyOverlap M L cpi) (hc : 0 < c) (hden : c ≤ e.tauLev r x)
    (hph : ∀ z ∈ L.T r.val.1 r.val.2, e.prop z x ∈ Icc (0 : ℝ) 1)
    (hsh : ∑ z ∈ L.T r.val.1 r.val.2, e.share r z x = 1) :
    |pooledQBin phi L e r.val.1 r.val.2 x +
        (e.tauLev r x)⁻¹ * (∑ z ∈ L.T r.val.1 r.val.2,
          instProb M z x * dphi z x (e.prop z x) * (M.prop z x - e.prop z x)) -
        L.qLev r.val.1 r.val.2 x| ≤
      (∑ z ∈ L.T r.val.1 r.val.2,
        |levelShares M L r.val.1 r.val.2 z x| * (Lip * (e.prop z x - M.prop z x)^2)) +
      (∑ z ∈ L.T r.val.1 r.val.2,
        |e.share r z x - levelShares M L r.val.1 r.val.2 z x| *
          (B * |e.prop z x - M.prop z x|)) +
      |e.tauLev r x - (levelSetProb M L).2 r.val.1 r.val.2 x| / c *
        (∑ z ∈ L.T r.val.1 r.val.2,
          |levelShares M L r.val.1 r.val.2 z x| * B * |e.prop z x - M.prop z x|) := by
  have ht : 0 < (levelSetProb M L).2 r.val.1 r.val.2 x := hov.1.trans_le
    (hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have ha : ∀ z ∈ L.T r.val.1 r.val.2, instProb M z x =
      levelShares M L r.val.1 r.val.2 z x * (levelSetProb M L).2 r.val.1 r.val.2 x := by
    intro z hz
    simp only [levelShares, if_pos hz, div_mul_cancel₀ _ ht.ne']
  have hs : ∑ z ∈ L.T r.val.1 r.val.2, levelShares M L r.val.1 r.val.2 z x = 1 := by
    simp only [levelShares, Finset.sum_ite_mem, Finset.inter_self]
    rw [← Finset.sum_div]
    change (levelSetProb M L).2 r.val.1 r.val.2 x /
      (levelSetProb M L).2 r.val.1 r.val.2 x = 1
    exact div_self ht.ne'
  have hcommon : ∀ z ∈ L.T r.val.1 r.val.2,
      phi z x (M.prop z x) = L.qLev r.val.1 r.val.2 x := by
    intro z hz
    exact (hOrder.2.2.2.2.2.2.1 x r.val.1 r.val.2 z r.property.1
      r.property.2.1 r.property.2.2).mp hz
  have hj0 : r.val.2 ≠ 0 := by have := r.property; omega
  have hj : ¬ L.l r.val.1 < r.val.2 := not_lt.mpr r.property.2.2
  simp only [pooledQBin, if_neg hj0, if_neg hj, dif_pos r.property]
  exact fitted_pooled_policy_remainder_bound phi dphi hd B Lip hB hLip hbound hlip
    _ x (fun z => M.prop z x) (fun z => e.prop z x)
    (fun z => levelShares M L r.val.1 r.val.2 z x) (fun z => e.share r z x)
    (fun z => instProb M z x) _ _ _ c hc hden ha
    (fun z _ => M.rangeProp z x) hph hcommon hs hsh

-- The pointwise expansion above now yields an integrated second-order bound.
-- True simplex shares are at most one, so no additional share moment is needed.
-- @node: fitted_pooled_policy_integrated_L2_bound
/-- Suppose [the policy has the specified derivative](hyp:hd),
[the derivative bound and Lipschitz constant are nonnegative](hyp:hB,hLip),
[the clipping threshold is positive](hyp:hc), and [the derivative is bounded](hyp:hbound) and
[Lipschitz](hyp:hlip) on the unit interval.
Assume almost everywhere that [the fitted set probability is at least the clipping threshold](hyp:hden),
[instrument masses equal true shares times true set probability](hyp:ha),
[true](hyp:hp) and [fitted](hyp:hph) propensities lie between zero and one,
[true policy values equal the reference level throughout the instrument set](hyp:hcommon),
[true](hyp:hs) and [fitted](hyp:hsh) shares sum to one, and
[true shares have absolute value at most one](hyp:hab).
If [each propensity error](hyp:hep), [each share error](hyp:hea), and
[the set-probability error](hyp:het) are square integrable and
[the corrected pooled policy error is almost everywhere strongly measurable](hyp:hm),
[that error is integrable and its integrated absolute value is bounded by the instrument sum
of the Lipschitz constant times integrated squared propensity error, the derivative bound times
the share-error and propensity-error L2 norm product, and the derivative bound divided by the
clipping threshold times the set-probability-error and propensity-error L2 norm product](goal). -/
lemma fitted_pooled_policy_integrated_L2_bound
    (ν : Measure X) (phi dphi : Z → X → ℝ → ℝ)
    (hd : PolicyDifferentiable phi dphi)
    (B Lip c : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip) (hc : 0 < c)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x r| ≤ Lip * |p-r|)
    (s : Finset Z) (p ph a ah mass : Z → X → ℝ) (q tau th : X → ℝ)
    (hden : ∀ᵐ x ∂ν, c ≤ th x)
    (ha : ∀ᵐ x ∂ν, ∀ z ∈ s, mass z x = a z x * tau x)
    (hp : ∀ᵐ x ∂ν, ∀ z ∈ s, p z x ∈ Icc (0 : ℝ) 1)
    (hph : ∀ᵐ x ∂ν, ∀ z ∈ s, ph z x ∈ Icc (0 : ℝ) 1)
    (hcommon : ∀ᵐ x ∂ν, ∀ z ∈ s, phi z x (p z x) = q x)
    (hs : ∀ᵐ x ∂ν, ∑ z ∈ s, a z x = 1)
    (hsh : ∀ᵐ x ∂ν, ∑ z ∈ s, ah z x = 1)
    (hab : ∀ᵐ x ∂ν, ∀ z ∈ s, |a z x| ≤ 1)
    (hep : ∀ z ∈ s, MemLp (fun x => ph z x - p z x) 2 ν)
    (hea : ∀ z ∈ s, MemLp (fun x => ah z x - a z x) 2 ν)
    (het : MemLp (fun x => th x - tau x) 2 ν)
    (hm : AEStronglyMeasurable (fun x =>
      (∑ z ∈ s, ah z x * phi z x (ph z x)) +
        (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x) ν) :
    let R := fun x => (∑ z ∈ s, ah z x * phi z x (ph z x)) +
      (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x
    Integrable R ν ∧
    (∫ x, |R x| ∂ν) ≤ ∑ z ∈ s,
      (Lip * (∫ x, (ph z x - p z x)^2 ∂ν) +
        B * ((eLpNorm (fun x => ah z x - a z x) 2 ν).toReal *
          (eLpNorm (fun x => ph z x - p z x) 2 ν).toReal) +
        (B / c) * ((eLpNorm (fun x => th x - tau x) 2 ν).toReal *
          (eLpNorm (fun x => ph z x - p z x) 2 ν).toReal)) := by
  let ep := fun z x => ph z x - p z x
  let ea := fun z x => ah z x - a z x
  let et := fun x => th x - tau x
  let E := fun x => ∑ z ∈ s,
    (Lip * (ep z x)^2 + B * |ea z x * ep z x| + (B / c) * |et x * ep z x|)
  have hi (z : Z) (hz : z ∈ s) : Integrable
      (fun x => Lip * (ep z x)^2 + B * |ea z x * ep z x| +
        (B / c) * |et x * ep z x|) ν :=
    (((hep z hz).integrable_sq.const_mul Lip).add
      (((hea z hz).integrable_mul (hep z hz)).abs.const_mul B)).add
      ((het.integrable_mul (hep z hz)).abs.const_mul (B / c))
  have hiE : Integrable E ν := integrable_finsetSum s hi
  have hRE : ∀ᵐ x ∂ν, |(∑ z ∈ s, ah z x * phi z x (ph z x)) +
      (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x| ≤ E x := by
    filter_upwards [hden, ha, hp, hph, hcommon, hs, hsh, hab] with x hx hax hpx hphx hqx hsx hshx habx
    have hb := fitted_pooled_policy_remainder_bound phi dphi hd B Lip hB hLip
      hbound hlip s x (fun z => p z x) (fun z => ph z x) (fun z => a z x)
      (fun z => ah z x) (fun z => mass z x) (q x) (tau x) (th x) c hc hx
      hax hpx hphx hqx hsx hshx
    apply hb.trans
    have h1 : (∑ z ∈ s, |a z x| * (Lip * (ph z x - p z x)^2)) ≤
        ∑ z ∈ s, Lip * (ep z x)^2 := by
      apply Finset.sum_le_sum
      intro z hz
      simpa only [ep, one_mul] using
        mul_le_mul_of_nonneg_right (habx z hz) (mul_nonneg hLip (sq_nonneg _))
    have h3 : (∑ z ∈ s, |a z x| * B * |ph z x - p z x|) ≤
        ∑ z ∈ s, B * |ep z x| := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right (habx z hz) hB) (abs_nonneg _)
    calc
      _ ≤ (∑ z ∈ s, Lip * (ep z x)^2) +
          (∑ z ∈ s, |ea z x| * (B * |ep z x|)) +
          |et x| / c * (∑ z ∈ s, B * |ep z x|) :=
        add_le_add (add_le_add h1 le_rfl)
          (mul_le_mul_of_nonneg_left h3 (by positivity))
      _ = E x := by
        simp only [E, Finset.mul_sum, ← Finset.sum_add_distrib, abs_mul]
        apply Finset.sum_congr rfl
        intro z hz
        ring
  have hiR : Integrable (fun x => (∑ z ∈ s, ah z x * phi z x (ph z x)) +
      (th x)⁻¹ * (∑ z ∈ s, mass z x * dphi z x (ph z x) * (p z x - ph z x)) - q x) ν := by
    apply hiE.mono' hm
    simpa only [Real.norm_eq_abs] using hRE
  refine ⟨hiR, (integral_mono_ae hiR.abs hiE hRE).trans ?_⟩
  rw [integral_finsetSum s hi]
  apply Finset.sum_le_sum
  intro z hz
  have i1 := (hep z hz).integrable_sq.const_mul Lip
  have i2 : Integrable (fun x => B * |(ah z x - a z x) * (ph z x - p z x)|) ν :=
    ((hea z hz).integrable_mul (hep z hz)).abs.const_mul B
  have i3 : Integrable (fun x => (B / c) * |(th x - tau x) * (ph z x - p z x)|) ν :=
    (het.integrable_mul (hep z hz)).abs.const_mul (B / c)
  dsimp only [ep, ea, et]
  rw [integral_add (i1.fun_add i2) i3, integral_add i1 i2]
  simp only [integral_const_mul]
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left
      (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm (hea z hz) (hep z hz)) hB))
    (mul_le_mul_of_nonneg_left
      (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm het (hep z hz)) (by positivity))

end Papers.TbsPrteOptimalTransport
