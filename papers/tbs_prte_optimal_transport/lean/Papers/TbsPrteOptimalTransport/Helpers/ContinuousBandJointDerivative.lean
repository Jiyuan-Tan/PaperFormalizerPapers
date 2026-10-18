module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandJointBias
/-! Integrated joint band cancellation and inheritance by regular product scores. -/
public section
set_option linter.unusedSectionVars false
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

-- Regression and assignment-denominator errors vanish jointly at first order.
-- The reference path may itself vary; only the displayed primitive components
-- must agree between the two paths.
-- @node: population_continuous_band_joint_regression_derivative
/-- Suppose [two nuisance paths agree at time zero](hyp:he0), [the denominator floor
c is positive](hyp:hc), [the coefficient-error constant D is nonnegative](hyp:hD), and
[the denominator-error constant C is nonnegative](hyp:hC). If [near zero the paths
share assignment denominators, propensity levels, quantiles, instrument propensities,
instrument shares, and pooled denominators; the upper and lower weighted propensity
coefficient changes define measurable coefficients of magnitude at most D times absolute
time; and the shared assignment denominators are measurable, at least c almost surely,
and within C times absolute time of their true instrument-set probabilities](hyp:hlocal),
then [the population weighted difference of the two band scores has derivative zero
at time zero](goal). -/
lemma population_continuous_band_joint_regression_derivative
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e b : ℝ → NuisanceCont L) (he0 : e 0 = b 0)
    (k : Fin L.K) (j : ℕ) (w : ℝ → X → ℝ)
    (vp vm : ℝ → X → ℝ) (c D C : ℝ)
    (hc : 0 < c) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (e t).piLev = (b t).piLev ∧ (e t).pLev = (b t).pLev ∧
      (e t).nu = (b t).nu ∧ (e t).prop = (b t).prop ∧
      (e t).share = (b t).share ∧ (e t).tauLev = (b t).tauLev ∧
      (∀ x, vp t x = w t x * (positiveValue (b t).pLev (k+1) x *
        (alphaHigh M L (e t) k j x - alphaHigh M L (b t) k j x))) ∧
      (∀ x, vm t x = w t x * (if k.val = 0 then 0 else
        -positiveValue (b t).pLev k x *
          (alphaLow M L (e t) k j x - alphaLow M L (b t) k j x))) ∧
      (∀ a, Measurable ((b t).piLev a)) ∧ Measurable (vp t) ∧ Measurable (vm t) ∧
      (∀ a, ∀ᵐ x ∂xLaw M, c ≤ (b t).piLev a x) ∧
      (∀ᵐ x ∂xLaw M, |vp t x| ≤ D * |t|) ∧
      (∀ᵐ x ∂xLaw M, |vm t x| ≤ D * |t|) ∧
      (∀ i, 1 ≤ i → i ≤ L.K → ∀ᵐ x ∂xLaw M,
        |positiveValue (b t).piLev i x - ∑ z ∈ L.S i, instProb M z x| ≤ C * |t|)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (contScoreComponents M phi dphi L (e t) k j o -
        contScoreComponents M phi dphi L (b t) k j o) ∂observationLaw M) 0 0 := by
  let f : ℝ → ℝ := fun t => ∫ o : Obs X Z, w t o.1 *
    (contScoreComponents M phi dphi L (e t) k j o -
      contScoreComponents M phi dphi L (b t) k j o) ∂observationLaw M
  have hf0 : f 0 = 0 := by simp only [f, he0, sub_self, mul_zero, integral_zero]
  have hb : ∀ᶠ t : ℝ in 𝓝 0, |f t| ≤ (2 * (D * C / c)) * t^2 := by
    filter_upwards [hlocal] with t ht
    rcases ht with ⟨hpi, hp, hn, hprop, hshare, htau, hvp, hvm,
      hpm, hvpm, hvmm, hclip, hBp, hBm, hden⟩
    exact population_continuous_band_joint_regression_bias_bound M phi dphi L (e t) (b t)
      hpi hp hn hprop hshare htau k j (w t) (vp t) (vm t) hvp hvm hpm hvpm hvmm
      c D C t hc hD hC hclip hBp hBm hden
  have ho : (fun t => f t - f 0) =O[𝓝 0] (fun t : ℝ => t^2) := by
    apply Asymptotics.IsBigO.of_bound (2 * (D * C / c))
    filter_upwards [hb] with t ht
    simpa only [hf0, sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht
  apply HasDerivAt.of_isLittleO
  simpa only [smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

-- Product-score inheritance retains a weight/regression product, rather than
-- requiring the fitted weight to equal its population value.
-- @node: continuous_band_joint_product_difference
/-- If [two nuisance specifications have the same regular-band weights](hyp:hg), then
[their product-score difference equals the common regular weight times their band-score
difference, plus their band outcome-contrast difference times the instrument's policy-set
membership indicator minus that weight](goal). -/
lemma continuous_band_joint_product_difference
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hg : e.gamma = b.gamma) (k j : ℕ) (o : Obs X Z) :
    psiProd M phi dphi L e k j o - psiProd M phi dphi L b k j o =
      regularValue e.gamma k j o.1 *
        (contScoreComponents M phi dphi L e k (j-1) o -
          contScoreComponents M phi dphi L b k (j-1) o) +
      (contJ L e k (j-1) o.1 - contJ L b k (j-1) o.1) *
        (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1) := by
  simp only [psiProd, hg]
  ring

-- The assignment residual disappears by the finite population law. Its
-- remaining fitted-weight defect is explicitly a product of two errors.
-- @node: population_continuous_band_joint_product_difference_mean
/-- Suppose [two nuisance specifications have equal regular-band weights](hyp:hg),
[the covariate function is their band outcome-contrast difference](hyp:hv),
[that function is measurable](hyp:hvm), and [it is integrable under the observation law](hyp:iv).
If [the regular-weighted band-score difference is integrable](hyp:is) and
[the contrast difference times the true policy-set probability minus the fitted weight
is integrable](hyp:ir), then [the product-score difference is integrable and its population
mean equals the mean regular-weighted band-score difference plus the mean product of
the outcome-contrast difference and the true-policy-set-probability minus fitted-weight defect](goal). -/
lemma population_continuous_band_joint_product_difference_mean
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hg : e.gamma = b.gamma) (k j : ℕ)
    (v : X → ℝ) (hv : ∀ x, v x = contJ L e k (j-1) x - contJ L b k (j-1) x)
    (hvm : Measurable v)
    (iv : Integrable (fun o : Obs X Z => v o.1) (observationLaw M))
    (is : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      (contScoreComponents M phi dphi L e k (j-1) o -
        contScoreComponents M phi dphi L b k (j-1) o)) (observationLaw M))
    (ir : Integrable (fun o : Obs X Z => v o.1 *
      ((∑ z ∈ policyUnion L k j, instProb M z o.1) - regularValue e.gamma k j o.1))
        (observationLaw M)) :
    Integrable (fun o => psiProd M phi dphi L e k j o - psiProd M phi dphi L b k j o)
      (observationLaw M) ∧
    (∫ o, psiProd M phi dphi L e k j o - psiProd M phi dphi L b k j o
      ∂observationLaw M) =
      (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
        (contScoreComponents M phi dphi L e k (j-1) o -
          contScoreComponents M phi dphi L b k (j-1) o) ∂observationLaw M) +
      ∫ o : Obs X Z, v o.1 *
        ((∑ z ∈ policyUnion L k j, instProb M z o.1) - regularValue e.gamma k j o.1)
        ∂observationLaw M := by
  have ia := population_assignment_residual_weighted_integrable M (policyUnion L k j) (fun o => v o.1) iv
  have za := population_assignment_weighted_integral_zero M (policyUnion L k j) v hvm ia
  have hid : (fun o => psiProd M phi dphi L e k j o - psiProd M phi dphi L b k j o) =
      (fun o : Obs X Z => regularValue e.gamma k j o.1 *
        (contScoreComponents M phi dphi L e k (j-1) o -
          contScoreComponents M phi dphi L b k (j-1) o) +
        v o.1 * (indicator (o.2.1 ∈ policyUnion L k j) -
          ∑ z ∈ policyUnion L k j, instProb M z o.1) +
        v o.1 * ((∑ z ∈ policyUnion L k j, instProb M z o.1) -
          regularValue e.gamma k j o.1)) := by
    funext o
    rw [continuous_band_joint_product_difference M phi dphi L e b hg, hv]
    ring
  rw [hid]
  refine ⟨(is.fun_add ia).fun_add ir, ?_⟩
  rw [integral_add (is.fun_add ia) ir, integral_add is ia, za, add_zero]

-- Joint changes in the product weight, J/M regressions, and pi leave only
-- regression/denominator and weight/regression products, as in the roadmap.
-- @node: population_continuous_band_joint_product_difference_bound
/-- Suppose two nuisance specifications have [equal assignment denominators](hyp:hpi),
[equal treatment-propensity levels](hyp:hp), [equal quantile boundaries](hyp:hn),
[equal instrument-specific propensities](hyp:hprop), [equal instrument shares](hyp:hshare),
and [equal pooled denominators](hyp:htau). Assume [the upper coefficient is the regular
weight times the upper propensity level times its propensity-coefficient change](hyp:hvp)
and [the lower coefficient is the regular weight times the negative lower propensity
level times its propensity-coefficient change, set to zero at level zero](hyp:hvm),
with [measurable assignment denominators](hyp:hpm), [a measurable upper coefficient](hyp:hvpmeas),
and [a measurable lower coefficient](hyp:hvmmeas). Let [c be a positive denominator floor](hyp:hc),
[D be nonnegative](hyp:hD), and [C be nonnegative](hyp:hC); suppose [denominators are at
least c almost surely](hyp:hclip), [the upper coefficient has magnitude at most D times
the absolute perturbation](hyp:hBp), [the lower coefficient obeys the same bound](hyp:hBm),
and [valid assignment-denominator errors relative to true instrument-set probabilities
are at most C times the absolute perturbation](hyp:hden). If [regular weights agree](hyp:hg),
[the contrast function is the band outcome-contrast difference](hyp:hv),
[that function is measurable](hyp:hvmeas), [the regular weight is measurable](hyp:hgm),
[E is nonnegative](hyp:hE), [G is nonnegative](hyp:hG), [the contrast difference is at
most E times the absolute perturbation in magnitude](hyp:hve), and [the true policy-set
probability minus fitted weight is at most G times the absolute perturbation in magnitude](hyp:hge),
then [the product-score difference is integrable and its absolute population mean is
at most (2DC/c + EG) times the squared perturbation](goal). -/
lemma population_continuous_band_joint_product_difference_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hp : e.pLev = b.pLev) (hn : e.nu = b.nu)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k : Fin L.K) (j : ℕ) (vp vm : X → ℝ)
    (hvp : ∀ x, vp x = regularValue e.gamma k (j+1) x * (positiveValue b.pLev (k+1) x *
      (alphaHigh M L e k j x - alphaHigh M L b k j x)))
    (hvm : ∀ x, vm x = regularValue e.gamma k (j+1) x * (if k.val = 0 then 0 else -positiveValue b.pLev k x *
      (alphaLow M L e k j x - alphaLow M L b k j x)))
    (hpm : ∀ a, Measurable (b.piLev a)) (hvpmeas : Measurable vp) (hvmmeas : Measurable vm)
    (c D C t : ℝ) (hc : 0 < c) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ b.piLev a x)
    (hBp : ∀ᵐ x ∂xLaw M, |vp x| ≤ D * |t|)
    (hBm : ∀ᵐ x ∂xLaw M, |vm x| ≤ D * |t|)
    (hden : ∀ i, 1 ≤ i → i ≤ L.K → ∀ᵐ x ∂xLaw M,
      |positiveValue b.piLev i x - ∑ z ∈ L.S i, instProb M z x| ≤ C * |t|)
    (hg : e.gamma = b.gamma) (v : X → ℝ)
    (hv : ∀ x, v x = contJ L e k j x - contJ L b k j x)
    (hvmeas : Measurable v) (hgm : Measurable (regularValue e.gamma k (j+1)))
    (E G : ℝ) (hE : 0 ≤ E) (hG : 0 ≤ G)
    (hve : ∀ᵐ x ∂xLaw M, |v x| ≤ E * |t|)
    (hge : ∀ᵐ x ∂xLaw M,
      |(∑ z ∈ policyUnion L k (j+1), instProb M z x) -
        regularValue e.gamma k (j+1) x| ≤ G * |t|) :
    Integrable (fun o => psiProd M phi dphi L e k (j+1) o -
      psiProd M phi dphi L b k (j+1) o) (observationLaw M) ∧
    |∫ o, psiProd M phi dphi L e k (j+1) o -
      psiProd M phi dphi L b k (j+1) o ∂observationLaw M| ≤
        (2 * (D * C / c) + E * G) * t^2 := by
  haveI : IsProbabilityMeasure (observationLaw M) := by
    unfold observationLaw
    exact Measure.isProbabilityMeasure_map
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
  have iv : Integrable (fun o : Obs X Z => v o.1) (observationLaw M) :=
    Integrable.of_bound (hvmeas.comp measurable_fst).aestronglyMeasurable (E * |t|)
      (observationLaw_covariate_ae M _ (by simpa only [Real.norm_eq_abs] using hve))
  let R : Obs X Z → ℝ := fun o => v o.1 *
    ((∑ z ∈ policyUnion L k (j+1), instProb M z o.1) -
      regularValue e.gamma k (j+1) o.1)
  have hprob := population_instrument_set_probability_measurable M (policyUnion L k (j+1))
  have hRm : Measurable R := (hvmeas.mul (hprob.sub hgm)).comp measurable_fst
  have hRb : ∀ᵐ o ∂observationLaw M, ‖R o‖ ≤ (E * G) * t^2 := by
    apply observationLaw_covariate_ae M (fun x => ‖v x *
      ((∑ z ∈ policyUnion L k (j+1), instProb M z x) -
        regularValue e.gamma k (j+1) x)‖ ≤ (E * G) * t^2)
    filter_upwards [hve, hge] with x hx hy
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (E * |t|) * (G * |t|) := mul_le_mul hx hy (abs_nonneg _) (by positivity)
      _ = (E * G) * t^2 := by rw [← sq_abs t]; ring
  have ir : Integrable R (observationLaw M) :=
    Integrable.of_bound hRm.aestronglyMeasurable ((E * G) * t^2) hRb
  have hrb : |∫ o, R o ∂observationLaw M| ≤ (E * G) * t^2 := by
    simpa using
      norm_integral_le_of_norm_le_const hRb
  have his := (population_continuous_band_joint_regression_bias M phi dphi L e b
    hpi hp hn hprop hshare htau k j (regularValue e.gamma k (j+1)) vp vm
    hvp hvm hpm hvpmeas hvmmeas c (D*|t|) (D*|t|) hc hclip
    (by simpa only [Real.norm_eq_abs] using hBp)
    (by simpa only [Real.norm_eq_abs] using hBm)).1
  have hsb := population_continuous_band_joint_regression_bias_bound M phi dphi L e b
    hpi hp hn hprop hshare htau k j (regularValue e.gamma k (j+1)) vp vm
    hvp hvm hpm hvpmeas hvmmeas c D C t hc hD hC hclip hBp hBm hden
  have hv' : ∀ x, v x = contJ L e k ((j+1)-1) x - contJ L b k ((j+1)-1) x := by
    simpa only [Nat.add_sub_cancel] using hv
  obtain ⟨hi, hz⟩ := population_continuous_band_joint_product_difference_mean M
    phi dphi L e b hg k (j+1) v hv' hvmeas iv (by simpa only [Nat.add_sub_cancel] using his) ir
  refine ⟨hi, ?_⟩
  rw [hz]
  apply (abs_add_le _ _).trans
  simpa only [Nat.add_sub_cancel, R] using
    (add_le_add hsb hrb).trans_eq (by ring)

-- The already integrated quadratic bias controls a simultaneous change of
-- regression, assignment denominator, and product weight. The reference path
-- retains the other primitive nuisances, so it can be used in a telescoping
-- assembly without freezing those nuisances at the truth.
-- @node: population_continuous_band_joint_product_derivative
/-- Suppose [two nuisance paths agree at time zero](hyp:he0), [the denominator floor
c is positive](hyp:hc), and [the coefficient-error constant D](hyp:hD),
[denominator-error constant C](hyp:hC), [outcome-contrast-error constant E](hyp:hE), and
[weight-error constant G](hyp:hG) are nonnegative. Assume [near zero the paths share
assignment denominators, propensity levels, quantiles, instrument propensities, instrument
shares, pooled denominators, and regular weights; their regular-weighted upper and lower
propensity-coefficient changes are measurable and bounded in magnitude by D times absolute
time; the shared assignment denominators are measurable, at least c almost surely, and
within C times absolute time of true instrument-set probabilities; and the measurable
band outcome-contrast difference and the true policy-set probability minus the measurable
regular weight are bounded in magnitude by E and G times absolute time, respectively](hyp:hlocal).
Then [the population difference of the two band product scores has derivative zero at time zero](goal). -/
lemma population_continuous_band_joint_product_derivative
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e b : ℝ → NuisanceCont L) (he0 : e 0 = b 0)
    (k : Fin L.K) (j : ℕ) (vp vm v : ℝ → X → ℝ)
    (c D C E G : ℝ) (hc : 0 < c)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hE : 0 ≤ E) (hG : 0 ≤ G)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (e t).piLev = (b t).piLev ∧ (e t).pLev = (b t).pLev ∧
      (e t).nu = (b t).nu ∧ (e t).prop = (b t).prop ∧
      (e t).share = (b t).share ∧ (e t).tauLev = (b t).tauLev ∧
      (e t).gamma = (b t).gamma ∧
      (∀ x, vp t x = regularValue (e t).gamma k (j+1) x *
        (positiveValue (b t).pLev (k+1) x *
          (alphaHigh M L (e t) k j x - alphaHigh M L (b t) k j x))) ∧
      (∀ x, vm t x = regularValue (e t).gamma k (j+1) x *
        (if k.val = 0 then 0 else -positiveValue (b t).pLev k x *
          (alphaLow M L (e t) k j x - alphaLow M L (b t) k j x))) ∧
      (∀ a, Measurable ((b t).piLev a)) ∧ Measurable (vp t) ∧ Measurable (vm t) ∧
      (∀ a, ∀ᵐ x ∂xLaw M, c ≤ (b t).piLev a x) ∧
      (∀ᵐ x ∂xLaw M, |vp t x| ≤ D * |t|) ∧
      (∀ᵐ x ∂xLaw M, |vm t x| ≤ D * |t|) ∧
      (∀ i, 1 ≤ i → i ≤ L.K → ∀ᵐ x ∂xLaw M,
        |positiveValue (b t).piLev i x - ∑ z ∈ L.S i, instProb M z x| ≤ C * |t|) ∧
      (∀ x, v t x = contJ L (e t) k j x - contJ L (b t) k j x) ∧
      Measurable (v t) ∧ Measurable (regularValue (e t).gamma k (j+1)) ∧
      (∀ᵐ x ∂xLaw M, |v t x| ≤ E * |t|) ∧
      (∀ᵐ x ∂xLaw M,
        |(∑ z ∈ policyUnion L k (j+1), instProb M z x) -
          regularValue (e t).gamma k (j+1) x| ≤ G * |t|)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiProd M phi dphi L (e t) k (j+1) o -
      psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) 0 0 := by
  let f : ℝ → ℝ := fun t => ∫ o, psiProd M phi dphi L (e t) k (j+1) o -
    psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M
  have hf0 : f 0 = 0 := by simp only [f, he0, sub_self, integral_zero]
  have hb : ∀ᶠ t : ℝ in 𝓝 0, |f t| ≤ (2 * (D * C / c) + E * G) * t^2 := by
    filter_upwards [hlocal] with t ht
    rcases ht with ⟨hpi, hp, hn, hprop, hshare, htau, hg, hvp, hvm,
      hpm, hvpm, hvmm, hclip, hBp, hBm, hden, hv, hvm', hgm, hve, hge⟩
    exact (population_continuous_band_joint_product_difference_bound M phi dphi L
      (e t) (b t) hpi hp hn hprop hshare htau k j (vp t) (vm t) hvp hvm
      hpm hvpm hvmm c D C t hc hD hC hclip hBp hBm hden hg (v t)
      hv hvm' hgm E G hE hG hve hge).2
  have ho : (fun t => f t - f 0) =O[𝓝 0] (fun t : ℝ => t^2) := by
    apply Asymptotics.IsBigO.of_bound (2 * (D * C / c) + E * G)
    filter_upwards [hb] with t ht
    simpa only [hf0, sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht
  apply HasDerivAt.of_isLittleO
  simpa only [smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

end Papers.TbsPrteOptimalTransport
