module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandJointDerivative
/-! Continuous band propensity cancellation with jointly fitted assignment denominators. -/
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

-- The fixed lower quantile has no direction. At j=0, pooledQ equals p_k,
-- which removes the constant lower-boundary term from the representer.
-- @node: continuous_band_fixed_denominator_propensity_difference
/-- For two nuisance collections with [equal assignment denominators](hyp:hpi),
[equal band quantiles](hyp:hn), [equal upper outcome regressions](hyp:hJp),
[equal lower outcome regressions](hyp:hJm), [equal upper indicator regressions](hyp:hMp),
[equal lower indicator regressions](hyp:hMm), [equal instrument propensities](hyp:hprop),
[equal pooling shares](hyp:hshare), and [equal pooled denominators](hyp:htau), at
[a band index below the level's band count](hyp:hj), [the score-component difference
equals the upper coefficient times the upper level-propensity change times its
normalized assignment defect, minus the analogous lower term with negated lower
coefficient; the lower term is zero at level zero](goal). -/
lemma continuous_band_fixed_denominator_propensity_difference
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hn : e.nu = b.nu)
    (hJp : e.Jplus = b.Jplus) (hJm : e.Jminus = b.Jminus)
    (hMp : e.Mplus = b.Mplus) (hMm : e.Mminus = b.Mminus)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k j : ℕ) (hj : j < L.l k) (o : Obs X Z) :
    contScoreComponents M phi dphi L e k j o - contScoreComponents M phi dphi L b k j o =
      (alphaHigh M L b k j o.1 *
        (positiveValue e.pLev (k+1) o.1 - positiveValue b.pLev (k+1) o.1)) *
        (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue b.piLev (k+1) o.1) -
      (if k = 0 then 0 else -alphaLow M L b k j o.1 *
        (positiveValue e.pLev k o.1 - positiveValue b.pLev k o.1)) *
        (1 - indicator (o.2.1 ∈ L.S k) / positiveValue b.piLev k o.1) := by
  have hn' : ∀ i, nuValue M e k i o.1 = nuValue M b k i o.1 := by
    intro i
    simp only [nuValue, hn]
  have hr : ∀ i, RqCont dphi L e k i o = RqCont dphi L b k i o := by
    intro i
    simp only [RqCont, htau, hprop]
  have hq1 : pooledQ phi L e k (j+1) o.1 = pooledQ phi L b k (j+1) o.1 := by
    simp only [pooledQ, if_neg (show j+1 ≠ 0 by omega),
      if_neg (show ¬ L.l k < j+1 by omega), shareValue, hshare, hprop]
  have hq0 : pooledQ phi L e k j o.1 =
      if j = 0 then positiveValue e.pLev k o.1 else pooledQ phi L b k j o.1 := by
    by_cases hj0 : j = 0
    · simp [pooledQ, hj0]
    · simp only [pooledQ, if_neg hj0, if_neg (show ¬ L.l k < j by omega),
        shareValue, hshare, hprop]
  simp only [contScoreComponents, contJ, IFJ, IFM, alphaHigh, alphaLow,
    RpCont, hn', hr, hq0, hq1, hpi, hJp, hJm, hMp, hMm]
  by_cases hk : k = 0 <;> by_cases hj0 : j = 0
  all_goals
    have hq : j = 0 → pooledQ phi L b k j o.1 = positiveValue b.pLev k o.1 := by
      intro h
      simp only [pooledQ, h, if_true]
    have hz (f : PositiveIndex L.K → X → ℝ) : positiveValue f 0 o.1 = 0 := by
      simp only [positiveValue, dif_neg (show ¬ (1 ≤ 0 ∧ 0 ≤ L.K) by omega)]
    try rw [hq hj0]
    simp [hk, hj0, hz, indicator, show (1 ≤ j) ↔ j ≠ 0 from by omega]
    <;> ring

-- A fitted denominator leaves the exact reciprocal defect. Both sides are
-- obtained from the finite-instrument population assignment identity.
-- @node: population_continuous_band_joint_propensity_bias
/-- Suppose two nuisance collections have [equal assignment denominators](hyp:hpi),
[equal band quantiles](hyp:hn), [equal upper outcome regressions](hyp:hJp),
[equal lower outcome regressions](hyp:hJm), [equal upper indicator regressions](hyp:hMp),
[equal lower indicator regressions](hyp:hMm), [equal instrument propensities](hyp:hprop),
[equal pooling shares](hyp:hshare), and [equal pooled denominators](hyp:htau), and
[the band index is below the level's band count](hyp:hj). If [the upper auxiliary
function is the covariate weight times the upper coefficient and upper
level-propensity change](hyp:hvp), [the lower auxiliary function is the weight
times the negated lower coefficient and lower level-propensity change, or zero at
level zero](hyp:hvm), [the reference assignment denominators are measurable](hyp:hpm),
[the upper auxiliary function is measurable](hyp:hvpmeas), [the lower auxiliary
function is measurable](hyp:hvmmeas), [the denominator floor is positive](hyp:hc),
[all reference assignment denominators exceed that floor almost surely](hyp:hclip),
[the upper auxiliary function is almost surely bounded by its designated constant](hyp:hBp),
and [the lower auxiliary function is almost surely bounded by its designated
constant](hyp:hBm), [the weighted score-component difference is integrable and its
expectation equals the upper auxiliary function's expected assignment-denominator
defect minus the lower auxiliary function's expected assignment-denominator defect,
where each defect is one minus the true instrument-set probability divided by the
fitted assignment denominator](goal). -/
lemma population_continuous_band_joint_propensity_bias
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hn : e.nu = b.nu)
    (hJp : e.Jplus = b.Jplus) (hJm : e.Jminus = b.Jminus)
    (hMp : e.Mplus = b.Mplus) (hMm : e.Mminus = b.Mminus)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) (w vp vm : X → ℝ)
    (hvp : ∀ x, vp x = w x * (alphaHigh M L b k j x *
      (positiveValue e.pLev (k+1) x - positiveValue b.pLev (k+1) x)))
    (hvm : ∀ x, vm x = w x * (if k.val = 0 then 0 else -alphaLow M L b k j x *
      (positiveValue e.pLev k x - positiveValue b.pLev k x)))
    (hpm : ∀ a, Measurable (b.piLev a)) (hvpmeas : Measurable vp) (hvmmeas : Measurable vm)
    (c Bp Bm : ℝ) (hc : 0 < c)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ b.piLev a x)
    (hBp : ∀ᵐ x ∂xLaw M, ‖vp x‖ ≤ Bp) (hBm : ∀ᵐ x ∂xLaw M, ‖vm x‖ ≤ Bm) :
    Integrable (fun o : Obs X Z => w o.1 *
      (contScoreComponents M phi dphi L e k j o -
        contScoreComponents M phi dphi L b k j o)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (contScoreComponents M phi dphi L e k j o -
        contScoreComponents M phi dphi L b k j o) ∂observationLaw M) =
      (∫ o : Obs X Z, vp o.1 *
        (1 - (∑ z ∈ L.S (k+1), instProb M z o.1) /
          positiveValue b.piLev (k+1) o.1) ∂observationLaw M) -
      (∫ o : Obs X Z, vm o.1 *
        (1 - (∑ z ∈ L.S k, instProb M z o.1) /
          positiveValue b.piLev k o.1) ∂observationLaw M) := by
  have hi : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ L.K := by omega
  obtain ⟨ip, irp, zp⟩ := population_fitted_normalized_assignment_defect M (L.S (k+1))
    (b.piLev ⟨k+1,hi⟩) vp (hpm _) hvpmeas c Bp hc (hclip _) hBp
  have hpos : positiveValue b.piLev (k+1) = b.piLev ⟨k+1,hi⟩ := by
    funext x
    simp only [positiveValue, dif_pos hi]
  rw [← hpos] at ip zp
  have hm : Integrable (fun o : Obs X Z => vm o.1 *
      (1 - indicator (o.2.1 ∈ L.S k) / positiveValue b.piLev k o.1)) (observationLaw M) ∧
      (∫ o : Obs X Z, vm o.1 *
        (1 - indicator (o.2.1 ∈ L.S k) / positiveValue b.piLev k o.1) ∂observationLaw M) =
      ∫ o : Obs X Z, vm o.1 *
        (1 - (∑ z ∈ L.S k, instProb M z o.1) / positiveValue b.piLev k o.1)
          ∂observationLaw M := by
    by_cases hk0 : k.val = 0
    · have hz : vm = fun _ => (0 : ℝ) := by
        funext x
        simp only [hvm, hk0, if_true, mul_zero]
      simp only [hz, zero_mul, integral_zero]
      exact ⟨integrable_zero _ _ _, True.intro⟩
    · have hi : 1 ≤ k.val ∧ k.val ≤ L.K := by omega
      obtain ⟨im, irm, zm⟩ := population_fitted_normalized_assignment_defect M (L.S k)
        (b.piLev ⟨k,hi⟩) vm (hpm _) hvmmeas c Bm hc (hclip _) hBm
      have hpos : positiveValue b.piLev k = b.piLev ⟨k,hi⟩ := by
        funext x
        simp only [positiveValue, dif_pos hi]
      rw [← hpos] at im zm
      exact ⟨im, zm⟩
  have hid : (fun o : Obs X Z => w o.1 *
      (contScoreComponents M phi dphi L e k j o - contScoreComponents M phi dphi L b k j o)) =
      (fun o => vp o.1 * (1 - indicator (o.2.1 ∈ L.S (k+1)) /
          positiveValue b.piLev (k+1) o.1) -
        vm o.1 * (1 - indicator (o.2.1 ∈ L.S k) / positiveValue b.piLev k o.1)) := by
    funext o
    rw [continuous_band_fixed_denominator_propensity_difference M phi dphi L e b
      hpi hn hJp hJm hMp hMm hprop hshare htau k j hj, hvp, hvm]
    ring
  rw [hid]
  exact ⟨ip.sub' hm.1, by rw [integral_sub ip hm.1, zp, hm.2]⟩

-- The assignment defect is first order in its denominator error; the
-- regression coefficient supplies the other first-order factor.
-- @node: population_continuous_band_joint_propensity_bias_bound
/-- Suppose two nuisance collections have [equal assignment denominators](hyp:hpi),
[equal band quantiles](hyp:hn), [equal upper outcome regressions](hyp:hJp),
[equal lower outcome regressions](hyp:hJm), [equal upper indicator regressions](hyp:hMp),
[equal lower indicator regressions](hyp:hMm), [equal instrument propensities](hyp:hprop),
[equal pooling shares](hyp:hshare), and [equal pooled denominators](hyp:htau), with
[a band index below the level's band count](hyp:hj). Assume [the upper auxiliary
function equals the weight times the upper coefficient and upper level-propensity
change](hyp:hvp), [the lower auxiliary function equals the weight times the negated
lower coefficient and lower level-propensity change, with zero at level zero](hyp:hvm),
[reference assignment denominators are measurable](hyp:hpm), [the upper auxiliary
function is measurable](hyp:hvpmeas), [the lower auxiliary function is measurable](hyp:hvmmeas),
[the denominator floor c is positive](hyp:hc), [the coefficient bound D is
nonnegative](hyp:hD), [the denominator-error bound C is nonnegative](hyp:hC),
[reference assignment denominators are almost surely at least c](hyp:hclip),
[the upper auxiliary magnitude is almost surely at most D times the absolute
perturbation t](hyp:hBp), [the lower auxiliary magnitude satisfies the same bound](hyp:hBm),
and [every fitted assignment denominator differs from its true instrument-set
probability by at most C times the absolute perturbation, almost surely](hyp:hden).
[The absolute expected weighted score-component difference is at most twice D
times C divided by c, multiplied by the square of t](goal). -/
lemma population_continuous_band_joint_propensity_bias_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hn : e.nu = b.nu)
    (hJp : e.Jplus = b.Jplus) (hJm : e.Jminus = b.Jminus)
    (hMp : e.Mplus = b.Mplus) (hMm : e.Mminus = b.Mminus)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) (w vp vm : X → ℝ)
    (hvp : ∀ x, vp x = w x * (alphaHigh M L b k j x *
      (positiveValue e.pLev (k+1) x - positiveValue b.pLev (k+1) x)))
    (hvm : ∀ x, vm x = w x * (if k.val = 0 then 0 else -alphaLow M L b k j x *
      (positiveValue e.pLev k x - positiveValue b.pLev k x)))
    (hpm : ∀ a, Measurable (b.piLev a)) (hvpmeas : Measurable vp) (hvmmeas : Measurable vm)
    (c D C t : ℝ) (hc : 0 < c) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ b.piLev a x)
    (hBp : ∀ᵐ x ∂xLaw M, |vp x| ≤ D * |t|)
    (hBm : ∀ᵐ x ∂xLaw M, |vm x| ≤ D * |t|)
    (hden : ∀ i, 1 ≤ i → i ≤ L.K → ∀ᵐ x ∂xLaw M,
      |positiveValue b.piLev i x - ∑ z ∈ L.S i, instProb M z x| ≤ C * |t|) :
    |∫ o : Obs X Z, w o.1 *
      (contScoreComponents M phi dphi L e k j o -
        contScoreComponents M phi dphi L b k j o) ∂observationLaw M| ≤
      (2 * (D * C / c)) * t^2 := by
  obtain ⟨_, hb⟩ := population_continuous_band_joint_propensity_bias M phi dphi L e b
    hpi hn hJp hJm hMp hMm hprop hshare htau k j hj w vp vm hvp hvm hpm hvpmeas hvmmeas
    c (D * |t|) (D * |t|) hc hclip
    (by simpa only [Real.norm_eq_abs] using hBp)
    (by simpa only [Real.norm_eq_abs] using hBm)
  have bound (v : X → ℝ) (hv : ∀ᵐ x ∂xLaw M, |v x| ≤ D * |t|)
      (i : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) :
      |∫ o : Obs X Z, v o.1 *
        (1 - (∑ z ∈ L.S i, instProb M z o.1) / positiveValue b.piLev i o.1)
          ∂observationLaw M| ≤ (D * C / c) * t^2 := by
    have hx : ∀ᵐ x ∂xLaw M, ‖v x *
        (1 - (∑ z ∈ L.S i, instProb M z x) / positiveValue b.piLev i x)‖ ≤
        (D * C / c) * t^2 := by
      filter_upwards [hv, hclip ⟨i,hi⟩, hden i hi.1 hi.2] with x hvx hcx hdx
      have hpx : c ≤ positiveValue b.piLev i x := by
        simpa only [positiveValue, dif_pos hi] using hcx
      have hh := continuous_full_coefficient_reciprocal_defect_bound
        (v x) 0 (positiveValue b.piLev i x) (∑ z ∈ L.S i, instProb M z x)
        1 D C 1 t c hc hpx (by simpa using hvx) hdx (by norm_num) hD hC
      simpa only [one_mul, sub_zero, Real.norm_eq_abs] using hh
    haveI : IsProbabilityMeasure (observationLaw M) := by
      unfold observationLaw
      exact Measure.isProbabilityMeasure_map
        (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
    simpa using
      norm_integral_le_of_norm_le_const (observationLaw_covariate_ae M _ hx)
  have hpBound := bound vp hBp (k+1) (by omega)
  have hmBound : |∫ o : Obs X Z, vm o.1 *
      (1 - (∑ z ∈ L.S k, instProb M z o.1) / positiveValue b.piLev k o.1)
        ∂observationLaw M| ≤ (D * C / c) * t^2 := by
    by_cases hk0 : k.val = 0
    · have hz : vm = fun _ => (0 : ℝ) := by
        funext x
        simp only [hvm, hk0, if_true, mul_zero]
      simp only [hz, zero_mul, integral_zero, abs_zero]
      positivity
    · exact bound vm hBm k (by omega)
  rw [hb]
  exact (abs_sub _ _).trans (by linarith)

-- Propensity and assignment-denominator errors vanish jointly at first order.
-- The reference path may itself vary; only the displayed primitive components
-- must agree between the two paths.
-- @node: population_continuous_band_joint_propensity_derivative
/-- For nuisance paths [agreeing at zero](hyp:he0) and [a band index below the
level's band count](hyp:hj), assume [a positive denominator floor c](hyp:hc),
[a nonnegative coefficient bound D](hyp:hD), and [a nonnegative denominator-error
bound C](hyp:hC). If [near zero the paths agree in assignment denominators,
quantiles, outcome and indicator regressions, instrument propensities, pooling
shares, and pooled denominators; the upper and lower auxiliary functions are the
weighted coefficient-times-level-propensity changes, with zero lower term at level
zero; reference assignment denominators and both auxiliary functions are
measurable; denominators are almost surely at least c; both auxiliary magnitudes
are bounded by D times the absolute perturbation; and denominator errors relative
to true instrument-set probabilities are bounded by C times that magnitude](hyp:hlocal),
[the expected weighted score-component difference has derivative zero at zero](goal). -/
lemma population_continuous_band_joint_propensity_derivative
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e b : ℝ → NuisanceCont L) (he0 : e 0 = b 0)
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) (w : ℝ → X → ℝ)
    (vp vm : ℝ → X → ℝ) (c D C : ℝ)
    (hc : 0 < c) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (e t).piLev = (b t).piLev ∧ (e t).nu = (b t).nu ∧
      (e t).Jplus = (b t).Jplus ∧ (e t).Jminus = (b t).Jminus ∧
      (e t).Mplus = (b t).Mplus ∧ (e t).Mminus = (b t).Mminus ∧ (e t).prop = (b t).prop ∧
      (e t).share = (b t).share ∧ (e t).tauLev = (b t).tauLev ∧
      (∀ x, vp t x = w t x * (alphaHigh M L (b t) k j x *
        (positiveValue (e t).pLev (k+1) x - positiveValue (b t).pLev (k+1) x))) ∧
      (∀ x, vm t x = w t x * (if k.val = 0 then 0 else
        -alphaLow M L (b t) k j x *
          (positiveValue (e t).pLev k x - positiveValue (b t).pLev k x))) ∧
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
    rcases ht with ⟨hpi, hn, hJp, hJm, hMp, hMm, hprop, hshare, htau, hvp, hvm,
      hpm, hvpm, hvmm, hclip, hBp, hBm, hden⟩
    exact population_continuous_band_joint_propensity_bias_bound M phi dphi L (e t) (b t)
      hpi hn hJp hJm hMp hMm hprop hshare htau k j hj (w t) (vp t) (vm t) hvp hvm hpm hvpm hvmm
      c D C t hc hD hC hclip hBp hBm hden
  have ho : (fun t => f t - f 0) =O[𝓝 0] (fun t : ℝ => t^2) := by
    apply Asymptotics.IsBigO.of_bound (2 * (D * C / c))
    filter_upwards [hb] with t ht
    simpa only [hf0, sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht
  apply HasDerivAt.of_isLittleO
  simpa only [smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

-- Joint changes in the product weight, J/M regressions, and pi leave only
-- propensity/denominator and weight/propensity products, as in the roadmap.
-- @node: population_continuous_band_joint_propensity_product_difference_bound
/-- Suppose two nuisance collections have [equal assignment denominators](hyp:hpi),
[equal band quantiles](hyp:hn), [equal upper outcome regressions](hyp:hJp),
[equal lower outcome regressions](hyp:hJm), [equal upper indicator regressions](hyp:hMp),
[equal lower indicator regressions](hyp:hMm), [equal instrument propensities](hyp:hprop),
[equal pooling shares](hyp:hshare), and [equal pooled denominators](hyp:htau), for
[a band index below the level's band count](hyp:hj). Assume [the upper auxiliary
function is the first collection's band weight times the upper coefficient and
upper level-propensity change](hyp:hvp), [the lower auxiliary function is that band
weight times the negated lower coefficient and lower level-propensity change,
with zero at level zero](hyp:hvm), [reference assignment denominators are
measurable](hyp:hpm), [the upper auxiliary function is measurable](hyp:hvpmeas),
[the lower auxiliary function is measurable](hyp:hvmmeas), [the denominator floor
c is positive](hyp:hc), [D is nonnegative](hyp:hD), [C is nonnegative](hyp:hC),
[reference assignment denominators are almost surely at least c](hyp:hclip),
[the upper auxiliary magnitude is at most D times the absolute perturbation t
almost surely](hyp:hBp), [the lower auxiliary magnitude satisfies the same bound](hyp:hBm),
and [assignment-denominator errors relative to true instrument-set probabilities
are at most C times the absolute perturbation almost surely](hyp:hden). If also
[the regular-band weights agree](hyp:hg), [the representer-change function equals
the first band's representer minus the second's](hyp:hv), [that change is
measurable](hyp:hvmeas), [the band weight is measurable](hyp:hgm), [its
representer-error bound E is nonnegative](hyp:hE), [its weight-error bound G is
nonnegative](hyp:hG), [the representer-change magnitude is almost surely at most
E times the absolute perturbation](hyp:hve), and [the band weight differs from
the true policy-union probability by at most G times the absolute perturbation
almost surely](hyp:hge), [the product-score difference is integrable and its
absolute expectation is at most the square of t times the sum of twice D times C
divided by c and E times G](goal). -/
lemma population_continuous_band_joint_propensity_product_difference_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hn : e.nu = b.nu)
    (hJp : e.Jplus = b.Jplus) (hJm : e.Jminus = b.Jminus)
    (hMp : e.Mplus = b.Mplus) (hMm : e.Mminus = b.Mminus)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) (vp vm : X → ℝ)
    (hvp : ∀ x, vp x = regularValue e.gamma k (j+1) x * (alphaHigh M L b k j x *
      (positiveValue e.pLev (k+1) x - positiveValue b.pLev (k+1) x)))
    (hvm : ∀ x, vm x = regularValue e.gamma k (j+1) x * (if k.val = 0 then 0 else -alphaLow M L b k j x *
      (positiveValue e.pLev k x - positiveValue b.pLev k x)))
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
  have his := (population_continuous_band_joint_propensity_bias M phi dphi L e b
    hpi hn hJp hJm hMp hMm hprop hshare htau k j hj (regularValue e.gamma k (j+1)) vp vm
    hvp hvm hpm hvpmeas hvmmeas c (D*|t|) (D*|t|) hc hclip
    (by simpa only [Real.norm_eq_abs] using hBp)
    (by simpa only [Real.norm_eq_abs] using hBm)).1
  have hsb := population_continuous_band_joint_propensity_bias_bound M phi dphi L e b
    hpi hn hJp hJm hMp hMm hprop hshare htau k j hj (regularValue e.gamma k (j+1)) vp vm
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
-- propensity, assignment denominator, and product weight. The reference path
-- retains the other primitive nuisances, so it can be used in a telescoping
-- assembly without freezing those nuisances at the truth.
-- @node: population_continuous_band_joint_propensity_product_derivative
/-- For nuisance paths [agreeing at zero](hyp:he0) and [a band index below the
level's band count](hyp:hj), assume [a positive denominator floor c](hyp:hc),
[a nonnegative coefficient bound D](hyp:hD), [a nonnegative denominator-error
bound C](hyp:hC), [a nonnegative representer-change bound E](hyp:hE), and
[a nonnegative weight-error bound G](hyp:hG). If [near zero the paths agree in
assignment denominators, band quantiles, outcome and indicator regressions,
instrument propensities, pooling shares, pooled denominators, and band weights;
the upper and lower auxiliary functions are the band-weighted coefficient-times-
level-propensity changes, with zero lower term at level zero; assignment
denominators and auxiliary functions are measurable; denominators are almost
surely at least c; auxiliary magnitudes are bounded by D times the absolute
perturbation and denominator errors by C times that magnitude; and the measurable
representer difference and measurable band weight have errors bounded almost
surely by E and G times the absolute perturbation, respectively, the latter
relative to the true policy-union probability](hyp:hlocal), [the expected
product-score difference has derivative zero at zero](goal). -/
lemma population_continuous_band_joint_propensity_product_derivative
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e b : ℝ → NuisanceCont L) (he0 : e 0 = b 0)
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) (vp vm v : ℝ → X → ℝ)
    (c D C E G : ℝ) (hc : 0 < c)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hE : 0 ≤ E) (hG : 0 ≤ G)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (e t).piLev = (b t).piLev ∧ (e t).nu = (b t).nu ∧
      (e t).Jplus = (b t).Jplus ∧ (e t).Jminus = (b t).Jminus ∧
      (e t).Mplus = (b t).Mplus ∧ (e t).Mminus = (b t).Mminus ∧ (e t).prop = (b t).prop ∧
      (e t).share = (b t).share ∧ (e t).tauLev = (b t).tauLev ∧
      (e t).gamma = (b t).gamma ∧
      (∀ x, vp t x = regularValue (e t).gamma k (j+1) x *
        (alphaHigh M L (b t) k j x *
          (positiveValue (e t).pLev (k+1) x - positiveValue (b t).pLev (k+1) x))) ∧
      (∀ x, vm t x = regularValue (e t).gamma k (j+1) x *
        (if k.val = 0 then 0 else -alphaLow M L (b t) k j x *
          (positiveValue (e t).pLev k x - positiveValue (b t).pLev k x))) ∧
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
    rcases ht with ⟨hpi, hn, hJp, hJm, hMp, hMm, hprop, hshare, htau, hg, hvp, hvm,
      hpm, hvpm, hvmm, hclip, hBp, hBm, hden, hv, hvm', hgm, hve, hge⟩
    exact (population_continuous_band_joint_propensity_product_difference_bound M phi dphi L
      (e t) (b t) hpi hn hJp hJm hMp hMm hprop hshare htau k j hj (vp t) (vm t) hvp hvm
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
