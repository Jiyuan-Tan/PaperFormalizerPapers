module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullJointBias
public import Papers.TbsPrteOptimalTransport.Helpers.FractionalRegressionOrthogonality
/-! Joint band regression and assignment-denominator errors retain a product remainder. -/
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

-- The J and M coefficients change together. The propensity representers
-- turn treatment-weighted residuals into assignment-centered differences.
-- @node: continuous_band_fixed_denominator_regression_difference
/-- For two nuisance specifications with [equal assignment denominators](hyp:hpi),
[equal treatment-propensity levels](hyp:hp), [equal quantile boundaries](hyp:hn),
[equal instrument-specific propensities](hyp:hprop), [equal instrument shares](hyp:hshare),
and [equal pooled denominators](hyp:htau), [their band-score difference is the upper
propensity level times the upper coefficient change times its normalized assignment
defect, minus the analogous lower term with a negative propensity factor; the lower
term is zero at treatment level zero](goal). -/
lemma continuous_band_fixed_denominator_regression_difference
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hp : e.pLev = b.pLev) (hn : e.nu = b.nu)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k j : ℕ) (o : Obs X Z) :
    contScoreComponents M phi dphi L e k j o - contScoreComponents M phi dphi L b k j o =
      (positiveValue b.pLev (k+1) o.1 *
        (alphaHigh M L e k j o.1 - alphaHigh M L b k j o.1)) *
        (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue b.piLev (k+1) o.1) -
      (if k = 0 then 0 else -positiveValue b.pLev k o.1 *
        (alphaLow M L e k j o.1 - alphaLow M L b k j o.1)) *
        (1 - indicator (o.2.1 ∈ L.S k) / positiveValue b.piLev k o.1) := by
  have hnu : ∀ i, nuValue M e k i o.1 = nuValue M b k i o.1 := by
    intro i
    simp only [nuValue, hn]
  have hq : ∀ i, pooledQ phi L e k i o.1 = pooledQ phi L b k i o.1 := by
    intro i
    simp only [pooledQ, shareValue, hshare, hprop, hp]
  have hr : ∀ i, RqCont dphi L e k i o = RqCont dphi L b k i o := by
    intro i
    simp only [RqCont, htau, hprop]
  simp only [contScoreComponents, contJ, IFJ, IFM, alphaHigh, alphaLow,
    RpCont, hnu, hq, hr, hpi, hp]
  by_cases hk : k = 0
  · subst k
    have hz : positiveValue b.pLev 0 o.1 = 0 := by simp [positiveValue]
    simp only [hz]
    simp
    ring
  · have hbeq : (k == 0) = false := by simp [hk]
    simp [hk, hbeq]
    ring

-- A fitted denominator leaves the exact reciprocal defect. Both sides are
-- obtained from the finite-instrument population assignment identity.
-- @node: population_continuous_band_joint_regression_bias
/-- Suppose two nuisance specifications have [equal assignment denominators](hyp:hpi),
[equal treatment-propensity levels](hyp:hp), [equal quantile boundaries](hyp:hn),
[equal instrument-specific propensities](hyp:hprop), [equal instrument shares](hyp:hshare),
and [equal pooled denominators](hyp:htau). Let [the upper coefficient be the covariate
weight times the upper propensity level times the upper coefficient change](hyp:hvp)
and [the lower coefficient be the weight times the negative lower propensity level
times the lower coefficient change, set to zero at level zero](hyp:hvm).
If [assignment denominators are measurable](hyp:hpm), [the upper coefficient is measurable](hyp:hvpmeas),
[the lower coefficient is measurable](hyp:hvmmeas), [the denominator floor is positive](hyp:hc),
[all assignment denominators exceed that floor almost surely](hyp:hclip),
[the upper coefficient is almost surely bounded by its specified constant](hyp:hBp),
and [the lower coefficient is almost surely bounded by its specified constant](hyp:hBm),
then [the weighted band-score difference is integrable and its mean is the upper
coefficient's mean normalized assignment-probability defect minus the lower coefficient's
mean normalized assignment-probability defect](goal). -/
lemma population_continuous_band_joint_regression_bias
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hp : e.pLev = b.pLev) (hn : e.nu = b.nu)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k : Fin L.K) (j : ℕ) (w vp vm : X → ℝ)
    (hvp : ∀ x, vp x = w x * (positiveValue b.pLev (k+1) x *
      (alphaHigh M L e k j x - alphaHigh M L b k j x)))
    (hvm : ∀ x, vm x = w x * (if k.val = 0 then 0 else -positiveValue b.pLev k x *
      (alphaLow M L e k j x - alphaLow M L b k j x)))
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
    rw [continuous_band_fixed_denominator_regression_difference M phi dphi L e b
      hpi hp hn hprop hshare htau, hvp, hvm]
    ring
  rw [hid]
  exact ⟨ip.sub' hm.1, by rw [integral_sub ip hm.1, zp, hm.2]⟩

-- The assignment defect is first order in its denominator error; the
-- regression coefficient supplies the other first-order factor.
-- @node: population_continuous_band_joint_regression_bias_bound
/-- Suppose two nuisance specifications have [equal assignment denominators](hyp:hpi),
[equal treatment-propensity levels](hyp:hp), [equal quantile boundaries](hyp:hn),
[equal instrument-specific propensities](hyp:hprop), [equal instrument shares](hyp:hshare),
and [equal pooled denominators](hyp:htau). Assume [the upper coefficient equals the
weight times the upper propensity level times its coefficient change](hyp:hvp),
[the lower coefficient equals the weight times the negative lower propensity level
times its coefficient change, with zero at level zero](hyp:hvm),
[assignment denominators are measurable](hyp:hpm), [the upper coefficient is measurable](hyp:hvpmeas),
and [the lower coefficient is measurable](hyp:hvmmeas). With [a positive denominator
floor c](hyp:hc), [a nonnegative coefficient-error constant D](hyp:hD),
[a nonnegative denominator-error constant C](hyp:hC), [denominators at least c almost surely](hyp:hclip),
[upper coefficient magnitude at most D times the absolute perturbation](hyp:hBp),
[the same bound on the lower coefficient](hyp:hBm), and [every valid assignment
denominator within C times the absolute perturbation of its true instrument-set probability](hyp:hden),
[the absolute population mean of the weighted band-score difference is at most
2DC/c times the squared perturbation](goal). -/
lemma population_continuous_band_joint_regression_bias_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hpi : e.piLev = b.piLev) (hp : e.pLev = b.pLev) (hn : e.nu = b.nu)
    (hprop : e.prop = b.prop) (hshare : e.share = b.share) (htau : e.tauLev = b.tauLev)
    (k : Fin L.K) (j : ℕ) (w vp vm : X → ℝ)
    (hvp : ∀ x, vp x = w x * (positiveValue b.pLev (k+1) x *
      (alphaHigh M L e k j x - alphaHigh M L b k j x)))
    (hvm : ∀ x, vm x = w x * (if k.val = 0 then 0 else -positiveValue b.pLev k x *
      (alphaLow M L e k j x - alphaLow M L b k j x)))
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
  obtain ⟨_, hb⟩ := population_continuous_band_joint_regression_bias M phi dphi L e b
    hpi hp hn hprop hshare htau k j w vp vm hvp hvm hpm hvpmeas hvmmeas
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

end Papers.TbsPrteOptimalTransport
