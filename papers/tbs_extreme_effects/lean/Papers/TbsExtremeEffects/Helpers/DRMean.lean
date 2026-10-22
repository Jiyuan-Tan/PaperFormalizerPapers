module
public import Papers.TbsExtremeEffects.Helpers.DRAssembly
public import Papers.TbsExtremeEffects.Helpers.ExponentScore
public import Papers.TbsExtremeEffects.Helpers.AngularFactor

/-! Integration of the DR nuisance-product bias and assembly of the score mean error. -/

@[expose] public section
set_option linter.unusedTactic false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- For the [experiment](hyp:E), [sample size](hyp:n), [fitted regression](hyp:reg),
[training outcome](hyp:w), and [population observation](hyp:v), [the DR bias integrand](goal)
multiplies the propensity error by the sum of the two treatment-specific regression errors,
each weighted by its fitted treatment probability. -/
-- @node: drBiasIntegrand
noncomputable def drBiasIntegrand (E : NeteExperiment M) (n : ℕ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om) (v : M.Om) : ℝ :=
  (M.p (M.X v) - E.pHat n w (M.X v)) *
    ((reg (M.X v, true, direction M v) - E.gHat n w (M.X v) true (direction M v)) /
        E.pHat n w (M.X v) +
      (reg (M.X v, false, direction M v) - E.gHat n w (M.X v) false (direction M v)) /
        (1 - E.pHat n w (M.X v)))

/-- For the [experiment](hyp:E), [sample size](hyp:n), [training outcome](hyp:w), and
[population observation](hyp:v), [the exponent-error mean integrand](goal) is the inverse-
propensity weighted outcome contrast times the discrepancy from using the fitted tail exponent. -/
-- @node: exponentMeanIntegrand
noncomputable def exponentMeanIntegrand (E : NeteExperiment M) (n : ℕ) (w : E.Om) (v : M.Om) : ℝ :=
  (M.p (M.X v) / E.pHat n w (M.X v) *
      (M.f (M.X v) true (M.U v) / radius M v ^ M.alpha) -
    (1 - M.p (M.X v)) / (1 - E.pHat n w (M.X v)) *
      (M.f (M.X v) false (M.U v) / radius M v ^ M.alpha)) *
    (radius M v ^ (M.alpha - E.alphaHat n w) - 1)

/-- For the [extreme-value model](hyp:M) and [population observation](hyp:v), [the normalized
regression contrast](goal) is the treated-minus-control conditional regression contrast divided
by the tail radius raised to the model's tail exponent. -/
-- @node: normalizedRegressionContrast
noncomputable def normalizedRegressionContrast (M : ExtremeModel q d) (v : M.Om) : ℝ :=
  (M.f (M.X v) true (M.U v) - M.f (M.X v) false (M.U v)) / radius M v ^ M.alpha

/-- For the [experiment](hyp:E), [sample size](hyp:n), [tail threshold](hyp:t), [regression
function](hyp:reg), and [training outcome](hyp:w), [the DR mean decomposition](goal) says that
the conditional DR-score bias equals the nuisance-product bias integral, the exponent-error
integral, and the normalized-regression target discrepancy. -/
-- @node: DrMeanDecomposition
def DrMeanDecomposition (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om) : Prop :=
  (∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M =
    (∫ v, drBiasIntegrand E n reg w v ∂tailLaw M t) +
      (∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t) +
      ((∫ v, normalizedRegressionContrast M v ∂tailLaw M t) - etaTarget M)

/-- If the measure is a probability measure, [the overlap constant is positive](hyp:hc),
[both fitted treatment probabilities are at least that constant almost everywhere](hyp:hph),
[the propensity error is bounded by `rp`](hyp:hp), and [both regression errors are bounded by
`rg`](hyp:hm), then [the absolute bias integral is at most `(2 / c) * rp * rg`](goal). -/
-- @node: dr_conditional_bias_integral_bound
lemma dr_conditional_bias_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p ph m1 m0 g1 g0 : Ω → ℝ)
    {c rp rg : ℝ} (hc : 0 < c)
    (hph : ∀ᵐ z ∂μ, c ≤ ph z ∧ c ≤ 1 - ph z)
    (hp : ∀ᵐ z ∂μ, |p z - ph z| ≤ rp)
    (hm : ∀ᵐ z ∂μ, |m1 z - g1 z| ≤ rg ∧ |m0 z - g0 z| ≤ rg) :
    |∫ z, (p z - ph z) * ((m1 z - g1 z) / ph z +
      (m0 z - g0 z) / (1 - ph z)) ∂μ| ≤ (2 / c) * rp * rg := by
  have hbound : ∀ᵐ z ∂μ,
      ‖(p z - ph z) * ((m1 z - g1 z) / ph z +
        (m0 z - g0 z) / (1 - ph z))‖ ≤ (2 / c) * rp * rg := by
    filter_upwards [hph, hp, hm] with z hz hpz hmz
    rw [Real.norm_eq_abs, ← dr_conditional_bias_identity
      (hc.trans_le hz.1).ne' (hc.trans_le hz.2).ne']
    exact dr_conditional_bias_bound hc hz.1 hz.2 hpz hmz.1 hmz.2
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using norm_integral_le_of_norm_le_const hbound

/-- Given [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a propensity-rate
function nonincreasing in sample size](hyp:hRp), and [nuisance fits whose propensity error and both treatment-specific regression errors obey their respective rates](hyp:hNuisance),
[the DR bias integrand is eventually bounded on the tail population](goal) by the product of the
propensity and regression rates, with the regression rate evaluated at the training count. -/
-- @node: dr_nuisance_bias_tail_bound
lemma dr_nuisance_bias_tail_bound (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n)
    {c t eps : ℝ} (hOverlap : EstimatedOverlap E c)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w) :
    ∀ᵐ v ∂tailLaw M t, |drBiasIntegrand E n reg w v| ≤
      (2 / c) * Rp (n / 2) eps * Rg (trainCount E n t w) eps := by
  have hp : ∀ᵐ v ∂tailLaw M t,
      |M.p (M.X v) - E.pHat n w (M.X v)| ≤ Rp (n / 2) eps := by
    have h := ae_of_ae_map M.measurable_X.aemeasurable hNuisance.2.1
    have htail : ∀ᵐ v ∂tailLaw M t,
        |M.p (M.X v) - E.pHat n w (M.X v)| ≤ Rp n eps :=
      cond_absolutelyContinuous.ae_le h
    exact htail.mono fun v hv =>
      hv.trans (hRp (Nat.div_le_self n 2))
  have hm (a : Bool) : ∀ᵐ v ∂tailLaw M t,
      |reg (M.X v, a, direction M v) - E.gHat n w (M.X v) a (direction M v)| ≤
        Rg (trainCount E n t w) eps := by
    exact ae_of_ae_map (M.measurable_X.prodMk (measurable_direction M)).aemeasurable
      (hNuisance.2.2 a)
  filter_upwards [hp, hm true, hm false] with v hpv h1 h0
  have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
  have hph' : c ≤ 1 - E.pHat n w (M.X v) := by linarith [hph.2]
  rw [drBiasIntegrand, ← dr_conditional_bias_identity
    (hOverlap.1.trans_le hph.1).ne' (hOverlap.1.trans_le hph').ne']
  exact dr_conditional_bias_bound hOverlap.1 hph.1 hph' hpv h1 h0

/-- If [the noise has regularly varying tails](hyp:hRV), [the sample size is even](hyp:hn),
[estimated overlap holds](hyp:hOverlap), [the propensity rate is antitone](hyp:hRp), and
[the nuisance estimators satisfy their error bounds](hyp:hNuisance), then [the absolute DR
bias integral is bounded](goal) by the corresponding propensity-rate and regression-rate product. -/
-- @node: dr_nuisance_bias_integral_bound
lemma dr_nuisance_bias_integral_bound (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) {n : ℕ} (hn : EvenSampleSize n)
    {c t eps : ℝ} (hOverlap : EstimatedOverlap E c)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w) :
    |∫ v, drBiasIntegrand E n reg w v ∂tailLaw M t| ≤
      (2 / c) * Rp (n / 2) eps * Rg (trainCount E n t w) eps := by
  let := tailLaw_probability M hRV t
  have hnorm : ∀ᵐ v ∂tailLaw M t, ‖drBiasIntegrand E n reg w v‖ ≤
      (2 / c) * Rp (n / 2) eps * Rg (trainCount E n t w) eps := by
    simpa only [Real.norm_eq_abs] using
      dr_nuisance_bias_tail_bound E hn hOverlap Rp Rg Ralpha hRp reg w hNuisance
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using norm_integral_le_of_norm_le_const hnorm

/-- If [the noise has regularly varying tails](hyp:hRV), [the sample size is even](hyp:hn),
[estimated overlap holds](hyp:hOverlap), [the propensity rate is antitone](hyp:hRp),
[the fitted regression is measurable](hyp:hreg), and [the nuisance estimators satisfy their
error bounds](hyp:hNuisance), then [the DR bias integrand is integrable on the tail law](goal). -/
-- @node: dr_nuisance_bias_integrable
lemma dr_nuisance_bias_integrable (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) {n : ℕ} (hn : EvenSampleSize n)
    {c t eps : ℝ} (hOverlap : EstimatedOverlap E c)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (hreg : Measurable reg)
    (w : E.Om) (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w) :
    Integrable (drBiasIntegrand E n reg w) (tailLaw M t) := by
  let := tailLaw_probability M hRV t
  have hm : Measurable (drBiasIntegrand E n reg w) := by
    unfold drBiasIntegrand
    first | fun_prop | skip
    have hp : Measurable (fun v => E.pHat n w (M.X v)) :=
      (E.pHat_training n).comp (measurable_const.prodMk M.measurable_X)
    have hr (a : Bool) : Measurable (fun v => reg (M.X v, a, direction M v)) :=
      hreg.comp (M.measurable_X.prodMk (measurable_const.prodMk (measurable_direction M)))
    have hg (a : Bool) : Measurable (fun v => E.gHat n w (M.X v) a (direction M v)) :=
      (E.gHat_training n).comp (measurable_const.prodMk
        (M.measurable_X.prodMk (measurable_const.prodMk (measurable_direction M))))
    exact ((M.measurable_p.comp M.measurable_X).sub hp).mul
      (((hr true).sub (hg true)).div hp |>.add
        (((hr false).sub (hg false)).div (measurable_const.sub hp)))
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((2 / c) * Rp (n / 2) eps * Rg (trainCount E n t w) eps)
  simpa only [Real.norm_eq_abs] using
    dr_nuisance_bias_tail_bound E hn hOverlap Rp Rg Ralpha hRp reg w hNuisance

/-- For the [experiment](hyp:E), [sample size](hyp:n), [tail threshold](hyp:t), [error level](hyp:eps),
[overlap constant](hyp:c), [regression bound](hyp:Cgb), [exponent constant](hyp:K), and [three
nuisance-rate functions](hyp:Rp), [the DR mean-bound provider](goal) requires every nuisance fit
with the stated mean decomposition to have conditional score bias no larger than the DR remainder. -/
-- @node: DrMeanBoundProvider
def DrMeanBoundProvider (E : NeteExperiment M) (n : ℕ) (t eps c Cgb K : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  ∀ reg w, NuisanceAt E n t eps Rp Rg Ralpha reg w →
    DrMeanDecomposition E n t reg w →
    |(∫ z, score E .dr n w z ∂obsTailLaw M t) - etaTarget M| ≤
      etaRemainder E .dr c Cgb K Rp Rg Ralpha n t eps w

/-- If [the noise has regularly varying tails](hyp:hRV), [covariates are bounded](hyp:hX),
[the model is asymptotically homogeneous](hyp:hHom), [the conditional mean version is available](hyp:hMean),
[the angular regression is bounded](hyp:hG), [the threshold is positive](hyp:ht), and [the tail
error envelope is bounded above](hyp:hb), then [the normalized regression contrast is integrable](goal)
under the tail law. -/
-- @node: normalizedRegressionContrast_integrable
lemma normalizedRegressionContrast_integrable (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) :
    Integrable (normalizedRegressionContrast M) (tailLaw M t) := by
  let := tailLaw_probability M hRV t
  apply Integrable.mono' (integrable_const (2 * (C + eBar M t)))
  · apply Measurable.aestronglyMeasurable
    have hm (a : Bool) : Measurable (fun v => M.f (M.X v) a (M.U v)) := by
      exact hMean.1.comp (M.measurable_X.prodMk (measurable_const.prodMk M.measurable_U))
    exact ((hm true).sub (hm false)).div (measurable_radius M |>.pow_const M.alpha)
  · have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
      cond_absolutelyContinuous.ae_le hX.2
    filter_upwards [hx, ae_cond_mem (μ := M.mu)
      (measurableSet_lt measurable_const (measurable_radius M))] with v hv hw
    rw [Real.norm_eq_abs, normalizedRegressionContrast, sub_div]
    exact (abs_sub _ _).trans (by
      have h := normalized_regression_tail_bound M hHom hG ht hb v hv hw
      linarith [h true, h false])

/-- If [the noise has regularly varying tails](hyp:hRV), [covariates are bounded](hyp:hX),
[the model is asymptotically homogeneous](hyp:hHom), and [the threshold is positive](hyp:ht), then
[the angular treated-minus-control contrast is integrable](goal) under the tail law. -/
-- @node: angular_contrast_tail_integrable
lemma angular_contrast_tail_integrable (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) {t : ℝ} (ht : 0 < t) :
    Integrable (fun v => M.g (M.X v) true (direction M v) -
      M.g (M.X v) false (direction M v)) (tailLaw M t) := by
  obtain ⟨H, hH⟩ := angular_contrast_bounded_extension M hHom
  let := tailLaw_probability M hRV t
  have hInt : Integrable (fun v => H (M.X v, direction M v)) (tailLaw M t) := by
    apply Integrable.mono' (integrable_const ‖H‖)
    · apply Measurable.aestronglyMeasurable
      have hm := H.continuous.measurable
      have hx := M.measurable_X
      fun_prop
    · exact Eventually.of_forall fun v => H.norm_coe_le_norm _
  apply hInt.congr
  have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  filter_upwards [hx, ae_cond_mem (μ := M.mu)
    (measurableSet_lt measurable_const (measurable_radius M))] with v hv hw
  exact hH _ hv _ (direction_mem_positiveSphere M (ht.trans hw))

/-- If [the noise has regularly varying tails](hyp:hRV), [covariates are bounded](hyp:hX),
[the model is asymptotically homogeneous](hyp:hHom), [the conditional mean version is available](hyp:hMean),
[the angular regression is bounded](hyp:hG), [the threshold is positive](hyp:ht), [the tail error
envelope is bounded above](hyp:hb), and [the angular approximation has its stated error bound](hyp:hAngular),
then [the normalized-contrast target error has the displayed bound](goal). -/
-- @node: normalized_contrast_target_bound
lemma normalized_contrast_target_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (hAngular : |angularFactor M t - etaTarget M| ≤ 2 * M.L * angularW1 M t) :
    |(∫ v, normalizedRegressionContrast M v ∂tailLaw M t) - etaTarget M| ≤
      2 * eBar M t + 2 * M.L * angularW1 M t := by
  let := tailLaw_probability M hRV t
  have hbound : ∀ᵐ v ∂tailLaw M t,
      ‖normalizedRegressionContrast M v -
        (M.g (M.X v) true (direction M v) - M.g (M.X v) false (direction M v))‖ ≤
      2 * eBar M t := by
    simpa only [Real.norm_eq_abs, normalizedRegressionContrast] using
      homogeneity_contrast_tail_ae M hX hHom ht hb
  have herr : |(∫ v, normalizedRegressionContrast M v ∂tailLaw M t) -
      angularFactor M t| ≤ 2 * eBar M t := by
    rw [angularFactor, ← integral_sub
      (normalizedRegressionContrast_integrable M hRV hX hHom hMean hG ht hb)
      (angular_contrast_tail_integrable M hRV hX hHom ht)]
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
      mul_one] using norm_integral_le_of_norm_le_const hbound
  exact (abs_sub_le _ (angularFactor M t) _).trans (add_le_add herr hAngular)

/-- If [the noise has regularly varying tails](hyp:hRV), [the sample size is even](hyp:hn),
[estimated overlap holds](hyp:hOverlap), [the propensity rate is antitone](hyp:hRp), [the exponent
rate is nonnegative](hyp:ha), [it is bounded by `a0`](hyp:haa0), [the exponent-error integral has
the stated bound](hyp:hExponent), and [the normalized contrast has the stated target bound](hyp:hTarget),
then [the DR mean-bound provider holds](goal). -/
-- @node: dr_mean_bound_provider
lemma dr_mean_bound_provider (E : NeteExperiment M) (hRV : NoiseRegularlyVarying M)
    {n : ℕ} (hn : EvenSampleSize n) {t eps c Cgb K a0 : ℝ}
    (hOverlap : EstimatedOverlap E c) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps)) (ha : 0 ≤ Ralpha n eps)
    (haa0 : Ralpha n eps ≤ a0)
    (hExponent : ∀ w a, 0 ≤ a → a ≤ a0 → |M.alpha - E.alphaHat n w| ≤ a →
      |∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t| ≤
        (2 * (Cgb + eBar M t) / c) * (t ^ a - 1 + K * a * t ^ a))
    (hTarget : |(∫ v, normalizedRegressionContrast M v ∂tailLaw M t) - etaTarget M| ≤
      2 * eBar M t + 2 * M.L * angularW1 M t) :
    DrMeanBoundProvider E n t eps c Cgb K Rp Rg Ralpha := by
  intro reg w hNuisance hIdentity
  have hb := dr_nuisance_bias_integral_bound E hRV hn hOverlap Rp Rg Ralpha hRp reg w
    hNuisance
  have he := hExponent w (Ralpha n eps) ha haa0
    (by simpa only [abs_sub_comm] using hNuisance.1)
  rw [hIdentity]
  calc
    _ ≤ |∫ v, drBiasIntegrand E n reg w v ∂tailLaw M t| +
        |∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t| +
        |(∫ v, normalizedRegressionContrast M v ∂tailLaw M t) - etaTarget M| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (2 / c) * Rp (n / 2) eps * Rg (trainCount E n t w) eps +
        (2 * (Cgb + eBar M t) / c) *
          (t ^ Ralpha n eps - 1 + K * Ralpha n eps * t ^ Ralpha n eps) +
        (2 * eBar M t + 2 * M.L * angularW1 M t) :=
      add_le_add (add_le_add hb he) hTarget
    _ = _ := by unfold etaRemainder; ring

end Papers.TbsExtremeEffects
