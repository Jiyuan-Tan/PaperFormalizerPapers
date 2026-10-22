module
public import Papers.TbsExtremeEffects.Helpers.DRMean

/-! Population IPW bias and fitted-exponent mean decomposition. -/

@[expose] public section
set_option linter.unusedTactic false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- If [the fitted propensity is nonzero](hyp:hph) and [its complement is nonzero](hyp:hph'), the [IPW conditional bias](goal) equals the propensity error times the sum of the two inverse-propensity weighted conditional means.
@node: ipw_conditional_bias_identity -/
lemma ipw_conditional_bias_identity {p ph m1 m0 : ℝ}
    (hph : ph ≠ 0) (hph' : 1 - ph ≠ 0) :
    p / ph * m1 - (1 - p) / (1 - ph) * m0 - (m1 - m0) =
      (p - ph) * (m1 / ph + m0 / (1 - ph)) := by
  simpa using dr_conditional_bias_identity (g1 := 0) (g0 := 0) hph hph'

/-- If [the overlap constant is positive](hyp:hc), [the fitted propensity and its complement are at least that constant](hyp:hph,hph'), [the propensity error is bounded by `rp`](hyp:hp), and [both conditional means are bounded by `G`](hyp:h1,h0), then [the absolute IPW conditional bias is at most `(2G/c) rp`](goal).
@node: ipw_conditional_bias_bound -/
lemma ipw_conditional_bias_bound {p ph m1 m0 c rp G : ℝ}
    (hc : 0 < c) (hph : c ≤ ph) (hph' : c ≤ 1 - ph)
    (hp : |p - ph| ≤ rp) (h1 : |m1| ≤ G) (h0 : |m0| ≤ G) :
    |p / ph * m1 - (1 - p) / (1 - ph) * m0 - (m1 - m0)| ≤
      (2 * G / c) * rp := by
  have h := dr_conditional_bias_bound (g1 := 0) (g0 := 0) hc hph hph' hp
    (by simpa using h1) (by simpa using h0)
  calc
    _ ≤ (2 / c) * rp * G := by simpa using h
    _ = _ := by ring

/-- For [a probability measure](hyp:μ), if [the overlap constant is positive](hyp:hc), [the fitted propensity has the stated overlap almost everywhere](hyp:hph), [its error is at most `rp` almost everywhere](hyp:hp), and [both conditional means are bounded by `G` almost everywhere](hyp:hm), then [the absolute integrated IPW bias is at most `(2G/c) rp`](goal).
@node: ipw_conditional_bias_integral_bound -/
lemma ipw_conditional_bias_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p ph m1 m0 : Ω → ℝ)
    {c rp G : ℝ} (hc : 0 < c)
    (hph : ∀ᵐ z ∂μ, c ≤ ph z ∧ c ≤ 1 - ph z)
    (hp : ∀ᵐ z ∂μ, |p z - ph z| ≤ rp)
    (hm : ∀ᵐ z ∂μ, |m1 z| ≤ G ∧ |m0 z| ≤ G) :
    |∫ z, p z / ph z * m1 z - (1 - p z) / (1 - ph z) * m0 z -
      (m1 z - m0 z) ∂μ| ≤ (2 * G / c) * rp := by
  have hbound : ∀ᵐ z ∂μ,
      ‖p z / ph z * m1 z - (1 - p z) / (1 - ph z) * m0 z -
        (m1 z - m0 z)‖ ≤ (2 * G / c) * rp := by
    filter_upwards [hph, hp, hm] with z hz hpz hmz
    rw [Real.norm_eq_abs]
    exact ipw_conditional_bias_bound hc hz.1 hz.2 hpz hmz.1 hmz.2
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using
    norm_integral_le_of_norm_le_const hbound

/-- [The extreme-value model](hyp:M), [experiment](hyp:E), [sample size](hyp:n), [training realization](hyp:w), and [population observation](hyp:v) define the [population IPW propensity-bias integrand](goal) after conditioning on treatment and outcome.
@node: ipwBiasIntegrand -/
noncomputable def ipwBiasIntegrand (E : NeteExperiment M) (n : ℕ)
    (w : E.Om) (v : M.Om) : ℝ :=
  (M.p (M.X v) - E.pHat n w (M.X v)) *
    ((M.f (M.X v) true (M.U v) / radius M v ^ M.alpha) / E.pHat n w (M.X v) +
      (M.f (M.X v) false (M.U v) / radius M v ^ M.alpha) /
        (1 - E.pHat n w (M.X v)))

/-- [The extreme-value model](hyp:M), [experiment](hyp:E), [sample size](hyp:n), [tail threshold](hyp:t), and [training realization](hyp:w) define the [IPW mean decomposition condition](goal): the score-mean error is the sum of propensity-bias, exponent-error, and target-approximation contributions.
@node: IpwMeanDecomposition -/
def IpwMeanDecomposition (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) : Prop :=
  (∫ z, score E .ipw n w z ∂obsTailLaw M t) - etaTarget M =
    (∫ v, ipwBiasIntegrand E n w v ∂tailLaw M t) +
      (∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t) +
      ((∫ v, normalizedRegressionContrast M v ∂tailLaw M t) - etaTarget M)

/-- Given [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression bound](hyp:hG), [a positive tail threshold](hyp:ht), [bounded tail error](hyp:hb), [a nonincreasing propensity-error rate](hyp:hRp), and [the nuisance event](hyp:hNuisance), [the IPW propensity-bias integrand is almost surely bounded on the tail](goal) by its displayed rate.
@node: ipw_nuisance_bias_tail_bound -/
lemma ipw_nuisance_bias_tail_bound (E : NeteExperiment M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t eps : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w) :
    ∀ᵐ v ∂tailLaw M t, |ipwBiasIntegrand E n w v| ≤
      (2 * (C + eBar M t) / c) * Rp (n / 2) eps := by
  have hp : ∀ᵐ v ∂tailLaw M t,
      |M.p (M.X v) - E.pHat n w (M.X v)| ≤ Rp (n / 2) eps := by
    have h := ae_of_ae_map M.measurable_X.aemeasurable hNuisance.2.1
    have htail : ∀ᵐ v ∂tailLaw M t,
        |M.p (M.X v) - E.pHat n w (M.X v)| ≤ Rp n eps :=
      cond_absolutelyContinuous.ae_le h
    exact htail.mono fun v hv => hv.trans (hRp (Nat.div_le_self n 2))
  have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  filter_upwards [hp, hx, ae_cond_mem (μ := M.mu)
    (measurableSet_lt measurable_const (measurable_radius M))] with v hpv hxv htv
  have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
  have hph' : c ≤ 1 - E.pHat n w (M.X v) := by linarith [hph.2]
  have hf := normalized_regression_tail_bound M hHom hG ht hb v hxv htv
  rw [ipwBiasIntegrand, ← ipw_conditional_bias_identity
    (hOverlap.1.trans_le hph.1).ne' (hOverlap.1.trans_le hph').ne']
  exact ipw_conditional_bias_bound hOverlap.1 hph.1 hph' hpv (hf true) (hf false)

/-- Under [regularly varying noise](hyp:hRV), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression bound](hyp:hG), [a positive threshold](hyp:ht), [bounded tail error](hyp:hb), [a nonincreasing propensity-error rate](hyp:hRp), and [the nuisance event](hyp:hNuisance), [the integrated IPW propensity bias is bounded by the displayed rate](goal).
@node: ipw_nuisance_bias_integral_bound -/
lemma ipw_nuisance_bias_integral_bound (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) {n : ℕ} (hn : EvenSampleSize n)
    {c C t eps : ℝ} (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w) :
    |∫ v, ipwBiasIntegrand E n w v ∂tailLaw M t| ≤
      (2 * (C + eBar M t) / c) * Rp (n / 2) eps := by
  let := tailLaw_probability M hRV t
  have hbound := ipw_nuisance_bias_tail_bound E hX hHom hn hOverlap hG ht hb
    Rp Rg Ralpha hRp reg w hNuisance
  have hnorm : ∀ᵐ v ∂tailLaw M t, ‖ipwBiasIntegrand E n w v‖ ≤
      (2 * (C + eBar M t) / c) * Rp (n / 2) eps := by
    simpa only [Real.norm_eq_abs] using hbound
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using norm_integral_le_of_norm_le_const hnorm

/-- Under [regularly varying noise](hyp:hRV), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional-mean version](hyp:hMean), [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression bound](hyp:hG), [a positive threshold](hyp:ht), [bounded tail error](hyp:hb), [a nonincreasing propensity-error rate](hyp:hRp), and [the nuisance event](hyp:hNuisance), [the IPW propensity-bias integrand is tail-integrable](goal).
@node: ipw_nuisance_bias_integrable -/
lemma ipw_nuisance_bias_integrable (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t eps : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w) :
    Integrable (ipwBiasIntegrand E n w) (tailLaw M t) := by
  let := tailLaw_probability M hRV t
  apply Integrable.mono' (integrable_const ((2 * (C + eBar M t) / c) * Rp (n / 2) eps))
  · have hp : Measurable (fun v => E.pHat n w (M.X v)) :=
      (E.pHat_training n).comp (measurable_const.prodMk M.measurable_X)
    have hf (a : Bool) : Measurable (fun v => M.f (M.X v) a (M.U v)) :=
      hMean.1.comp (M.measurable_X.prodMk (measurable_const.prodMk M.measurable_U))
    have hm : Measurable (ipwBiasIntegrand E n w) := by
      unfold ipwBiasIntegrand
      exact ((M.measurable_p.comp M.measurable_X).sub hp).mul
        (((hf true).div ((measurable_radius M).pow_const M.alpha)).div hp |>.add
          (((hf false).div ((measurable_radius M).pow_const M.alpha)).div
            (measurable_const.sub hp)))
    exact hm.aestronglyMeasurable
  · simpa only [Real.norm_eq_abs] using
      ipw_nuisance_bias_tail_bound E hX hHom hn hOverlap hG ht hb
        Rp Rg Ralpha hRp reg w hNuisance

/-- [The extreme-value model](hyp:M), [experiment](hyp:E), [sample size](hyp:n), [tail threshold](hyp:t), [accuracy level](hyp:eps), [overlap constant](hyp:c), [regression bound](hyp:Cgb), [exponent constant](hyp:K), and [the three nuisance-rate functions](hyp:Rp,Rg,Ralpha) define the [IPW mean-bound provider property](goal): every nuisance realization satisfying the decomposition has the stated remainder bound.
@node: IpwMeanBoundProvider -/
def IpwMeanBoundProvider (E : NeteExperiment M) (n : ℕ) (t eps c Cgb K : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  ∀ reg w, NuisanceAt E n t eps Rp Rg Ralpha reg w →
    IpwMeanDecomposition E n t w →
    |(∫ z, score E .ipw n w z ∂obsTailLaw M t) - etaTarget M| ≤
      etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t eps w

/-- Given [regular variation](hyp:hRV), [bounded covariates](hyp:hX), [homogeneity](hyp:hHom), [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression bound](hyp:hG), [a positive threshold](hyp:ht), [bounded tail error](hyp:hb), [a nonincreasing propensity rate](hyp:hRp), [a nonnegative exponent rate](hyp:ha), [its upper bound](hyp:haa0), [the exponent-integral bound](hyp:hExponent), and [the target approximation bound](hyp:hTarget), [the experiment provides the stated IPW mean bound](goal).
@node: ipw_mean_bound_provider -/
lemma ipw_mean_bound_provider (E : NeteExperiment M) (hRV : NoiseRegularlyVarying M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    {n : ℕ} (hn : EvenSampleSize n) {t eps c Cgb K a0 : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M Cgb) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps)) (ha : 0 ≤ Ralpha n eps)
    (haa0 : Ralpha n eps ≤ a0)
    (hExponent : ∀ w a, 0 ≤ a → a ≤ a0 → |M.alpha - E.alphaHat n w| ≤ a →
      |∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t| ≤
        (2 * (Cgb + eBar M t) / c) * (t ^ a - 1 + K * a * t ^ a))
    (hTarget : |(∫ v, normalizedRegressionContrast M v ∂tailLaw M t) - etaTarget M| ≤
      2 * eBar M t + 2 * M.L * angularW1 M t) :
    IpwMeanBoundProvider E n t eps c Cgb K Rp Rg Ralpha := by
  intro reg w hNuisance hIdentity
  have hBias := ipw_nuisance_bias_integral_bound E hRV hX hHom hn hOverlap hG ht hb
    Rp Rg Ralpha hRp reg w hNuisance
  have hExp := hExponent w (Ralpha n eps) ha haa0
    (by simpa only [abs_sub_comm] using hNuisance.1)
  rw [hIdentity]
  calc
    _ ≤ |∫ v, ipwBiasIntegrand E n w v ∂tailLaw M t| +
        |∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t| +
        |(∫ v, normalizedRegressionContrast M v ∂tailLaw M t) - etaTarget M| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (2 * (Cgb + eBar M t) / c) * Rp (n / 2) eps +
        (2 * (Cgb + eBar M t) / c) *
          (t ^ Ralpha n eps - 1 + K * Ralpha n eps * t ^ Ralpha n eps) +
        (2 * eBar M t + 2 * M.L * angularW1 M t) :=
      add_le_add (add_le_add hBias hExp) hTarget
    _ = _ := by unfold etaRemainder; ring

/-- [The extreme-value model](hyp:M), [experiment](hyp:E), [sample size](hyp:n), [training realization](hyp:w), and [population observation](hyp:v) define the [fitted-IPW population integrand](goal) after conditioning on treatment and outcome.
@node: ipwFittedMeanIntegrand -/
noncomputable def ipwFittedMeanIntegrand (E : NeteExperiment M) (n : ℕ)
    (w : E.Om) (v : M.Om) : ℝ :=
  M.p (M.X v) / E.pHat n w (M.X v) *
    (M.f (M.X v) true (M.U v) / radius M v ^ E.alphaHat n w) -
  (1 - M.p (M.X v)) / (1 - E.pHat n w (M.X v)) *
    (M.f (M.X v) false (M.U v) / radius M v ^ E.alphaHat n w)

/-- [The extreme-value model](hyp:M), [experiment](hyp:E), [sample size](hyp:n), [tail threshold](hyp:t), and [training realization](hyp:w) define the [conditional IPW score-mean identity](goal), equating the observed score mean with the fitted population integrand mean.
@node: IpwConditionalScoreMean -/
def IpwConditionalScoreMean (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) : Prop :=
  (∫ z, score E .ipw n w z ∂obsTailLaw M t) =
    ∫ v, ipwFittedMeanIntegrand E n w v ∂tailLaw M t

/-- If [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap), and [the observation has positive radius](hyp:hr), then [the fitted-IPW integrand decomposes](goal) into propensity bias, exponent error, and normalized regression contrast.
@node: ipw_fitted_mean_integrand_decomposition -/
lemma ipw_fitted_mean_integrand_decomposition (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n) {c : ℝ} (hOverlap : EstimatedOverlap E c)
    (w : E.Om) (v : M.Om) (hr : 0 < radius M v) :
    ipwFittedMeanIntegrand E n w v = ipwBiasIntegrand E n w v +
      exponentMeanIntegrand E n w v + normalizedRegressionContrast M v := by
  have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
  have hp0 := (hOverlap.1.trans_le hph.1).ne'
  have hp1 : 1 - E.pHat n w (M.X v) ≠ 0 := by
    have : c ≤ 1 - E.pHat n w (M.X v) := by linarith [hph.2]
    exact (hOverlap.1.trans_le this).ne'
  have hBias := ipw_conditional_bias_identity
    (p := M.p (M.X v))
    (m1 := M.f (M.X v) true (M.U v) / radius M v ^ M.alpha)
    (m0 := M.f (M.X v) false (M.U v) / radius M v ^ M.alpha) hp0 hp1
  unfold ipwFittedMeanIntegrand ipwBiasIntegrand exponentMeanIntegrand
    normalizedRegressionContrast
  rw [Real.rpow_sub hr]
  rw [← hBias, sub_div]
  field_simp [Real.rpow_pos_of_pos hr M.alpha |>.ne',
    Real.rpow_pos_of_pos hr (E.alphaHat n w) |>.ne']
  ring

/-- If [the sample size is even](hyp:hn), [estimated overlap holds](hyp:hOverlap), and [the tail threshold is positive](hyp:ht), then [the fitted-IPW integrand has the stated decomposition almost everywhere on the tail](goal).
@node: ipw_fitted_mean_integrand_decomposition_ae -/
lemma ipw_fitted_mean_integrand_decomposition_ae (E : NeteExperiment M)
    {n : ℕ} (hn : EvenSampleSize n) {c t : ℝ} (hOverlap : EstimatedOverlap E c)
    (ht : 0 < t) (w : E.Om) :
    ipwFittedMeanIntegrand E n w =ᵐ[tailLaw M t] fun v => ipwBiasIntegrand E n w v +
      exponentMeanIntegrand E n w v + normalizedRegressionContrast M v := by
  filter_upwards [ae_cond_mem (μ := M.mu)
    (measurableSet_lt measurable_const (measurable_radius M))] with v hv
  exact ipw_fitted_mean_integrand_decomposition E hn hOverlap w v (ht.trans hv)

/-- Given [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional-mean version](hyp:hMean), [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression bound](hyp:hG), [a tail threshold at least one](hyp:ht), [bounded tail error](hyp:hb), [an exponent-estimation error bound](hyp:hErr), and [an integrable radial increment](hyp:hRad), [the exponent-error integrand is tail-integrable](goal).
@node: exponentMeanIntegrand_integrable -/
lemma exponentMeanIntegrand_integrable (E : NeteExperiment M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) {n : ℕ} (hn : EvenSampleSize n)
    {c C t a : ℝ} (hOverlap : EstimatedOverlap E c) (hG : GBound M C)
    (ht : 1 ≤ t) (hb : BddAbove (M.e '' Set.Ici t))
    (w : E.Om) (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t)) :
    Integrable (exponentMeanIntegrand E n w) (tailLaw M t) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hconst : 0 ≤ 2 * (C + eBar M t) / c := by
    exact div_nonneg (mul_nonneg (by norm_num)
      (add_nonneg hG.1 (eBar_nonneg M hHom htpos hb))) hOverlap.1.le
  apply Integrable.mono' (hRad.const_mul (2 * (C + eBar M t) / c))
  · have hm : Measurable (exponentMeanIntegrand E n w) := by
      unfold exponentMeanIntegrand
      first | fun_prop | skip
      have hp : Measurable (fun v => E.pHat n w (M.X v)) :=
        (E.pHat_training n).comp (measurable_const.prodMk M.measurable_X)
      have hf (a : Bool) : Measurable (fun v => M.f (M.X v) a (M.U v)) :=
        hMean.1.comp (M.measurable_X.prodMk (measurable_const.prodMk M.measurable_U))
      exact (((M.measurable_p.comp M.measurable_X).div hp |>.mul
        ((hf true).div ((measurable_radius M).pow_const M.alpha))).sub
        ((measurable_const.sub (M.measurable_p.comp M.measurable_X)).div
          (measurable_const.sub hp) |>.mul
            ((hf false).div ((measurable_radius M).pow_const M.alpha)))).mul
        (((measurable_radius M).pow_const _).sub measurable_const)
    exact hm.aestronglyMeasurable
  · have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
      cond_absolutelyContinuous.ae_le hX.2
    filter_upwards [hx, ae_cond_mem (μ := M.mu)
      (measurableSet_lt measurable_const (measurable_radius M))] with v hv hw
    have hr : 1 ≤ radius M v := ht.trans hw.le
    have hp := M.p_range (M.X v)
    have hph := hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)
    have hf := normalized_regression_tail_bound M hHom hG htpos hb v hv hw
    rw [Real.norm_eq_abs, exponentMeanIntegrand, abs_mul]
    exact mul_le_mul
      (propensity_weighted_regression_bound hOverlap.1 hp.1 hp.2 hph.1
        (by linarith [hph.2]) (hf true) (hf false))
      (abs_rpow_sub_one_le_increment hr hErr) (abs_nonneg _) hconst

/-- Given [regularly varying noise](hyp:hRV), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional-mean version](hyp:hMean), [an even sample size](hyp:hn), [estimated overlap](hyp:hOverlap), [a regression bound](hyp:hG), [a threshold at least one](hyp:ht), [bounded tail error](hyp:hb), [a nonincreasing propensity rate](hyp:hRp), [the nuisance event](hyp:hNuisance), [an exponent-error bound](hyp:hErr), [an integrable radial increment](hyp:hRad), and [the conditional score identity](hyp:hIdentity), [the IPW mean decomposition holds](goal).
@node: ipw_mean_decomposition_of_conditional_score_mean -/
lemma ipw_mean_decomposition_of_conditional_score_mean (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {n : ℕ} (hn : EvenSampleSize n) {c C t eps a : ℝ}
    (hOverlap : EstimatedOverlap E c) (hG : GBound M C) (ht : 1 ≤ t)
    (hb : BddAbove (M.e '' Set.Ici t)) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (hRp : Antitone (fun k => Rp k eps))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hNuisance : NuisanceAt E n t eps Rp Rg Ralpha reg w)
    (hErr : |M.alpha - E.alphaHat n w| ≤ a)
    (hRad : Integrable (fun v => radius M v ^ a - 1) (tailLaw M t))
    (hIdentity : IpwConditionalScoreMean E n t w) : IpwMeanDecomposition E n t w := by
  have htpos := zero_lt_one.trans_le ht
  have hBias := ipw_nuisance_bias_integrable E hRV hX hHom hMean hn hOverlap hG
    htpos hb Rp Rg Ralpha hRp reg w hNuisance
  have hExp := exponentMeanIntegrand_integrable E hX hHom hMean hn hOverlap hG
    ht hb w hErr hRad
  have hTarget := normalizedRegressionContrast_integrable M hRV hX hHom hMean hG htpos hb
  unfold IpwMeanDecomposition
  rw [hIdentity, integral_congr_ae
    (ipw_fitted_mean_integrand_decomposition_ae E hn hOverlap htpos w),
    integral_add (show Integrable (fun v => ipwBiasIntegrand E n w v +
      exponentMeanIntegrand E n w v) (tailLaw M t) from hBias.add hExp) hTarget,
    integral_add hBias hExp]
  ring

end Papers.TbsExtremeEffects
