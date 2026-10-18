module
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileIndicatorConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRemainderRates
public import Causalean.Stat.Limit.ContinuousMapping
/-! Stochastic convergence of the quantile indicator part of the DML score.
The local density bound controls small boundary errors, and the quadratic
remote-error bound controls the remaining covariates. -/
public section
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology ENNReal

-- @node: dml_quarter_rate_tendsto_probability_zero
/-- If [an error is of smaller order in probability than the inverse fourth root of the
even sample size](hyp:he), then [the error converges to zero in probability](goal). -/
lemma dml_quarter_rate_tendsto_probability_zero {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (e : ℕ → A → ℝ)
    (he : Causalean.Stat.IsLittleOp e
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) e atTop
      (fun _ _ => 0) := by
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
  intro eps heps
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (he eps heps)
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a ha
  change eps ≤ ‖e n a - 0‖ at ha
  simp only [sub_zero] at ha
  change eps * ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ) ≤ ‖e n a‖
  have hr : ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · have hn : 1 ≤ 2 * (n + 1) := by omega
      exact_mod_cast hn
    · norm_num
  calc
    _ ≤ eps * 1 := mul_le_mul_of_nonneg_left hr heps.le
    _ = eps := mul_one eps
    _ ≤ _ := ha

-- @node: probability_zero_of_nonneg_le
/-- If [an upper bound converges to zero in probability](hyp:hg) and [the quantity of
interest lies between zero and that bound almost surely at every sample size](hyp:hbound),
then [the quantity of interest converges to zero in probability](goal). -/
lemma probability_zero_of_nonneg_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f g : ℕ → A → ℝ)
    (hg : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) g atTop
      (fun _ _ => 0))
    (hbound : ∀ n, ∀ᵐ a ∂μ, 0 ≤ f n a ∧ f n a ≤ g n a) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) f atTop
      (fun _ _ => 0) := by
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hg ⊢
  intro eps heps
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg eps heps)
    (fun _ => zero_le)
  intro n
  apply measure_mono_ae
  filter_upwards [hbound n] with a ha
  intro hf
  change eps ≤ ‖g n a - 0‖
  change eps ≤ ‖f n a - 0‖ at hf
  simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg ha.1] at hf
  simpa only [sub_zero, Real.norm_eq_abs] using
    hf.trans (ha.2.trans (le_abs_self _))

-- The probability mapping step applies to the actual local-plus-remote
-- bound, without requiring expected training-sample errors to converge.
-- @node: linear_quadratic_bound_tendsto_probability_zero
/-- If [an error converges to zero in probability](hyp:he) and [a nonnegative remainder
is almost surely bounded by C times that error plus its square divided by r squared](hyp:hbound),
then [the remainder converges to zero in probability](goal). -/
lemma linear_quadratic_bound_tendsto_probability_zero {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (R e : ℕ → A → ℝ) (C r : ℝ)
    (he : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) e atTop
      (fun _ _ => 0))
    (hbound : ∀ n, ∀ᵐ a ∂μ, 0 ≤ R n a ∧
      R n a ≤ C * e n a + e n a ^ 2 / r ^ 2) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) R atTop
      (fun _ _ => 0) := by
  have hcont : Continuous (fun t : ℝ => C * t + t ^ 2 / r ^ 2) := by fun_prop
  have h := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hcont.continuousAt he
  simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero] at h
  exact probability_zero_of_nonneg_le μ R _ h hbound

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- The rate predicate uses sqrt of the squared-error integral; the
-- conditional-law bounds use the library L2 norm. They are the same norm.
-- @node: l2Error_eq_eLpNorm
/-- If [the difference between two functions is square integrable under the covariate law](hyp:he),
then [the square root of its integrated squared error equals its real-valued L2 norm](goal). -/
lemma l2Error_eq_eLpNorm (M : LatentIVModel Ω X Z) (f g : X → ℝ)
    (he : MemLp (fun x => f x - g x) 2 (xLaw M)) :
    finiteL2Error M f g = (eLpNorm (fun x => f x - g x) 2 (xLaw M)).toReal := by
  have hpow (y : ℝ) : ‖y‖ ^ (2 : ℝ) = y ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]
  rw [he.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  simp_rw [hpow]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun x => sq_nonneg (f x - g x)) _)]
  unfold finiteL2Error
  rw [Real.sqrt_eq_rpow]
  norm_num

-- @node: treatedLaw_quantile_indicator_sq_tendsto_probability_zero
/-- Suppose [the true boundary is measurable](hyp:htruth), [the fitted boundaries are measurable](hyp:hfit),
[the neighborhood radius is positive](hyp:hr), [the density bound is nonnegative](hyp:hC),
and [all boundary errors are square integrable under the covariate law](hyp:he).
If [treated outcome probabilities of intervals within that radius of the true boundary are bounded
by C times interval length for almost every covariate](hyp:hdensity) and [the boundary L2 error
is of smaller order in probability than the inverse fourth root of the even sample size](hyp:hrate),
then [the squared difference between fitted and true threshold indicators, integrated over the
treated outcome and covariate laws, converges to zero in probability](goal). -/
lemma treatedLaw_quantile_indicator_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (truth : X → ℝ) (fit : ℕ → A → X → ℝ) (r C : ℝ)
    (htruth : Measurable truth) (hfit : ∀ n a, Measurable (fit n a))
    (hr : 0 < r) (hC : 0 ≤ C)
    (he : ∀ n a, MemLp (fun x => fit n a x - truth x) 2 (xLaw M))
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, truth x - r ≤ u → u ≤ v → v ≤ truth x + r →
      (treatedLaw M L k x (Set.Ioc u v)).toReal ≤ C * (v - u))
    (hrate : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (fit (2 * (n + 1)) a) truth)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (indicator (y ≤ fit (2 * (n + 1)) a x) - indicator (y ≤ truth x)) ^ 2
          ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  apply linear_quadratic_bound_tendsto_probability_zero μ _
    (fun n a => finiteL2Error M (fit (2 * (n + 1)) a) truth) C r
    (dml_quarter_rate_tendsto_probability_zero μ _ hrate)
  intro n
  apply Eventually.of_forall
  intro a
  refine ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _, ?_⟩
  have hb := (treatedLaw_quantile_indicator_L2_bound M L k truth
    (fit (2 * (n + 1)) a) r C htruth (hfit _ a) hr hC (he _ a) hdensity).2
  simpa only [l2Error_eq_eLpNorm M _ _ (he _ a)] using hb

-- This wrapper consumes the componentwise rate in the theorem's regime.
-- @node: nuisanceRates_quantile_indicator_sq_tendsto_probability_zero
/-- At the chosen nuisance coordinate, suppose [the true boundary is measurable](hyp:htruth),
[fitted boundaries are measurable](hyp:hfit), [the radius is positive](hyp:hr),
[C is nonnegative](hyp:hC), and [boundary errors are square integrable](hyp:he).
If [the treated outcome law assigns each interval near the true boundary probability at most
C times its length, almost everywhere in covariates](hyp:hdensity), and [all nuisance coordinates
satisfy the fourth-root little-order rates](hyp:hrates), then [the integrated squared threshold-indicator
error at even sample sizes converges to zero in probability](goal). -/
lemma nuisanceRates_quantile_indicator_sq_tendsto_probability_zero {B : Type*}
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (truth : B → X → ℝ) (fit : ℕ → A → B → X → ℝ) (c : B) (r C : ℝ)
    (htruth : Measurable (truth c)) (hfit : ∀ n a, Measurable (fit n a c))
    (hr : 0 < r) (hC : 0 ≤ C)
    (he : ∀ n a, MemLp (fun x => fit n a c x - truth c x) 2 (xLaw M))
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, truth c x - r ≤ u → u ≤ v →
      v ≤ truth c x + r → (treatedLaw M L k x (Set.Ioc u v)).toReal ≤ C * (v - u))
    (hrates : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (indicator (y ≤ fit (2 * (n + 1)) a c x) - indicator (y ≤ truth c x)) ^ 2
          ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  exact treatedLaw_quantile_indicator_sq_tendsto_probability_zero M μ L k
    (truth c) (fun n a => fit n a c) r C htruth hfit hr hC he hdensity (hrates c)

-- @node: nuisanceRates_quantile_indicator_l2_tendsto_probability_zero
/-- At the selected coordinate, assume [the true boundary is measurable](hyp:htruth),
[the fitted boundaries are measurable](hyp:hfit), [the radius is positive](hyp:hr),
[the density constant is nonnegative](hyp:hC), and [boundary errors are square integrable](hyp:he).
If [treated outcome interval probabilities near the true boundary are bounded by C times length
for almost every covariate](hyp:hdensity) and [the nuisance coordinates satisfy fourth-root
little-order rates](hyp:hrates), then [the L2 distance between fitted and true threshold indicators
under the treated outcome and covariate laws converges to zero in probability at even sample sizes](goal). -/
lemma nuisanceRates_quantile_indicator_l2_tendsto_probability_zero {B : Type*}
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (truth : B → X → ℝ) (fit : ℕ → A → B → X → ℝ) (c : B) (r C : ℝ)
    (htruth : Measurable (truth c)) (hfit : ∀ n a, Measurable (fit n a c))
    (hr : 0 < r) (hC : 0 ≤ C)
    (he : ∀ n a, MemLp (fun x => fit n a c x - truth c x) 2 (xLaw M))
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, truth c x - r ≤ u → u ≤ v →
      v ≤ truth c x + r → (treatedLaw M L k x (Set.Ioc u v)).toReal ≤ C * (v - u))
    (hrates : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ x, ∫ y,
        (indicator (y ≤ fit (2 * (n + 1)) a c x) - indicator (y ≤ truth c x)) ^ 2
          ∂treatedLaw M L k x ∂xLaw M)) atTop (fun _ _ => 0) := by
  have h := nuisanceRates_quantile_indicator_sq_tendsto_probability_zero
    M μ L k truth fit c r C htruth hfit hr hC he hdensity hrates
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt h

-- Clipped boundary estimates on the compact outcome interval supply their
-- own L2 integrability. No separate moment premise is needed here.
-- @node: clipped_nuisanceRates_quantile_indicator_l2_tendsto_probability_zero
/-- Suppose [the true boundary is measurable](hyp:htruth), [fitted boundaries are measurable](hyp:hfit),
[the true boundary lies in the model's outcome interval almost everywhere](hyp:htruthRange),
and [every fitted boundary lies in that interval](hyp:hfitRange). If [the radius is positive](hyp:hr),
[C is nonnegative](hyp:hC), [treated outcome interval probabilities near the true boundary are
bounded by C times length almost everywhere in covariates](hyp:hdensity), and [all nuisance
coordinates satisfy fourth-root little-order rates](hyp:hrates), then [the treated-law L2
threshold-indicator error converges to zero in probability at even sample sizes](goal). -/
lemma clipped_nuisanceRates_quantile_indicator_l2_tendsto_probability_zero {B : Type*}
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (truth : B → X → ℝ) (fit : ℕ → A → B → X → ℝ) (c : B) (r C : ℝ)
    (htruth : Measurable (truth c)) (hfit : ∀ n a, Measurable (fit n a c))
    (htruthRange : ∀ᵐ x ∂xLaw M, truth c x ∈ Set.Icc M.yMin M.yMax)
    (hfitRange : ∀ n a x, fit n a c x ∈ Set.Icc M.yMin M.yMax)
    (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, truth c x - r ≤ u → u ≤ v →
      v ≤ truth c x + r → (treatedLaw M L k x (Set.Ioc u v)).toReal ≤ C * (v - u))
    (hrates : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ x, ∫ y,
        (indicator (y ≤ fit (2 * (n + 1)) a c x) - indicator (y ≤ truth c x)) ^ 2
          ∂treatedLaw M L k x ∂xLaw M)) atTop (fun _ _ => 0) := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  apply nuisanceRates_quantile_indicator_l2_tendsto_probability_zero
    M μ L k truth fit c r C htruth hfit hr hC _ hdensity hrates
  intro n a
  have ht : MemLp (truth c) 2 (xLaw M) := by
    apply memLp_of_bounded htruthRange
    fun_prop
  have hf : MemLp (fit n a c) 2 (xLaw M) := by
    apply memLp_of_bounded (Eventually.of_forall (hfitRange n a))
    fun_prop
  exact hf.sub ht

end Papers.TbsPrteOptimalTransport
