module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPooledPolicyConvergence
/-! Population marginal errors in the exact-recovery argument.
Cauchy--Schwarz bounds the training-conditional marginal error by the
first-stage L2 error. The policy derivative bound gives the same rate for
policy marginals, uniformly over the finite instrument support. -/
public section
set_option linter.unusedFintypeInType false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: recovery_marginal_l2Error_bound
/-- If [the first covariate function has a finite second moment](hyp:hf) and
[the second has a finite second moment](hyp:hg), then [the absolute difference
between their population means is bounded by their population root mean
squared difference](goal). -/
lemma recovery_marginal_l2Error_bound (f g : X → ℝ)
    (hf : MemLp f 2 (xLaw M)) (hg : MemLp g 2 (xLaw M)) :
    |(∫ x, f x ∂xLaw M) - ∫ x, g x ∂xLaw M| ≤ finiteL2Error M f g := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  rw [← integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num)),
    l2Error_eq_eLpNorm M f g (hf.sub hg)]
  exact Causalean.Stat.abs_integral_le_eLpNorm_two (hf.sub hg)

-- @node: recovery_unit_interval_memLp
/-- A [measurable covariate function](hyp:hf) that [takes values between zero
and one everywhere](hyp:hr) [has a finite second moment under the population
covariate distribution](goal). -/
lemma recovery_unit_interval_memLp (f : X → ℝ) (hf : Measurable f)
    (hr : ∀ x, f x ∈ Icc (0 : ℝ) 1) : MemLp f 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  apply MemLp.of_bound hf.aestronglyMeasurable 1
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hr x).1]
    exact (hr x).2)

variable [Fintype Z]

-- @node: recovery_policy_marginal_l2Error_bound
/-- For [a measurable policy transformation preserving the unit interval](hyp:hphi)
that [has the specified derivative on that interval](hyp:hd), suppose [the
derivative bound is nonnegative](hyp:hB) and [the absolute derivative never
exceeds that bound](hyp:hder). If [the first input propensity is measurable](hyp:hf),
[the second is measurable](hyp:hg), and [each takes values between zero and
one](hyp:hfr,hgr), then [the absolute difference between their transformed
population means is at most the derivative bound times their population root
mean squared difference](goal). -/
lemma recovery_policy_marginal_l2Error_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (B : ℝ) (hB : 0 ≤ B)
    (hder : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (z : Z) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfr : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hgr : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    |(∫ x, phi z x (f x) ∂xLaw M) - ∫ x, phi z x (g x) ∂xLaw M| ≤
      B * finiteL2Error M f g := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hqf : Measurable (fun x => phi z x (f x)) := by
    first | fun_prop | exact hphi.1.comp (measurable_const.prodMk
      (measurable_id.prodMk (hf.subtype_mk (h := hfr))))
  have hqg : Measurable (fun x => phi z x (g x)) := by
    first | fun_prop | exact hphi.1.comp (measurable_const.prodMk
      (measurable_id.prodMk (hg.subtype_mk (h := hgr))))
  have hfl := recovery_unit_interval_memLp M f hf hfr
  have hgl := recovery_unit_interval_memLp M g hg hgr
  have hqfl := recovery_unit_interval_memLp M _ hqf (fun x => hphi.2 z x _ (hfr x))
  have hqgl := recovery_unit_interval_memLp M _ hqg (fun x => hphi.2 z x _ (hgr x))
  have hlip := policy_lipschitz_of_derivative_bound phi dphi hd B hder
  rw [← integral_sub (hqfl.integrable (by norm_num)) (hqgl.integrable (by norm_num))]
  calc
    _ ≤ ∫ x, |phi z x (f x) - phi z x (g x)| ∂xLaw M := abs_integral_le_integral_abs
    _ ≤ ∫ x, B * |f x - g x| ∂xLaw M :=
      integral_mono_ae ((hqfl.sub hqgl).integrable (by norm_num)).abs
        (((hfl.sub hgl).integrable (by norm_num)).abs.const_mul B)
        (Eventually.of_forall (fun x => hlip z x _ _ (hfr x) (hgr x)))
    _ = B * ∫ x, |f x - g x| ∂xLaw M := integral_const_mul _ _
    _ ≤ B * finiteL2Error M f g := by
      apply mul_le_mul_of_nonneg_left _ hB
      have hb := Causalean.Stat.abs_integral_le_eLpNorm_two (hfl.sub hgl).norm
      rw [abs_of_nonneg (integral_nonneg (fun x => norm_nonneg (f x - g x))),
        eLpNorm_norm] at hb
      rw [l2Error_eq_eLpNorm M f g (hfl.sub hgl)]
      simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_def] using hb


-- @node: firstStageRate_baseline_marginal_quarter_rate
/-- Under [the threshold-crossing model](hyp:h), suppose [each fitted propensity
is measurable in covariates](hyp:hm), [all fitted propensities lie between zero
and one](hyp:hr), and [their maximum population root mean squared error has
the first-stage little-o quarter rate in probability](hyp:hRate). Then [at
sample sizes twice one plus the index, the largest absolute baseline marginal
error across instrument values is little-o in probability of sample size to
the minus one-quarter power](goal). -/
lemma firstStageRate_baseline_marginal_quarter_rate
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (h : ThresholdCrossing M) (pHat : ℕ → A → Z → X → ℝ)
    (hm : ∀ n a z, Measurable (pHat n a z))
    (hr : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat) :
    Causalean.Stat.IsLittleOp (fun n a => Finset.univ.sup' Finset.univ_nonempty
      (fun z => |(∫ x, pHat (2*(n+1)) a z x ∂xLaw M) -
        ∫ x, M.prop z x ∂xLaw M|))
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hRate
  intro n a
  have hn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun z => |(∫ x, pHat (2*(n+1)) a z x ∂xLaw M) -
        ∫ x, M.prop z x ∂xLaw M|) := by
    obtain ⟨z⟩ := ‹Nonempty Z›
    apply (Finset.le_sup' _ (Finset.mem_univ z)).trans'
    exact abs_nonneg _
  rw [abs_of_nonneg hn, one_mul]
  apply Finset.sup'_le
  intro z _
  exact (recovery_marginal_l2Error_bound M _ _
    (recovery_unit_interval_memLp M _ (hm _ a z) (hr _ a z))
    (recovery_unit_interval_memLp M _
      (h.2.1.comp (measurable_const.prodMk measurable_id)) (M.rangeProp z))).trans
    ((Finset.le_sup' (fun z => finiteL2Error M (pHat (2*(n+1)) a z) (M.prop z))
      (Finset.mem_univ z)).trans (le_abs_self _))

-- @node: firstStageRate_policy_marginal_quarter_rate
/-- Under [the threshold-crossing model](hyp:h), assume [covariate measurability
of fitted propensities](hyp:hm), [their values lie between zero and one](hyp:hr),
and [their maximum population root mean squared error has the first-stage
little-o quarter rate in probability](hyp:hRate). For [a measurable policy
transformation preserving the unit interval](hyp:hphi) that [has the specified
derivative](hyp:hd), with [a uniformly bounded and Lipschitz derivative](hyp:hDerivative),
[the largest absolute policy marginal error across instruments, at sample
sizes twice one plus the index, is little-o in probability of sample size to
the minus one-quarter power](goal). -/
lemma firstStageRate_policy_marginal_quarter_rate
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (h : ThresholdCrossing M) (pHat : ℕ → A → Z → X → ℝ)
    (hm : ∀ n a z, Measurable (pHat n a z))
    (hr : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi) :
    Causalean.Stat.IsLittleOp (fun n a => Finset.univ.sup' Finset.univ_nonempty
      (fun z => |(∫ x, phi z x (pHat (2*(n+1)) a z x) ∂xLaw M) -
        ∫ x, phi z x (M.prop z x) ∂xLaw M|))
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (show 0 < B + 1 by linarith) hRate
  intro n a
  have hn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun z => |(∫ x, phi z x (pHat (2*(n+1)) a z x) ∂xLaw M) -
        ∫ x, phi z x (M.prop z x) ∂xLaw M|) := by
    obtain ⟨z⟩ := ‹Nonempty Z›
    apply (Finset.le_sup' _ (Finset.mem_univ z)).trans'
    exact abs_nonneg _
  rw [abs_of_nonneg hn]
  apply Finset.sup'_le
  intro z _
  calc
    _ ≤ B * finiteL2Error M (pHat (2*(n+1)) a z) (M.prop z) :=
      recovery_policy_marginal_l2Error_bound M phi dphi hphi hd B hB
        (fun z x p hp => (hder z x p p hp hp).1) z _ _ (hm _ a z)
        (h.2.1.comp (measurable_const.prodMk measurable_id)) (hr _ a z) (M.rangeProp z)
    _ ≤ (B + 1) * finiteL2Error M (pHat (2*(n+1)) a z) (M.prop z) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((Finset.le_sup' (fun z => finiteL2Error M (pHat (2*(n+1)) a z) (M.prop z))
      (Finset.mem_univ z)).trans (le_abs_self _)) (by linarith)

-- These are the population-mean consistency inputs for the finite recovery
-- graph, before adding the evaluation-sample concentration error.
-- @node: firstStageRate_fitted_marginals_consistent
/-- Under [the threshold-crossing model](hyp:h), suppose [fitted propensities are
measurable in covariates](hyp:hm), [take values between zero and one](hyp:hr),
and [satisfy the first-stage little-o quarter rate in probability](hyp:hRate).
For [a measurable policy transformation preserving the unit interval](hyp:hphi)
that [has the specified derivative](hyp:hd), with [a uniformly bounded and
Lipschitz derivative](hyp:hDerivative), [both the fitted baseline marginal mean
and the fitted policy marginal mean converge in probability to their population
counterparts at every instrument value, along sample sizes twice one plus the
index](goal). -/
lemma firstStageRate_fitted_marginals_consistent
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (h : ThresholdCrossing M) (pHat : ℕ → A → Z → X → ℝ)
    (hm : ∀ n a z, Measurable (pHat n a z))
    (hr : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi) :
    (∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, pHat (2*(n+1)) a z x ∂xLaw M) atTop
      (fun _ _ => ∫ x, M.prop z x ∂xLaw M)) ∧
    (∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, phi z x (pHat (2*(n+1)) a z x) ∂xLaw M) atTop
      (fun _ _ => ∫ x, phi z x (M.prop z x) ∂xLaw M)) := by
  have hp := firstStageRate_baseline_marginal_quarter_rate M μ h pHat hm hr hRate
  have hq := firstStageRate_policy_marginal_quarter_rate M μ h pHat hm hr hRate
    phi dphi hphi hd hDerivative
  constructor
  · intro z
    have hz : Causalean.Stat.IsLittleOp
        (fun n a => (∫ x, pHat (2*(n+1)) a z x ∂xLaw M) -
          ∫ x, M.prop z x ∂xLaw M)
        (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
      apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hp
      intro n a
      rw [one_mul]
      exact (Finset.le_sup' (fun z => |(∫ x, pHat (2*(n+1)) a z x ∂xLaw M) -
        ∫ x, M.prop z x ∂xLaw M|) (Finset.mem_univ z)).trans (le_abs_self _)
    have hc := dml_quarter_rate_tendsto_probability_zero μ _ hz
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hc ⊢
    simpa only [sub_zero] using hc
  · intro z
    have hz : Causalean.Stat.IsLittleOp
        (fun n a => (∫ x, phi z x (pHat (2*(n+1)) a z x) ∂xLaw M) -
          ∫ x, phi z x (M.prop z x) ∂xLaw M)
        (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
      apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hq
      intro n a
      rw [one_mul]
      exact (Finset.le_sup'
        (fun z => |(∫ x, phi z x (pHat (2*(n+1)) a z x) ∂xLaw M) -
          ∫ x, phi z x (M.prop z x) ∂xLaw M|)
        (Finset.mem_univ z)).trans (le_abs_self _)
    have hc := dml_quarter_rate_tendsto_probability_zero μ _ hz
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hc ⊢
    simpa only [sub_zero] using hc

end Papers.TbsPrteOptimalTransport
