module
public import Papers.TbsExtremeEffects.Helpers.JointTailLaw

/-! Bounded continuous joint tests and removal of the uniform truncation error. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

/-- If [the truncation error is uniformly small for sufficiently large truncation and index](hyp:herror), [each fixed positive truncation converges](hyp:hfixed), and [the fixed-truncation limits converge as truncation grows](hyp:hlimit), then [the original functions converge to the limiting value](goal).

The three errors are the uniform truncation error, the fixed-truncation limit, and its limiting tail. -/
-- @node: tendsto_of_uniform_truncation_error
lemma tendsto_of_uniform_truncation_error (f : ℝ → ℝ) (fB : ℝ → ℝ → ℝ)
    (lB : ℝ → ℝ) (l : ℝ)
    (herror : ∀ ε > 0, ∃ B₀ t₀ : ℝ, 0 < B₀ ∧
      ∀ B ≥ B₀, ∀ t ≥ t₀, |f t - fB B t| ≤ ε)
    (hfixed : ∀ B > 0, Tendsto (fB B) atTop (𝓝 (lB B)))
    (hlimit : Tendsto lB atTop (𝓝 l)) : Tendsto f atTop (𝓝 l) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨B₀, t₀, hB₀, he⟩ := herror (ε / 3) (by positivity)
  obtain ⟨B₁, hB₁⟩ := Metric.tendsto_atTop.mp hlimit (ε / 3) (by positivity)
  let B := max B₀ B₁
  have hB : 0 < B := hB₀.trans_le (le_max_left _ _)
  obtain ⟨t₁, ht₁⟩ := Metric.tendsto_atTop.mp (hfixed B hB) (ε / 3) (by positivity)
  refine ⟨max t₀ t₁, ?_⟩
  intro t ht
  have h₁ := he B (le_max_left _ _) t ((le_max_left _ _).trans ht)
  have h₂ := ht₁ t ((le_max_right _ _).trans ht)
  have h₃ := hB₁ B (le_max_right _ _)
  rw [Real.dist_eq] at h₂ h₃ ⊢
  have htriangle : |f t - l| ≤ |f t - fB B t| +
      |fB B t - lB B| + |lB B - l| :=
    (abs_sub_le (f t) (lB B) l).trans
      (add_le_add (abs_sub_le (f t) (fB B t) (lB B)) le_rfl)
  linarith

/-- [The clipped joint contrast](goal) averages over [the extreme model's covariate law](hyp:M) the test function [H](hyp:H), multiplied by a radial power from [the clipping level](hyp:B) and [the radial-angular point](hyp:z), with the result clipped between the two bounds.

Extending the radial coordinate by `max 1` makes the test continuous everywhere, including when the homogeneity exponent is negative. -/
-- @node: clippedJointContrast
noncomputable def clippedJointContrast (M : ExtremeModel q d)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (B : ℝ) (z : ℝ × (Fin d → ℝ)) : ℝ :=
  ∫ x, max (-B) (min B (H (x, z.2) * (max 1 z.1) ^ M.alpha)) ∂M.mu.map M.X

-- @node: clippedJointContrast_bound
/-- If [the clipping level is nonnegative](hyp:hB), then [the absolute value of the clipped joint contrast is at most that level](goal). -/
lemma clippedJointContrast_bound (M : ExtremeModel q d)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (z : ℝ × (Fin d → ℝ)) :
    |clippedJointContrast M H B z| ≤ B := by
  let : IsProbabilityMeasure (M.mu.map M.X) :=
    Measure.isProbabilityMeasure_map M.measurable_X.aemeasurable
  have hbound : ∀ x, ‖max (-B) (min B (H (x, z.2) * (max 1 z.1) ^ M.alpha))‖ ≤ B := by
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  simpa [clippedJointContrast, Real.norm_eq_abs] using
    norm_integral_le_of_norm_le (integrable_const B (μ := M.mu.map M.X))
      (Eventually.of_forall hbound)

-- @node: continuous_clippedJointContrast
/-- If [the clipping level is nonnegative](hyp:hB), then [the clipped joint contrast varies continuously with the radial-angular point](goal). -/
@[fun_prop] lemma continuous_clippedJointContrast (M : ExtremeModel q d)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    {B : ℝ} (hB : 0 ≤ B) : Continuous (clippedJointContrast M H B) := by
  first | fun_prop | skip
  let : IsProbabilityMeasure (M.mu.map M.X) :=
    Measure.isProbabilityMeasure_map M.measurable_X.aemeasurable
  unfold clippedJointContrast
  apply continuous_of_dominated (bound := fun _ => B)
  · intro z
    apply Continuous.aestronglyMeasurable
    fun_prop
  · intro z
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · exact integrable_const _
  · apply Eventually.of_forall
    intro x
    apply Continuous.max continuous_const
    apply Continuous.min continuous_const
    apply Continuous.mul
    · fun_prop
    · apply Continuous.rpow_const
      · fun_prop
      · intro z
        exact Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left 1 z.1)))

-- @node: weightedAngularContrast_clip_eq_joint_average
/-- If [the noise is regularly varying](hyp:hRV), [the noise is independent](hyp:hNoise), [the covariates are bounded](hyp:hX), [the bounded test agrees with the treatment contrast on the relevant covariate ball and positive sphere](hyp:hH), [the threshold is positive](hyp:ht), and [the clipping level is nonnegative](hyp:hB), then [the clipped weighted angular contrast has the same average under the tail law as the clipped joint contrast under the radial-angular law](goal). -/
lemma weightedAngularContrast_clip_eq_joint_average (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (hH : ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
      H (x, s) = M.g x true s - M.g x false s)
    {t B : ℝ} (ht : 0 < t) (hB : 0 ≤ B) :
    (∫ w, max (-B) (min B (weightedAngularContrast M t w)) ∂tailLaw M t) =
      ∫ z, clippedJointContrast M H B z ∂radialAngularLaw M t := by
  let F : (Fin q → ℝ) × (ℝ × (Fin d → ℝ)) → ℝ :=
    fun z => max (-B) (min B (H (z.1, z.2.2) * (max 1 z.2.1) ^ M.alpha))
  have hF : Measurable F := by fun_prop
  have heq : (fun w => max (-B) (min B (weightedAngularContrast M t w))) =ᵐ[tailLaw M t]
      (fun w => F (M.X w, radialAngularMap M t w)) := by
    filter_upwards [weightedAngularContrast_ae_extension M hX H hH ht,
      scaled_radius_ge_one_tailLaw M ht] with w hw hrad
    have hr : 0 ≤ radius M w := by
      have := (le_div_iff₀ ht).mp hrad
      linarith
    simp only [F, radialAngularMap, max_eq_right hrad, hw, Real.div_rpow hr ht.le]
  have hpair : Measurable (fun w => (M.X w, radialAngularMap M t w)) := by
    have hx := M.measurable_X
    fun_prop
  let := radialAngularLaw_probability M hRV t
  let : IsProbabilityMeasure (M.mu.map M.X) :=
    Measure.isProbabilityMeasure_map M.measurable_X.aemeasurable
  have hInt : Integrable F ((M.mu.map M.X).prod (radialAngularLaw M t)) := by
    apply Integrable.mono' (integrable_const B) hF.aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  calc
    _ = ∫ w, F (M.X w, radialAngularMap M t w) ∂tailLaw M t := integral_congr_ae heq
    _ = ∫ z, F z ∂(M.mu.map M.X).prod (radialAngularLaw M t) := by
      rw [← integral_map hpair.aemeasurable hF.aestronglyMeasurable,
        covariate_radialAngular_tail_pair_law M hRV hNoise t]
    _ = _ := integral_prod_symm F hInt

/-- If [the noise is regularly varying](hyp:hRV), [the radial-angular laws converge weakly to the proposed probability law](hyp:hweak), and [the clipping level is nonnegative](hyp:hB), then [the averages of the clipped joint contrast converge to its average under that limiting law](goal). -/
-- @node: clippedJointContrast_tendsto_of_weak_limit
lemma clippedJointContrast_tendsto_of_weak_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (ν : ProbabilityMeasure (ℝ × (Fin d → ℝ)))
    (hweak : Tendsto (fun t => (⟨radialAngularLaw M t,
      radialAngularLaw_probability M hRV t⟩ : ProbabilityMeasure (ℝ × (Fin d → ℝ))))
      atTop (nhds (X := ProbabilityMeasure (ℝ × (Fin d → ℝ))) ν)) {B : ℝ} (hB : 0 ≤ B) :
    Tendsto (fun t => ∫ z, clippedJointContrast M H B z ∂radialAngularLaw M t)
      atTop (𝓝 (∫ z, clippedJointContrast M H B z ∂(ν : Measure _))) := by
  let test : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨clippedJointContrast M H B, continuous_clippedJointContrast M H hB⟩ (2 * B) (by
        intro z z'
        change dist (clippedJointContrast M H B z) (clippedJointContrast M H B z') ≤ 2 * B
        rw [Real.dist_eq]
        exact (abs_sub _ _).trans (by
          linarith [clippedJointContrast_bound M H hB z,
            clippedJointContrast_bound M H hB z']))
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) test

-- @node: abs_clip_le_abs
/-- If [the clipping level is nonnegative](hyp:hB), then [clipping a real number between the two bounds cannot increase its absolute value](goal). -/
lemma abs_clip_le_abs (v : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    |max (-B) (min B v)| ≤ |v| := by
  apply abs_le.mpr
  constructor
  · exact le_max_of_le_right (le_min (by linarith [abs_nonneg v]) (neg_abs_le v))
  · exact max_le (by linarith [abs_nonneg v]) ((min_le_right _ _).trans (le_abs_self v))

/-- If [the radial power is integrable under the limiting law](hyp:hRad), then [the clipped joint-contrast averages converge, as the clipping level grows, to the corresponding unclipped radial-power average](goal). -/
-- @node: clippedJointContrast_limit
lemma clippedJointContrast_limit (M : ExtremeModel q d)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (ν : ProbabilityMeasure (ℝ × (Fin d → ℝ)))
    (hRad : Integrable (fun z : ℝ × (Fin d → ℝ) => (max 1 z.1) ^ M.alpha)
      (ν : Measure _)) :
    Tendsto (fun B => ∫ z, clippedJointContrast M H B z ∂(ν : Measure _)) atTop
      (𝓝 (∫ z : ℝ × (Fin d → ℝ), (∫ x, H (x, z.2) ∂M.mu.map M.X) * (max 1 z.1) ^ M.alpha
        ∂(ν : Measure _))) := by
  let : IsProbabilityMeasure (M.mu.map M.X) :=
    Measure.isProbabilityMeasure_map M.measurable_X.aemeasurable
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖H‖ * (max 1 z.1) ^ M.alpha)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    exact (continuous_clippedJointContrast M H hB).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    apply Eventually.of_forall
    intro z
    have hpow : 0 ≤ (max 1 z.1) ^ M.alpha := Real.rpow_nonneg (by positivity) _
    have hbound (x : Fin q → ℝ) :
        ‖max (-B) (min B (H (x, z.2) * (max 1 z.1) ^ M.alpha))‖ ≤
          ‖H‖ * (max 1 z.1) ^ M.alpha := by
      rw [Real.norm_eq_abs]
      apply (abs_clip_le_abs _ hB).trans
      rw [abs_mul, abs_of_nonneg hpow]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using H.norm_coe_le_norm (x, z.2)) hpow
    simpa [clippedJointContrast] using norm_integral_le_of_norm_le
      (integrable_const (‖H‖ * (max 1 z.1) ^ M.alpha) (μ := M.mu.map M.X))
      (Eventually.of_forall hbound)
  · exact hRad.const_mul ‖H‖
  · apply Eventually.of_forall
    intro z
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (‖H‖ * (max 1 z.1) ^ M.alpha)] with B hB
    have hpow : 0 ≤ (max 1 z.1) ^ M.alpha := Real.rpow_nonneg (by positivity) _
    have heq (x : Fin q → ℝ) :
        max (-B) (min B (H (x, z.2) * (max 1 z.1) ^ M.alpha)) =
          H (x, z.2) * (max 1 z.1) ^ M.alpha := by
      have hb : |H (x, z.2) * (max 1 z.1) ^ M.alpha| ≤ B := by
        rw [abs_mul, abs_of_nonneg hpow]
        exact (mul_le_mul_of_nonneg_right
          (by simpa only [Real.norm_eq_abs] using H.norm_coe_le_norm (x, z.2)) hpow).trans hB
      rw [min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
    simp only [clippedJointContrast, heq, integral_mul_const]

/-- If [the noise is regularly varying](hyp:hRV), [the covariates are bounded](hyp:hX), [the bounded test agrees with the treatment contrast on the relevant covariate ball and positive sphere](hyp:hH), [the radial power is integrable](hyp:hRad), and [its radial moment has the stated value](hyp:hMoment), then [the clipped joint-contrast averages under the radial-spectral product law converge to the target contrast times that moment](goal).

Fubini evaluates the limiting product law using its radial moment. -/
-- @node: clippedJointContrast_product_limit
lemma clippedJointContrast_product_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (hH : ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
      H (x, s) = M.g x true s - M.g x false s)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hRad : Integrable (fun r => (max 1 r) ^ M.alpha) ρ)
    (hMoment : (∫ r, (max 1 r) ^ M.alpha ∂ρ) = M.beta / (M.beta - M.alpha)) :
    Tendsto (fun B => ∫ z, clippedJointContrast M H B z ∂ρ.prod M.S) atTop
      (𝓝 (etaTarget M * (M.beta / (M.beta - M.alpha)))) := by
  let : IsProbabilityMeasure M.S := hRV.2.2.spectral_probability
  let ν : ProbabilityMeasure (ℝ × (Fin d → ℝ)) := ⟨ρ.prod M.S, inferInstance⟩
  have hlim := clippedJointContrast_limit M H ν (hRad.comp_fst M.S)
  have hxe : ∀ᵐ x ∂M.mu.map M.X, l1Norm x ≤ M.R := by
    apply (ae_map_iff M.measurable_X.aemeasurable
      (measurableSet_le measurable_l1Norm measurable_const)).mpr hX.2
  have hAngular : (∫ s, (∫ x, H (x, s) ∂M.mu.map M.X) ∂M.S) = etaTarget M := by
    apply integral_congr_ae
    filter_upwards [spectral_ae_sphere M hRV] with s hs
    apply integral_congr_ae
    filter_upwards [hxe] with x hx
    exact hH x hx s hs
  have hTarget : (∫ z : ℝ × (Fin d → ℝ),
      (∫ x, H (x, z.2) ∂M.mu.map M.X) * (max 1 z.1) ^ M.alpha ∂ρ.prod M.S) =
      etaTarget M * (M.beta / (M.beta - M.alpha)) := by
    simp_rw [mul_comm (∫ x, H (x, _) ∂M.mu.map M.X)]
    rw [integral_prod_mul (fun r : ℝ => (max 1 r) ^ M.alpha)
      (fun s : Fin d → ℝ => ∫ x, H (x, s) ∂M.mu.map M.X), hMoment, hAngular, mul_comm]
  change Tendsto (fun B => ∫ z, clippedJointContrast M H B z ∂ρ.prod M.S) atTop
    (𝓝 (∫ z : ℝ × (Fin d → ℝ),
      (∫ x, H (x, z.2) ∂M.mu.map M.X) * (max 1 z.1) ^ M.alpha ∂ρ.prod M.S)) at hlim
  rw [hTarget] at hlim
  exact hlim

/-- If [the noise is regularly varying](hyp:hRV), [the noise is independent](hyp:hNoise), [the covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the homogeneity exponent is smaller than the tail exponent](hyp:hAlpha), [the bounded test agrees with the treatment contrast on the relevant covariate ball and positive sphere](hyp:hH), [the radial-angular laws converge weakly](hyp:hweak), and [the clipped limiting averages converge](hyp:hlimit), then [the untruncated weighted angular-contrast averages converge to the same limit](goal).

The uniform moment bound removes truncation after taking the weak limit. -/
-- @node: weightedAngularContrast_tendsto_of_truncated_joint_limit
lemma weightedAngularContrast_tendsto_of_truncated_joint_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hAlpha : M.alpha < M.beta)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (hH : ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
      H (x, s) = M.g x true s - M.g x false s)
    (ν : ProbabilityMeasure (ℝ × (Fin d → ℝ)))
    (hweak : Tendsto (fun t => (⟨radialAngularLaw M t,
      radialAngularLaw_probability M hRV t⟩ : ProbabilityMeasure (ℝ × (Fin d → ℝ))))
      atTop (nhds (X := ProbabilityMeasure (ℝ × (Fin d → ℝ))) ν)) {l : ℝ}
    (hlimit : Tendsto (fun B => ∫ z, clippedJointContrast M H B z ∂(ν : Measure _))
      atTop (𝓝 l)) :
    Tendsto (fun t => ∫ w, weightedAngularContrast M t w ∂tailLaw M t)
      atTop (𝓝 l) := by
  apply tendsto_of_uniform_truncation_error _
    (fun B t => ∫ w, max (-B) (min B (weightedAngularContrast M t w)) ∂tailLaw M t)
    _ l _ _ hlimit
  · intro ε hε
    obtain ⟨B₀, t₀, hB₀, _, he⟩ :=
      weightedAngularContrast_uniform_truncation M hRV hX hHom hAlpha hε
    exact ⟨B₀, t₀, hB₀, he⟩
  · intro B hB
    apply (clippedJointContrast_tendsto_of_weak_limit M hRV H ν hweak hB.le).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (weightedAngularContrast_clip_eq_joint_average M hRV hNoise hX H hH ht hB.le).symm

end Papers.TbsExtremeEffects
