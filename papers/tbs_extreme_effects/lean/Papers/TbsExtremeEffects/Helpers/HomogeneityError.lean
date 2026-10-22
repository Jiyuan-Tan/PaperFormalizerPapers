module
public import Papers.TbsExtremeEffects.Helpers.RegularVariation

/-! Tail-envelope control and the realized-radius homogeneity error in identification. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

/-- Under [asymptotic homogeneity](hyp:hHom), the error envelope's values beyond a sufficiently
large radius [are bounded above](goal).
@node: eBar_eventually_bddAbove -/
lemma eBar_eventually_bddAbove (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) :
    ∀ᶠ t in atTop, BddAbove (M.e '' Set.Ici t) := by
  have hsmall : ∀ᶠ r in atTop, M.e r < 1 :=
    (tendsto_order.mp hHom.2.1).2 1 (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hsmall
  filter_upwards [eventually_ge_atTop T] with t ht
  refine ⟨1, ?_⟩
  rintro y ⟨r, hr, rfl⟩
  exact (hT r (ht.trans hr)).le

/-- If [the error envelope beyond a threshold is bounded above](hyp:hbounded) and [the radius is at
least that threshold](hyp:hr), then [the error at that radius is no larger than its tail supremum](goal).
@node: e_le_eBar -/
lemma e_le_eBar (M : ExtremeModel q d) {t r : ℝ}
    (hbounded : BddAbove (M.e '' Set.Ici t)) (hr : t ≤ r) :
    M.e r ≤ eBar M t :=
  le_csSup hbounded ⟨r, hr, rfl⟩

/-- Under [asymptotic homogeneity](hyp:hHom), if [the threshold is positive](hyp:ht) and [the
error envelope beyond it is bounded above](hyp:hbounded), then [its tail supremum is nonnegative](goal).
@node: eBar_nonneg -/
lemma eBar_nonneg (M : ExtremeModel q d) (hHom : AsymptoticHomogeneity M)
    {t : ℝ} (ht : 0 < t) (hbounded : BddAbove (M.e '' Set.Ici t)) :
    0 ≤ eBar M t :=
  (hHom.1 t ht).trans (e_le_eBar M hbounded le_rfl)

/-- Under [asymptotic homogeneity](hyp:hHom), the tail supremum of the error envelope
[tends to zero as the threshold grows](goal).
@node: eBar_tendsto_zero -/
lemma eBar_tendsto_zero (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) : Tendsto (eBar M) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (0 : ℝ), eBar_eventually_bddAbove M hHom]
      with t ht hb
    exact ha.trans_le (eBar_nonneg M hHom ht hb)
  · intro b hb
    have hsmall : ∀ᶠ r in atTop, M.e r < b / 2 :=
      (tendsto_order.mp hHom.2.1).2 _ (by linarith)
    obtain ⟨T, hT⟩ := eventually_atTop.mp hsmall
    filter_upwards [eventually_ge_atTop T] with t ht
    have hsup : eBar M t ≤ b / 2 := by
      unfold eBar
      apply csSup_le (s := M.e '' Set.Ici t)
        (show (M.e '' Set.Ici t).Nonempty from ⟨M.e t, t, Set.mem_Ici.mpr le_rfl, rfl⟩)
      rintro y ⟨r, hr, rfl⟩
      exact (hT r (ht.trans hr)).le
    exact hsup.trans_lt (by linarith)

/-- Under [asymptotic homogeneity](hyp:hHom), for a realization whose [covariate is bounded](hyp:hX)
and whose [radius is positive](hyp:hR), the normalized outcome [differs from its directional limit by at most the error envelope](goal).
@node: homogeneity_at_realized_radius -/
lemma homogeneity_at_realized_radius (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) (w : M.Om) (a : Bool)
    (hX : l1Norm (M.X w) ≤ M.R) (hR : 0 < radius M w) :
    |M.f (M.X w) a (M.U w) / radius M w ^ M.alpha -
      M.g (M.X w) a (direction M w)| ≤ M.e (radius M w) := by
  have hscale : (fun i => radius M w * direction M w i) = M.U w := by
    funext i
    dsimp [direction]
    field_simp
  have hbound := hHom.2.2.1 (radius M w) hR a (M.X w) hX
    (direction M w) (direction_mem_positiveSphere M hR)
  rwa [hscale] at hbound

/-- Under [asymptotic homogeneity](hyp:hHom), if [the threshold is positive](hyp:ht), [the tail
error envelope is bounded](hyp:hb), and a realization has a [bounded covariate](hyp:hX) and [radius above the threshold](hyp:hw), then [its normalized treatment contrast is within twice the tail error supremum of the directional contrast](goal).
@node: homogeneity_contrast_tail_bound -/
lemma homogeneity_contrast_tail_bound (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) {t : ℝ} (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) (w : M.Om)
    (hX : l1Norm (M.X w) ≤ M.R) (hw : t < radius M w) :
    |(M.f (M.X w) true (M.U w) - M.f (M.X w) false (M.U w)) /
      radius M w ^ M.alpha -
      (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w))| ≤
      2 * eBar M t := by
  have hR := ht.trans hw
  have h1 := homogeneity_at_realized_radius M hHom w true hX hR
  have h0 := homogeneity_at_realized_radius M hHom w false hX hR
  have he := e_le_eBar M hb hw.le
  rw [sub_div]
  calc
    _ = |(M.f (M.X w) true (M.U w) / radius M w ^ M.alpha -
          M.g (M.X w) true (direction M w)) -
        (M.f (M.X w) false (M.U w) / radius M w ^ M.alpha -
          M.g (M.X w) false (direction M w))| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ M.e (radius M w) + M.e (radius M w) := add_le_add h1 h0
    _ ≤ 2 * eBar M t := by linarith

/-- If [covariates are bounded almost surely](hyp:hX), [asymptotic homogeneity holds](hyp:hHom),
[the threshold is positive](hyp:ht), and [the tail error envelope is bounded](hyp:hb), then [almost every tail realization satisfies the normalized contrast bound](goal).
@node: homogeneity_contrast_tail_ae -/
lemma homogeneity_contrast_tail_ae (M : ExtremeModel q d)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    {t : ℝ} (ht : 0 < t) (hb : BddAbove (M.e '' Set.Ici t)) :
    ∀ᵐ w ∂tailLaw M t,
      |(M.f (M.X w) true (M.U w) - M.f (M.X w) false (M.U w)) /
        radius M w ^ M.alpha -
        (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w))| ≤
        2 * eBar M t := by
  have hx : ∀ᵐ w ∂tailLaw M t, l1Norm (M.X w) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  filter_upwards [hx, ae_cond_mem (μ := M.mu)
    (measurableSet_lt measurable_const (measurable_radius M))] with w hwX hw
  exact homogeneity_contrast_tail_bound M hHom ht hb w hwX hw

/-- If [the noise is regularly varying](hyp:hRV), [asymptotic homogeneity holds](hyp:hHom), and
[the outcome exponent is below the tail index](hyp:hAlpha), then [the radial error bound tends to zero](goal).
@node: homogeneity_radial_error_tendsto_zero -/
lemma homogeneity_radial_error_tendsto_zero (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hHom : AsymptoticHomogeneity M)
    (hAlpha : M.alpha < M.beta) :
    Tendsto (fun t => 2 * eBar M t * radialFactor M t) atTop (𝓝 0) := by
  have hlim := ((tendsto_const_nhds (x := (2 : ℝ))).mul (eBar_tendsto_zero M hHom)).mul
    (radial_moment_limit M hRV hAlpha)
  simpa only [mul_zero, zero_mul] using hlim

/-- If [the noise is regularly varying](hyp:hRV) and [the power is below the tail index](hyp:ha),
then [the corresponding normalized radial power is integrable under sufficiently high tail conditioning](goal).
@node: conditional_radial_power_integrable -/
lemma conditional_radial_power_integrable (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {a : ℝ} (ha : a < M.beta) :
    ∀ᶠ t in atTop, Integrable (fun w => radius M w ^ a / t ^ a) (tailLaw M t) := by
  by_cases hzero : a = 0
  · filter_upwards [] with t
    let := tailLaw_probability M hRV t
    simpa only [hzero, Real.rpow_zero, div_one] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : M.Om => (1 : ℝ)) (tailLaw M t))
  · filter_upwards [tail_power_kernel_eventually_integrable M hRV ha hzero,
      eventually_gt_atTop (0 : ℝ)] with t hTail ht
    let := tailLaw_probability M hRV t
    have hZ : Measurable (fun w => radius M w / t) := by fun_prop
    have hTail' : IntegrableOn
        (fun r : ℝ => r ^ (a - 1) * (tailLaw M t).real {w | r < radius M w / t})
        (Set.Ioi 1) := by
      apply hTail.congr_fun _ measurableSet_Ioi
      intro r hr
      dsimp only
      rw [tailLaw_scaled_radius_survival M ht (Set.mem_Ioi.mp hr).le]
    apply ((power_moment_layercake (tailLaw M t) _ hZ
      (scaled_radius_ge_one_tailLaw M ht) hzero hTail').1).congr
    filter_upwards [scaled_radius_ge_one_tailLaw M ht] with w hw
    have hr : 0 ≤ radius M w := by
      have := (le_div_iff₀ ht).mp hw
      linarith
    exact Real.div_rpow hr ht.le a

/-- Under [asymptotic homogeneity](hyp:hHom), if [the threshold is positive](hyp:ht), [the tail
error envelope is bounded](hyp:hb), and a realization has a [bounded covariate](hyp:hX) and [radius above the threshold](hyp:hw), then [the threshold-scaled contrast error is bounded by the radial weight times twice the tail error supremum](goal).
@node: homogeneity_weighted_contrast_tail_bound -/
lemma homogeneity_weighted_contrast_tail_bound (M : ExtremeModel q d)
    (hHom : AsymptoticHomogeneity M) {t : ℝ} (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) (w : M.Om)
    (hX : l1Norm (M.X w) ≤ M.R) (hw : t < radius M w) :
    |(M.f (M.X w) true (M.U w) - M.f (M.X w) false (M.U w)) / t ^ M.alpha -
      (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w)) *
        (radius M w ^ M.alpha / t ^ M.alpha)| ≤
      2 * eBar M t * (radius M w ^ M.alpha / t ^ M.alpha) := by
  have hR : 0 < radius M w := ht.trans hw
  have hp : 0 < radius M w ^ M.alpha := Real.rpow_pos_of_pos hR _
  have htP : 0 < t ^ M.alpha := Real.rpow_pos_of_pos ht _
  have heq :
      (M.f (M.X w) true (M.U w) - M.f (M.X w) false (M.U w)) / t ^ M.alpha -
        (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w)) *
          (radius M w ^ M.alpha / t ^ M.alpha) =
      ((M.f (M.X w) true (M.U w) - M.f (M.X w) false (M.U w)) /
        radius M w ^ M.alpha -
        (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w))) *
          (radius M w ^ M.alpha / t ^ M.alpha) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (div_pos hp htP)]
  exact mul_le_mul_of_nonneg_right
    (homogeneity_contrast_tail_bound M hHom ht hb w hX hw) (div_pos hp htP).le

/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [asymptotic
homogeneity holds](hyp:hHom), and [the outcome exponent is below the tail index](hyp:hAlpha), then [eventually the integrated contrast error is bounded by the radial error bound](goal).
@node: homogeneity_integrated_error_bound -/
lemma homogeneity_integrated_error_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hAlpha : M.alpha < M.beta) :
    ∀ᶠ t in atTop,
      |∫ w, (M.f (M.X w) true (M.U w) - M.f (M.X w) false (M.U w)) / t ^ M.alpha -
        (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w)) *
          (radius M w ^ M.alpha / t ^ M.alpha) ∂tailLaw M t| ≤
        2 * eBar M t * radialFactor M t := by
  filter_upwards [conditional_radial_power_integrable M hRV hAlpha,
    eBar_eventually_bddAbove M hHom, eventually_gt_atTop (0 : ℝ)] with t hint hb ht
  have hx : ∀ᵐ w ∂tailLaw M t, l1Norm (M.X w) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  have hbound : ∀ᵐ w ∂tailLaw M t,
      ‖(M.f (M.X w) true (M.U w) - M.f (M.X w) false (M.U w)) / t ^ M.alpha -
        (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w)) *
          (radius M w ^ M.alpha / t ^ M.alpha)‖ ≤
        (2 * eBar M t) * (radius M w ^ M.alpha / t ^ M.alpha) := by
    filter_upwards [hx, ae_cond_mem (μ := M.mu)
      (measurableSet_lt measurable_const (measurable_radius M))] with w hwX hw
    simpa only [Real.norm_eq_abs] using
      homogeneity_weighted_contrast_tail_bound M hHom ht hb w hwX hw
  have hnorm := norm_integral_le_of_norm_le (hint.const_mul (2 * eBar M t)) hbound
  simpa only [Real.norm_eq_abs, integral_const_mul, radialFactor] using hnorm

/-- If [the noise is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [asymptotic
homogeneity holds](hyp:hHom), and [the outcome exponent is below the tail index](hyp:hAlpha), then [the integrated contrast error tends to zero](goal).
@node: homogeneity_integrated_error_tendsto_zero -/
lemma homogeneity_integrated_error_tendsto_zero (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hAlpha : M.alpha < M.beta) :
    Tendsto (fun t => ∫ w,
      (M.f (M.X w) true (M.U w) - M.f (M.X w) false (M.U w)) / t ^ M.alpha -
        (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w)) *
          (radius M w ^ M.alpha / t ^ M.alpha) ∂tailLaw M t) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (homogeneity_radial_error_tendsto_zero M hRV hHom hAlpha)
  simpa only [Real.norm_eq_abs] using
    homogeneity_integrated_error_bound M hRV hX hHom hAlpha

end Papers.TbsExtremeEffects
