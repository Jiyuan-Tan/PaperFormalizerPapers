module
public import Papers.TbsExtremeEffects.Helpers.OutcomeConditioning
public import Papers.TbsExtremeEffects.Helpers.TailRegressionProjection
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! Identification of finite sign-limit regressions on integrable localizations. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- If [the conditioning sigma-algebra is contained in the ambient one](hyp:hG), [the outcome is integrable](hyp:hY), [the outcome is everywhere nonnegative](hyp:hYn), [the proposed limit is measurable with respect to the conditioning information](hyp:hHm), and [conditional expectations of its increasing truncations converge almost surely to that limit](hyp:hlim), then [the limit is almost surely the conditional expectation of the outcome](goal).

@node: conditional_positive_limit_eq_condExp -/
lemma conditional_positive_limit_eq_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    (Y H : Ω → ℝ) (hY : Integrable Y μ) (hYn : ∀ w, 0 ≤ Y w)
    (hHm : Measurable[G] H)
    (hlim : ∀ᵐ w ∂μ, Tendsto
      (fun k : ℕ => μ[(fun v => min (Y v) (k : ℝ)) | G] w) atTop (𝓝 (H w))) :
    H =ᵐ[μ] μ[Y | G] := by
  let F : ℕ → Ω → ℝ := fun k v => min (Y v) (k : ℝ)
  have hF (k : ℕ) : Integrable (F k) μ := by
    apply hY.mono'
      ((continuous_id.min continuous_const).comp_aestronglyMeasurable hY.aestronglyMeasurable)
    exact Eventually.of_forall fun w => by
      change ‖min (Y w) (k : ℝ)‖ ≤ Y w
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hYn w) (Nat.cast_nonneg k))]
      exact min_le_left _ _
  have hbound (k : ℕ) (w : Ω) : 0 ≤ F k w ∧ F k w ≤ Y w :=
    ⟨le_min (hYn w) (Nat.cast_nonneg k), min_le_left _ _⟩
  have hFlim : ∀ᵐ w ∂μ, Tendsto (fun k => F k w) atTop (𝓝 (Y w)) := by
    apply Eventually.of_forall
    intro w
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Y w))]
      with k hk
    exact (min_eq_left hk).symm
  have hInt : Integrable H μ := by
    simpa only [one_mul] using (@weighted_conditional_limit_integral Ω mΩ μ _ G hG
      (fun _ => 1) measurable_const (fun _ => by norm_num) F Y H hF
      (by simpa only [one_mul] using hY) hbound hlim hFlim).1
  apply ae_eq_condExp_of_forall_setIntegral_eq hG hY
    (fun _ _ _ => hInt.integrableOn) _ hHm.aestronglyMeasurable
  intro S hS _
  let I : Ω → ℝ := S.indicator (fun _ => 1)
  have hI : Measurable[G] I := measurable_const.indicator hS
  have hIn : ∀ w, 0 ≤ I w := fun w => by
    by_cases hw : w ∈ S <;> simp [I, hw]
  have hIY : Integrable (fun w => I w * Y w) μ := by
    apply (hY.indicator (hG _ hS)).congr
    exact Eventually.of_forall fun w => by
      by_cases hw : w ∈ S <;> simp [I, hw]
  have heq := (@weighted_conditional_limit_integral Ω mΩ μ _ G hG I hI hIn F Y H
    hF hIY hbound hlim hFlim).2
  have hid (Z : Ω → ℝ) : (fun w => I w * Z w) = S.indicator Z := by
    funext w
    by_cases hw : w ∈ S <;> simp [I, hw]
  rw [hid H, hid Y, integral_indicator (hG _ hS), integral_indicator (hG _ hS)] at heq
  exact heq

/-- If [the conditioning sigma-algebra is contained in the ambient one](hyp:hG), [the outcome is integrable](hyp:hY), [the proposed positive and negative limits are conditioning-measurable](hyp:hP,hN), [the conditional expectations of the truncated positive part converge to the positive limit](hyp:hp), and [those of the truncated negative part converge to the negative limit](hyp:hn), then [their difference is almost surely the conditional expectation of the outcome](goal).

@node: conditional_signed_limits_eq_condExp -/
lemma conditional_signed_limits_eq_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    (Y P N : Ω → ℝ) (hY : Integrable Y μ)
    (hP : Measurable[G] P) (hN : Measurable[G] N)
    (hp : ∀ᵐ w ∂μ, Tendsto (fun k : ℕ =>
      μ[(fun v => min (max (Y v) 0) (k : ℝ)) | G] w) atTop (𝓝 (P w)))
    (hn : ∀ᵐ w ∂μ, Tendsto (fun k : ℕ =>
      μ[(fun v => min (max (-Y v) 0) (k : ℝ)) | G] w) atTop (𝓝 (N w))) :
    (fun w => P w - N w) =ᵐ[μ] μ[Y | G] := by
  have hpos := @conditional_positive_limit_eq_condExp Ω mΩ μ _ G hG _ P hY.pos_part
    (fun _ => le_max_right _ _) hP hp
  have hneg := @conditional_positive_limit_eq_condExp Ω mΩ μ _ G hG _ N hY.neg_part
    (fun _ => le_max_right _ _) hN hn
  have hsub := condExp_sub hY.pos_part hY.neg_part G
  have hsplit : (fun v => max (Y v) 0 - max (-Y v) 0) = Y := by
    funext v
    rcases le_total 0 (Y v) with hv | hv
    · rw [max_eq_left hv, max_eq_right (neg_nonpos.mpr hv), sub_zero]
    · rw [max_eq_right hv, max_eq_left (neg_nonneg.mpr hv)]
      ring
  simp only [Pi.sub_def] at hsub
  rw [hsplit] at hsub
  filter_upwards [hpos, hneg, hsub] with v hpv hnv hsv
  simpa only [hpv, hnv, Pi.sub_apply] using hsv.symm

variable {q d : ℕ}

/-- If [the noise tail is regularly varying](hyp:hRV), [the model’s conditional mean version is valid](hyp:hMean), [the set is measurable from covariates, treatment, and latent variables](hyp:hS), and [the normalized outcome is integrable on that set under the tail law](hyp:hY), then [the set integral of the normalized realized regression equals that of the normalized outcome](goal).

@node: normalized_observed_mean_setIntegral -/
lemma normalized_observed_mean_setIntegral (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hMean : ConditionalMeanVersion M) (t : ℝ)
    (S : Set M.Om) (hS : MeasurableSet[sigmaXDU M] S)
    (hY : IntegrableOn (fun v => M.Y v / radius M v ^ M.alpha) S (tailLaw M t)) :
    (∫ v in S, M.f (M.X v) (M.D v) (M.U v) / radius M v ^ M.alpha
      ∂tailLaw M t) = ∫ v in S, M.Y v / radius M v ^ M.alpha ∂tailLaw M t := by
  have hle : sigmaXDU M ≤ M.measurableSpace :=
    (M.measurable_X.prodMk (M.measurable_D.prodMk M.measurable_U)).comap_le
  have hpair : Measurable[sigmaXDU M] (fun v => (M.X v, M.D v, M.U v)) :=
    Measurable.of_comap_le le_rfl
  let H : M.Om → ℝ := S.indicator (fun v => (radius M v ^ M.alpha)⁻¹)
  have hHm : Measurable[sigmaXDU M] H := by
    first | fun_prop | skip
    exact ((measurable_l1Norm.comp hpair.snd.snd).pow_const M.alpha).inv.indicator hS
  have hrep (Z : M.Om → ℝ) : (fun v => H v * Z v) =
      S.indicator (fun v => Z v / radius M v ^ M.alpha) := by
    funext v
    by_cases hv : v ∈ S <;> simp [H, hv, div_eq_mul_inv, mul_comm]
  have hYi : Integrable (fun v => H v * M.Y v) (tailLaw M t) := by
    rw [hrep]
    exact (integrable_indicator_iff (hle _ hS)).mpr hY
  have hEq := (weighted_observed_mean_integral_tailLaw M hRV hMean t H hHm hYi).2
  rw [hrep, hrep, integral_indicator (hle _ hS), integral_indicator (hle _ hS)] at hEq
  exact hEq

/-- [The selected signed, truncated tail-regression component evaluated at an observation equals the conditional expectation of the corresponding truncated normalized outcome](goal).

@node: tail_regression_part_comp_eq_condExp -/
lemma tail_regression_part_comp_eq_condExp (M : ExtremeModel q d) (t : ℝ)
    (negative : Bool) (k : ℕ) :
    (fun v => tailRegressionPart M t negative k (M.X v, M.D v, direction M v)) =
      (tailLaw M t)[(fun v => min (max (if negative then
        -(M.Y v / radius M v ^ M.alpha) else M.Y v / radius M v ^ M.alpha) 0)
          (k : ℝ)) | MeasurableSpace.comap
            (fun v => (M.X v, M.D v, direction M v)) inferInstance] := by
  exact (Classical.choose_spec (stronglyMeasurable_condExp
    (μ := tailLaw M t)
    (f := fun v => min (max (if negative then -(M.Y v / radius M v ^ M.alpha)
      else M.Y v / radius M v ^ M.alpha) 0) (k : ℝ))
    (m := MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v)) inferInstance)
      |>.exists_eq_measurable_comp)).2.symm

/-- If [the noise tail is regularly varying](hyp:hRV), [the regression equals the tail conditional regression almost surely](hyp:hreg), [the localization set is measurable from covariates, treatment, and direction](hyp:hS), and [the normalized outcome is integrable on that set](hyp:hY), then [on that set, the tail regression is almost surely the conditional expectation of the normalized outcome given covariates, treatment, and direction](goal).

@node: tail_regression_eq_condExp_on_integrable_set -/
lemma tail_regression_eq_condExp_on_integrable_set (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (t : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hreg : IsTailRegressionVersion M t reg) (S : Set M.Om)
    (hS : MeasurableSet[MeasurableSpace.comap
      (fun v => (M.X v, M.D v, direction M v)) inferInstance] S)
    (hY : IntegrableOn (fun v => M.Y v / radius M v ^ M.alpha) S (tailLaw M t)) :
    (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[(tailLaw M t).restrict S]
      ((tailLaw M t).restrict S)[(fun v => M.Y v / radius M v ^ M.alpha) |
        MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v)) inferInstance] := by
  let := tailLaw_probability M hRV t
  let G := MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v)) inferInstance
  have hle : G ≤ M.measurableSpace :=
    (M.measurable_X.prodMk (M.measurable_D.prodMk (measurable_direction M))).comap_le
  let H : Bool → M.Om → ℝ := fun b v => limUnder atTop
    (fun k => tailRegressionPart M t b k (M.X v, M.D v, direction M v))
  have hHm (b : Bool) : Measurable[G] (H b) := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.limUnder
    intro k
    rw [tail_regression_part_comp_eq_condExp]
    exact stronglyMeasurable_condExp
  have hlim (b : Bool) : ∀ᵐ v ∂(tailLaw M t).restrict S, Tendsto
      (fun k : ℕ => ((tailLaw M t).restrict S)[(fun v => min
        (max (if b then -(M.Y v / radius M v ^ M.alpha)
          else M.Y v / radius M v ^ M.alpha) 0) (k : ℝ)) | G] v)
      atTop (𝓝 (H b v)) := by
    have hEq := ae_all_iff.mpr (fun k : ℕ =>
      condExp_restrict_ae_eq_restrict (m0 := M.measurableSpace) hle hS
        (@integrable_sign_truncation M.Om M.measurableSpace (tailLaw M t) _ _
          (M.measurable_Y.div ((measurable_radius M).pow_const M.alpha)) b k))
    have hDefined := ae_restrict_of_ae (s := S) hreg.2.1
    filter_upwards [hEq, hDefined] with v hv hd
    have hex : ∃ l : ℝ, Tendsto (fun k => tailRegressionPart M t b k
        (M.X v, M.D v, direction M v)) atTop (𝓝 l) := by
      cases b
      · exact hd.1
      · exact hd.2
    obtain ⟨l, hl⟩ := hex
    change Tendsto _ atTop (𝓝 (limUnder atTop _))
    rw [hl.limUnder_eq]
    apply hl.congr
    intro k
    exact (congrFun (tail_regression_part_comp_eq_condExp M t b k) v).trans
      (hv k).symm
  have hSigned := @conditional_signed_limits_eq_condExp M.Om M.measurableSpace
    ((tailLaw M t).restrict S) _ G hle
    (fun v => M.Y v / radius M v ^ M.alpha) (H false) (H true) hY
    (hHm false) (hHm true) (hlim false) (hlim true)
  have hVersion : (fun v => reg (M.X v, M.D v, direction M v))
      =ᵐ[(tailLaw M t).restrict S] (fun v => H false v - H true v) :=
    ae_restrict_of_ae hreg.2.2
  exact hVersion.trans hSigned

/-- If [the noise tail is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the conditional mean version is valid](hyp:hMean), [the regression envelope is bounded](hyp:hG), [the threshold is positive](hyp:ht), [the tail envelope is bounded above beyond it](hyp:hb), [the candidate regression is measurable, the tail regression at this threshold is defined, and the candidate agrees with it almost surely under the tail law at the observed covariates, treatment and direction](hyp:hreg), [the localization set is measurable from covariates, treatment, and direction](hyp:hS), and [the normalized outcome is integrable there](hyp:hY), then [on that set the tail regression is almost surely the conditional expectation of the normalized realized regression given covariates, treatment, and direction](goal).

@node: tail_regression_projection_on_integrable_set -/
lemma tail_regression_projection_on_integrable_set (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hreg : IsTailRegressionVersion M t reg) (S : Set M.Om)
    (hS : MeasurableSet[MeasurableSpace.comap
      (fun v => (M.X v, M.D v, direction M v)) inferInstance] S)
    (hY : IntegrableOn (fun v => M.Y v / radius M v ^ M.alpha) S (tailLaw M t)) :
    (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[(tailLaw M t).restrict S]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) | MeasurableSpace.comap
          (fun v => (M.X v, M.D v, direction M v)) inferInstance] := by
  let := tailLaw_probability M hRV t
  let G := MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v)) inferInstance
  have hle : G ≤ M.measurableSpace :=
    (M.measurable_X.prodMk (M.measurable_D.prodMk (measurable_direction M))).comap_le
  have hFine : G ≤ sigmaXDU M := by
    have hz : Measurable[sigmaXDU M] (fun v => (M.X v, M.D v, M.U v)) :=
      Measurable.of_comap_le le_rfl
    have hdir : Measurable[sigmaXDU M] (direction M) := by
      first | fun_prop | skip
      let : MeasurableSpace M.Om := sigmaXDU M
      unfold direction radius
      apply measurable_pi_iff.mpr
      intro i
      exact ((measurable_pi_apply i).comp hz.snd.snd).div
        (measurable_l1Norm.comp hz.snd.snd)
    exact (hz.fst.prodMk (hz.snd.fst.prodMk hdir)).comap_le
  have hf := normalized_realized_regression_tail_integrable M hRV hX hHom hMean hG ht hb
  have hEq : ((tailLaw M t).restrict S)[(fun v => M.Y v / radius M v ^ M.alpha) | G]
      =ᵐ[(tailLaw M t).restrict S]
      ((tailLaw M t).restrict S)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) | G] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hle hf.restrict
      (fun _ _ _ => integrable_condExp.integrableOn) _
      stronglyMeasurable_condExp.aestronglyMeasurable
    intro A hA _
    rw [setIntegral_condExp hle hY hA]
    rw [Measure.restrict_restrict (hle _ hA)]
    exact (normalized_observed_mean_setIntegral M hRV hMean t (A ∩ S)
      ((hFine _ hA).inter (hFine _ hS)) (hY.mono_set Set.inter_subset_right)).symm
  have hRestrict := condExp_restrict_ae_eq_restrict (m0 := M.measurableSpace) hle hS hf
  exact (tail_regression_eq_condExp_on_integrable_set M hRV t reg hreg S hS hY).trans
    (hEq.trans hRestrict)

/-- If [the noise tail is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the conditional mean version is valid](hyp:hMean), [the regression envelope is bounded](hyp:hG), [the threshold is positive](hyp:ht), [the tail envelope is bounded above beyond it](hyp:hb), [the candidate regression is measurable, the tail regression at this threshold is defined, and the candidate agrees with it almost surely under the tail law at the observed covariates, treatment and direction](hyp:hreg), [every set in the localization sequence is measurable from covariates, treatment, and direction](hyp:hS), [these sets cover almost every tail observation](hyp:hCover), and [the normalized outcome is integrable on each one](hyp:hY), then [the tail regression is almost surely the conditional expectation of the normalized realized regression](goal).

@node: tail_regression_projection_of_integrable_cover -/
lemma tail_regression_projection_of_integrable_cover (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hreg : IsTailRegressionVersion M t reg) (S : ℕ → Set M.Om)
    (hS : ∀ k, MeasurableSet[MeasurableSpace.comap
      (fun v => (M.X v, M.D v, direction M v)) inferInstance] (S k))
    (hCover : ∀ᵐ v ∂tailLaw M t, ∃ k, v ∈ S k)
    (hY : ∀ k, IntegrableOn (fun v => M.Y v / radius M v ^ M.alpha)
      (S k) (tailLaw M t)) :
    (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[tailLaw M t]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) | MeasurableSpace.comap
          (fun v => (M.X v, M.D v, direction M v)) inferInstance] := by
  have hle : MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v))
      inferInstance ≤ M.measurableSpace :=
    (M.measurable_X.prodMk (M.measurable_D.prodMk (measurable_direction M))).comap_le
  have hLocal := ae_all_iff.mpr (fun k => (ae_restrict_iff' (hle _ (hS k))).mp
    (tail_regression_projection_on_integrable_set M hRV hX hHom hMean hG ht hb
      reg hreg (S k) (hS k) (hY k)))
  filter_upwards [hLocal, hCover] with v hv hc
  obtain ⟨k, hk⟩ := hc
  exact hv k hk

/-- If [the conditioning sigma-algebra is contained in the ambient one](hyp:hG), [the nonnegative outcome is measurable](hyp:hY), [it is everywhere nonnegative](hyp:hYn), [the localization set is conditioning-measurable](hyp:hS), and [every truncated conditional expectation is uniformly bounded on that set](hyp:hBound), then [the outcome is integrable on the set](goal).

@node: integrableOn_of_conditional_truncation_bound -/
lemma integrableOn_of_conditional_truncation_bound {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {G : MeasurableSpace Ω} (hG : G ≤ mΩ) (Y : Ω → ℝ) (hY : Measurable[mΩ] Y)
    (hYn : ∀ v, 0 ≤ Y v) (S : Set Ω) (hS : MeasurableSet[G] S) (C : ℝ)
    (hBound : ∀ k : ℕ, ∀ᵐ v ∂μ.restrict S,
      μ[(fun v => min (Y v) (k : ℝ)) | G] v ≤ C) :
    IntegrableOn Y S μ := by
  let F : ℕ → Ω → ℝ := fun k v => min (Y v) (k : ℝ)
  have hF (k : ℕ) : Integrable (F k) μ := by
    have hm : Measurable[mΩ] (F k) := hY.min measurable_const
    apply Integrable.of_bound (hm.aestronglyMeasurable (μ := μ)) (k : ℝ)
    exact Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hYn v) (Nat.cast_nonneg k))]
      exact min_le_right _ _
  have hIntBound (k : ℕ) : (∫⁻ v, ENNReal.ofReal (F k v) ∂μ.restrict S) ≤
      ENNReal.ofReal (C * μ.real S) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hF k).restrict
      (Eventually.of_forall fun v => le_min (hYn v) (Nat.cast_nonneg k))]
    apply ENNReal.ofReal_le_ofReal
    rw [← setIntegral_condExp hG (hF k) hS]
    calc
      _ ≤ ∫ _ in S, C ∂μ := integral_mono_ae integrable_condExp.restrict
        (integrable_const _) (hBound k)
      _ = _ := by simp [measureReal_def, mul_comm]
  have hlim (v : Ω) : Tendsto (fun k => ENNReal.ofReal (F k v)) atTop
      (𝓝 (ENNReal.ofReal (Y v))) := by
    apply ENNReal.tendsto_ofReal
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Y v))]
      with k hk
    exact (min_eq_left hk).symm
  have hfatou : (∫⁻ v, ENNReal.ofReal (Y v) ∂μ.restrict S) ≤
      liminf (fun k => ∫⁻ v, ENNReal.ofReal (F k v) ∂μ.restrict S) atTop := by
    have heq : (fun v => liminf (fun k => ENNReal.ofReal (F k v)) atTop) =
        fun v => ENNReal.ofReal (Y v) := funext fun v => (hlim v).liminf_eq
    rw [← heq]
    apply lintegral_liminf_le'
    intro k
    have hm : Measurable[mΩ] (F k) := hY.min measurable_const
    exact hm.ennreal_ofReal.aemeasurable
  refine ⟨hY.aestronglyMeasurable (μ := μ.restrict S), ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hYn)).mpr
  have hL := liminf_le_of_frequently_le'
    (Frequently.of_forall (f := atTop) hIntBound)
  exact lt_of_le_of_lt (hfatou.trans hL) ENNReal.ofReal_lt_top

/-- If [the noise tail is regularly varying](hyp:hRV) and [the tail-regression limits are defined almost surely](hyp:hDefined), then [there is a countable measurable cover of almost every tail observation on whose every set the normalized outcome is integrable](goal).

@node: tail_regression_integrable_cover -/
lemma tail_regression_integrable_cover (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) (hDefined : TailRegressionDefined M t) :
    ∃ S : ℕ → Set M.Om,
      (∀ k, MeasurableSet[MeasurableSpace.comap
        (fun v => (M.X v, M.D v, direction M v)) inferInstance] (S k)) ∧
      (∀ᵐ v ∂tailLaw M t, ∃ k, v ∈ S k) ∧
      ∀ k, IntegrableOn (fun v => M.Y v / radius M v ^ M.alpha) (S k) (tailLaw M t) := by
  let := tailLaw_probability M hRV t
  let G := MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v)) inferInstance
  let S : ℕ → Set M.Om := fun k => {v | ∀ b : Bool, ∀ j : ℕ,
    tailRegressionPart M t b j (M.X v, M.D v, direction M v) ≤ (k : ℝ)}
  have hle : G ≤ M.measurableSpace :=
    (M.measurable_X.prodMk (M.measurable_D.prodMk (measurable_direction M))).comap_le
  have hSm (k : ℕ) : MeasurableSet[G] (S k) := by
    dsimp only [S]
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro b
    apply MeasurableSet.iInter
    intro j
    have hm : Measurable[G] (fun v =>
        tailRegressionPart M t b j (M.X v, M.D v, direction M v)) := by
      rw [tail_regression_part_comp_eq_condExp]
      exact stronglyMeasurable_condExp.measurable
    exact measurableSet_le hm measurable_const
  refine ⟨S, hSm, ?_, ?_⟩
  · filter_upwards [hDefined] with v hv
    obtain ⟨p, hp⟩ := hv.1
    obtain ⟨n, hn⟩ := hv.2
    obtain ⟨Cp, hCp⟩ := hp.bddAbove_range
    obtain ⟨Cn, hCn⟩ := hn.bddAbove_range
    obtain ⟨k, hk⟩ := exists_nat_ge (max Cp Cn)
    refine ⟨k, ?_⟩
    intro b j
    cases b
    · exact (hCp (Set.mem_range_self j)).trans ((le_max_left _ _).trans hk)
    · exact (hCn (Set.mem_range_self j)).trans ((le_max_right _ _).trans hk)
  · intro k
    have hi (b : Bool) : IntegrableOn (fun v =>
        max (if b then -(M.Y v / radius M v ^ M.alpha)
          else M.Y v / radius M v ^ M.alpha) 0) (S k) (tailLaw M t) := by
      have hm : Measurable[M.measurableSpace] (fun v => max
          (if b then -(M.Y v / radius M v ^ M.alpha)
            else M.Y v / radius M v ^ M.alpha) 0) := by
        first | fun_prop | skip
        have hy := M.measurable_Y.div ((measurable_radius M).pow_const M.alpha)
        cases b
        · exact hy.max measurable_const
        · exact hy.neg.max measurable_const
      apply @integrableOn_of_conditional_truncation_bound M.Om M.measurableSpace
        (tailLaw M t) _ G hle _ hm (fun _ => le_max_right _ _) (S k) (hSm k) (k : ℝ)
      intro j
      filter_upwards [ae_restrict_mem (μ := tailLaw M t) (hle _ (hSm k))] with v hv
      have hb := hv b j
      rw [congrFun (tail_regression_part_comp_eq_condExp M t b j) v] at hb
      exact hb
    have hInt := (hi false).sub (hi true)
    apply hInt.congr
    exact Eventually.of_forall fun v => by
      simp only [Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]
      rcases le_total 0 (M.Y v / radius M v ^ M.alpha) with hv | hv
      · rw [max_eq_left hv, max_eq_right (neg_nonpos.mpr hv), sub_zero]
      · rw [max_eq_right hv, max_eq_left (neg_nonneg.mpr hv)]
        ring

/-- If [the noise tail is regularly varying](hyp:hRV), [covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the conditional mean version is valid](hyp:hMean), [the regression envelope is bounded](hyp:hG), [the threshold is positive](hyp:ht), [the tail envelope is bounded above beyond it](hyp:hb), and [the candidate regression is measurable, the tail regression at this threshold is defined, and the candidate agrees with it almost surely under the tail law at the observed covariates, treatment and direction](hyp:hreg), then [the tail regression is almost surely the conditional expectation of the normalized realized regression given covariates, treatment, and direction](goal).

@node: tail_regression_normalized_projection -/
lemma tail_regression_normalized_projection (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hreg : IsTailRegressionVersion M t reg) :
    (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[tailLaw M t]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) | MeasurableSpace.comap
          (fun v => (M.X v, M.D v, direction M v)) inferInstance] := by
  obtain ⟨S, hS, hCover, hY⟩ := tail_regression_integrable_cover M hRV t hreg.2.1
  exact tail_regression_projection_of_integrable_cover M hRV hX hHom hMean hG ht hb
    reg hreg S hS hCover hY

end Papers.TbsExtremeEffects
