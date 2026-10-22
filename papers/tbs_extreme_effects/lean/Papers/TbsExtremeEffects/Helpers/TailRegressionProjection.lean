module
public import Papers.TbsExtremeEffects.Helpers.ExponentScore
public import Papers.TbsExtremeEffects.Helpers.TailRegressionSections
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! Homogeneity bounds for the population tail regression after projection.
The generalized outcome-conditioning identity is kept separate from these
bounded, integrable population regression calculations. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {q d : ℕ}

-- @node: normalized_realized_regression_tail_bound
/-- For [an extreme-value model](hyp:M), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a valid regression bound](hyp:hG), [a positive tail threshold](hyp:ht), and [a bounded-above remainder on the relevant tail](hyp:hb), [the realized regression divided by the radial power is eventually bounded in absolute value under the tail law](goal). -/
lemma normalized_realized_regression_tail_bound (M : ExtremeModel q d)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) :
    ∀ᵐ v ∂tailLaw M t,
      |M.f (M.X v) (M.D v) (M.U v) / radius M v ^ M.alpha| ≤ C + eBar M t := by
  have hx : ∀ᵐ v ∂tailLaw M t, l1Norm (M.X v) ≤ M.R :=
    cond_absolutelyContinuous.ae_le hX.2
  filter_upwards [hx, ae_cond_mem (μ := M.mu)
    (measurableSet_lt measurable_const (measurable_radius M))] with v hxv hv
  exact normalized_regression_tail_bound M hHom hG ht hb v hxv hv (M.D v)

-- @node: normalized_realized_regression_tail_integrable
/-- For [an extreme-value model](hyp:M), [regularly varying noise](hyp:hRV), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional-mean version](hyp:hMean), [a valid regression bound](hyp:hG), [a positive tail threshold](hyp:ht), and [a bounded-above remainder on the relevant tail](hyp:hb), [the radial-power-normalized realized regression is integrable under the tail law](goal). -/
lemma normalized_realized_regression_tail_integrable (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t)) :
    Integrable (fun v => M.f (M.X v) (M.D v) (M.U v) /
      radius M v ^ M.alpha) (tailLaw M t) := by
  let := tailLaw_probability M hRV t
  have hm : Measurable (fun v => M.f (M.X v) (M.D v) (M.U v) /
      radius M v ^ M.alpha) := by
    try fun_prop
    exact (hMean.1.comp (M.measurable_X.prodMk
      (M.measurable_D.prodMk M.measurable_U))).div
        ((measurable_radius M).pow_const M.alpha)
  apply Integrable.of_bound hm.aestronglyMeasurable (C + eBar M t)
  simpa only [Real.norm_eq_abs] using
    normalized_realized_regression_tail_bound M hX hHom hG ht hb

-- @node: tail_regression_bound_of_normalized_projection
/-- For [an extreme-value model](hyp:M), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a valid regression bound](hyp:hG), [a positive tail threshold](hyp:ht), [a bounded-above remainder on the relevant tail](hyp:hb), and [a regression equal almost everywhere to the conditional projection of the normalized realized regression](hyp:hProjection), [that regression is eventually bounded in absolute value under the tail law](goal). -/
lemma tail_regression_bound_of_normalized_projection (M : ExtremeModel q d)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hProjection : (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[tailLaw M t]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) |
        MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v)) inferInstance]) :
    ∀ᵐ v ∂tailLaw M t, |reg (M.X v, M.D v, direction M v)| ≤ C + eBar M t := by
  have hbound := ae_bdd_abs_condExp_of_ae_bdd_abs
    (m := MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v)) inferInstance)
    (R := C + eBar M t)
    (normalized_realized_regression_tail_bound M hX hHom hG ht hb)
  filter_upwards [hProjection, hbound] with v hp hv
  rw [hp]
  exact hv

-- @node: normalized_projection_weighted_integral
/-- For [an extreme-value model](hyp:M), [regularly varying noise](hyp:hRV), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [a conditional-mean version](hyp:hMean), [a valid regression bound](hyp:hG), [a positive tail threshold](hyp:ht), [a bounded-above remainder on the relevant tail](hyp:hb), [a regression equal almost everywhere to the relevant conditional projection](hyp:hProjection), [a measurable weight](hyp:hH), and [an integrable product of that weight with the normalized realized regression](hyp:hProduct), [the weighted projected regression is integrable and has the same tail-law integral as the weighted normalized realized regression](goal). -/
lemma normalized_projection_weighted_integral (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) (hMean : ConditionalMeanVersion M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hProjection : (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[tailLaw M t]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) |
        MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v)) inferInstance])
    (H : M.Om → ℝ)
    (hH : Measurable[MeasurableSpace.comap
      (fun v => (M.X v, M.D v, direction M v)) inferInstance] H)
    (hProduct : Integrable (fun v => H v *
      (M.f (M.X v) (M.D v) (M.U v) / radius M v ^ M.alpha)) (tailLaw M t)) :
    Integrable (fun v => H v * reg (M.X v, M.D v, direction M v)) (tailLaw M t) ∧
      (∫ v, H v * reg (M.X v, M.D v, direction M v) ∂tailLaw M t) =
        ∫ v, H v * (M.f (M.X v) (M.D v) (M.U v) /
          radius M v ^ M.alpha) ∂tailLaw M t := by
  let := tailLaw_probability M hRV t
  have hle : MeasurableSpace.comap
      (fun v => (M.X v, M.D v, direction M v)) inferInstance ≤ M.measurableSpace :=
    (M.measurable_X.prodMk (M.measurable_D.prodMk (measurable_direction M))).comap_le
  have hf := normalized_realized_regression_tail_integrable M hRV hX hHom hMean hG ht hb
  have hpull := condExp_mul_of_stronglyMeasurable_left hH.stronglyMeasurable hProduct hf
  simp only [Pi.mul_def] at hpull
  have heq : (tailLaw M t)[(fun v => H v *
      (M.f (M.X v) (M.D v) (M.U v) / radius M v ^ M.alpha)) |
      MeasurableSpace.comap (fun v => (M.X v, M.D v, direction M v)) inferInstance]
      =ᵐ[tailLaw M t] (fun v => H v * reg (M.X v, M.D v, direction M v)) := by
    filter_upwards [hpull, hProjection] with v hp hr
    simpa only [Pi.mul_apply, ← hr] using hp
  refine ⟨integrable_condExp.congr heq, ?_⟩
  rw [← integral_congr_ae heq, integral_condExp hle]

end Papers.TbsExtremeEffects
