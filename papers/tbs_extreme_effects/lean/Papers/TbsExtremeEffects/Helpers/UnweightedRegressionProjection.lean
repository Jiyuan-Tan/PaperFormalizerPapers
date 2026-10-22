module
public import Papers.TbsExtremeEffects.Helpers.WeightedRegressionProjection
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Removing treatment probabilities from the population regression projection
by bounded reciprocal truncations and dominated convergence. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

-- @node: tendsto_integral_reciprocal_cutoff
/-- If [the treatment-probability function is measurable](hyp:hp), [it is positive almost everywhere](hyp:hpos), and [the target function is integrable](hyp:hf), then [integrating it with increasingly loose reciprocal-probability cutoffs converges to its ordinary integral](goal). -/
lemma tendsto_integral_reciprocal_cutoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p f : Ω → ℝ) (hp : Measurable p)
    (hpos : ∀ᵐ v ∂μ, 0 < p v) (hf : Integrable f μ) :
    Tendsto (fun k : ℕ => ∫ v, (1 / max (p v) (1 / ((k : ℝ) + 1))) *
      f v * p v ∂μ) atTop (𝓝 (∫ v, f v ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun v => ‖f v‖)
  · intro k
    exact ((measurable_const.div (hp.max measurable_const)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable).mul hp.aestronglyMeasurable
  · exact hf.norm
  · intro k
    filter_upwards [hpos] with v hv
    have hd : 0 < max (p v) (1 / ((k : ℝ) + 1)) := hv.trans_le (le_max_left _ _)
    have hq : 0 ≤ p v / max (p v) (1 / ((k : ℝ) + 1)) := div_nonneg hv.le hd.le
    have hq1 : p v / max (p v) (1 / ((k : ℝ) + 1)) ≤ 1 :=
      (div_le_one hd).mpr (le_max_left _ _)
    have heq : (1 / max (p v) (1 / ((k : ℝ) + 1))) * f v * p v =
        (p v / max (p v) (1 / ((k : ℝ) + 1))) * f v := by ring
    rw [heq, norm_mul, Real.norm_eq_abs, abs_of_nonneg hq]
    exact mul_le_of_le_one_left (norm_nonneg _) hq1
  · filter_upwards [hpos] with v hv
    have hmax : Tendsto (fun k : ℕ => max (p v) (1 / ((k : ℝ) + 1)))
        atTop (𝓝 (p v)) := by
      simpa only [max_eq_left hv.le] using
        (tendsto_const_nhds (x := p v)).max tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).div hmax hv.ne').mul_const
      (f v) |>.mul_const (p v)
    simpa [Pi.div_apply, one_div, mul_comm, mul_left_comm, mul_assoc, hv.ne'] using hlim

variable {q d : ℕ}

-- @node: tail_regression_section_integral_of_normalized_projection
/-- If [the noise is regularly varying](hyp:hRV), [the noise is independent](hyp:hNoise), [the covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the conditional mean is correctly represented](hyp:hMean), [the identification side conditions hold](hyp:hSide), [the regression bound holds](hyp:hG), [the tail threshold is positive](hyp:ht), [the tail-score range above it is bounded](hyp:hb), [the proposed regression is measurable](hyp:hreg), and [it is a normalized projection under the tail law](hyp:hProjection), then [the tail-law average of its section at either treatment equals the tail-law average of the corresponding normalized outcome regression](goal). -/
lemma tail_regression_section_integral_of_normalized_projection (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) (hSide : IdentificationSideConditions M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (hreg : Measurable reg)
    (hProjection : (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[tailLaw M t]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) | MeasurableSpace.comap
          (fun v => (M.X v, M.D v, direction M v)) inferInstance]) (a : Bool) :
    (∫ v, reg (M.X v, a, direction M v) ∂tailLaw M t) =
      ∫ v, M.f (M.X v) a (M.U v) / radius M v ^ M.alpha ∂tailLaw M t := by
  let p : M.Om → ℝ := fun v => if a then M.p (M.X v) else 1 - M.p (M.X v)
  have hp : Measurable p := by
    have hm := M.measurable_p.comp M.measurable_X
    cases a <;> dsimp [p] <;> fun_prop
  have hpos : ∀ᵐ v ∂tailLaw M t, 0 < p v := by
    filter_upwards [cond_absolutelyContinuous.ae_le hSide.1] with v hv
    cases a <;> dsimp [p] <;> linarith [hv.1, hv.2]
  have hr := tail_regression_sections_integrable_of_bound M hRV hNoise hSide t
    (C + eBar M t) reg hreg
    (tail_regression_bound_of_normalized_projection M hX hHom hG ht hb reg hProjection) a
  have hf := normalized_regression_section_tail_integrable M hRV hX hHom hMean hG ht hb a
  have hleft := tendsto_integral_reciprocal_cutoff (tailLaw M t) p _ hp hpos hr
  have hright := tendsto_integral_reciprocal_cutoff (tailLaw M t) p _ hp hpos hf
  have heq : (fun k : ℕ => ∫ v, (1 / max (p v) (1 / ((k : ℝ) + 1))) *
      reg (M.X v, a, direction M v) * p v ∂tailLaw M t) =
      (fun k : ℕ => ∫ v, (1 / max (p v) (1 / ((k : ℝ) + 1))) *
      (M.f (M.X v) a (M.U v) / radius M v ^ M.alpha) * p v ∂tailLaw M t) := by
    funext k
    let W : ((Fin q → ℝ) × (Fin d → ℝ)) → ℝ := fun z =>
      1 / max (if a then M.p z.1 else 1 - M.p z.1) (1 / ((k : ℝ) + 1))
    have hW : Measurable W := by
      have hm := M.measurable_p.comp
        (measurable_fst : Measurable (Prod.fst : ((Fin q → ℝ) × (Fin d → ℝ)) → _))
      cases a <;> dsimp [W] <;> fun_prop
    have hbound : ∀ᵐ v ∂tailLaw M t, ‖W (M.X v, direction M v)‖ ≤ (k : ℝ) + 1 := by
      apply Eventually.of_forall
      intro v
      have hk : 0 < (k : ℝ) + 1 := by positivity
      have hd : 0 < max (p v) (1 / ((k : ℝ) + 1)) :=
        (one_div_pos.mpr hk).trans_le (le_max_right _ _)
      change ‖1 / max (p v) (1 / ((k : ℝ) + 1))‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd)]
      calc
        _ ≤ 1 / (1 / ((k : ℝ) + 1)) :=
          one_div_le_one_div_of_le (one_div_pos.mpr hk) (le_max_right _ _)
        _ = _ := one_div_one_div _
    have hwm : AEStronglyMeasurable (fun v => W (M.X v, direction M v)) (tailLaw M t) :=
      (hW.comp (M.measurable_X.prodMk (measurable_direction M))).aestronglyMeasurable
    exact treatment_weighted_regression_projection M hRV hNoise hX hHom hMean hG ht hb
      reg hreg hProjection W hW a (hf.bdd_mul hwm hbound) (hr.bdd_mul hwm hbound)
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

-- @node: tail_regression_contrast_integral_of_normalized_projection
/-- If [the noise is regularly varying](hyp:hRV), [the noise is independent](hyp:hNoise), [the covariates are bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the conditional mean is correctly represented](hyp:hMean), [the identification side conditions hold](hyp:hSide), [the regression bound holds](hyp:hG), [the tail threshold is positive](hyp:ht), [the tail-score range above it is bounded](hyp:hb), [the proposed regression is measurable](hyp:hreg), and [it is a normalized projection under the tail law](hyp:hProjection), then [the tail-law average of its treatment contrast equals the tail-law average of the normalized regression contrast](goal). -/
lemma tail_regression_contrast_integral_of_normalized_projection (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hMean : ConditionalMeanVersion M) (hSide : IdentificationSideConditions M)
    {C t : ℝ} (hG : GBound M C) (ht : 0 < t)
    (hb : BddAbove (M.e '' Set.Ici t))
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (hreg : Measurable reg)
    (hProjection : (fun v => reg (M.X v, M.D v, direction M v)) =ᵐ[tailLaw M t]
      (tailLaw M t)[(fun v => M.f (M.X v) (M.D v) (M.U v) /
        radius M v ^ M.alpha) | MeasurableSpace.comap
          (fun v => (M.X v, M.D v, direction M v)) inferInstance]) :
    (∫ v, reg (M.X v, true, direction M v) -
      reg (M.X v, false, direction M v) ∂tailLaw M t) =
      ∫ v, normalizedRegressionContrast M v ∂tailLaw M t := by
  have hr := tail_regression_sections_integrable_of_bound M hRV hNoise hSide t
    (C + eBar M t) reg hreg
    (tail_regression_bound_of_normalized_projection M hX hHom hG ht hb reg hProjection)
  have hf := normalized_regression_section_tail_integrable M hRV hX hHom hMean hG ht hb
  have heq := tail_regression_section_integral_of_normalized_projection M hRV hNoise
    hX hHom hMean hSide hG ht hb reg hreg hProjection
  rw [integral_sub (hr true) (hr false), heq true, heq false]
  rw [← integral_sub (hf true) (hf false)]
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    simp only [normalizedRegressionContrast, sub_div]

end Papers.TbsExtremeEffects
