module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Papers.TbsExtremeEffects.Helpers.RegressionPositivity
public import Papers.TbsExtremeEffects.Helpers.RegularVariation
public import Toolkit.Foundations.Probability.Conditioning.ConditioningOnEvent

/-! Treatment probabilities after conditioning on a radial exceedance. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {q d : ℕ}

-- @node: propensity_condExp_tail_given_XU
/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV) and [noise independent of treatment given covariates](hyp:hNoise), [the conditional expectation of the treatment indicator under a tail law, given covariates and noise, equals the propensity score almost everywhere](goal). -/
lemma propensity_condExp_tail_given_XU (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M) (t : ℝ) :
    (tailLaw M t)[(fun w => if M.D w then (1 : ℝ) else 0) | sigmaXU M]
      =ᵐ[tailLaw M t] (fun w => M.p (M.X w)) := by
  have hG : sigmaXU M ≤ M.measurableSpace :=
    (M.measurable_X.prodMk M.measurable_U).comap_le
  have hA : MeasurableSet[sigmaXU M] {w | t < radius M w} := by
    refine ⟨{z : (Fin q → ℝ) × (Fin d → ℝ) | t < l1Norm z.2}, ?_, rfl⟩
    exact measurableSet_lt measurable_const (measurable_l1Norm.comp measurable_snd)
  have hpos : M.mu {w | t < radius M w} ≠ 0 := by
    intro hz
    have hp := tailProb_pos_of_regularVariation M hRV t
    simp only [tailProb, hz, ENNReal.toReal_zero] at hp
    exact (lt_irrefl 0) hp
  have hi : Integrable (fun w => if M.D w then (1 : ℝ) else 0) M.mu := by
    have hm : Measurable (fun w => if M.D w then (1 : ℝ) else 0) :=
      measurable_const.ite (M.measurable_D (measurableSet_singleton true)) measurable_const
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall fun w => by cases M.D w <;> norm_num
  exact (Toolkit.Foundations.Probability.Conditioning.condExp_cond_ae_eq_condExp_of_measurableSet M.mu hG hA hpos hi).trans
    (cond_absolutelyContinuous.ae_le (propensity_condExp_given_XU M hNoise))

-- @node: treatment_condExp_tail_given_XU
/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV) and [noise independent of treatment given covariates](hyp:hNoise), [the conditional expectation of a specified treatment indicator under a tail law, given covariates and noise, equals its propensity or its complement almost everywhere](goal). -/
lemma treatment_condExp_tail_given_XU (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M) (t : ℝ) (a : Bool) :
    (tailLaw M t)[({w | M.D w = a}).indicator (fun _ => (1 : ℝ)) | sigmaXU M]
      =ᵐ[tailLaw M t] (fun w => if a then M.p (M.X w) else 1 - M.p (M.X w)) := by
  let := tailLaw_probability M hRV t
  have hG : sigmaXU M ≤ M.measurableSpace :=
    (M.measurable_X.prodMk M.measurable_U).comap_le
  have hi : Integrable (fun w => if M.D w then (1 : ℝ) else 0) (tailLaw M t) := by
    have hm : Measurable (fun w => if M.D w then (1 : ℝ) else 0) :=
      measurable_const.ite (M.measurable_D (measurableSet_singleton true)) measurable_const
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall fun w => by cases M.D w <;> norm_num
  have hp := propensity_condExp_tail_given_XU M hRV hNoise t
  cases a
  · have heq : ({w | M.D w = false}).indicator (fun _ => (1 : ℝ)) =
        (fun _ => (1 : ℝ)) - (fun w => if M.D w then (1 : ℝ) else 0) := by
      funext w
      cases h : M.D w <;> simp [h]
    rw [heq]
    have hc := condExp_sub (m := sigmaXU M) (integrable_const (1 : ℝ)) hi
    filter_upwards [hc, hp] with w hc hp
    simpa only [Pi.sub_apply, condExp_const hG, hp, Bool.false_eq_true, ↓reduceIte] using hc
  · have heq : ({w | M.D w = true}).indicator (fun _ => (1 : ℝ)) =
        (fun w => if M.D w then (1 : ℝ) else 0) := by
      funext w
      cases h : M.D w <;> simp [h]
    rw [heq]
    exact hp

/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV), [noise independent of treatment given covariates](hyp:hNoise), [a weight measurable from covariates and noise](hyp:hm), and [an integrable weighted treatment-indicator product](hyp:hi), [the product formed with the corresponding propensity is integrable and has the same tail-law integral](goal).

Replace a treatment indicator by its conditional probability, allowing an unbounded weight. Only the treated product needs to be integrable. -/
-- @node: treatment_weighted_integral_tail
lemma treatment_weighted_integral_tail (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M) (t : ℝ) (a : Bool)
    (h : M.Om → ℝ) (hm : Measurable[sigmaXU M] h)
    (hi : Integrable (fun v => h v * ({v | M.D v = a}).indicator
      (fun _ => (1 : ℝ)) v) (tailLaw M t)) :
    Integrable (fun v => h v * (if a then M.p (M.X v) else 1 - M.p (M.X v)))
      (tailLaw M t) ∧
    (∫ v, h v * ({v | M.D v = a}).indicator (fun _ => (1 : ℝ)) v ∂tailLaw M t) =
      ∫ v, h v * (if a then M.p (M.X v) else 1 - M.p (M.X v)) ∂tailLaw M t := by
  let := tailLaw_probability M hRV t
  have hG : sigmaXU M ≤ M.measurableSpace :=
    (M.measurable_X.prodMk M.measurable_U).comap_le
  have hInd : Integrable (({v | M.D v = a}).indicator (fun _ => (1 : ℝ)))
      (tailLaw M t) :=
    (integrable_const (1 : ℝ)).indicator (M.measurable_D (measurableSet_singleton a))
  have hc := condExp_mul_of_stronglyMeasurable_left hm.stronglyMeasurable hi hInd
  have heq := hc.trans ((treatment_condExp_tail_given_XU M hRV hNoise t a).mono
    (fun v hv => by simp only [Pi.mul_apply]; rw [hv]))
  refine ⟨integrable_condExp.congr heq, ?_⟩
  rw [← integral_condExp hG]
  exact integral_congr_ae heq

end Papers.TbsExtremeEffects
