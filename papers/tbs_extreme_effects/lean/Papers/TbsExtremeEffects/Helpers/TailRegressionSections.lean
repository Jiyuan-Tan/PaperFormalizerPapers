module
public import Papers.TbsExtremeEffects.Helpers.TailTreatment

/-! Weak treatment overlap transfers a bound on the realized regression to
both treatment sections. No reciprocal propensity moment is needed. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

-- @node: ae_bound_of_bound_on_event_of_conditional_positive
/-- If [the conditioning sigma-algebra is contained in the ambient one](hyp:hG), [the event is measurable](hyp:hE), [the function is measurable for the conditioning sigma-algebra](hyp:hf), [the event has positive conditional probability almost everywhere](hyp:hpos), and [the function is almost everywhere bounded on that event](hyp:hbound), then [the function is almost everywhere bounded everywhere](goal). -/
lemma ae_bound_of_bound_on_event_of_conditional_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ)
    {E : Set Ω} (hE : @MeasurableSet Ω mΩ E) {f : Ω → ℝ} {C : ℝ}
    (hf : Measurable[G] f)
    (hpos : ∀ᵐ w ∂μ, 0 < μ[E.indicator (fun _ => (1 : ℝ)) | G] w)
    (hbound : ∀ᵐ w ∂μ, w ∈ E → |f w| ≤ C) :
    ∀ᵐ w ∂μ, |f w| ≤ C := by
  let : MeasurableSpace Ω := mΩ
  have hmax : Measurable[G] (fun w => max (|f w| - C) 0) := by
    fun_prop
  have hz : (fun w => max (|f w| - C) 0) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    apply ae_eq_of_eq_on_event_of_conditional_positive μ hG hE
      hmax measurable_const hpos
    filter_upwards [hbound] with w hw he
    exact max_eq_right (sub_nonpos.mpr (hw he))
  filter_upwards [hz] with w hw
  have hh := le_max_left (|f w| - C) 0
  rw [hw] at hh
  exact sub_nonpos.mp hh

variable {q d : ℕ}

-- @node: treatment_conditional_positive_tail
/-- For [an extreme-value model](hyp:M), [regularly varying noise](hyp:hRV), [noise independent of treatment given covariates](hyp:hNoise), and [the identification side conditions](hyp:hSide), [each treatment group has positive conditional probability almost everywhere under every tail law](goal). -/
lemma treatment_conditional_positive_tail (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hSide : IdentificationSideConditions M) (t : ℝ) (a : Bool) :
    ∀ᵐ w ∂tailLaw M t,
      0 < (tailLaw M t)[({w | M.D w = a}).indicator (fun _ => (1 : ℝ)) |
        sigmaXU M] w := by
  have hp := treatment_condExp_tail_given_XU M hRV hNoise t a
  have hs : ∀ᵐ w ∂tailLaw M t, 0 < M.p (M.X w) ∧ M.p (M.X w) < 1 :=
    cond_absolutelyContinuous.ae_le hSide.1
  filter_upwards [hp, hs] with w hw hs
  rw [hw]
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    linarith [hs.2]
  · exact hs.1

-- @node: tail_regression_section_bound
/-- For [an extreme-value model](hyp:M), [regularly varying noise](hyp:hRV), [noise independent of treatment given covariates](hyp:hNoise), [the identification side conditions](hyp:hSide), [a measurable regression](hyp:hreg), and [an almost-everywhere bound on its realized-treatment values](hyp:hbound), [the same bound holds almost everywhere for either fixed treatment section under the tail law](goal). -/
lemma tail_regression_section_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hSide : IdentificationSideConditions M) (t C : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hreg : Measurable reg)
    (hbound : ∀ᵐ w ∂tailLaw M t, |reg (M.X w, M.D w, direction M w)| ≤ C)
    (a : Bool) :
    ∀ᵐ w ∂tailLaw M t, |reg (M.X w, a, direction M w)| ≤ C := by
  let := tailLaw_probability M hRV t
  have hG : sigmaXU M ≤ M.measurableSpace :=
    (M.measurable_X.prodMk M.measurable_U).comap_le
  have hpair : Measurable[sigmaXU M] (fun w => (M.X w, M.U w)) :=
    Measurable.of_comap_le le_rfl
  have hdir : Measurable[sigmaXU M] (direction M) := by
    have hU : Measurable[sigmaXU M] M.U := hpair.snd
    unfold direction radius
    fun_prop
  have hm : Measurable[sigmaXU M] (fun w => reg (M.X w, a, direction M w)) := by
    exact hreg.comp (hpair.fst.prodMk (measurable_const.prodMk hdir))
  apply ae_bound_of_bound_on_event_of_conditional_positive (tailLaw M t) hG
    (M.measurable_D (measurableSet_singleton a)) hm
    (treatment_conditional_positive_tail M hRV hNoise hSide t a)
  filter_upwards [hbound] with w hw ha
  change M.D w = a at ha
  rw [ha] at hw
  exact hw

-- @node: tail_regression_sections_integrable_of_bound
/-- For [an extreme-value model](hyp:M), [regularly varying noise](hyp:hRV), [noise independent of treatment given covariates](hyp:hNoise), [the identification side conditions](hyp:hSide), [a measurable regression](hyp:hreg), and [an almost-everywhere bound on its realized-treatment values](hyp:hbound), [both fixed-treatment regression sections are integrable under the tail law](goal). -/
lemma tail_regression_sections_integrable_of_bound (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hSide : IdentificationSideConditions M) (t C : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ)
    (hreg : Measurable reg)
    (hbound : ∀ᵐ w ∂tailLaw M t, |reg (M.X w, M.D w, direction M w)| ≤ C) :
    ∀ a : Bool, Integrable (fun w => reg (M.X w, a, direction M w)) (tailLaw M t) := by
  let := tailLaw_probability M hRV t
  intro a
  have hm : Measurable (fun w => reg (M.X w, a, direction M w)) := by
    exact hreg.comp (M.measurable_X.prodMk (measurable_const.prodMk (measurable_direction M)))
  apply Integrable.of_bound hm.aestronglyMeasurable C
  simpa only [Real.norm_eq_abs] using
    tail_regression_section_bound M hRV hNoise hSide t C reg hreg hbound a

end Papers.TbsExtremeEffects
