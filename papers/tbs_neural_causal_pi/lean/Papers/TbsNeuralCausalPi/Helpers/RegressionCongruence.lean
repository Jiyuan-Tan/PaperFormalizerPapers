module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
/-! # Regression versions under almost sure changes of the covariates -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter

/-- Suppose [the original covariates are measurable](hyp:hs), [the replacement
covariates are measurable](hyp:hs'), [the two covariates agree almost surely](hyp:heq),
[the original outcome is integrable](hyp:hY), and [the replacement outcome
agrees with it almost surely](hyp:hYY). If [the replacement regression function
is measurable](hyp:hf'), [the two evaluated regressions agree almost surely](hyp:hff),
and [the original evaluated regression is the conditional mean of the original
outcome given the original covariates](hyp:hreg), then [the replacement evaluated
regression is almost surely the conditional mean of the replacement outcome
given the replacement covariates](goal). -/
-- @node: regression_version_congr_ae
lemma regression_version_congr_ae
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s s' : Ω → X)
    (hs : Measurable s) (hs' : Measurable s') (heq : s =ᵐ[μ] s')
    (Y Y' : Ω → ℝ) (hY : Integrable Y μ) (hYY : Y =ᵐ[μ] Y')
    (f f' : X → ℝ) (hf' : Measurable f')
    (hff : (fun ω => f (s ω)) =ᵐ[μ] (fun ω => f' (s' ω)))
    (hreg : (fun ω => f (s ω)) =ᵐ[μ]
      μ[Y | MeasurableSpace.comap s ‹MeasurableSpace X›]) :
    (fun ω => f' (s' ω)) =ᵐ[μ]
      μ[Y' | MeasurableSpace.comap s' ‹MeasurableSpace X›] := by
  have hi : Integrable (fun ω => f (s ω)) μ := integrable_condExp.congr hreg.symm
  have hi' : Integrable (fun ω => f' (s' ω)) μ := hi.congr hff
  apply ae_eq_condExp_of_forall_setIntegral_eq hs'.comap_le (hY.congr hYY)
    (fun _ _ _ => hi'.integrableOn)
  · rintro _ ⟨t, ht, rfl⟩ _
    have hsets : s ⁻¹' t =ᵐ[μ] s' ⁻¹' t := by
      filter_upwards [heq] with ω hω
      change (s ω ∈ t) = (s' ω ∈ t)
      rw [hω]
    calc
      ∫ ω in s' ⁻¹' t, f' (s' ω) ∂μ = ∫ ω in s' ⁻¹' t, f (s ω) ∂μ :=
        setIntegral_congr_ae (hs' ht) (hff.symm.mono fun _ h _ => h)
      _ = ∫ ω in s ⁻¹' t, f (s ω) ∂μ := setIntegral_congr_set hsets.symm
      _ = ∫ ω in s ⁻¹' t, μ[Y | MeasurableSpace.comap s ‹MeasurableSpace X›] ω ∂μ :=
        setIntegral_congr_ae (hs ht) (hreg.mono fun _ h _ => h)
      _ = ∫ ω in s ⁻¹' t, Y ω ∂μ := setIntegral_condExp hs.comap_le hY ⟨t, ht, rfl⟩
      _ = ∫ ω in s' ⁻¹' t, Y ω ∂μ := setIntegral_congr_set hsets
      _ = ∫ ω in s' ⁻¹' t, Y' ω ∂μ :=
        setIntegral_congr_ae (hs' ht) (hYY.mono fun _ h _ => h)
  · exact (hf'.comp (show Measurable[MeasurableSpace.comap s' ‹MeasurableSpace X›] s'
      from comap_measurable s')).stronglyMeasurable.aestronglyMeasurable

end Papers.TbsNeuralCausalPi
