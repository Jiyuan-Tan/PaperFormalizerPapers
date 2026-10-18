module
public import Papers.TbsNeuralCausalPi.Helpers.EstimationAssembly
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.L2Space
/-! # Change of treatment measure in the finite-sample rate

The square-integrable Radon--Nikodym derivative transfers the reference-law
mean-square bound to the intervention objective. All constants are independent
of the candidate and of the optimization radius.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal

-- @node: estimation_rnDeriv_square_integrable
/-- For two sigma-finite measures, if [the squared Radon–Nikodym density has finite extended integral over the chosen set under the reference measure](hyp:hfinite), then [its real-valued square is integrable there and its integral equals the real value of that extended integral](goal). -/
lemma estimation_rnDeriv_square_integrable
    {X : Type*} [MeasurableSpace X] (mu nu : Measure X)
    [SigmaFinite mu] [SigmaFinite nu] (s : Set X)
    (hfinite : (∫⁻ x in s, (mu.rnDeriv nu x)^2 ∂nu) < ⊤) :
    Integrable (fun x => ((mu.rnDeriv nu x).toReal)^2) (nu.restrict s) ∧
      (∫ x in s, ((mu.rnDeriv nu x).toReal)^2 ∂nu) =
        (∫⁻ x in s, (mu.rnDeriv nu x)^2 ∂nu).toReal := by
  have hm : AEMeasurable (fun x => (mu.rnDeriv nu x)^2) (nu.restrict s) := by
    fun_prop
  have hi := integrable_toReal_of_lintegral_ne_top hm hfinite.ne
  have hae : ∀ᵐ x ∂nu.restrict s, (mu.rnDeriv nu x)^2 < ⊤ :=
    ae_lt_top (by fun_prop) hfinite.ne
  simpa only [ENNReal.toReal_pow] using
    And.intro hi (integral_toReal hm hae)

-- @node: estimation_abs_integral_mul_le_sqrt
/-- If [the first real function is almost everywhere strongly measurable](hyp:hf), [the second is almost everywhere strongly measurable](hyp:hg), [the first has integrable square](hyp:hf2), and [the second has integrable square](hyp:hg2), then [the absolute integral of their product is at most the product of the square roots of their square integrals](goal). -/
lemma estimation_abs_integral_mul_le_sqrt
    {X : Type*} [MeasurableSpace X] (nu : Measure X) (f g : X → ℝ)
    (hf : AEStronglyMeasurable f nu) (hg : AEStronglyMeasurable g nu)
    (hf2 : Integrable (fun x => (f x)^2) nu)
    (hg2 : Integrable (fun x => (g x)^2) nu) :
    |∫ x, f x * g x ∂nu| ≤
      Real.sqrt (∫ x, (f x)^2 ∂nu) * Real.sqrt (∫ x, (g x)^2 ∂nu) := by
  have hfL : MemLp f 2 nu := (memLp_two_iff_integrable_sq hf).2 hf2
  have hgL : MemLp g 2 nu := (memLp_two_iff_integrable_sq hg).2 hg2
  have hholder := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      (2 : ℝ).HolderConjugate 2)
    (by simpa using hfL) (by simpa using hgL)
  have hnorm : |∫ x, f x * g x ∂nu| ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂nu := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      norm_integral_le_integral_norm (f := fun x => f x * g x)
  apply hnorm.trans
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow] using hholder

-- @node: estimation_change_measure_square_bound
/-- Suppose [the integration set is measurable](hyp:hs), [the target measure is absolutely continuous with respect to the reference measure](hyp:hac), [the real function is almost everywhere strongly measurable on that set under the reference measure](hyp:hf), [its square is integrable there](hyp:hf2), and [the squared density has finite extended integral there](hyp:hfinite). Then [the absolute integral under the target measure is at most the square root of the reference square integral times the square root of the density's extended square integral converted to a real number](goal). -/
lemma estimation_change_measure_square_bound
    {X : Type*} [MeasurableSpace X] (mu nu : Measure X)
    [SigmaFinite mu] [SigmaFinite nu] (s : Set X) (hs : MeasurableSet s)
    (hac : mu ≪ nu) (f : X → ℝ)
    (hf : AEStronglyMeasurable f (nu.restrict s))
    (hf2 : Integrable (fun x => (f x)^2) (nu.restrict s))
    (hfinite : (∫⁻ x in s, (mu.rnDeriv nu x)^2 ∂nu) < ⊤) :
    |∫ x in s, f x ∂mu| ≤
      Real.sqrt (∫ x in s, (f x)^2 ∂nu) *
        Real.sqrt (∫⁻ x in s, (mu.rnDeriv nu x)^2 ∂nu).toReal := by
  obtain ⟨hr2, heq⟩ := estimation_rnDeriv_square_integrable mu nu s hfinite
  rw [← setIntegral_rnDeriv_smul hac hs]
  simp only [smul_eq_mul]
  have hr : AEStronglyMeasurable (fun x => (mu.rnDeriv nu x).toReal)
      (nu.restrict s) := by
    first | fun_prop | exact (Measure.measurable_rnDeriv mu nu).ennreal_toReal.aestronglyMeasurable
  have h := estimation_abs_integral_mul_le_sqrt (nu.restrict s)
    f (fun x => (mu.rnDeriv nu x).toReal) hf hr hf2 hr2
  simpa only [mul_comm, heq] using h

end Papers.TbsNeuralCausalPi
