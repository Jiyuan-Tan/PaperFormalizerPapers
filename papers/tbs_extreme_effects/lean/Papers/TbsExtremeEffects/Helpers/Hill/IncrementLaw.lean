module
public import Papers.TbsExtremeEffects.Helpers.Hill.ExponentialLaw
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exact centered exponential moments for independent standard exponential
spacings, before assembling the Hill supermartingales. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- For a [tilt below one](hyp:hs), [the centered exponential moment under a standard exponential distribution has its stated closed form](goal).
-/
-- @node: hill_centered_exponential_integral
lemma hill_centered_exponential_integral {s : ℝ} (hs : s < 1) :
    (∫ x, Real.exp (s * (x - 1)) ∂expMeasure 1) = Real.exp (-s) / (1 - s) := by
  change (∫ x, Real.exp (s * (x - 1))
    ∂volume.withDensity (exponentialPDF 1)) = _
  rw [integral_withDensity_eq_integral_toReal_smul]
  · have hpoint : (fun x : ℝ => (exponentialPDF 1 x).toReal •
        Real.exp (s * (x - 1))) = Set.indicator (Set.Ici 0)
          (fun x => Real.exp (-s) * Real.exp ((s - 1) * x)) := by
      funext x
      rw [exponentialPDF_eq]
      by_cases hx : 0 ≤ x
      · simp only [if_pos hx, one_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
          smul_eq_mul, Set.indicator_of_mem (show x ∈ Set.Ici 0 from hx), ← Real.exp_add]
        congr 1
        ring
      · simp [hx]
    rw [hpoint, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, integral_exp_mul_Ioi (by linarith : s - 1 < 0)]
    simp only [mul_zero, Real.exp_zero]
    field_simp [show s - 1 ≠ 0 by linarith, show 1 - s ≠ 0 by linarith]
    ring
  · exact (measurable_exponentialPDFReal 1).ennreal_ofReal
  · exact ae_of_all _ fun x => ENNReal.ofReal_lt_top

/-- If [the variable is measurable](hyp:hV), [it has the standard exponential distribution](hyp:hLaw), and [the tilt is below one](hyp:hs), then [its centered exponential moment has the stated closed form](goal).
-/
-- @node: hill_centered_exponential_moment_of_law
lemma hill_centered_exponential_moment_of_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (V : Ω → ℝ) (hV : Measurable V)
    (hLaw : P.map V = expMeasure 1) {s : ℝ} (hs : s < 1) :
    (∫ w, Real.exp (s * (V w - 1)) ∂P) = Real.exp (-s) / (1 - s) := by
  rw [← hill_centered_exponential_integral hs, ← hLaw]
  have hf : AEStronglyMeasurable (fun x : ℝ => Real.exp (s * (x - 1))) (P.map V) := by
    fun_prop
  exact (integral_map hV.aemeasurable hf).symm

/-- If [the variable is measurable](hyp:hV), [it has the standard exponential distribution](hyp:hLaw), [the conditioning information is contained in the ambient information](hyp:hG), [the variable is independent of that information](hyp:hInd), and [the tilt is below one](hyp:hs), then [its conditional centered exponential moment equals its unconditional closed form almost surely](goal).
-/
-- @node: hill_centered_exponential_conditional_moment
lemma hill_centered_exponential_conditional_moment {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V : Ω → ℝ) (hV : Measurable V)
    (hLaw : P.map V = expMeasure 1) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hInd : Indep (MeasurableSpace.comap V inferInstance) G P)
    {s : ℝ} (hs : s < 1) :
    P[(fun w => Real.exp (s * (V w - 1))) | G] =ᵐ[P]
      fun _ => Real.exp (-s) / (1 - s) := by
  have hmeas : StronglyMeasurable[MeasurableSpace.comap V inferInstance]
      (fun w => Real.exp (s * (V w - 1))) := by
    apply Measurable.stronglyMeasurable
    have hv : Measurable[MeasurableSpace.comap V inferInstance] V := comap_measurable V
    fun_prop
  have h := condExp_indep_eq hV.comap_le hG hmeas hInd
  have hInt := @hill_centered_exponential_moment_of_law Ω mΩ P V hV hLaw s hs
  simpa only [hInt] using h

/-- If [each partial sum is measurable](hyp:hB), [every increment before the horizon has the standard exponential law and is independent of prior information](hyp:hLaw), [the tilt is positive](hyp:hlam), and [the tilt is below one](hyp:hlamone), then [the positive and negative exponential increments have their exact conditional moments before the horizon](goal).
-/
-- @node: hill_spacing_conditional_moments_of_increment_laws
lemma hill_spacing_conditional_moments_of_increment_laws
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ mΩ) (hB : ∀ i, Measurable (B i)) (n : ℕ)
    (hLaw : ∀ i < n,
      P.map (fun w => B (i + 1) w - B i w + 1) = expMeasure 1 ∧
      Indep (MeasurableSpace.comap (fun w => B (i + 1) w - B i w + 1)
        inferInstance) (ℱ i) P)
    {lam : ℝ} (hlam : 0 < lam) (hlamone : lam < 1) :
    ∀ i < n,
      P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] (fun _ => Real.exp (-lam) / (1 - lam)) ∧
      P[(fun w => Real.exp (-lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] (fun _ => Real.exp lam / (1 + lam)) := by
  intro i hi
  have hm : Measurable (fun w => B (i + 1) w - B i w + 1) := by fun_prop
  have hp := hill_centered_exponential_conditional_moment P _ hm (hLaw i hi).1
    (ℱ i) (ℱ.le i) (hLaw i hi).2 hlamone
  have hn := hill_centered_exponential_conditional_moment P _ hm (hLaw i hi).1
    (ℱ i) (ℱ.le i) (hLaw i hi).2 (show -lam < 1 by linarith)
  constructor
  · simpa only [add_sub_cancel_right] using hp
  · simpa only [add_sub_cancel_right, neg_neg, sub_neg_eq_add] using hn

end Papers.TbsExtremeEffects
