module
public import Papers.TsAdaptiveEstimationInference.Helpers.SpectralInterpolation
/-! Real CFC comparison and vector fractional-power norm interpolation. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped InnerProductSpace
attribute [local instance 2000]
  Causalean.Estimation.NPIV.Complexification.instAlgebraRealLpCLM

-- @node: realCFC_congr_real
/-- For [a self-adjoint operator](hyp:hA), if [the first symbol is continuous](hyp:hf),
[the second symbol is continuous](hyp:hg), and [the symbols agree on the operator's
real spectrum](hyp:hfg), then [they define the same real functional-calculus operator](goal). -/
lemma realCFC_congr_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ spectrum ℝ A, f x = g x) :
    Causalean.Estimation.NPIV.Complexification.realCFC A f =
      Causalean.Estimation.NPIV.Complexification.realCFC A g := by
  open Causalean.Estimation.NPIV.Complexification in
  have hsub (u : Lp ℝ 2 μ) : realCFC A (fun x => f x - g x) u =
      realCFC A f u - realCFC A g u := by
    change realCFC A (f - g) u = _
    rw [realCFC_apply A hA (f - g) (hf.sub hg), realCFC_apply A hA f hf,
      realCFC_apply A hA g hg]
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    rw [cfc_sub (fun z : ℂ => (f z.re : ℂ)) (fun z : ℂ => (g z.re : ℂ)) (complexLift A)
      (hf := (show Continuous (fun z : ℂ => (f z.re : ℂ)) by fun_prop).continuousOn)
      (hg := (show Continuous (fun z : ℂ => (g z.re : ℂ)) by fun_prop).continuousOn)]
    simp only [sub_apply, map_sub]
  apply ContinuousLinearMap.ext
  intro u
  apply sub_eq_zero.mp
  apply norm_le_zero_iff.mp
  rw [← hsub]
  simpa using Causalean.Estimation.NPIV.Complexification.realCFC_norm_le A hA
    (fun x => f x - g x) (hf.sub hg) 0 le_rfl
    (fun x hx => by rw [hfg x hx]; simp) u

-- @node: realCFC_one_apply
/-- For [a self-adjoint operator](hyp:hA), [applying the real functional calculus
with the constant-one symbol leaves every vector unchanged](goal). -/
lemma realCFC_one_apply {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A) (u : Lp ℝ 2 μ) :
    Causalean.Estimation.NPIV.Complexification.realCFC A (fun _ => 1) u = u := by
  open Causalean.Estimation.NPIV.Complexification in
  rw [realCFC_apply A hA _ continuous_const]
  simp only [Complex.ofReal_one]
  rw [cfc_const 1 _ (complexLift_isSelfAdjoint hA).isStarNormal]
  simpa using reLp_comp_ιLp u

-- @node: realCFC_norm_sq
/-- For [a self-adjoint operator](hyp:hA) and [a continuous real spectral symbol](hyp:hf),
[the squared norm of the symbol's operator applied to a vector equals the quadratic
form of the squared symbol at that vector](goal). -/
lemma realCFC_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) (u : Lp ℝ 2 μ) :
    ‖Causalean.Estimation.NPIV.Complexification.realCFC A f u‖ ^ 2 =
      inner ℝ (Causalean.Estimation.NPIV.Complexification.realCFC A
        (fun x => f x * f x) u) u := by
  open Causalean.Estimation.NPIV.Complexification in
  rw [realCFC_mul A hA f f hf hf, ContinuousLinearMap.comp_apply]
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (realCFC_isSelfAdjoint A hA f hf)
  exact (real_inner_self_eq_norm_sq _).symm.trans (hs _ _).symm

-- @node: realCFC_inner_mono_real
/-- For [a self-adjoint operator](hyp:hA), if [the first symbol is continuous](hyp:hf),
[the second symbol is continuous](hyp:hg), and [the first is no larger than the second
on the operator's real spectrum](hyp:hfg), then [the first symbol's quadratic form
is no larger than the second's at every vector](goal). -/
lemma realCFC_inner_mono_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ spectrum ℝ A, f x ≤ g x) (u : Lp ℝ 2 μ) :
    inner ℝ (Causalean.Estimation.NPIV.Complexification.realCFC A f u) u ≤
      inner ℝ (Causalean.Estimation.NPIV.Complexification.realCFC A g u) u := by
  let d := fun x => max (g x - f x) 0
  have hd : Continuous d := by fun_prop
  have hp := realCFC_inner_nonneg A hA d hd (fun x _ => le_max_right _ _) u
  have he := realCFC_congr_real A hA (fun x => f x + d x) g (hf.add hd) hg (by
    intro x hx
    dsimp [d]
    rw [max_eq_left (sub_nonneg.mpr (hfg x hx))]
    ring)
  have hi := realCFC_inner_add A hA f d hf hd u
  rw [he] at hi
  linarith

-- @node: realCFC_power_norm_sq
/-- For [a self-adjoint operator](hyp:hA) and [a nonnegative exponent b](hyp:hb),
[the squared norm obtained by applying the positive-part spectral power with exponent
b divided by two equals the quadratic form of the positive-part power with exponent b](goal). -/
lemma realCFC_power_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    {b : ℝ} (hb : 0 ≤ b) (u : Lp ℝ 2 μ) :
    ‖Causalean.Estimation.NPIV.Complexification.realCFC A
      (fun x => (max x 0) ^ (b / 2)) u‖ ^ 2 =
      inner ℝ (Causalean.Estimation.NPIV.Complexification.realCFC A
        (fun x => (max x 0) ^ b) u) u := by
  have hc : Continuous (fun x : ℝ => (max x 0) ^ (b / 2)) := by
    fun_prop (disch := positivity)
  rw [realCFC_norm_sq A hA _ hc]
  congr 3
  funext x
  rw [← Real.rpow_add_of_nonneg (le_max_right x 0) (by positivity) (by positivity)]
  congr 1
  ring

-- @node: realCFC_fractional_norm_sq
/-- For [a self-adjoint operator](hyp:hA) with [nonnegative real spectrum](hyp:hpos),
if [b lies strictly between zero and one](hyp:hb), then [the squared norm of its
positive-part spectral power with exponent b divided by two, applied to any vector,
is at most the operator's quadratic form to power b times the vector's squared norm
to power one minus b](goal). -/
lemma realCFC_fractional_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (hpos : ∀ x ∈ spectrum ℝ A, 0 ≤ x)
    {b : ℝ} (hb : b ∈ Set.Ioo (0 : ℝ) 1) (u : Lp ℝ 2 μ) :
    ‖Causalean.Estimation.NPIV.Complexification.realCFC A
      (fun x => (max x 0) ^ (b / 2)) u‖ ^ 2 ≤
        (inner ℝ (A u) u) ^ b * (‖u‖ ^ 2) ^ (1 - b) := by
  open Causalean.Estimation.NPIV.Complexification in
  have hb0 : 0 ≤ b := hb.1.le
  have hc : Continuous (fun x : ℝ => (max x 0) ^ (b / 2)) := by
    fun_prop (disch := positivity)
  have hsq : (fun x : ℝ => (max x 0) ^ (b / 2) * (max x 0) ^ (b / 2)) =
      (fun x : ℝ => (max x 0) ^ b) := by
    funext x
    rw [← Real.rpow_add_of_nonneg (le_max_right x 0) (by positivity) (by positivity)]
    congr 1
    ring
  rw [realCFC_norm_sq A hA _ hc, hsq]
  have hh := realCFC_inner_holder A hA (fun x => max x 0) (fun _ => 1)
    (by fun_prop) continuous_const (fun x _ => le_max_right x 0)
    (fun _ _ => zero_le_one) hb u
  have hmax := realCFC_congr_real A hA (fun x => max x 0) id
    (by fun_prop) continuous_id (fun x hx => max_eq_left (hpos x hx))
  simpa only [max_assoc, max_self, max_eq_left (zero_le_one : (0 : ℝ) ≤ 1), Real.one_rpow,
    mul_one, hmax, realCFC_id A hA, realCFC_one_apply A hA, real_inner_self_eq_norm_sq]
    using hh

end Papers.TsAdaptiveEstimationInference
