module
public import Papers.TsAdaptiveEstimationInference.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Vector quadratic-form comparisons for the real functional calculus. -/
@[expose] public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open Causalean.Estimation.NPIV.Complexification
open scoped InnerProductSpace
attribute [local instance 2000] instAlgebraRealLpCLM

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
include hA

/-- If the operator is self-adjoint and [the spectral symbol is continuous](hyp:hf),
[its real quadratic form at any vector equals the real part of the corresponding
complex quadratic form at the embedded vector](goal). -/
lemma realCFC_inner_eq (f : ℝ → ℝ) (hf : Continuous f) (u : Lp ℝ 2 μ) :
    inner ℝ (realCFC A f u) u =
      (inner ℂ (cfc f (complexLift A) (ιLp u)) (ιLp u)).re := by
  rw [realCFC_apply A hA f hf, inner_reLp_left,
    ← cfc_real_eq_complex (ha := complexLift_isSelfAdjoint hA)]

/-- For a self-adjoint operator, if [the first symbol is continuous](hyp:hf),
[the second symbol is continuous](hyp:hg), and [the first is no larger than the second
on the real spectrum of the complexified operator](hyp:hfg), then [the first symbol's
quadratic form is no larger than the second's at every vector](goal). -/
lemma realCFC_inner_mono (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ spectrum ℝ (complexLift A), f x ≤ g x) (u : Lp ℝ 2 μ) :
    inner ℝ (realCFC A f u) u ≤ inner ℝ (realCFC A g u) u := by
  rw [realCFC_inner_eq A hA f hf, realCFC_inner_eq A hA g hg]
  have hp := (ContinuousLinearMap.le_def _ _).mp
    (cfc_mono hfg hf.continuousOn hg.continuousOn)
  have hi := hp.re_inner_nonneg_left (ιLp u)
  simpa only [sub_apply, inner_sub_left, map_sub,
    RCLike.re_to_complex, sub_nonneg] using hi

/-- For a self-adjoint operator, [a continuous first spectral symbol](hyp:hf),
and [a continuous second spectral symbol](hyp:hg), [the quadratic form of their sum equals the sum
of their quadratic forms at any vector](goal). -/
lemma realCFC_inner_add (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (u : Lp ℝ 2 μ) :
    inner ℝ (realCFC A (fun x => f x + g x) u) u =
      inner ℝ (realCFC A f u) u + inner ℝ (realCFC A g u) u := by
  rw [realCFC_inner_eq A hA (fun x => f x + g x) (by fun_prop), realCFC_inner_eq A hA f hf,
    realCFC_inner_eq A hA g hg, cfc_add _ f g hf.continuousOn hg.continuousOn]
  simp only [add_apply, inner_add_left, Complex.add_re]

/-- For a self-adjoint operator and [a continuous spectral symbol](hyp:hf),
[multiplying the symbol by a real scalar multiplies its quadratic form at any vector
by that same scalar](goal). -/
lemma realCFC_inner_smul (c : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (u : Lp ℝ 2 μ) :
    inner ℝ (realCFC A (fun x => c * f x) u) u =
      c * inner ℝ (realCFC A f u) u := by
  rw [realCFC_inner_eq A hA (fun x => c * f x) (by fun_prop), realCFC_inner_eq A hA f hf,
    cfc_const_mul c f _ hf.continuousOn]
  change (inner ℂ ((c : ℂ) • (cfc f (complexLift A) (ιLp u))) (ιLp u)).re = _
  rw [inner_smul_left]
  simp

/-- For a self-adjoint operator, suppose [the first symbol is continuous](hyp:hf)
and [nonnegative on the real spectrum of the complexified operator](hyp:hf0), and
[the second symbol is continuous](hyp:hg) and [nonnegative on that spectrum](hyp:hg0).
If [the interpolation weight lies strictly between zero and one](hyp:hθ),
[the first moment is bounded above by a](hyp:hfa), [the second moment is bounded
above by b](hyp:hgb), and [a is strictly positive](hyp:ha) and [b is strictly positive](hyp:hb), then
[the quadratic form of the product of the nonnegative parts of the symbols, raised
to complementary weights, is at most a to the first weight times b to the second](goal). -/
lemma realCFC_inner_holder_bound (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x ∈ spectrum ℝ (complexLift A), 0 ≤ f x)
    (hg0 : ∀ x ∈ spectrum ℝ (complexLift A), 0 ≤ g x)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (u : Lp ℝ 2 μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hfa : inner ℝ (realCFC A f u) u ≤ a)
    (hgb : inner ℝ (realCFC A g u) u ≤ b) :
    inner ℝ (realCFC A
      (fun x => (max (f x) 0) ^ θ * (max (g x) 0) ^ (1 - θ)) u) u ≤
      a ^ θ * b ^ (1 - θ) := by
  let k := a ^ θ * b ^ (1 - θ)
  have hk : 0 < k := mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  have hcont : Continuous (fun x => (max (f x) 0) ^ θ *
      (max (g x) 0) ^ (1 - θ)) :=
    ((hf.max continuous_const).rpow_const (fun _ => Or.inr hθ.1.le)).mul
      ((hg.max continuous_const).rpow_const (fun _ => Or.inr (by linarith [hθ.2])))
  have h := realCFC_inner_mono A hA _
    (fun x => k * (θ / a * f x + (1 - θ) / b * g x)) hcont (by fun_prop)
    (fun x hx => ?_) u
  · rw [realCFC_inner_smul A hA k _ (by fun_prop),
      realCFC_inner_add A hA (fun x => θ / a * f x) (fun x => (1 - θ) / b * g x)
        (by fun_prop) (by fun_prop),
      realCFC_inner_smul A hA (θ / a) f hf,
      realCFC_inner_smul A hA ((1 - θ) / b) g hg] at h
    calc
      _ ≤ k * (θ / a * inner ℝ (realCFC A f u) u +
          (1 - θ) / b * inner ℝ (realCFC A g u) u) := h
      _ ≤ k * (θ / a * a + (1 - θ) / b * b) := by
        apply mul_le_mul_of_nonneg_left _ hk.le
        exact add_le_add
          (mul_le_mul_of_nonneg_left hfa (div_nonneg hθ.1.le ha.le))
          (mul_le_mul_of_nonneg_left hgb (div_nonneg (by linarith [hθ.2]) hb.le))
      _ = a ^ θ * b ^ (1 - θ) := by
        rw [div_mul_cancel₀ _ ha.ne', div_mul_cancel₀ _ hb.ne']
        simp [k]
  · rw [max_eq_left (hf0 x hx), max_eq_left (hg0 x hx)]
    have hy := Real.geom_mean_le_arith_mean2_weighted hθ.1.le
      (show 0 ≤ 1 - θ by linarith [hθ.2])
      (div_nonneg (hf0 x hx) ha.le) (div_nonneg (hg0 x hx) hb.le) (by ring)
    rw [Real.div_rpow (hf0 x hx) ha.le, Real.div_rpow (hg0 x hx) hb.le,
      div_mul_div_comm] at hy
    have hy' := (div_le_iff₀ hk).mp hy
    convert hy' using 1 <;> first | rfl | ring

/-- For a self-adjoint operator, if [a spectral symbol is continuous](hyp:hf)
and [nonnegative on the real spectrum of the complexified operator](hyp:hf0), then
[its quadratic form is nonnegative at every vector](goal). -/
lemma realCFC_inner_nonneg (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ x ∈ spectrum ℝ (complexLift A), 0 ≤ f x) (u : Lp ℝ 2 μ) :
    0 ≤ inner ℝ (realCFC A f u) u := by
  have h := realCFC_inner_mono A hA (fun _ => 0) f continuous_const hf hf0 u
  rw [realCFC_inner_eq A hA (fun _ => 0) continuous_const] at h
  simpa using h

/-- For a self-adjoint operator, suppose [the first symbol is continuous](hyp:hf)
and [nonnegative on the real spectrum of the complexified operator](hyp:hf0), and
[the second symbol is continuous](hyp:hg) and [nonnegative on that spectrum](hyp:hg0).
If [the interpolation weight lies strictly between zero and one](hyp:hθ), then
[the quadratic form of the product of the nonnegative parts of the symbols, raised
to complementary weights, is bounded by the product of their quadratic forms raised
to those same weights](goal).

The bound includes zero moments and follows from the scalar Young inequality. -/
lemma realCFC_inner_holder (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x ∈ spectrum ℝ (complexLift A), 0 ≤ f x)
    (hg0 : ∀ x ∈ spectrum ℝ (complexLift A), 0 ≤ g x)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (u : Lp ℝ 2 μ) :
    inner ℝ (realCFC A
      (fun x => (max (f x) 0) ^ θ * (max (g x) 0) ^ (1 - θ)) u) u ≤
      (inner ℝ (realCFC A f u) u) ^ θ *
        (inner ℝ (realCFC A g u) u) ^ (1 - θ) := by
  let a := inner ℝ (realCFC A f u) u
  let b := inner ℝ (realCFC A g u) u
  have ha : 0 ≤ a := realCFC_inner_nonneg A hA f hf hf0 u
  have hb : 0 ≤ b := realCFC_inner_nonneg A hA g hg hg0 u
  have ha_lim : Filter.Tendsto (fun n : ℕ => a + 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds a) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := a)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hb_lim : Filter.Tendsto (fun n : ℕ => b + 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds b) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := b)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply ge_of_tendsto' ((ha_lim.rpow_const (Or.inr hθ.1.le)).mul
    (hb_lim.rpow_const (Or.inr (show 0 ≤ 1 - θ by linarith [hθ.2]))))
  intro n
  have he : 0 < 1 / ((n : ℝ) + 1) := by positivity
  exact realCFC_inner_holder_bound A hA f g hf hg hf0 hg0 hθ u
    (add_pos_of_nonneg_of_pos ha he) (add_pos_of_nonneg_of_pos hb he)
    (le_add_of_nonneg_right he.le) (le_add_of_nonneg_right he.le)

end Papers.TsAdaptiveEstimationInference
