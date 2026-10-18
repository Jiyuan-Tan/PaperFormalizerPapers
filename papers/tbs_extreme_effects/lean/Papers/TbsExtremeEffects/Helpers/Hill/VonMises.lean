module
public import Papers.TbsExtremeEffects.Helpers.Hill.RadialTail
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

/-! Tail quantiles and the von Mises bias calculation. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

/-- If [the lower point does not exceed the upper point](hyp:hzy), [the derivative equals a baseline plus an error throughout the interval](hyp:hderiv), and [that error is bounded on the interval](hyp:hbound), then [the centered increment is bounded by interval length times the error bound](goal).
@node: hill_increment_of_derivative_envelope -/
lemma hill_increment_of_derivative_envelope (L eta : ℝ → ℝ) (g b z y : ℝ)
    (hzy : z ≤ y)
    (hderiv : ∀ u ∈ Set.Icc z y, HasDerivAt L (g + eta u) u)
    (hbound : ∀ u ∈ Set.Ico z y, |eta u| ≤ b) :
    |L y - L z - g * (y - z)| ≤ b * (y - z) := by
  have hd : ∀ u ∈ Set.Icc z y,
      HasDerivWithinAt (fun v => L v - g * v) (eta u) (Set.Icc z y) u := by
    intro u hu
    convert ((hderiv u hu).sub ((hasDerivAt_id u).const_mul g)).hasDerivWithinAt using 1 <;>
      first | rfl | ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun u hu => by simpa only [Real.norm_eq_abs] using hbound u hu) y ⟨hzy, le_rfl⟩
  convert h using 1 <;> congr 1 <;> ring

/-- If [the quantile has the stated derivative at the exponential argument](hyp:hQ), [its value is positive](hyp:hpos), and [its scaled derivative differs from the baseline by the stated bias](hyp:heta), then [the log-quantile along exponential arguments has derivative baseline plus bias](goal).
@node: hill_log_quantile_derivative -/
lemma hill_log_quantile_derivative (Q : ℝ → ℝ) {u v g e : ℝ}
    (hQ : HasDerivAt Q v (Real.exp u)) (hpos : 0 < Q (Real.exp u))
    (heta : Real.exp u * v / Q (Real.exp u) - g = e) :
    HasDerivAt (fun y => Real.log (Q (Real.exp y))) (g + e) u := by
  have h := ((hQ.comp u (Real.hasDerivAt_exp u)).log hpos.ne')
  simp only [Function.comp_apply] at h
  convert h using 1
  rw [← heta]
  ring

/-- If [the interval is ordered](hyp:hzy), [the quantile is differentiable above its lower endpoint](hyp:hQ), [it is positive there](hyp:hpos), [its scaled derivative has the stated bias](hyp:heta), and [that bias is bounded](hyp:hbound), then [the logarithmic quantile increment is controlled by the bias bound](goal).
@node: hill_log_quantile_increment -/
lemma hill_log_quantile_increment (Q Q' eta : ℝ → ℝ) (g b z y : ℝ)
    (hzy : z ≤ y)
    (hQ : ∀ u ≥ z, HasDerivAt Q (Q' (Real.exp u)) (Real.exp u))
    (hpos : ∀ u ≥ z, 0 < Q (Real.exp u))
    (heta : ∀ u ≥ z,
      Real.exp u * Q' (Real.exp u) / Q (Real.exp u) - g = eta (Real.exp u))
    (hbound : ∀ u ≥ z, |eta (Real.exp u)| ≤ b) :
    |Real.log (Q (Real.exp y)) - Real.log (Q (Real.exp z)) - g * (y - z)| ≤
      b * (y - z) := by
  apply hill_increment_of_derivative_envelope
    (fun u => Real.log (Q (Real.exp u))) (fun u => eta (Real.exp u)) g b z y hzy
  · intro u hu
    exact hill_log_quantile_derivative Q (hQ u hu.1) (hpos u hu.1) (heta u hu.1)
  · intro u hu
    exact hbound u hu.1

end Papers.TbsExtremeEffects
