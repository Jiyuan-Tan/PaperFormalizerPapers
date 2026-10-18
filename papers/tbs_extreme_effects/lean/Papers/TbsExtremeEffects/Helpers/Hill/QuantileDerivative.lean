module
public import Papers.TbsExtremeEffects.Helpers.Hill.TailDerivative
public import Papers.TbsExtremeEffects.Helpers.Hill.TailRatio
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! Differentiability of the continuous radial tail quantile from its survival inverse. -/

public section
namespace Papers.TbsExtremeEffects
open Filter
open scoped Topology

/-- If [the level is positive](hyp:hv), [the density value is nonzero](hyp:hf), [survival has derivative `-f` at the quantile](hyp:hS), [the quantile is continuous there](hyp:hQ), and [their reciprocal identity holds locally](hyp:hInverse), then [the quantile has derivative `(v² f)⁻¹`](goal). -/
-- @node: hill_quantile_hasDerivAt_of_continuous_inverse
lemma hill_quantile_hasDerivAt_of_continuous_inverse (S Q : ℝ → ℝ)
    {v f : ℝ} (hv : 0 < v) (hf : f ≠ 0)
    (hS : HasDerivAt S (-f) (Q v)) (hQ : ContinuousAt Q v)
    (hInverse : ∀ᶠ w in 𝓝 v, S (Q w) = w⁻¹) :
    HasDerivAt Q (v ^ 2 * f)⁻¹ v := by
  have hInv : (fun w => S (Q w)) =ᶠ[𝓝 v] (fun w => w⁻¹) := hInverse
  have hvalue : S (Q v) = v⁻¹ := hInv.eq_of_nhds
  have hnonzero : S (Q v) ≠ 0 := by rw [hvalue]; exact inv_ne_zero hv.ne'
  have hrecip : HasDerivAt (fun x => (S x)⁻¹) (v ^ 2 * f) (Q v) := by
    convert! hS.inv hnonzero using 1
    rw [hvalue]
    field_simp
  apply HasDerivAt.of_local_left_inverse hQ hrecip (mul_ne_zero (pow_ne_zero _ hv.ne') hf)
  filter_upwards [hInverse] with w hw
  rw [hw, inv_inv]

/-- If [the level is positive](hyp:hv), [the density value is nonzero](hyp:hf), [the quantile is nonzero](hyp:hQpos), [survival has derivative `-f` at the quantile](hyp:hS), [the quantile is continuous there](hyp:hQ), and [the reciprocal identity holds locally](hyp:hInverse), then [the quantile derivative exists and its scaled derivative equals the radial hazard ratio](goal). -/
-- @node: hill_continuous_quantile_derivative_and_ratio
lemma hill_continuous_quantile_derivative_and_ratio (S Q : ℝ → ℝ)
    {v f : ℝ} (hv : 0 < v) (hf : f ≠ 0) (hQpos : Q v ≠ 0)
    (hS : HasDerivAt S (-f) (Q v)) (hQ : ContinuousAt Q v)
    (hInverse : ∀ᶠ w in 𝓝 v, S (Q w) = w⁻¹) :
    HasDerivAt Q (v ^ 2 * f)⁻¹ v ∧
      v * (v ^ 2 * f)⁻¹ / Q v = S (Q v) / (Q v * f) := by
  have hderiv := hill_quantile_hasDerivAt_of_continuous_inverse S Q hv hf hS hQ hInverse
  exact ⟨hderiv, hill_quantile_survival_ratio_identity S Q hv hf hQpos hS hderiv hInverse⟩

end Papers.TbsExtremeEffects
