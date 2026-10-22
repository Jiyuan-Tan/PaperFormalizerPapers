module
public import Papers.TbsExtremeEffects.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

/-! Stability of the radial survival/density ratio in the Hill bias calculation.
The relative survival and density errors are added before dividing by the
density, whose relative value is at least one half in the eventual tail. -/

public section
namespace Papers.TbsExtremeEffects
open Filter
open scoped Topology

/-- If [the tail index is positive](hyp:hβ), [the normalized survival error is bounded](hyp:hs),
[the normalized density error is bounded](hyp:hf), and [the normalized density stays above one half](hyp:hfloor),
then [the normalized ratio error is bounded by four times the common error](goal).
@node: hill_normalized_tail_ratio_bound -/
lemma hill_normalized_tail_ratio_bound {s f b β : ℝ}
    (hβ : 0 < β) (hs : |s - 1| ≤ b) (hf : |f - 1| ≤ b)
    (hfloor : 1 / 2 ≤ f) :
    |(s / f - 1) / β| ≤ 4 * b / β := by
  have hfpos : 0 < f := by linarith
  have hb : 0 ≤ b := (abs_nonneg _).trans hs
  have hdiff : |s - f| ≤ 2 * b := by
    calc
      |s - f| = |(s - 1) - (f - 1)| := by congr 1; ring
      _ ≤ |s - 1| + |f - 1| := abs_sub _ _
      _ ≤ 2 * b := by linarith
  have hratio : |s / f - 1| ≤ 4 * b := by
    rw [show s / f - 1 = (s - f) / f by field_simp,
      abs_div, abs_of_pos hfpos]
    apply (div_le_iff₀ hfpos).mpr
    nlinarith
  rw [abs_div, abs_of_pos hβ]
  exact div_le_div_of_nonneg_right hratio hβ.le

/-- If [a normalized density is within an error bound of one](hyp:hf) and [that error is at most
one half](hyp:hb), then [the normalized density is at least one half](goal).
@node: hill_relative_density_floor -/
lemma hill_relative_density_floor {f b : ℝ} (hf : |f - 1| ≤ b)
    (hb : b ≤ 1 / 2) : 1 / 2 ≤ f := by
  have := (abs_le.mp hf).1
  linarith

/-- When [the radius is positive](hyp:hr), [the tail constant is positive](hyp:hC), [the tail
index is positive](hyp:hβ), and [the density is nonzero](hyp:hf), the raw radial ratio [equals its
normalized survival-and-density ratio](goal).
@node: hill_radial_ratio_identity -/
lemma hill_radial_ratio_identity {S f r C₀ β : ℝ}
    (hr : 0 < r) (hC : 0 < C₀) (hβ : 0 < β) (hf : f ≠ 0) :
    S / (r * f) - 1 / β =
      ((S / (C₀ * r ^ (-β))) /
        (f / (β * C₀ * r ^ (-β - 1))) - 1) / β := by
  have hp : r ^ (-β - 1) = r ^ (-β) / r := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_neg_one]
    rfl
  rw [hp]
  have hpow : r ^ (-β) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  field_simp

/-- If [the radius](hyp:hr), [tail constant](hyp:hC), and [tail index](hyp:hβ) are positive,
[normalized survival](hyp:hs) and [density](hyp:hf) errors are bounded by the same amount, and
[that amount is at most one half](hyp:hb), then [the density is positive and the radial ratio error is controlled](goal).
@node: hill_radial_ratio_bound -/
lemma hill_radial_ratio_bound {S f r C₀ β b : ℝ}
    (hr : 0 < r) (hC : 0 < C₀) (hβ : 0 < β)
    (hs : |S / (C₀ * r ^ (-β)) - 1| ≤ b)
    (hf : |f / (β * C₀ * r ^ (-β - 1)) - 1| ≤ b)
    (hb : b ≤ 1 / 2) :
    0 < f ∧ |S / (r * f) - 1 / β| ≤ 4 * b / β := by
  have hfloor := hill_relative_density_floor hf hb
  have hscale : 0 < β * C₀ * r ^ (-β - 1) := by positivity
  have hfpos : 0 < f := (div_pos_iff_of_pos_right hscale).mp (by linarith)
  refine ⟨hfpos, ?_⟩
  rw [hill_radial_ratio_identity hr hC hβ hfpos.ne']
  exact hill_normalized_tail_ratio_bound hβ hs hf hfloor

/-- Given [a positive quantile level](hyp:hv), [a nonzero density](hyp:hf), a [nonzero quantile](hyp:hQpos),
[the survival derivative](hyp:hS), [the quantile derivative](hyp:hQ), and [their local reciprocal
identity](hyp:hInverse), the quantile logarithmic derivative [equals the survival-to-density ratio](goal).
@node: hill_quantile_survival_ratio_identity -/
lemma hill_quantile_survival_ratio_identity (S Q : ℝ → ℝ) {v f Q' : ℝ}
    (hv : 0 < v) (hf : f ≠ 0) (hQpos : Q v ≠ 0)
    (hS : HasDerivAt S (-f) (Q v)) (hQ : HasDerivAt Q Q' v)
    (hInverse : ∀ᶠ w in 𝓝 v, S (Q w) = w⁻¹) :
    v * Q' / Q v = S (Q v) / (Q v * f) := by
  have hInv : (fun w => S (Q w)) =ᶠ[𝓝 v] (fun w => w⁻¹) := hInverse
  have hcomp := (hS.comp v hQ).congr_of_eventuallyEq hInv.symm
  have hderiv := hcomp.unique (hasDerivAt_inv hv.ne')
  have hvalue : S (Q v) = v⁻¹ := hInv.eq_of_nhds
  rw [hvalue]
  field_simp at hderiv ⊢
  nlinarith

end Papers.TbsExtremeEffects
