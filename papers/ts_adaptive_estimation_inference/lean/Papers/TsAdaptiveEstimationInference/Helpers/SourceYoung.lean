module
public import Mathlib.Analysis.MeanInequalities
/-! Scalar Young estimates for the source-condition variational bounds. -/
public section
namespace Papers.TsAdaptiveEstimationInference

-- @node: source_scalar_young
/-- If [the source exponent is positive and at most one](hyp:hb), [the absorption
constant is positive](hyp:hε), [the amplitude is nonnegative](hyp:ha), and [the norm
variable is nonnegative](hyp:hu), then [twice the amplitude times the norm variable to the power one
minus the source exponent is bounded by the absorption constant times the squared
norm variable plus the amplitude to the power two divided by one plus the source
exponent, multiplied by the absorption constant times two over that constant to
the same power](goal). -/
lemma source_scalar_young {b ε a u : ℝ} (hb : b ∈ Set.Ioc (0 : ℝ) 1)
    (hε : 0 < ε) (ha : 0 ≤ a) (hu : 0 ≤ u) :
    2 * a * u ^ (1 - b) ≤ ε * u ^ 2 +
      (ε * (2 / ε) ^ (2 / (1 + b))) * a ^ (2 / (1 + b)) := by
  have hd : 0 < 1 + b := by linarith [hb.1]
  let p := (1 + b) / 2
  let q := (1 - b) / 2
  let A := (2 * a / ε) ^ (2 / (1 + b))
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := by dsimp [q]; linarith [hb.2]
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have heA : A ^ p = 2 * a / ε := by
    dsimp [A, p]
    rw [← Real.rpow_mul (by positivity)]
    rw [show 2 / (1 + b) * ((1 + b) / 2) = 1 by field_simp]
    exact Real.rpow_one _
  have heu : (u ^ 2) ^ q = u ^ (1 - b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
    congr 1
    dsimp [q]
    ring
  have hy := Real.geom_mean_le_arith_mean2_weighted hp hq hA (sq_nonneg u)
    (show p + q = 1 by dsimp [p, q]; ring)
  rw [heA, heu] at hy
  have hsum : p * A + q * u ^ 2 ≤ A + u ^ 2 := by
    have hp1 : p ≤ 1 := by dsimp [p]; linarith [hb.2]
    have hq1 : q ≤ 1 := by dsimp [q]; linarith [hb.1]
    nlinarith [mul_le_mul_of_nonneg_right hp1 hA,
      mul_le_mul_of_nonneg_right hq1 (sq_nonneg u)]
  have hm := mul_le_mul_of_nonneg_left (hy.trans hsum) hε.le
  have he : ε * (2 * a / ε) = 2 * a := by field_simp
  have hexp : A = (2 / ε) ^ (2 / (1 + b)) * a ^ (2 / (1 + b)) := by
    dsimp [A]
    rw [show 2 * a / ε = (2 / ε) * a by ring, Real.mul_rpow (by positivity) ha]
  rw [← mul_assoc, he, hexp] at hm
  nlinarith

-- @node: source_scalar_energy_sq
/-- If [the source exponent is positive and at most one](hyp:hb), [the regularization
parameter is positive](hyp:hlam), [the first norm variable is nonnegative](hyp:hx),
and [the second norm variable is nonnegative](hyp:hy), then [the square of the product
of the regularization parameter times
the first variable to the source exponent times the second to one minus that
exponent is bounded by the regularization parameter to one plus the source exponent
times the sum of the first variable squared and the regularization parameter times
the second variable squared](goal). -/
lemma source_scalar_energy_sq {b lam x y : ℝ} (hb : b ∈ Set.Ioc (0 : ℝ) 1)
    (hlam : 0 < lam) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (lam * x ^ b * y ^ (1 - b)) ^ 2 ≤
      lam ^ (1 + b) * (x ^ 2 + lam * y ^ 2) := by
  have hb0 : 0 ≤ b := hb.1.le
  have hb1 : 0 ≤ 1 - b := by linarith [hb.2]
  have hm := Real.geom_mean_le_arith_mean2_weighted hb0 hb1 (sq_nonneg x)
    (mul_nonneg hlam.le (sq_nonneg y)) (show b + (1 - b) = 1 by ring)
  have hm' : (x ^ 2) ^ b * (lam * y ^ 2) ^ (1 - b) ≤ x ^ 2 + lam * y ^ 2 := by
    have hp := mul_nonneg hb1 (sq_nonneg x)
    have hq := mul_nonneg hb0 (mul_nonneg hlam.le (sq_nonneg y))
    nlinarith
  have hpow (t r : ℝ) (ht : 0 ≤ t) : (t ^ r) ^ 2 = (t ^ 2) ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht,
      ← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    ring
  have hl : lam ^ (1 + b) * lam ^ (1 - b) = lam ^ 2 := by
    rw [← Real.rpow_add hlam]
    norm_num
  have he : (lam * x ^ b * y ^ (1 - b)) ^ 2 =
      lam ^ (1 + b) * ((x ^ 2) ^ b * (lam * y ^ 2) ^ (1 - b)) := by
    rw [mul_pow, mul_pow, hpow x b hx, hpow y (1 - b) hy,
      Real.mul_rpow hlam.le (sq_nonneg y)]
    calc
      _ = (lam ^ (1 + b) * lam ^ (1 - b)) *
          ((x ^ 2) ^ b * (y ^ 2) ^ (1 - b)) := by rw [hl]
        <;> ring
      _ = _ := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hm' (Real.rpow_nonneg hlam.le _)

-- @node: source_scalar_energy_young
/-- If [the absorption constant is positive](hyp:hε), [the mixed term is nonnegative](hyp:hz),
[the energy is nonnegative](hyp:hE), [the remainder is nonnegative](hyp:hD), and [the squared
mixed term is bounded by the energy times the remainder](hyp:h), then [twice the
mixed term is at most the absorption constant times the energy plus the remainder
divided by that constant](goal). -/
lemma source_scalar_energy_young {ε z E D : ℝ} (hε : 0 < ε)
    (hz : 0 ≤ z) (hE : 0 ≤ E) (hD : 0 ≤ D) (h : z ^ 2 ≤ E * D) :
    2 * z ≤ ε * E + ε⁻¹ * D := by
  have he : (ε * E + ε⁻¹ * D) ^ 2 = (ε * E - ε⁻¹ * D) ^ 2 + 4 * E * D := by
    field_simp
    <;> ring
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [he]
  nlinarith [sq_nonneg (ε * E - ε⁻¹ * D)]

end Papers.TsAdaptiveEstimationInference
