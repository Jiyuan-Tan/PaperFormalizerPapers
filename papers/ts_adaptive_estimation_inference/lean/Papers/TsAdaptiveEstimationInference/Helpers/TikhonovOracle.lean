module
public import Papers.TsAdaptiveEstimationInference.Helpers.Acceptance

/-! Scalar oracle estimates and boundedness for the one-step TRAE rate. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped Topology

/-- If [the hypothesis class and its function versions are bounded by B](hyp:hb)
and [h belongs to that class](hyp:hh), then [the Hilbert norm of h is at most B](goal). -/
-- @node: trae_hypothesis_norm_le
lemma trae_hypothesis_norm_le {𝒲 𝒳 𝒵 : Type*}
    [MeasurableSpace 𝒲] [MeasurableSpace 𝒳] [MeasurableSpace 𝒵]
    (V : IVWorld 𝒲 𝒳 𝒵) (B : ℝ) (hb : TRAEBoundedness V B)
    (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) : ‖h‖ ≤ B := by
  have ha : ∀ᵐ w ∂V.law, ‖(h : Lp ℝ 2 V.law) w‖ ≤ B := by
    filter_upwards [hb.2.2.1, V.primal_coherent h] with w hw heq
    simpa only [← heq, Real.norm_eq_abs, primalVersion] using hw h hh
  have hn := Lp.norm_le_of_ae_bound hb.1 ha
  simpa [measureUnivNNReal] using hn

/-- If [the grid factor lies between one-half inclusive and one exclusive](hyp:hρ)
and [the penalty belongs to the finite regularization grid](hyp:hlam), then
[the penalty is positive and at most two](goal). -/
-- @node: trae_grid_domain
lemma trae_grid_domain (ρ : ℝ) (hρ : GridDomain ρ) (n : ℕ)
    (lam : ℝ) (hlam : lam ∈ regGrid ρ n) : lam ∈ Set.Ioc (0 : ℝ) 2 := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
  have hpos : 0 < ρ := by linarith [hρ.1]
  constructor
  · exact mul_pos (by norm_num) (pow_pos hpos k)
  · have := pow_le_one₀ hpos.le hρ.2.le (n := k)
    dsimp [gridValue]
    linarith

/-- Suppose [the grid factor lies between one-half inclusive and one exclusive](hyp:hρ),
[c is positive](hyp:hc) and [at most one](hyp:hc1), [p exceeds one](hyp:hp)
and [is at most two](hyp:hp2), [d is positive](hyp:hd) and [at most c](hyp:hdc),
[the sample size is positive](hyp:hn), and [its reciprocal is at most d squared](hyp:hfloor).
Then [the oracle point at radius c times d to the power 2/p belongs to the grid
and lies between that radius times the grid factor and the radius itself](goal). -/
-- @node: trae_small_noise_oracle
lemma trae_small_noise_oracle (ρ c p d : ℝ) (n : ℕ)
    (hρ : GridDomain ρ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 1 < p) (hp2 : p ≤ 2) (hd : 0 < d) (hdc : d ≤ c)
    (hn : 0 < n) (hfloor : 1 / (n : ℝ) ≤ d ^ 2) :
    oraclePoint ρ n (c * d ^ (2 / p)) ∈ regGrid ρ n ∧
      ρ * (c * d ^ (2 / p)) ≤ oraclePoint ρ n (c * d ^ (2 / p)) ∧
      oraclePoint ρ n (c * d ^ (2 / p)) ≤ c * d ^ (2 / p) := by
  have hd1 : d ≤ 1 := hdc.trans hc1
  have hpow : d ^ 2 ≤ d ^ (2 / p) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge hd hd1
      ((div_le_iff₀ (by linarith : 0 < p)).2 (by linarith))
  have hdpow : d ^ (2 / p) ≤ 1 :=
    Real.rpow_le_one hd.le hd1 (by positivity)
  apply oraclePoint_radius_bounds ρ _ n hρ (by nlinarith)
  have ht := terminalGrid_le ρ hρ n hn
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (n : ℝ)) hfloor 2
  have hd2c : d ^ 2 ≤ c := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
  calc
    gridValue ρ (terminalIndex ρ n) ≤ 1 / (n : ℝ) ^ 2 := ht
    _ = (1 / (n : ℝ)) ^ 2 := by ring
    _ ≤ (d ^ 2) ^ 2 := hsq
    _ ≤ c * d ^ 2 := by nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hd2c)]
    _ ≤ c * d ^ (2 / p) := mul_le_mul_of_nonneg_left hpow hc.le

/-- If [the bias coefficient is nonnegative](hyp:hCb), [c is nonnegative](hyp:hc),
[p is positive](hyp:hp), [d is nonnegative](hyp:hd), [the penalty is nonnegative](hyp:hlam)
and [at most c times d to the power 2/p](hyp:hupper), and [the bias coefficient
times c to the power p is at most one-half](hyp:hsmall), then [the bias coefficient
times the penalty to the power p is at most half of d squared](goal). -/
-- @node: trae_oracle_bias_crossing
lemma trae_oracle_bias_crossing (Cb c p d lam : ℝ)
    (hCb : 0 ≤ Cb) (hc : 0 ≤ c) (hp : 0 < p) (hd : 0 ≤ d)
    (hlam : 0 ≤ lam) (hupper : lam ≤ c * d ^ (2 / p))
    (hsmall : Cb * c ^ p ≤ 1 / 2) : Cb * lam ^ p ≤ 1 / 2 * d ^ 2 := by
  have heq : (c * d ^ (2 / p)) ^ p = c ^ p * d ^ 2 := by
    rw [Real.mul_rpow hc (Real.rpow_nonneg hd _), ← Real.rpow_mul hd,
      div_mul_cancel₀ _ hp.ne', Real.rpow_two]
  calc
    Cb * lam ^ p ≤ Cb * (c * d ^ (2 / p)) ^ p :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlam hupper hp.le) hCb
    _ = (Cb * c ^ p) * d ^ 2 := by rw [heq]; ring
    _ ≤ 1 / 2 * d ^ 2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg d)

/-- If [the grid factor is positive](hyp:hρ), [c is positive](hyp:hc),
[p is positive](hyp:hp), [d is positive](hyp:hd), and [the penalty is at least
the grid factor times c times d to the power 2/p](hyp:hlower), then [d squared
divided by the penalty is at most the reciprocal of the grid factor times c,
multiplied by d to the power 2(p−1)/p](goal). -/
-- @node: trae_oracle_variance_rate
lemma trae_oracle_variance_rate (ρ c p d lam : ℝ)
    (hρ : 0 < ρ) (hc : 0 < c) (hp : 0 < p) (hd : 0 < d)
    (hlower : ρ * (c * d ^ (2 / p)) ≤ lam) :
    d ^ 2 / lam ≤ (ρ * c)⁻¹ * d ^ (2 * (p - 1) / p) := by
  have hr : 0 < ρ * (c * d ^ (2 / p)) := by positivity
  calc
    d ^ 2 / lam ≤ d ^ 2 / (ρ * (c * d ^ (2 / p))) :=
      div_le_div_of_nonneg_left (sq_nonneg d) hr hlower
    _ = (ρ * c)⁻¹ * d ^ (2 * (p - 1) / p) := by
      have he : 2 * (p - 1) / p = 2 - 2 / p := by field_simp
      rw [he, Real.rpow_sub hd, Real.rpow_two]
      field_simp

/-- If [c is positive](hyp:hc) and [at most one](hyp:hc1), [d is at least c](hyp:hdc),
and [the exponent is nonnegative](hyp:ha) and [at most two](hyp:ha2), then
[both d squared and d to that exponent are at least c squared](goal). -/
-- @node: trae_large_noise_floor
lemma trae_large_noise_floor (c d a : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hdc : c ≤ d) (ha : 0 ≤ a) (ha2 : a ≤ 2) :
    c ^ 2 ≤ d ^ 2 ∧ c ^ 2 ≤ d ^ a := by
  constructor
  · exact pow_le_pow_left₀ hc.le hdc 2
  · calc
      c ^ 2 = c ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ ≤ c ^ a := Real.rpow_le_rpow_of_exponent_ge hc hc1 ha2
      _ ≤ d ^ a := Real.rpow_le_rpow hc.le hdc ha

end Papers.TsAdaptiveEstimationInference
