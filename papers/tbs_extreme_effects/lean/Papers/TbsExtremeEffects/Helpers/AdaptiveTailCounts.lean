module
public import Papers.TbsExtremeEffects.Helpers.Hill.QuantileLower
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A polynomial radial lower tail makes the endpoint exceedance counts
diverge in both adaptive-threshold regimes. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped Topology
variable {q d m : ℕ}

/-- For [an extreme-value model](hyp:M), [tail parameters](hyp:tp), [regularly varying noise](hyp:hRV), and [a Pareto tail representation](hyp:model), [there is a positive polynomial lower envelope for the radial tail beyond some threshold](goal). -/
-- @node: radial_polynomial_tail_lower
lemma radial_polynomial_tail_lower (M : ExtremeModel q d) (tp : TailParams)
    (hRV : NoiseRegularlyVarying M) (model : ParetoTailModel M m tp) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, ∀ t ≥ T, C * t ^ (-M.beta) ≤ tailProb M t := by
  obtain ⟨k, hk, kappa, hkappa, hTransfer⟩ := hill_radial_survival_transfer M tp model
  have hm : 0 < m := by
    obtain ⟨hd, hdm⟩ := model.constants.1
    omega
  let i : Fin m := ⟨0, hm⟩
  let a := l1Norm (fun r => model.A r i)
  have ha : 0 < a := model.constants.2.1.trans_le (model.matrix.2.1 i).1
  let cutoff := tp.u * (tp.zeta * (k : ℝ) ^ ((1 - 2 * tp.s) / M.beta))
  refine ⟨kappa * (a / 2) ^ M.beta,
    mul_pos hkappa (Real.rpow_pos_of_pos (by positivity) _), max (cutoff + 1) tp.u, ?_⟩
  intro t ht
  have hcut : cutoff < t := by linarith [le_max_left (cutoff + 1) tp.u]
  rw [hTransfer t hcut]
  have hnominal := hill_nominal_matrix_tail_lower hRV.1 model.A model.matrix.1
    (fun j => model.constants.2.1.trans_le (model.matrix.2.1 j).1) i
    ((model.matrix.2.1 i).2.trans ((le_max_right _ _).trans ht))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hnominal hkappa.le

/-- If [the lower-envelope constant is positive](hyp:hC), [the threshold multiplier is positive](hyp:hc), [the threshold exponent is positive](hyp:hk), [the resulting count exponent is positive](hyp:hCount), and [the tail obeys the stated lower envelope](hyp:hLower), then [expected exceedance counts at the polynomial threshold diverge](goal). -/
-- @node: polynomial_tail_count_tendsto_atTop
lemma polynomial_tail_count_tendsto_atTop (F : ℝ → ℝ) {beta C T c kappa : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hk : 0 < kappa) (hCount : 0 < 1 - beta * kappa)
    (hLower : ∀ t ≥ T, C * t ^ (-beta) ≤ F t) :
    Tendsto (fun n : ℕ => (n : ℝ) * F (c * (n : ℝ) ^ kappa)) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hThreshold : Tendsto (fun n : ℕ => c * (n : ℝ) ^ kappa) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr ((tendsto_rpow_atTop hk).comp hn)
  have hCoefficient : 0 < C * c ^ (-beta) :=
    mul_pos hC (Real.rpow_pos_of_pos hc _)
  have hScale : Tendsto (fun n : ℕ =>
      (C * c ^ (-beta)) * (n : ℝ) ^ (1 - beta * kappa)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hCoefficient).mpr
      ((tendsto_rpow_atTop hCount).comp hn)
  apply tendsto_atTop_mono' atTop _ hScale
  filter_upwards [hThreshold.eventually (eventually_ge_atTop T),
    eventually_ge_atTop (1 : ℕ)] with n hlarge hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    _ = (n : ℝ) * (C * (c * (n : ℝ) ^ kappa) ^ (-beta)) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hnpos.le _),
        ← Real.rpow_mul hnpos.le,
        show 1 - beta * kappa = 1 + kappa * (-beta) by ring,
        Real.rpow_add hnpos, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hLower _ hlarge) hnpos.le

/-- For [an extreme-value model](hyp:M) with [tail parameters](hyp:tp), if [its noise is regularly varying](hyp:hRV), [it admits a Pareto tail representation](hyp:hTail), [the threshold multiplier is positive](hyp:hc), [the threshold exponent is positive](hyp:hk), [the target count exponent is positive](hyp:hr), and [the exponents satisfy the displayed identity](hyp:hCount), then [the expected band count diverges](goal). -/
-- @node: adaptive_band_count_tendsto_atTop
lemma adaptive_band_count_tendsto_atTop (M : ExtremeModel q d) (tp : TailParams)
    (hRV : NoiseRegularlyVarying M) (hTail : Nonempty (ParetoTailModel M m tp))
    {c kappa r : ℝ} (hc : 0 < c) (hk : 0 < kappa) (hr : 0 < r)
    (hCount : (1 - M.beta * kappa) / 2 = r) :
    Tendsto (fun n : ℕ => (n : ℝ) * tailProb M (c * (n : ℝ) ^ kappa)) atTop atTop := by
  obtain ⟨model⟩ := hTail
  obtain ⟨C, hC, T, hLower⟩ := radial_polynomial_tail_lower M tp hRV model
  exact polynomial_tail_count_tendsto_atTop (tailProb M) hC hc hk (by linarith) hLower

end Papers.TbsExtremeEffects
