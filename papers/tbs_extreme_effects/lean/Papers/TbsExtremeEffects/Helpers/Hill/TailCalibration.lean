module
public import Papers.TbsExtremeEffects.Helpers.Hill.NumericalBudget
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Choosing the fixed density-error coefficient and its tail threshold. -/

public section
namespace Papers.TbsExtremeEffects
open Filter
open scoped Topology

/-- If [the scaling coefficient is positive](hyp:hB) and [the shift error is nonnegative](hyp:hS),
there [exists a nonnegative coefficient controlling both the scaled error and shift](goal).
@node: hill_tail_coefficient_exists -/
lemma hill_tail_coefficient_exists {A B S : ℝ}
    (hB : 0 < B) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ A ≤ B * (C / 2) ∧ S ≤ C / 2 := by
  refine ⟨2 * max (A / B) S, ?_, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (hS.trans (le_max_right _ _))
  · have h := (div_le_iff₀ hB).mp (le_max_left (A / B) S)
    nlinarith
  · nlinarith [le_max_right (A / B) S]

/-- When [the tail index is positive](hyp:hb), the stated coefficient times the corresponding
power, or boundary logarithmic, envelope [tends to zero at large arguments](goal).
@node: hill_tail_envelope_tendsto_zero -/
lemma hill_tail_envelope_tendsto_zero {beta : ℝ} (hb : 0 < beta) (C : ℝ) :
    Tendsto (fun v : ℝ => if beta = 1 then C * v ^ (-1 : ℝ) * Real.log v
      else C * v ^ (-min 1 (1 / beta))) atTop (𝓝 0) := by
  by_cases heq : beta = 1
  · simp only [heq, if_true, Real.rpow_neg_one]
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul C
    simpa only [pow_one, one_mul, mul_one, add_zero, mul_zero, div_eq_mul_inv, mul_comm,
      mul_left_comm, mul_assoc] using h
  · simp only [if_neg heq]
    have hp : 0 < min 1 (1 / beta) := lt_min (by norm_num) (by positivity)
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hp).const_mul C

/-- When [the tail index is positive](hyp:hb), the stated power or boundary-logarithmic envelope
[is eventually no larger than one half](goal).
@node: hill_tail_envelope_eventually_small -/
lemma hill_tail_envelope_eventually_small {beta : ℝ} (hb : 0 < beta) (C : ℝ) :
    ∀ᶠ v : ℝ in atTop, (if beta = 1 then C * v ^ (-1 : ℝ) * Real.log v
      else C * v ^ (-min 1 (1 / beta))) ≤ 1 / 2 := by
  exact ((tendsto_order.mp (hill_tail_envelope_tendsto_zero hb C)).2 (1 / 2)
    (by norm_num)).mono (fun _ h => h.le)

/-- If [the tail index is positive](hyp:hb) and [the scale is positive](hyp:hc), then eventually
the argument is at least one and the Pareto quantile lower bound [exceeds `exp(1)`](goal).
@node: hill_quantile_lower_eventually_large -/
lemma hill_quantile_lower_eventually_large {beta c : ℝ} (hb : 0 < beta) (hc : 0 < c) :
    ∀ᶠ v : ℝ in atTop, 1 ≤ v ∧ Real.exp 1 ≤ c * v ^ (1 / beta) := by
  have h := (tendsto_rpow_atTop (by positivity : 0 < 1 / beta)).eventually
    (eventually_ge_atTop (Real.exp 1 / c))
  filter_upwards [eventually_ge_atTop (1 : ℝ), h] with v hv hpow
  exact ⟨hv, by have := (div_le_iff₀ hc).mp hpow; nlinarith⟩

/-- If [the tail index is positive](hyp:hb) and [the scale is positive](hyp:hc), then the Pareto
quantile lower bound [eventually exceeds the given cutoff](goal).
@node: hill_quantile_lower_eventually_above_cutoff -/
lemma hill_quantile_lower_eventually_above_cutoff {beta c : ℝ}
    (hb : 0 < beta) (hc : 0 < c) (r : ℝ) :
    ∀ᶠ v : ℝ in atTop, r < c * v ^ (1 / beta) := by
  have h := (tendsto_rpow_atTop (by positivity : 0 < 1 / beta)).eventually
    (eventually_ge_atTop ((r + 1) / c))
  filter_upwards [h] with v hv
  have := (div_le_iff₀ hc).mp hv
  nlinarith

end Papers.TbsExtremeEffects
