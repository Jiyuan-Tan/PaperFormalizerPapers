module

public import Papers.HawkesD75660b.Helpers.AnalyticBorel.RootedTreeNormalization
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.IntermediateValue

/-! Borel normalization and the generating series, proved from the explicit masses. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Papers.HawkesD75660b.AnalyticBorel

/-- For [a real Borel parameter ρ](hyp:ρ) and [a real argument x](hyp:x),
the [Borel probability generating function](goal) is the infinite sum of the
Borel mass at each nonnegative integer j times x to the jth power. -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borelPGF
def borelPGF (ρ x : ℝ) : ℝ := ∑' j : ℕ, borelMass ρ j * x ^ j

/-- If [the Borel parameter ρ is positive](hyp:hρ),
[the Borel mass at every nonnegative integer j is nonnegative](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borelMass_nonneg
lemma borelMass_nonneg {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) : 0 ≤ borelMass ρ j := by
  unfold borelMass
  split_ifs
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (mul_nonneg hρ.le (Nat.cast_nonneg j)) _)) (Nat.cast_nonneg _)

/-- If [the Borel parameter ρ lies strictly between zero and one](hyp:hρ),
[the Borel masses sum to one](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borelMass_sum
lemma borelMass_sum {ρ : ℝ} (hρ : 0 < ρ ∧ ρ < 1) :
    HasSum (borelMass ρ) 1 := by
  have hs := (rootedTreeTerm_summable
    (mul_pos hρ.1 (Real.exp_pos (-ρ))).le (borel_tree_argument_lt hρ)).hasSum
  change HasSum (rootedTreeTerm (ρ * Real.exp (-ρ)))
    (rootedTreeSeries (ρ * Real.exp (-ρ))) at hs
  rw [rootedTreeSeries_borel_argument hρ] at hs
  convert hs.mul_left ρ⁻¹ using 1 <;> try rfl
  · exact funext (borelMass_eq_rootedTreeTerm hρ.1)
  · exact (inv_mul_cancel₀ hρ.1.ne').symm

/-- If [the Borel parameter ρ lies strictly between zero and one](hyp:hρ),
[the Borel measure is a probability measure](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borel_probability
lemma borel_probability {ρ : ℝ} (hρ : 0 < ρ ∧ ρ < 1) :
    IsProbabilityMeasure (borelMeasure ρ) := by
  constructor
  rw [borelMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (borelMass_nonneg hρ.1)
    (borelMass_sum hρ).summable, (borelMass_sum hρ).tsum_eq]
  norm_num

/-- If [ρ is positive](hyp:hρ) and [r is positive](hyp:hr),
[the Borel mass with parameter ρ at j equals r divided by ρ times the Borel
mass with parameter r at j times the jth power of the product of ρ divided by r
and the exponential of r − ρ](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borelMass_tilt
lemma borelMass_tilt {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (j : ℕ) :
    borelMass ρ j = (r / ρ) * borelMass r j * ((ρ / r) * Real.exp (r - ρ)) ^ j := by
  cases j with
  | zero => simp [borelMass]
  | succ j =>
    have he : Real.exp (-r * (j + 1)) * Real.exp ((j + 1) * (r - ρ)) =
        Real.exp (-ρ * (j + 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [borelMass, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one, mul_pow, div_pow, ← Real.exp_nat_mul] 
    rw [pow_succ ρ, pow_succ r]
    field_simp
    simpa only [neg_mul, mul_comm] using he.symm

/-- If [ρ is positive](hyp:hρ) and [x lies in the interval `(0, 1]`](hyp:hx),
[there exists a positive r no greater than ρ such that r times the exponential
of −r equals x times ρ times the exponential of −ρ](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borel_tilt_parameter
lemma borel_tilt_parameter {ρ x : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ r * Real.exp (-r) = x * ρ * Real.exp (-ρ) := by
  have hxpos : 0 < x := hx.1
  have hxone : x ≤ 1 := hx.2
  have hc : ContinuousOn (fun r : ℝ => r * Real.exp (-r)) (Set.Icc 0 ρ) := by
    fun_prop
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hρ.le hc
    (show x * ρ * Real.exp (-ρ) ∈
      Set.Icc ((0 : ℝ) * Real.exp (-0)) (ρ * Real.exp (-ρ)) from
      ⟨by simpa only [zero_mul] using (mul_pos (mul_pos hxpos hρ) (Real.exp_pos (-ρ))).le,
        by nlinarith [mul_pos hρ (Real.exp_pos (-ρ))]⟩)
  have hrpos : 0 < r := by
    by_contra hn
    have hz : r = 0 := le_antisymm (le_of_not_gt hn) hr.1
    subst r
    have hp : 0 < x * ρ * Real.exp (-ρ) := by positivity
    simp only [zero_mul] at he
    linarith
  exact ⟨r, hrpos, hr.2, he⟩

/-- [The Borel probability generating function at zero equals zero for every real parameter ρ](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borelPGF_zero
lemma borelPGF_zero (ρ : ℝ) : borelPGF ρ 0 = 0 := by
  unfold borelPGF
  have hz (j : ℕ) : borelMass ρ j * (0 : ℝ) ^ j = 0 := by
    cases j <;> simp [borelMass]
  simp only [hz, tsum_zero]

/-- If [ρ lies strictly between zero and one](hyp:hρ), [r is positive](hyp:hr),
[r is no greater than ρ](hyp:hrρ), and [r times the exponential of −r equals
x times ρ times the exponential of −ρ](hyp:he), then
[the Borel probability generating function with parameter ρ at x equals r divided by ρ](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borelPGF_tilt_value
lemma borelPGF_tilt_value {ρ r x : ℝ} (hρ : 0 < ρ ∧ ρ < 1)
    (hr : 0 < r) (hrρ : r ≤ ρ)
    (he : r * Real.exp (-r) = x * ρ * Real.exp (-ρ)) :
    borelPGF ρ x = r / ρ := by
  have hscale : ρ * Real.exp (r - ρ) * x = r := by
    calc
      ρ * Real.exp (r - ρ) * x = (x * ρ * Real.exp (-ρ)) * Real.exp r := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ = (r * Real.exp (-r)) * Real.exp r := by rw [he]
      _ = r := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hfactor : (ρ / r * Real.exp (r - ρ)) * x = 1 := by
    calc
      (ρ / r * Real.exp (r - ρ)) * x = (ρ * Real.exp (r - ρ) * x) / r := by ring
      _ = 1 := by rw [hscale, div_self hr.ne']
  have hterm (j : ℕ) : borelMass ρ j * x ^ j = (r / ρ) * borelMass r j := by
    rw [borelMass_tilt hρ.1 hr, mul_assoc, ← mul_pow, hfactor, one_pow, mul_one]
  have hs : HasSum (fun j : ℕ => borelMass ρ j * x ^ j) (r / ρ) := by
    simpa only [hterm, mul_one] using
      (borelMass_sum ⟨hr, hrρ.trans_lt hρ.2⟩).mul_left (r / ρ)
  exact hs.tsum_eq

/-- If [ρ lies strictly between zero and one](hyp:hρ) and
[x lies between zero and one, inclusive](hyp:hx), then
[the Borel probability generating function at x equals x times the exponential
of the product of ρ and the difference between its value and one, and its value
lies between zero and one, inclusive](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borelPGF_equation
lemma borelPGF_equation {ρ x : ℝ} (hρ : 0 < ρ ∧ ρ < 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    borelPGF ρ x = x * Real.exp (ρ * (borelPGF ρ x - 1)) ∧
      0 ≤ borelPGF ρ x ∧ borelPGF ρ x ≤ 1 := by
  by_cases hx0 : x = 0
  · subst x
    rw [borelPGF_zero]
    simp
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  obtain ⟨r, hr, hrρ, he⟩ := borel_tilt_parameter hρ.1 ⟨hxpos, hx.2⟩
  rw [borelPGF_tilt_value hρ hr hrρ he]
  refine ⟨?_, (div_pos hr hρ.1).le, (div_le_one hρ.1).mpr hrρ⟩
  have hexp : Real.exp (ρ * (r / ρ - 1)) = Real.exp (r - ρ) := by
    congr 1
    field_simp [hρ.1.ne']
  rw [hexp]
  apply (div_eq_iff hρ.1.ne').mpr
  calc
    r = (r * Real.exp (-r)) * Real.exp r := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = (x * ρ * Real.exp (-ρ)) * Real.exp r := by rw [he]
    _ = x * Real.exp (r - ρ) * ρ := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring

end Papers.HawkesD75660b.AnalyticBorel
