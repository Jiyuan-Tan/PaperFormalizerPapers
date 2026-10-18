module
public import Causalean.Experimentation.Sequential.Ville
public import Mathlib.Tactic
public import Papers.TbsExtremeEffects.Helpers.Hill.Renyi
public import Toolkit.Foundations.Probability.Concentration.ExponentialSupermartingale

/-! Finite-horizon exponential concentration for the Hill spacing process.
Ville's inequality controls each sign; the Bernstein tilt gives the roadmap's
threshold with its exact constants. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- If [the horizon scale is positive](hyp:hm) and [the deviation budget is positive](hyp:hx), then [there is a tilt between zero and one whose Bernstein exponent at the stated threshold equals minus the budget](goal).
-/
-- @node: hill_bernstein_tilt
lemma hill_bernstein_tilt {m x : ℝ} (hm : 0 < m) (hx : 0 < x) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧
      -lam * (Real.sqrt (2 * m * x) + x) + m * (lam ^ 2 / (2 * (1 - lam))) = -x := by
  let s := Real.sqrt (2 * x / m)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hsone : 0 < 1 + s := by positivity
  have hsq : s ^ 2 = 2 * x / m := Real.sq_sqrt (by positivity)
  have hxrep : x = m * s ^ 2 / 2 := by
    have hh := (eq_div_iff hm.ne').mp hsq
    nlinarith
  have hroot : Real.sqrt (2 * m * x) = m * s := by
    have hsq' : (m * s) ^ 2 = 2 * m * x := by rw [hxrep]; ring
    have hr := Real.sq_sqrt (show 0 ≤ 2 * m * x by positivity)
    have hrnonneg := Real.sqrt_nonneg (2 * m * x)
    have hms : 0 < m * s := mul_pos hm hs
    nlinarith
  refine ⟨s / (1 + s), div_pos hs hsone, (div_lt_one hsone).mpr (by linarith), ?_⟩
  rw [hroot, hxrep]
  have hden : 1 - s / (1 + s) = 1 / (1 + s) := by field_simp; ring
  rw [hden]
  field_simp
  <;> ring

/-- If [the process starts at zero](hyp:hzero), [both signed Bernstein exponentials are supermartingales for every admissible tilt](hyp:hSuper), [the horizon has at least one observation](hyp:hm), and [the deviation budget is positive](hyp:hx), then [the probability that any partial sum crosses the Bernstein threshold is at most twice its exponential tail probability](goal).
-/
-- @node: hill_spacing_maximal_probability
lemma hill_spacing_maximal_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hzero : ∀ w, B 0 w = 0)
    (hSuper : ∀ lam : ℝ, 0 < lam → lam < 1 →
      Supermartingale (fun i w => Real.exp
        (lam * B i w - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) ℱ P ∧
      Supermartingale (fun i w => Real.exp
        (lam * (-B i w) - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) ℱ P)
    {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) :
    P.real {w | ∃ i ≤ m, Real.sqrt (2 * (m : ℝ) * x) + x < |B i w|} ≤
      2 * Real.exp (-x) := by
  obtain ⟨lam, hlam, hlamone, htilt⟩ :=
    hill_bernstein_tilt (show 0 < (m : ℝ) by exact_mod_cast hm) hx
  have hc : 0 ≤ lam ^ 2 / (2 * (1 - lam)) := by positivity
  have hplus := Toolkit.Foundations.Probability.Concentration.measureReal_exists_le_lt_le_exp_of_supermartingale_exp P B ℱ hlam hc hzero
    (hSuper lam hlam hlamone).1 m (a := Real.sqrt (2 * (m : ℝ) * x) + x)
  have hminus := Toolkit.Foundations.Probability.Concentration.measureReal_exists_le_lt_le_exp_of_supermartingale_exp P (fun i w => -B i w) ℱ hlam hc
    (fun w => by simp [hzero w]) (hSuper lam hlam hlamone).2 m
    (a := Real.sqrt (2 * (m : ℝ) * x) + x)
  rw [htilt] at hplus hminus
  have hsub : {w | ∃ i ≤ m, Real.sqrt (2 * (m : ℝ) * x) + x < |B i w|} ⊆
      {w | ∃ i ≤ m, Real.sqrt (2 * (m : ℝ) * x) + x < B i w} ∪
      {w | ∃ i ≤ m, Real.sqrt (2 * (m : ℝ) * x) + x < -B i w} := by
    rintro w ⟨i, hi, hcross⟩
    rcases lt_abs.mp hcross with h | h
    · exact Or.inl ⟨i, hi, h⟩
    · exact Or.inr ⟨i, hi, by linarith⟩
  calc
    _ ≤ P.real ({w | ∃ i ≤ m, Real.sqrt (2 * (m : ℝ) * x) + x < B i w} ∪
        {w | ∃ i ≤ m, Real.sqrt (2 * (m : ℝ) * x) + x < -B i w}) := measureReal_mono hsub
    _ ≤ P.real {w | ∃ i ≤ m, Real.sqrt (2 * (m : ℝ) * x) + x < B i w} +
        P.real {w | ∃ i ≤ m, Real.sqrt (2 * (m : ℝ) * x) + x < -B i w} :=
      measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-x) := by linarith

/-- For a confidence level [in the stated admissible domain](hyp:hd), [the logarithmic Hill budget is strictly positive](goal).
-/
-- @node: hill_logBudget_pos
lemma hill_logBudget_pos (n : ℕ) {delta : ℝ} (hd : ConfidenceDomain delta) :
    0 < hillLogBudget n delta := by
  apply Real.log_pos
  apply (lt_div_iff₀ hd.1).mpr
  have hJone : (1 : ℝ) ≤ hillGridSize n := by
    exact_mod_cast (show 1 ≤ hillGridSize n by unfold hillGridSize; omega)
  linarith [hd.2]

end Papers.TbsExtremeEffects
