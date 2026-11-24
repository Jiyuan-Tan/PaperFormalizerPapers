module

public import Papers.HawkesD75660b.Helpers.AnalyticBorel.Basic
public import Papers.HawkesD75660b.Helpers.AnalyticBorel.AbelIdentity
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Independent convergence bounds for the rooted-tree series used in Borel normalization.
No result in this file uses normalization or the Borel generating-function equation. -/

@[expose] public section

noncomputable section

namespace Papers.HawkesD75660b.AnalyticBorel

/-- For [a real argument z](hyp:z) and [a nonnegative integer degree n](hyp:n),
the [rooted labelled-tree exponential generating-series term](goal) is zero
when n is zero and otherwise equals n to the power n minus one, times z to the
power n, divided by n factorial. -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeTerm
def rootedTreeTerm (z : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (n - 1) * z ^ n / (n.factorial : ℝ)

/-- If [z is nonnegative](hyp:hz), then [every rooted-tree term at z is
nonnegative](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeTerm_nonneg
lemma rootedTreeTerm_nonneg {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ rootedTreeTerm z n := by
  unfold rootedTreeTerm
  split_ifs <;> positivity

/-- If [z is nonnegative](hyp:hz), then [the degree-n rooted-tree term at z
is at most the nth power of the product of z and exp(1)](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeTerm_le_geometric
lemma rootedTreeTerm_le_geometric {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    rootedTreeTerm z n ≤ (z * Real.exp 1) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp [rootedTreeTerm]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hp : (n : ℝ) ^ (n - 1) ≤ (n : ℝ) ^ n :=
    pow_le_pow_right₀ hn1 (Nat.sub_le n 1)
  have he := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  calc
    rootedTreeTerm z n = ((n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) * z ^ n := by
      simp only [rootedTreeTerm, hn, ↓reduceIte]
      ring
    _ ≤ Real.exp (n : ℝ) * z ^ n := by
      gcongr
      exact (div_le_div_of_nonneg_right hp (Nat.cast_nonneg _)).trans he
    _ = (z * Real.exp 1) ^ n := by
      rw [mul_pow, ← Real.exp_nat_mul]
      simp [mul_comm]

/-- If [z is nonnegative](hyp:hz) and [less than exp(−1)](hyp:hzlt), then
[the rooted-tree terms at z form a summable series](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeTerm_summable
lemma rootedTreeTerm_summable {z : ℝ} (hz : 0 ≤ z) (hzlt : z < Real.exp (-1)) :
    Summable (rootedTreeTerm z) := by
  have hq : z * Real.exp 1 < 1 := by
    calc
      z * Real.exp 1 < Real.exp (-1) * Real.exp 1 :=
        mul_lt_mul_of_pos_right hzlt (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add]; norm_num
  exact Summable.of_nonneg_of_le (rootedTreeTerm_nonneg hz)
    (rootedTreeTerm_le_geometric hz)
    (summable_geometric_of_lt_one (mul_nonneg hz (Real.exp_pos _).le) hq)

/-- At [a real argument z](hyp:z), the [rooted-tree series](goal) is the
infinite sum of the rooted-tree terms over all nonnegative integer degrees. -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries
def rootedTreeSeries (z : ℝ) : ℝ := ∑' n : ℕ, rootedTreeTerm z n

/-- [The rooted-tree series equals zero at zero](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_zero
lemma rootedTreeSeries_zero : rootedTreeSeries 0 = 0 := by
  have hz (n : ℕ) : rootedTreeTerm 0 n = 0 := by
    cases n <;> simp [rootedTreeTerm]
  simp only [rootedTreeSeries, hz, tsum_zero]

/-- If [x is nonnegative](hyp:hx) and [x is at most y](hyp:hxy), then
[each rooted-tree term at x is at most the corresponding term at y](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeTerm_mono
lemma rootedTreeTerm_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    rootedTreeTerm x n ≤ rootedTreeTerm y n := by
  unfold rootedTreeTerm
  split_ifs
  · exact le_rfl
  · gcongr

/-- [For any fixed degree, the rooted-tree term is a continuous function of its
real argument](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeTerm_continuous
@[fun_prop] lemma rootedTreeTerm_continuous (n : ℕ) :
    Continuous (fun z : ℝ => rootedTreeTerm z n) := by
  unfold rootedTreeTerm
  split_ifs <;> fun_prop

/-- If [a is nonnegative](hyp:ha) and [less than exp(−1)](hyp:halt), then
[the rooted-tree series is continuous on the closed interval from zero to a](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_continuousOn
@[fun_prop] lemma rootedTreeSeries_continuousOn {a : ℝ} (ha : 0 ≤ a)
    (halt : a < Real.exp (-1)) : ContinuousOn rootedTreeSeries (Set.Icc 0 a) := by
  apply continuousOn_tsum (fun n => (rootedTreeTerm_continuous n).continuousOn)
    (rootedTreeTerm_summable ha halt)
  intro n x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (rootedTreeTerm_nonneg hx.1 n)]
  exact rootedTreeTerm_mono hx.1 hx.2 n

/-- If [ρ is positive](hyp:hρ), then [each Borel mass equals the corresponding
rooted-tree term evaluated at ρ times exp(−ρ), divided by ρ](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borelMass_eq_rootedTreeTerm
lemma borelMass_eq_rootedTreeTerm {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    borelMass ρ n = ρ⁻¹ * rootedTreeTerm (ρ * Real.exp (-ρ)) n := by
  cases n with
  | zero => simp [borelMass, rootedTreeTerm]
  | succ n =>
    simp only [borelMass, rootedTreeTerm, Nat.succ_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel, mul_pow, ← Real.exp_nat_mul]
    rw [pow_succ ρ]
    have he : (n + 1 : ℝ) * -ρ = -ρ * (n + 1) := by ring
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [he]
    field_simp

/-- If [ρ lies strictly between zero and one](hyp:hρ), then [ρ times exp(−ρ)
is strictly less than exp(−1)](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borel_tree_argument_lt
lemma borel_tree_argument_lt {ρ : ℝ} (hρ : 0 < ρ ∧ ρ < 1) :
    ρ * Real.exp (-ρ) < Real.exp (-1) := by
  have h : ρ < Real.exp (ρ - 1) := by
    have := Real.add_one_lt_exp (show ρ - 1 ≠ 0 by linarith)
    linarith
  calc
    ρ * Real.exp (-ρ) < Real.exp (ρ - 1) * Real.exp (-ρ) :=
      mul_lt_mul_of_pos_right h (Real.exp_pos _)
    _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring

/-- If [ρ lies strictly between zero and one](hyp:hρ), then [the Borel masses
with parameter ρ form a summable series](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.borelMass_summable_independent
lemma borelMass_summable_independent {ρ : ℝ} (hρ : 0 < ρ ∧ ρ < 1) :
    Summable (borelMass ρ) := by
  change Summable (fun n => borelMass ρ n)
  simpa only [borelMass_eq_rootedTreeTerm hρ.1] using
    (rootedTreeTerm_summable (mul_pos hρ.1 (Real.exp_pos _)).le
      (borel_tree_argument_lt hρ)).mul_left ρ⁻¹

/-- [The function sending t to t times exp(−t) is strictly increasing on the
closed interval from zero to one](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeArgument_strictMonoOn
lemma treeArgument_strictMonoOn :
    StrictMonoOn (fun t : ℝ => t * Real.exp (-t)) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by fun_prop)
  intro t ht
  rw [interior_Icc] at ht
  have hd : HasDerivAt (fun t : ℝ => t * Real.exp (-t))
      (Real.exp (-t) * (1 - t)) t := by
    convert (hasDerivAt_id t).mul ((Real.hasDerivAt_exp (-t)).comp t
      (hasDerivAt_id t).neg) using 1 <;> first | rfl | (dsimp; ring)
  rw [hd.deriv]
  exact mul_pos (Real.exp_pos _) (sub_pos.mpr ht.2)

/-- [The function sending t to t times exp(−t) is one-to-one on the closed
interval from zero to one](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.treeArgument_injOn
lemma treeArgument_injOn :
    Set.InjOn (fun t : ℝ => t * Real.exp (-t)) (Set.Icc 0 1) :=
  treeArgument_strictMonoOn.injOn

end Papers.HawkesD75660b.AnalyticBorel
