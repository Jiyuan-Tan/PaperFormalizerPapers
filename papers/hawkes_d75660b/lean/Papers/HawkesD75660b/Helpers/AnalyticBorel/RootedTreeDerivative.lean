module

public import Papers.HawkesD75660b.Helpers.AnalyticBorel.RootedTreeConvolution
public import Mathlib.Analysis.Calculus.SmoothSeries

/-! Termwise differentiation of the rooted-tree series, independently of normalization. -/

@[expose] public section

noncomputable section

namespace Papers.HawkesD75660b.AnalyticBorel

/-- At [a real argument z](hyp:z) and [a nonnegative integer degree n](hyp:n),
the [derivative term of the rooted-tree series](goal) is zero for degree zero and
otherwise equals n to the power n minus one, times n times z to the power n minus
one, divided by n factorial. -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeDerivTerm
def rootedTreeDerivTerm (z : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (n : ℝ) ^ (n - 1) * ((n : ℝ) * z ^ (n - 1)) / (n.factorial : ℝ)

/-- [Each rooted-tree term has derivative equal to its corresponding derivative
term at every real argument](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeTerm_hasDerivAt
lemma rootedTreeTerm_hasDerivAt (z : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rootedTreeTerm x n) (rootedTreeDerivTerm z n) z := by
  by_cases hn : n = 0
  · subst n
    simpa [rootedTreeTerm, rootedTreeDerivTerm] using hasDerivAt_const z (0 : ℝ)
  · simpa [rootedTreeTerm, rootedTreeDerivTerm, hn] using
      (((hasDerivAt_id z).pow n).const_mul ((n : ℝ) ^ (n - 1))).div_const
        (n.factorial : ℝ)

/-- [Multiplying a rooted-tree derivative term by its argument gives the
corresponding degree-weighted rooted-tree term](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeDerivTerm_mul
lemma rootedTreeDerivTerm_mul (z : ℝ) (n : ℕ) :
    z * rootedTreeDerivTerm z n = rootedTreeWeightedTerm z n := by
  cases n with
  | zero => simp [rootedTreeDerivTerm, rootedTreeWeightedTerm]
  | succ n =>
    simp only [rootedTreeDerivTerm, rootedTreeWeightedTerm, rootedTreeTerm,
      Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [pow_succ z]
    ring

/-- If [a is positive](hyp:ha) and [less than exp(−1)](hyp:halt), then
[the rooted-tree derivative terms at a form a summable series](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeDerivTerm_summable
lemma rootedTreeDerivTerm_summable {a : ℝ} (ha : 0 < a)
    (halt : a < Real.exp (-1)) : Summable (rootedTreeDerivTerm a) := by
  have he (n : ℕ) : rootedTreeDerivTerm a n =
      a⁻¹ * rootedTreeWeightedTerm a n := by
    rw [← rootedTreeDerivTerm_mul]
    field_simp
  change Summable (fun n => rootedTreeDerivTerm a n)
  simpa only [he] using (rootedTreeWeightedTerm_summable ha.le halt).mul_left a⁻¹

/-- If [the absolute value of x is at most a](hyp:hx), then [the absolute value
of each rooted-tree derivative term at x is bounded by the corresponding
derivative term at a](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeDerivTerm_norm_le
lemma rootedTreeDerivTerm_norm_le {a x : ℝ} (hx : |x| ≤ a)
    (n : ℕ) : ‖rootedTreeDerivTerm x n‖ ≤ rootedTreeDerivTerm a n := by
  unfold rootedTreeDerivTerm
  split_ifs
  · simp
  · simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
      abs_of_nonneg (Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ n.factorial)]
    gcongr

/-- If [the absolute value of z is less than exp(−1)](hyp:hz), then
[the rooted-tree series is differentiable at z, with derivative equal to the
sum of its derivative terms](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_hasDerivAt
lemma rootedTreeSeries_hasDerivAt {z : ℝ} (hz : |z| < Real.exp (-1)) :
    HasDerivAt rootedTreeSeries (∑' n, rootedTreeDerivTerm z n) z := by
  obtain ⟨a, hza, halt⟩ := exists_between hz
  have ha : 0 < a := (abs_nonneg z).trans_lt hza
  apply hasDerivAt_tsum_of_isPreconnected
    (rootedTreeDerivTerm_summable ha halt) isOpen_Ioo (convex_Ioo (-a) a).isPreconnected
    (g := fun n x => rootedTreeTerm x n) (g' := fun n x => rootedTreeDerivTerm x n)
    (y₀ := 0)
  · intro n y _
    exact rootedTreeTerm_hasDerivAt y n
  · intro n y hy
    exact rootedTreeDerivTerm_norm_le (abs_le.mpr ⟨hy.1.le, hy.2.le⟩) n
  · exact ⟨neg_neg_of_pos ha, ha⟩
  · have he (n : ℕ) : rootedTreeTerm 0 n = 0 := by
      cases n <;> simp [rootedTreeTerm]
    simp only [he, summable_zero]
  · exact abs_lt.mp hza

/-- If [z is nonnegative](hyp:hz) and [less than exp(−1)](hyp:hzlt), then
[z times the derivative of the rooted-tree series at z, times one minus the
series value at z, equals the series value at z](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_differential
lemma rootedTreeSeries_differential {z : ℝ} (hz : 0 ≤ z)
    (hzlt : z < Real.exp (-1)) :
    z * deriv rootedTreeSeries z * (1 - rootedTreeSeries z) = rootedTreeSeries z := by
  have hd := rootedTreeSeries_hasDerivAt (by rwa [abs_of_nonneg hz])
  have hw : z * deriv rootedTreeSeries z = rootedTreeWeightedSeries z := by
    rw [hd.deriv, rootedTreeWeightedSeries,
      ← tsum_mul_left, show (fun n => z * rootedTreeDerivTerm z n) =
        rootedTreeWeightedTerm z from funext (rootedTreeDerivTerm_mul z)]
  rw [hw]
  have hc := rootedTreeSeries_convolution hz hzlt
  nlinarith [hc]

/-- [The rooted-tree series has derivative one at zero](goal). -/
-- @node: Papers.HawkesD75660b.AnalyticBorel.rootedTreeSeries_hasDerivAt_zero
lemma rootedTreeSeries_hasDerivAt_zero : HasDerivAt rootedTreeSeries 1 0 := by
  have hd := rootedTreeSeries_hasDerivAt
    (show |(0 : ℝ)| < Real.exp (-1) by simpa using Real.exp_pos (-1))
  have hs : (∑' n, rootedTreeDerivTerm 0 n) = 1 := by
    rw [tsum_eq_single 1]
    · norm_num [rootedTreeDerivTerm]
    · intro n hn
      cases n with
      | zero => simp [rootedTreeDerivTerm]
      | succ n =>
        cases n with
        | zero => exact (hn rfl).elim
        | succ n => simp [rootedTreeDerivTerm]
  rwa [hs] at hd

end Papers.HawkesD75660b.AnalyticBorel
