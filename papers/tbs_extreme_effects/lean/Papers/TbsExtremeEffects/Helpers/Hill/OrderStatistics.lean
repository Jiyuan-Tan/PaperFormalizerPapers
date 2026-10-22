module
public import Papers.TbsExtremeEffects.Helpers.Hill.Threshold

/-! Measurability of decreasing finite order statistics. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped BigOperators

/-- For [a decreasing ordering of the observations](hyp:hY) that [is a permutation of the original data](hyp:hsort), [an order statistic exceeds a threshold exactly when more observations than its rank exceed that threshold](goal). -/
-- @node: hill_order_statistic_exceedance_iff
lemma hill_order_statistic_exceedance_iff {n : ℕ}
    (V Y : Fin n → ℝ) (hY : Antitone Y)
    (hsort : ∃ σ : Equiv.Perm (Fin n), ∀ i, Y i = V (σ i))
    (k : Fin n) (z : ℝ) :
    z < Y k ↔ (k : ℝ) < ∑ i : Fin n, if z < V i then (1 : ℝ) else 0 := by
  classical
  obtain ⟨σ, hσ⟩ := hsort
  have hsum : (∑ i : Fin n, if z < V i then (1 : ℝ) else 0) =
      ∑ i : Fin n, if z < Y i then (1 : ℝ) else 0 := by
    simp_rw [hσ]
    exact (Equiv.sum_comp σ (fun v => if z < V v then (1 : ℝ) else 0)).symm
  rw [hsum, Finset.sum_boole]
  exact_mod_cast (Tuple.lt_card_gt_iff_apply_gt_of_antitone hY).symm

/-- Given [a finite collection of real-valued observations indexed by the sample](hyp:V), [an outcome](hyp:w), and [an order-statistic rank](hyp:i), [the decreasing Hill order statistic](goal) is the observation at that rank after sorting the sample from largest to smallest. -/
-- @node: hillDecreasingOrder
noncomputable def hillDecreasingOrder {Ω : Type*} {n : ℕ} (V : Fin n → Ω → ℝ)
    (w : Ω) (i : Fin n) : ℝ :=
  V (Tuple.sort (fun j => V j w) i.rev) w

/-- For [a finite collection of real-valued observations](hyp:V), [the decreasing Hill order statistics are decreasing in rank at every outcome and are a permutation of the original observations](goal). -/
-- @node: hill_decreasing_order_data
lemma hill_decreasing_order_data {Ω : Type*} {n : ℕ} (V : Fin n → Ω → ℝ) :
    (∀ w, Antitone (hillDecreasingOrder V w)) ∧
    (∀ w, ∃ σ : Equiv.Perm (Fin n), ∀ i, hillDecreasingOrder V w i = V (σ i) w) := by
  constructor
  · intro w i j hij
    exact Tuple.monotone_sort (fun l => V l w) (Fin.rev_le_rev.mpr hij)
  · intro w
    exact ⟨Fin.revPerm.trans (Tuple.sort (fun j => V j w)), fun _ => rfl⟩

/-- If [each observation coordinate is measurable](hyp:hV), then [the selected decreasing Hill order statistic is measurable](goal). -/
-- @node: hill_decreasing_order_measurable
@[fun_prop]
lemma hill_decreasing_order_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (V : Fin n → Ω → ℝ) (hV : ∀ i, Measurable (V i)) (k : Fin n) :
    Measurable (fun w => hillDecreasingOrder V w k) := by
  apply measurable_of_Ioi
  intro z
  have hcount : Measurable (fun w => ∑ i : Fin n,
      if z < V i w then (1 : ℝ) else 0) := by
    exact Finset.measurable_sum _ (fun i _ =>
      Measurable.ite (measurableSet_lt measurable_const (hV i))
        measurable_const measurable_const)
  have hset : (fun w => hillDecreasingOrder V w k) ⁻¹' Set.Ioi z =
      {w | (k : ℝ) < ∑ i : Fin n, if z < V i w then (1 : ℝ) else 0} := by
    ext w
    exact hill_order_statistic_exceedance_iff (fun i => V i w) (hillDecreasingOrder V w)
      ((hill_decreasing_order_data V).1 w) ((hill_decreasing_order_data V).2 w) k z
  rw [hset]
  exact measurableSet_lt measurable_const hcount

end Papers.TbsExtremeEffects
