module
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationStep
/-! # Transport recurrences charged only at active topological slots

The exponent counts visited nodes rather than the length of the evaluation
horizon. Assigned-coordinate errors are accumulated once per node.
-/
public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal ENNReal

/-- Suppose [the finite node schedule assigns distinct times to distinct nodes](hyp:hinj),
[the accumulated error is a nonnegative, possibly infinite sequence](hyp:E),
[the amplification factor is nonnegative and possibly infinite](hyp:A),
[this factor is at least one](hyp:hA), and [each node has a nonnegative, possibly infinite error allowance](hyp:e).
If [the initial accumulated error is zero](hyp:hzero),
[each scheduled update is bounded by the amplified previous error plus that node's allowance](hyp:hstep),
and [unused time slots leave the error unchanged](hyp:hempty), then
[at any horizon the error is at most the amplification factor raised to the number of nodes scheduled before that horizon, times the sum of their allowances](goal). -/
-- @node: active_node_transport_recurrence
lemma active_node_transport_recurrence
    {I : Type*} [Fintype I] [DecidableEq I]
    (order : I → ℕ) (hinj : Function.Injective order)
    (E : ℕ → ℝ≥0∞) (A : ℝ≥0∞) (hA : 1 ≤ A) (e : I → ℝ≥0∞)
    (hzero : E 0 = 0)
    (hstep : ∀ i, E (order i+1) ≤ A * E (order i) + e i)
    (hempty : ∀ r, (∀ i, order i ≠ r) → E (r+1) = E r)
    (r : ℕ) :
    E r ≤ A ^ (Finset.univ.filter (fun i => order i < r)).card *
      ∑ i ∈ Finset.univ.filter (fun i => order i < r), e i := by
  classical
  induction r with
  | zero => simp [hzero]
  | succ r ih =>
    by_cases h : ∃ i, order i = r
    · obtain ⟨i, hi⟩ := h
      let S := Finset.univ.filter (fun j => order j < r)
      have hnot : i ∉ S := by simp [S, hi]
      have hnext : Finset.univ.filter (fun j => order j < r+1) = insert i S := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, S]
        constructor
        · intro hj
          by_cases heq : order j = r
          · exact Or.inl (hinj (heq.trans hi.symm))
          · exact Or.inr (by omega)
        · rintro (rfl | hj) <;> omega
      rw [hnext, Finset.card_insert_of_notMem hnot, Finset.sum_insert hnot, pow_succ]
      have hpow : 1 ≤ A ^ S.card * A :=
        (one_le_pow₀ hA).trans (le_mul_of_one_le_right zero_le hA)
      calc
        E (r+1) ≤ A * E r + e i := by simpa only [hi] using hstep i
        _ ≤ A * (A ^ S.card * ∑ j ∈ S, e j) + e i := by gcongr
        _ ≤ A * (A ^ S.card * ∑ j ∈ S, e j) + (A ^ S.card * A) * e i := by
          gcongr
          exact le_mul_of_one_le_left' hpow
        _ = _ := by ring
    · have he : ∀ i, order i ≠ r := by simpa only [not_exists] using h
      have hnext : Finset.univ.filter (fun j => order j < r+1) =
          Finset.univ.filter (fun j => order j < r) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := he j
        omega
      rw [hempty r he, hnext]
      exact ih

/-- Suppose [distinct nodes have distinct scheduled times](hyp:hinj),
[the accumulated error is a nonnegative, possibly infinite sequence](hyp:E),
[the amplification factor is nonnegative and possibly infinite](hyp:A),
[this factor is at least one](hyp:hA), and [each node has a nonnegative, possibly infinite error allowance](hyp:e).
If [the initial error is zero](hyp:hzero),
[each scheduled update is bounded by the amplified previous error plus the node's allowance](hyp:hstep),
and [unused time slots leave the error unchanged](hyp:hempty), then
[at every horizon the error is at most the amplification factor raised to the total number of nodes, times the sum of all node allowances](goal). -/
-- @node: active_node_transport_uniform_bound
lemma active_node_transport_uniform_bound
    {I : Type*} [Fintype I] [DecidableEq I]
    (order : I → ℕ) (hinj : Function.Injective order)
    (E : ℕ → ℝ≥0∞) (A : ℝ≥0∞) (hA : 1 ≤ A) (e : I → ℝ≥0∞)
    (hzero : E 0 = 0)
    (hstep : ∀ i, E (order i+1) ≤ A * E (order i) + e i)
    (hempty : ∀ r, (∀ i, order i ≠ r) → E (r+1) = E r)
    (r : ℕ) :
    E r ≤ A ^ Fintype.card I * ∑ i, e i := by
  refine (active_node_transport_recurrence order hinj E A hA e hzero hstep hempty r).trans ?_
  apply mul_le_mul'
  · exact pow_le_pow_right₀ hA (Finset.card_le_univ _)
  · exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end Papers.TbsNeuralCausalPi
