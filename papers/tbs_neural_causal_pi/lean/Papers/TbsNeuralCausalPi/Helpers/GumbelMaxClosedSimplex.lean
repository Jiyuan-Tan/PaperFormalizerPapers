module
public import Papers.TbsNeuralCausalPi.Helpers.GumbelMax
/-! # Gumbel winning probabilities on the closed probability simplex

Zero-weight labels have extended-log score minus infinity and cannot win.
The positive competitors give the same CDF product and Laplace integral as
in the strictly positive case.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- If [all label weights are nonnegative](hyp:hp), [their sum is positive](hyp:hsum),
and [label i is the smallest-index maximizer of extended log weights plus the
given real score offsets](hyp:hi), then [its weight is positive and its log weight
plus offset is at least that of every positive-weight label](goal). -/
-- @node: firstArgmax_positive_and_maximizes
lemma firstArgmax_positive_and_maximizes {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : 0 < ∑ j, p j) (G : Fin n → ℝ) (i : Fin n)
    (hi : firstArgmax (fun j => extendedLog (p j) + (G j : EReal)) = some i) :
    0 < p i ∧ ∀ j, 0 < p j → Real.log (p j) + G j ≤ Real.log (p i) + G i := by
  rw [firstArgmax_eq_firstPositiveArgmax p hp hsum G] at hi
  have h := List.find?_some (by simpa only [firstPositiveArgmax] using hi)
  simpa using h

/-- If [all competitor weights are nonnegative](hyp:hp) and [the candidate weight a
is positive](hyp:ha), then [the probability that every positive-weight competitor's
log weight plus its independent standard Gumbel draw is at most log(a) plus x
equals exp(−(the sum of competitor weights divided by a) exp(−x))](goal). -/
-- @node: gumbel_competitors_probability_nonneg
lemma gumbel_competitors_probability_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (a : ℝ) (ha : 0 < a) (x : ℝ) :
    gumbelInputs n {G | ∀ j, 0 < p j → G j ≤ Real.log a + x - Real.log (p j)} =
      ENNReal.ofReal (Real.exp (-((∑ j, p j) / a) * Real.exp (-x))) := by
  classical
  let := gumbelLaw_probability
  have heq : {G : Fin n → ℝ | ∀ j, 0 < p j →
      G j ≤ Real.log a + x - Real.log (p j)} =
      Set.pi Set.univ (fun j => if 0 < p j then
        Set.Iic (Real.log a + x - Real.log (p j)) else Set.univ) := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
    apply forall_congr'
    intro j
    by_cases hj : 0 < p j <;> simp [hj]
  rw [heq, gumbelInputs, Measure.pi_pi]
  have hfactor (j : Fin n) :
      gumbelLaw (if 0 < p j then Set.Iic (Real.log a + x - Real.log (p j)) else Set.univ) =
        ENNReal.ofReal (Real.exp (-(p j / a * Real.exp (-x)))) := by
    by_cases hj : 0 < p j
    · rw [if_pos hj, gumbelLaw_Iic]
      congr 2
      have hexp : Real.exp (-(Real.log a + x - Real.log (p j))) =
          p j / a * Real.exp (-x) := by
        rw [neg_sub, Real.exp_sub, Real.exp_log hj, Real.exp_add, Real.exp_log ha,
          Real.exp_neg]
        field_simp
      rw [hexp]
    · have hz : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
      simp [hz]
  simp_rw [hfactor]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul, ← Finset.sum_div]
  ring

/-- If [all label weights are nonnegative](hyp:hp), [their sum is one](hyp:hsum),
and [label i has positive weight](hyp:hi), then [the probability that its log weight
plus its independent standard Gumbel draw is at least the corresponding score of
every positive-weight label equals its weight](goal). -/
-- @node: gumbel_maximum_probability_nonneg
lemma gumbel_maximum_probability_nonneg {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) (i : Fin (n + 1)) (hi : 0 < p i) :
    gumbelInputs (n + 1) {G | ∀ j, 0 < p j →
      Real.log (p j) + G j ≤ Real.log (p i) + G i} = ENNReal.ofReal (p i) := by
  let := gumbelLaw_probability
  let := gumbelInputs_probability n
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let F : Set (ℝ × (Fin n → ℝ)) :=
    {z | ∀ j, 0 < p (i.succAbove j) →
      z.2 j ≤ Real.log (p i) + z.1 - Real.log (p (i.succAbove j))}
  have hF : MeasurableSet F := by
    simp only [F, Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (by fun_prop) (by fun_prop)
  have hpre : {G | ∀ j, 0 < p j →
      Real.log (p j) + G j ≤ Real.log (p i) + G i} = e ⁻¹' F := by
    ext G
    change (∀ j, 0 < p j → Real.log (p j) + G j ≤ Real.log (p i) + G i) ↔
      ∀ j : Fin n, 0 < p (i.succAbove j) → G (i.succAbove j) ≤
        Real.log (p i) + G i - Real.log (p (i.succAbove j))
    constructor
    · intro h j hj
      have := h (i.succAbove j) hj
      linarith
    · intro h
      rw [i.forall_iff_succAbove]
      refine ⟨fun _ => le_rfl, ?_⟩
      intro j hj
      have := h j hj
      linarith
  have hsplit : (gumbelInputs (n + 1)).map e = gumbelLaw.prod (gumbelInputs n) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gumbelLaw) i).map_eq
  rw [hpre, ← Measure.map_apply e.measurable hF, hsplit, Measure.prod_apply hF]
  have hinner (x : ℝ) : (gumbelInputs n) ((fun y => (x,y)) ⁻¹' F) =
      ENNReal.ofReal (Real.exp ((1-(p i)⁻¹) * Real.exp (-x))) := by
    change (gumbelInputs n) {G | ∀ j, 0 < p (i.succAbove j) → G j ≤
      Real.log (p i) + x - Real.log (p (i.succAbove j))} = _
    rw [gumbel_competitors_probability_nonneg _ (fun j => hp _) _ hi]
    congr 2
    have hsum' := Fin.sum_univ_succAbove p i
    rw [hsum] at hsum'
    have hratio : -((∑ j : Fin n, p (i.succAbove j)) / p i) = 1 - (p i)⁻¹ := by
      field_simp
      linarith
    rw [hratio]
  simp_rw [hinner]
  rw [gumbel_laplace_exp_neg _ (inv_pos.mpr hi), inv_inv]

/-- If [all label weights are nonnegative](hyp:hp) and [their sum is one](hyp:hsum),
then [maximizing extended log weights plus independent standard Gumbel draws,
choosing the smallest index in a tie, selects label i with probability equal to
its weight](goal). Zero weights have extended log equal to minus infinity. -/
-- @node: gumbel_firstArgmax_probability_nonneg
lemma gumbel_firstArgmax_probability_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) (i : Fin n) :
    gumbelInputs n {G | firstArgmax
      (fun k => extendedLog (p k) + (G k : EReal)) = some i} =
      ENNReal.ofReal (p i) := by
  have hsumpos : 0 < ∑ j, p j := by rw [hsum]; exact zero_lt_one
  by_cases hi : 0 < p i
  · have heq : {G | firstArgmax (fun k => extendedLog (p k) + (G k : EReal)) = some i}
        =ᵐ[gumbelInputs n] {G | ∀ j, 0 < p j →
          Real.log (p j) + G j ≤ Real.log (p i) + G i} := by
      filter_upwards [gumbel_scores_ne_ae p] with G hG
      apply propext
      change (firstArgmax (fun k => extendedLog (p k) + (G k : EReal)) = some i) ↔
        ∀ j, 0 < p j → Real.log (p j) + G j ≤ Real.log (p i) + G i
      constructor
      · intro h
        exact (firstArgmax_positive_and_maximizes p hp hsumpos G i h).2
      · intro h
        obtain ⟨j, hj⟩ := firstArgmax_exists (Nat.zero_lt_of_lt i.isLt)
          (fun k => extendedLog (p k) + (G k : EReal))
        obtain ⟨hpj, hmax⟩ := firstArgmax_positive_and_maximizes p hp hsumpos G j hj
        have hji : j = i := by
          by_contra hne
          exact hG j i hne (le_antisymm (h j hpj) (hmax i hi))
        simpa only [hji] using hj
    rw [measure_congr heq]
    cases n with
    | zero => exact Fin.elim0 i
    | succ n => exact gumbel_maximum_probability_nonneg p hp hsum i hi
  · have hz : p i = 0 := le_antisymm (le_of_not_gt hi) (hp i)
    have hempty : {G : Fin n → ℝ | firstArgmax
        (fun k => extendedLog (p k) + (G k : EReal)) = some i}
        = ∅ := by
      ext G
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hG
      exact hi (firstArgmax_positive_and_maximizes p hp hsumpos G i hG).1
    rw [hempty, measure_empty, hz, ENNReal.ofReal_zero]

end Papers.TbsNeuralCausalPi
