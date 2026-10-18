module
public import Papers.TbsNeuralCausalPi.Helpers.GumbelSoftmax
/-! # Winning probabilities for the Gumbel maximum selector -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- If [r is positive](hyp:hr), then [the expectation of exp((1 − r)X) for a
unit-rate exponential random variable X equals the reciprocal of r](goal). -/
-- @node: exponential_unit_laplace
lemma exponential_unit_laplace (r : ℝ) (hr : 0 < r) :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((1-r)*x)) ∂expMeasure 1) =
      ENNReal.ofReal r⁻¹ := by
  change (∫⁻ x, ENNReal.ofReal (Real.exp ((1-r)*x))
    ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold exponentialPDF; fun_prop) (by fun_prop)]
  have heq (x : ℝ) : exponentialPDF 1 x * ENNReal.ofReal (Real.exp ((1-r)*x)) =
      ENNReal.ofReal r⁻¹ * exponentialPDF r x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [one_mul, one_mul, ← Real.exp_add]
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul]
      congr 1
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
        exponentialPDF_of_neg (lt_of_not_ge hx), zero_mul, mul_zero]
  change (∫⁻ x, exponentialPDF 1 x * ENNReal.ofReal (Real.exp ((1-r)*x))) = _
  simp_rw [heq]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one hr, mul_one]

/-- If [r is positive](hyp:hr), then [the expectation of exp((1 − r) exp(−X)) for
a standard Gumbel random variable X equals the reciprocal of r](goal). -/
-- @node: gumbel_laplace_exp_neg
lemma gumbel_laplace_exp_neg (r : ℝ) (hr : 0 < r) :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((1-r)*Real.exp (-x))) ∂gumbelLaw) =
      ENNReal.ofReal r⁻¹ := by
  rw [gumbelLaw, lintegral_map (by fun_prop) (by fun_prop)]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp ((1-r)*x)) ∂expMeasure 1 := by
      apply lintegral_congr_ae
      filter_upwards [exponential_one_ae_pos] with x hx
      simp only [neg_neg, Real.exp_log hx]
    _ = _ := exponential_unit_laplace r hr

/-- If [all competitor weights are positive](hyp:hp) and [the candidate weight a
is positive](hyp:ha), then [the probability that every competitor's log weight
plus its independent standard Gumbel draw is at most log(a) plus x equals
exp(−(the sum of competitor weights divided by a) exp(−x))](goal). -/
-- @node: gumbel_competitors_probability
lemma gumbel_competitors_probability {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (a : ℝ) (ha : 0 < a) (x : ℝ) :
    gumbelInputs n {G | ∀ j, G j ≤ Real.log a + x - Real.log (p j)} =
      ENNReal.ofReal (Real.exp (-((∑ j, p j) / a) * Real.exp (-x))) := by
  let := gumbelLaw_probability
  have heq : {G : Fin n → ℝ | ∀ j, G j ≤ Real.log a + x - Real.log (p j)} =
      Set.pi Set.univ (fun j => Set.Iic (Real.log a + x - Real.log (p j))) := by
    ext G
    simp [Pi.le_def]
  rw [heq, gumbelInputs, Measure.pi_pi]
  simp_rw [gumbelLaw_Iic]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  have hexp (j : Fin n) :
      Real.exp (-(Real.log a + x - Real.log (p j))) = p j / a * Real.exp (-x) := by
    rw [neg_sub, Real.exp_sub, Real.exp_log (hp j), Real.exp_add, Real.exp_log ha,
      Real.exp_neg]
    field_simp
  simp_rw [hexp]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul, ← Finset.sum_div]
  ring

/-- If [all label weights are positive](hyp:hp) and [their sum is one](hyp:hsum),
then [the probability that label i's log weight plus its independent standard
Gumbel draw is at least every label's corresponding score equals its weight](goal). -/
-- @node: gumbel_maximum_probability
lemma gumbel_maximum_probability {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1) (i : Fin (n + 1)) :
    gumbelInputs (n + 1) {G | ∀ j, Real.log (p j) + G j ≤ Real.log (p i) + G i} =
      ENNReal.ofReal (p i) := by
  let := gumbelLaw_probability
  let := gumbelInputs_probability n
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let F : Set (ℝ × (Fin n → ℝ)) :=
    {z | ∀ j, z.2 j ≤ Real.log (p i) + z.1 - Real.log (p (i.succAbove j))}
  have hF : MeasurableSet F := by
    have heq : F = ⋂ j : Fin n, {z : ℝ × (Fin n → ℝ) |
        z.2 j ≤ Real.log (p i) + z.1 - Real.log (p (i.succAbove j))} := by
      ext z
      simp [F]
    rw [heq]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have hpre : {G | ∀ j, Real.log (p j) + G j ≤ Real.log (p i) + G i} = e ⁻¹' F := by
    ext G
    change (∀ j, Real.log (p j) + G j ≤ Real.log (p i) + G i) ↔
      ∀ j : Fin n, G (i.succAbove j) ≤
        Real.log (p i) + G i - Real.log (p (i.succAbove j))
    constructor
    · intro h j
      have := h (i.succAbove j)
      linarith
    · intro h
      rw [i.forall_iff_succAbove]
      refine ⟨le_rfl, ?_⟩
      intro j
      have := h j
      linarith
  have hsplit : (gumbelInputs (n + 1)).map e = gumbelLaw.prod (gumbelInputs n) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gumbelLaw) i).map_eq
  rw [hpre, ← Measure.map_apply e.measurable hF, hsplit, Measure.prod_apply hF]
  have hinner (x : ℝ) : (gumbelInputs n) ((fun y => (x,y)) ⁻¹' F) =
      ENNReal.ofReal (Real.exp ((1-(p i)⁻¹) * Real.exp (-x))) := by
    change (gumbelInputs n) {G | ∀ j, G j ≤
      Real.log (p i) + x - Real.log (p (i.succAbove j))} = _
    rw [gumbel_competitors_probability _ (fun j => hp _) _ (hp i)]
    congr 2
    have hsum' := Fin.sum_univ_succAbove p i
    rw [hsum] at hsum'
    have hi : p i ≠ 0 := ne_of_gt (hp i)
    have hratio : -((∑ j : Fin n, p (i.succAbove j)) / p i) = 1 - (p i)⁻¹ := by
      field_simp
      linarith
    rw [hratio]
  simp_rw [hinner]
  rw [gumbel_laplace_exp_neg _ (inv_pos.mpr (hp i)), inv_inv]

/-- If [all label weights are positive](hyp:hp) and [their sum is one](hyp:hsum),
then [maximizing log weights plus independent standard Gumbel draws, choosing the
smallest index in a tie, selects label i with probability equal to its weight](goal). -/
-- @node: gumbel_firstArgmax_probability
lemma gumbel_firstArgmax_probability {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1) (i : Fin n) :
    gumbelInputs n {G | firstArgmax
      (fun k => extendedLog (p k) + (G k : EReal)) = some i} =
      ENNReal.ofReal (p i) := by
  have heq : {G | firstArgmax (fun k => extendedLog (p k) + (G k : EReal)) = some i}
      =ᵐ[gumbelInputs n] {G | ∀ j, Real.log (p j) + G j ≤ Real.log (p i) + G i} := by
    filter_upwards [gumbel_scores_ne_ae p] with G hG
    apply propext
    change (firstArgmax (fun k => extendedLog (p k) + (G k : EReal)) = some i) ↔
      ∀ j, Real.log (p j) + G j ≤ Real.log (p i) + G i
    constructor
    · intro h
      exact firstArgmax_log_score_maximizes p hp G i h
    · intro h
      obtain ⟨j, hj⟩ := firstArgmax_exists (Nat.zero_lt_of_lt i.isLt)
        (fun k => extendedLog (p k) + (G k : EReal))
      have hji : j = i := by
        by_contra hne
        exact hG j i hne (le_antisymm (h j)
          (firstArgmax_log_score_maximizes p hp G j hj i))
      simpa only [hji] using hj
  rw [measure_congr heq]
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact gumbel_maximum_probability p hp hsum i

end Papers.TbsNeuralCausalPi
