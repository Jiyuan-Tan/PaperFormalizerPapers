module
public import Papers.TbsPrteOptimalTransport.Helpers.BinaryBranches
/-! Quadratic fitted-branch control at the fixed zero baseline boundary. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
universe v
open MeasureTheory Filter
open scoped Classical Topology

-- The lower boundary is fixed at zero. Its separation from the outcome
-- boundary suffices; no separation between the policy level and zero is used.
-- @node: binary_structural_zero_fitted_remainder
/-- If [the separation constant is positive](hyp:hc), [the baseline boundary is
at least that constant above zero](hyp:hbc), [the baseline policy level and
boundary are separated by at least that constant](hyp:hbq), and [the absolute
policy perturbation](hyp:hq) and [absolute boundary perturbation](hyp:hb) are
each at most the error envelope, [the absolute remainder in the positive part
of policy minus the positive part of the boundary, after subtracting the policy
perturbation on the fitted active branch and adding the boundary perturbation
when the fitted boundary lies strictly between zero and the fitted policy level,
is at most sixteen times the squared envelope divided by the separation constant](goal). -/
lemma binary_structural_zero_fitted_remainder {q b dq db err c : ℝ}
    (hc : 0 < c) (hbc : c ≤ b) (hbq : c ≤ |b - q|)
    (hq : |dq| ≤ err) (hb : |db| ≤ err) :
    |max 0 (q + dq - max 0 (b + db)) - max 0 (q - max 0 b) -
      (indicator (q + dq > max 0 (b + db)) * dq -
        indicator (0 < b + db ∧ b + db < q + dq) * db)| ≤
      (16 / c) * err ^ 2 := by
  have he0 : 0 ≤ err := (abs_nonneg dq).trans hq
  have hb0 : 0 < b := hc.trans_le hbc
  by_cases he : err < c / 4
  · have hbt : 0 < b + db := by
      have hd := (abs_le.mp hb).1
      linarith
    rw [max_eq_right hb0.le, max_eq_right hbt.le]
    by_cases hlt : b < q
    · have hsep : c ≤ q - b := by
        simpa only [abs_of_neg (sub_neg.mpr hlt), neg_sub] using hbq
      have ht : b + db < q + dq := by
        have hdq := (abs_le.mp hq).1
        have hdb := (abs_le.mp hb).2
        linarith
      simp only [indicator, if_pos ht, if_pos (And.intro hbt ht), one_mul,
        max_eq_right (by linarith : 0 ≤ q + dq - (b + db)),
        max_eq_right (sub_nonneg.mpr hlt.le)]
      have hz : q + dq - (b + db) - (q - b) - (dq - db) = 0 := by ring
      rw [hz, abs_zero]
      positivity
    · have hsep : c ≤ b - q := by
        simpa only [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hlt))] using hbq
      have ht : ¬ b + db < q + dq := by
        have hdq := (abs_le.mp hq).2
        have hdb := (abs_le.mp hb).1
        linarith
      simp only [indicator, if_neg ht, if_neg (show ¬ (0 < b + db ∧ b + db < q + dq)
        from fun h => ht h.2), zero_mul,
        max_eq_left (by linarith : q + dq - (b + db) ≤ 0),
        max_eq_left (by linarith : q - b ≤ 0), sub_zero, abs_zero]
      positivity
  · have hi : |max 0 (b + db) - max 0 b| ≤ err := by
      have h := abs_max_sub_max_le_max 0 (b + db) 0 b
      simp only [sub_self, abs_zero, add_sub_cancel_left] at h
      exact h.trans (max_le he0 hb)
    have hh : |max 0 (q + dq - max 0 (b + db)) - max 0 (q - max 0 b)| ≤ 2 * err := by
      have h := abs_max_sub_max_le_max 0 (q + dq - max 0 (b + db)) 0 (q - max 0 b)
      have hid : q + dq - max 0 (b + db) - (q - max 0 b) =
          dq - (max 0 (b + db) - max 0 b) := by ring
      rw [sub_self, abs_zero, hid] at h
      exact h.trans (max_le (by linarith) ((abs_sub _ _).trans (by linarith)))
    have hI : |indicator (q + dq > max 0 (b + db)) * dq| ≤ err := by
      unfold indicator
      split_ifs
      · simpa using hq
      · simpa using he0
    have hD : |indicator (0 < b + db ∧ b + db < q + dq) * db| ≤ err := by
      unfold indicator
      split_ifs
      · simpa using hb
      · simpa using he0
    have hlin := (abs_sub _ _).trans (add_le_add hh ((abs_sub _ _).trans (add_le_add hI hD)))
    have hquad : 4 * err ≤ (16 / c) * err ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).mpr
      have hp : 0 ≤ err * (4 * err - c) := mul_nonneg he0 (by linarith)
      nlinarith
    exact hlin.trans (by linarith)

-- The fitted residuals cancel the fitted linear term even on the wrong branch.
-- @node: binary_structural_zero_debiased_remainder
/-- If [the separation constant is positive](hyp:hc), [the baseline boundary is
at least that constant above zero](hyp:hbc), [the baseline policy level and
boundary are separated by at least that constant](hyp:hbq), [the absolute policy
perturbation](hyp:hq) and [absolute boundary perturbation](hyp:hb) are bounded by
the error envelope, [the boundary residual differs from the boundary perturbation
by at most its approximation bound](hyp:hrB), and [the policy residual differs
from the negative policy perturbation by at most its approximation bound](hyp:hrQ),
[the absolute change in the positive part of policy minus the positive part of
the boundary, corrected by adding the boundary residual when the fitted boundary
lies strictly between zero and the fitted policy and the policy residual on the
fitted active branch, is at most sixteen times the squared envelope divided by
the separation constant plus both residual approximation bounds](goal). -/
lemma binary_structural_zero_debiased_remainder {q b dq db err c rB rQ EB EQ : ℝ}
    (hc : 0 < c) (hbc : c ≤ b) (hbq : c ≤ |b - q|)
    (hq : |dq| ≤ err) (hb : |db| ≤ err)
    (hrB : |rB - db| ≤ EB) (hrQ : |rQ + dq| ≤ EQ) :
    |max 0 (q + dq - max 0 (b + db)) - max 0 (q - max 0 b) +
      indicator (0 < b + db ∧ b + db < q + dq) * rB +
      indicator (q + dq > max 0 (b + db)) * rQ| ≤
      (16 / c) * err ^ 2 + EB + EQ := by
  let I := indicator (q + dq > max 0 (b + db))
  let D := indicator (0 < b + db ∧ b + db < q + dq)
  let R := max 0 (q + dq - max 0 (b + db)) - max 0 (q - max 0 b) - (I * dq - D * db)
  have hR : |R| ≤ (16 / c) * err ^ 2 :=
    binary_structural_zero_fitted_remainder hc hbc hbq hq hb
  have hB : |D * (rB - db)| ≤ EB := by
    dsimp only [D]
    unfold indicator
    split_ifs
    · simpa using hrB
    · simpa using (abs_nonneg (rB - db)).trans hrB
  have hQ : |I * (rQ + dq)| ≤ EQ := by
    dsimp only [I]
    unfold indicator
    split_ifs
    · simpa using hrQ
    · simpa using (abs_nonneg (rQ + dq)).trans hrQ
  have hid : max 0 (q + dq - max 0 (b + db)) - max 0 (q - max 0 b) + D * rB + I * rQ =
      R + D * (rB - db) + I * (rQ + dq) := by
    dsimp only [R]
    ring
  change |max 0 (q + dq - max 0 (b + db)) - max 0 (q - max 0 b) + D * rB + I * rQ| ≤ _
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add hR hB)) hQ)

-- The branch bound integrates against the same L2 envelope used in the DML
-- argument, while residual approximation errors remain explicit.
-- @node: binary_structural_zero_integrated_remainder
/-- Suppose [the separation constant is positive](hyp:hc), [the policy level](hyp:hq),
[boundary](hyp:hb), [policy perturbation](hyp:hdq), [boundary perturbation](hyp:hdb),
[boundary residual](hyp:hrB), and [policy residual](hyp:hrQ) are measurable,
[the error envelope is square integrable](hyp:herr), and [the boundary residual
approximation bound](hyp:hEB) and [policy residual approximation bound](hyp:hEQ)
are integrable. If [the baseline boundary is at least the separation constant
above zero and at least that far from the baseline policy level almost everywhere](hyp:hgap),
[both absolute perturbations are bounded by the envelope almost everywhere](hyp:herrors),
and [the boundary residual approximates the boundary perturbation and the policy
residual approximates its negative perturbation within their respective bounds
almost everywhere](hyp:hres), [the change in the positive part of policy minus
the positive part of the boundary, corrected by the boundary residual on the
branch where the fitted boundary lies strictly between zero and the fitted
policy and by the policy residual on the fitted active branch, is integrable,
and the absolute value of its integral is bounded by sixteen divided by the
separation constant times the integrated squared envelope, plus the integrals
of both residual approximation bounds](goal). -/
lemma binary_structural_zero_integrated_remainder {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q b dq db rB rQ err EB EQ : X → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : Measurable q) (hb : Measurable b) (hdq : Measurable dq) (hdb : Measurable db)
    (hrB : Measurable rB) (hrQ : Measurable rQ)
    (herr : MemLp err 2 μ) (hEB : Integrable EB μ) (hEQ : Integrable EQ μ)
    (hgap : ∀ᵐ x ∂μ, c ≤ b x ∧ c ≤ |b x - q x|)
    (herrors : ∀ᵐ x ∂μ, |dq x| ≤ err x ∧ |db x| ≤ err x)
    (hres : ∀ᵐ x ∂μ, |rB x - db x| ≤ EB x ∧ |rQ x + dq x| ≤ EQ x) :
    let R := fun x => max 0 (q x + dq x - max 0 (b x + db x)) - max 0 (q x - max 0 (b x)) +
      indicator (0 < b x + db x ∧ b x + db x < q x + dq x) * rB x +
      indicator (q x + dq x > max 0 (b x + db x)) * rQ x
    Integrable R μ ∧ |∫ x, R x ∂μ| ≤
      (16 / c) * (∫ x, err x ^ 2 ∂μ) + (∫ x, EB x ∂μ) + (∫ x, EQ x ∂μ) := by
  dsimp only
  let R := fun x => max 0 (q x + dq x - max 0 (b x + db x)) - max 0 (q x - max 0 (b x)) +
    indicator (0 < b x + db x ∧ b x + db x < q x + dq x) * rB x +
    indicator (q x + dq x > max 0 (b x + db x)) * rQ x
  have hI : Measurable (fun x => indicator (q x + dq x > max 0 (b x + db x))) := by
    fun_prop
  have hD : Measurable (fun x => indicator (0 < b x + db x ∧ b x + db x < q x + dq x)) := by
    fun_prop
  have hR : Measurable R := by dsimp only [R]; fun_prop
  have hbound : ∀ᵐ x ∂μ, |R x| ≤ (16 / c) * err x ^ 2 + EB x + EQ x := by
    filter_upwards [hgap, herrors, hres] with x hg he hr
    exact binary_structural_zero_debiased_remainder hc hg.1 hg.2 he.1 he.2 hr.1 hr.2
  have hdom : Integrable (fun x => (16 / c) * err x ^ 2 + EB x + EQ x) μ :=
    ((herr.integrable_sq.const_mul _).fun_add hEB).fun_add hEQ
  have hi : Integrable R μ := hdom.mono' hR.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |R x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ x, (16 / c) * err x ^ 2 + EB x + EQ x ∂μ := integral_mono_ae hi.abs hdom hbound
    _ = _ := by
      rw [integral_add ((herr.integrable_sq.const_mul _).fun_add hEB) hEQ,
        integral_add (herr.integrable_sq.const_mul _) hEB, integral_const_mul]

-- At k = 0, j = 1 the lower pooled level is identically zero for every
-- nuisance vector, so the preceding bound applies to the actual score hinge.
-- @node: hMinus_structural_zero_fitted_remainder
/-- For the score hinge with lower pooled level zero and upper index one, suppose
[the separation constant is positive](hyp:hc), [the baseline upper boundary,
given by the positive upper level minus the full baseline term, is at least
that constant above zero](hyp:hbc), [this boundary is separated from the baseline
pooled policy level by at least that constant](hyp:hbq), [the absolute change
in the pooled policy level is bounded by the error envelope](hyp:hq), and
[the absolute change in the upper boundary is bounded by the same envelope](hyp:hb).
Then [the absolute change in the hinge minus the fitted active indicator times
the policy change plus the fitted boundary indicator times the boundary change
is at most sixteen times the squared envelope divided by the separation constant](goal). -/
lemma hMinus_structural_zero_fitted_remainder {X Z : Type v}
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e0 e1 : NuisanceBin L)
    (x : X) (err c : ℝ) (hc : 0 < c)
    (hbc : c ≤ positiveValue e0.pLev 1 x - binFullJ L e0 0 x)
    (hbq : c ≤ |positiveValue e0.pLev 1 x - binFullJ L e0 0 x -
      pooledQBin phi L e0 0 1 x|)
    (hq : |pooledQBin phi L e1 0 1 x - pooledQBin phi L e0 0 1 x| ≤ err)
    (hb : |(positiveValue e1.pLev 1 x - binFullJ L e1 0 x) -
      (positiveValue e0.pLev 1 x - binFullJ L e0 0 x)| ≤ err) :
    |hMinus phi L e1 0 1 x - hMinus phi L e0 0 1 x -
      (Iact phi L e1 0 1 x * (pooledQBin phi L e1 0 1 x - pooledQBin phi L e0 0 1 x) -
        Dbd phi L e1 0 1 x * ((positiveValue e1.pLev 1 x - binFullJ L e1 0 x) -
          (positiveValue e0.pLev 1 x - binFullJ L e0 0 x)))| ≤ (16 / c) * err ^ 2 := by
  have hzero (e : NuisanceBin L) : pooledQBin phi L e 0 0 x = 0 := by
    simp [pooledQBin, positiveValue]
  have h := binary_structural_zero_fitted_remainder hc hbc hbq hq hb
  simpa only [hMinus, Iact, Dbd, Nat.reduceSub, Nat.reduceAdd, hzero, add_sub_cancel]
    using h

end Papers.TbsPrteOptimalTransport
