module
public import Papers.TbsExtremeEffects.Helpers.Count
public import Papers.TbsExtremeEffects.Helpers.Hill.Renyi

/-! The oracle quantile threshold event, from the finite-sample count lower tail. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

/-- If [the order index is within the sample](hyp:hk), [the displayed observations are decreasing](hyp:hY),
[they are a permutation of the original observations](hyp:hsort), and [the `(k+1)`-st displayed observation
is below the threshold](hyp:hz), then [at most `k` original observations exceed the threshold](goal).
@node: hill_sorted_exceedance_count_le -/
lemma hill_sorted_exceedance_count_le {n k : ℕ} (hk : k < n)
    (V Y : Fin n → ℝ) (hY : Antitone Y)
    (hsort : ∃ σ : Equiv.Perm (Fin n), ∀ i, Y i = V (σ i))
    {z : ℝ} (hz : Y ⟨k, hk⟩ < z) :
    (∑ i : Fin n, if z < V i then (1 : ℝ) else 0) ≤ k := by
  classical
  obtain ⟨σ, hσ⟩ := hsort
  have hsum : (∑ i : Fin n, if z < V i then (1 : ℝ) else 0) =
      ∑ i : Fin n, if z < Y i then (1 : ℝ) else 0 := by
    simp_rw [hσ]
    exact (Equiv.sum_comp σ (fun v => if z < V v then (1 : ℝ) else 0)).symm
  rw [hsum]
  calc
    _ ≤ ∑ i : Fin n, if i.val < k then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i.val < k
      · simp only [hi, ite_true]
        split_ifs <;> norm_num
      · have hy : Y i < z := (hY (show (⟨k, hk⟩ : Fin n) ≤ i from
            le_of_not_gt hi)).trans_lt hz
        simp [hi, not_lt_of_ge hy.le]
    _ = k := by
      rw [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hk.le]

/-- If [the order index is within the sample](hyp:hk), [the observations are measurable](hyp:hV) and
[independent](hyp:hind), their [pointwise ordering is decreasing](hyp:hY) and [comes from a permutation](hyp:hsort),
and [each threshold-exceedance indicator has mean `2k/n`](hyp:hmean), then [the chance that the order statistic falls below the threshold is exponentially small](goal).
@node: hill_quantile_threshold_failure -/
lemma hill_quantile_threshold_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n k : ℕ} (hk : k < n)
    (V : Fin n → Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (hV : ∀ i, Measurable (V i)) (hind : iIndepFun V P)
    (hY : ∀ w, Antitone (Y w))
    (hsort : ∀ w, ∃ σ : Equiv.Perm (Fin n), ∀ i, Y w i = V (σ i) w)
    (z : ℝ)
    (hmean : ∀ i, (∫ w, if z < V i w then (1 : ℝ) else 0 ∂P) =
      2 * (k : ℝ) / n) :
    P.real {w | Y w ⟨k, hk⟩ < z} ≤ Real.exp (-(k : ℝ) / 4) := by
  classical
  let f : ℝ → ℝ := fun v => if z < v then 1 else 0
  have hf : Measurable f := by
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const
  let X : Fin n → Ω → ℝ := fun i w => f (V i w)
  have hX : ∀ i, Measurable (X i) := fun i => hf.comp (hV i)
  have hcount := finite_bounded_count_lower_tail P X hX
    (hind.comp (fun _ => f) (fun _ => hf))
    (fun i w => by dsimp [X, f]; split_ifs <;> norm_num)
    Finset.univ (p := 2 * (k : ℝ) / n) (by positivity)
    (fun i _ => hmean i)
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hhalf : (n : ℝ) * (2 * (k : ℝ) / n) / 2 = k := by field_simp
  have hexponent : -((n : ℝ) * (2 * (k : ℝ) / n)) / 8 = -(k : ℝ) / 4 := by
    field_simp
    ring
  simp only [Finset.card_univ, Fintype.card_fin, hhalf, hexponent] at hcount
  apply (measureReal_mono (h₂ := measure_ne_top P _) ?_).trans hcount
  intro w hw
  exact hill_sorted_exceedance_count_le hk (fun i => V i w) (Y w) (hY w) (hsort w) hw

/-- If [the order index is within the sample](hyp:hk), [the observations are measurable](hyp:hV) and
[independent](hyp:hind), their [pointwise ordering is decreasing](hyp:hY) and [comes from a permutation](hyp:hsort),
[the order statistic is measurable](hyp:hmeas), [each threshold-exceedance indicator has mean `2k/n`](hyp:hmean),
[the confidence parameter is positive](hyp:hd), and [the sample-size budget holds](hyp:hbudget), then [the upper-threshold event is measurable and has the claimed confidence](goal).
@node: hill_quantile_threshold_probability -/
lemma hill_quantile_threshold_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n k : ℕ} (hk : k < n)
    (V : Fin n → Ω → ℝ) (Y : Ω → Fin n → ℝ)
    (hV : ∀ i, Measurable (V i)) (hind : iIndepFun V P)
    (hY : ∀ w, Antitone (Y w))
    (hsort : ∀ w, ∃ σ : Equiv.Perm (Fin n), ∀ i, Y w i = V (σ i) w)
    (z : ℝ) (hmeas : Measurable (fun w => Y w ⟨k, hk⟩))
    (hmean : ∀ i, (∫ w, if z < V i w then (1 : ℝ) else 0 ∂P) =
      2 * (k : ℝ) / n)
    {delta : ℝ} (hd : 0 < delta)
    (hbudget : 4 * Real.log (2 / delta) ≤ k) :
    MeasurableSet {w | z ≤ Y w ⟨k, hk⟩} ∧
      1 - delta / 2 ≤ P.real {w | z ≤ Y w ⟨k, hk⟩} := by
  have hm : MeasurableSet {w | z ≤ Y w ⟨k, hk⟩} :=
    measurableSet_le measurable_const hmeas
  refine ⟨hm, ?_⟩
  have hfailure := hill_quantile_threshold_failure P hk V Y hV hind hY hsort z hmean
  have hcal : Real.exp (-(k : ℝ) / 4) ≤ delta / 2 := by
    calc
      _ ≤ Real.exp (-Real.log (2 / delta)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  have hcompl : {w | Y w ⟨k, hk⟩ < z} = {w | z ≤ Y w ⟨k, hk⟩}ᶜ := by
    ext w
    simp
  rw [hcompl, measureReal_compl hm, probReal_univ] at hfailure
  linarith

end Papers.TbsExtremeEffects
