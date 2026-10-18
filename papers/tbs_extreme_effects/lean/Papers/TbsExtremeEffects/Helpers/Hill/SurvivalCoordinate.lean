module
public import Papers.TbsExtremeEffects.Helpers.Hill.QuantileConstruction
public import Papers.TbsExtremeEffects.Helpers.Hill.OrderStatistics

/-! Recovery of ordered tail radii from their logarithmic survival coordinates. -/

public section
namespace Papers.TbsExtremeEffects
open Set MeasureTheory ProbabilityTheory
open scoped Topology

/-- If [the tail index is positive](hyp:hv₀), [survival is decreasing](hyp:hS), [survival and the quantile are reciprocal inverses on the tail](hyp:hInv), and [the quantile covers every radius above its starting point](hyp:hRange), then [survival is positive at every radius](goal). -/
-- @node: hill_survival_positive_of_quantile_range
lemma hill_survival_positive_of_quantile_range (S Q : ℝ → ℝ) {v₀ : ℝ}
    (hv₀ : 0 < v₀) (hS : Antitone S)
    (hInv : ∀ v ≥ v₀, S (Q v) = v⁻¹)
    (hRange : ∀ x > Q v₀, ∃ v ≥ v₀, Q v = x) : ∀ x, 0 < S x := by
  intro x
  obtain ⟨v, hv, hQv⟩ := hRange (max x (Q v₀) + 1) (by
    have := le_max_right x (Q v₀)
    linarith)
  have hpos : 0 < S (max x (Q v₀) + 1) := by
    rw [← hQv, hInv v hv]
    exact inv_pos.mpr (hv₀.trans_le hv)
  exact hpos.trans_le (hS (by
    have := le_max_left x (Q v₀)
    linarith))

/-- If [survival is decreasing](hyp:hS) and [strictly positive everywhere](hyp:hpos), then [minus its log-survival coordinate is increasing](goal).
Here [the survival function](hyp:S) is the function being transformed. -/
-- @node: hill_log_survival_monotone
lemma hill_log_survival_monotone (S : ℝ → ℝ) (hS : Antitone S)
    (hpos : ∀ x, 0 < S x) : Monotone (fun x => -Real.log (S x)) := by
  intro x y hxy
  exact neg_le_neg (Real.log_le_log (hpos y) (hS hxy))

/-- If [a survival function is measurable](hyp:hS), then [its negative log transform is measurable](goal).
Here [the survival function](hyp:S) is the function being transformed. -/
@[fun_prop]
-- @node: hill_log_survival_measurable
lemma hill_log_survival_measurable (S : ℝ → ℝ) (hS : Measurable S) :
    Measurable (fun x => -Real.log (S x)) := by
  fun_prop

/-- If [the tail index is positive](hyp:hv₀), [survival and the quantile are reciprocal inverses on the tail](hyp:hInv), [the quantile covers the upper tail](hyp:hRange), and [the radius is at least the initial quantile](hyp:hx), then [the log-survival coordinate lies in the quantile domain and maps back to that radius](goal).
Here [the survival function and quantile](hyp:S,Q) provide the coordinate system. -/
-- @node: hill_quantile_recovers_log_survival
lemma hill_quantile_recovers_log_survival (S Q : ℝ → ℝ) {v₀ x : ℝ}
    (hv₀ : 0 < v₀) (hInv : ∀ v ≥ v₀, S (Q v) = v⁻¹)
    (hRange : ∀ x > Q v₀, ∃ v ≥ v₀, Q v = x)
    (hx : Q v₀ ≤ x) :
    v₀ ≤ Real.exp (-Real.log (S x)) ∧ Q (Real.exp (-Real.log (S x))) = x := by
  have hcover : ∃ v ≥ v₀, Q v = x := by
    rcases hx.eq_or_lt with heq | hlt
    · exact ⟨v₀, le_rfl, heq⟩
    · exact hRange x hlt
  obtain ⟨v, hv, hQv⟩ := hcover
  have hcoordinate : Real.exp (-Real.log (S x)) = v := by
    rw [← hQv, hInv v hv, Real.log_inv, neg_neg]
    exact Real.exp_log (hv₀.trans_le hv)
  rw [hcoordinate]
  exact ⟨hv, hQv⟩

/-- If [the tail index is positive](hyp:hv₀), [survival is decreasing](hyp:hS) and [positive](hyp:hpos), [survival and quantile are reciprocal inverses on the tail](hyp:hInv), [the tail level is admissible](hyp:hv), and [the radius exceeds that quantile](hyp:hx), then [its log-survival coordinate is at least that tail level](goal).
Here [the survival function and quantile](hyp:S,Q) define the coordinate. -/
-- @node: hill_log_survival_above_quantile
lemma hill_log_survival_above_quantile (S Q : ℝ → ℝ) {v₀ v x : ℝ}
    (hv₀ : 0 < v₀) (hS : Antitone S) (hpos : ∀ x, 0 < S x)
    (hInv : ∀ v ≥ v₀, S (Q v) = v⁻¹) (hv : v₀ ≤ v) (hx : Q v ≤ x) :
    v ≤ Real.exp (-Real.log (S x)) := by
  have hlog := hill_log_survival_monotone S hS hpos hx
  change -Real.log (S (Q v)) ≤ -Real.log (S x) at hlog
  rw [hInv v hv, Real.log_inv, neg_neg] at hlog
  simpa only [Real.exp_log (hv₀.trans_le hv)] using Real.exp_le_exp.mpr hlog

/-- For [a sample size](hyp:n), [observations](hyp:R), [an increasing transform](hyp:f) satisfying [monotonicity](hyp:hf), [an outcome](hyp:w), and [a rank](hyp:i), [ordering after transformation equals transforming the decreasing order statistic](goal). -/
-- @node: hill_decreasing_order_comp_monotone
lemma hill_decreasing_order_comp_monotone {Ω : Type*} {n : ℕ}
    (R : Fin n → Ω → ℝ) (f : ℝ → ℝ) (hf : Monotone f) (w : Ω) (i : Fin n) :
    hillDecreasingOrder (fun j w => f (R j w)) w i =
      f (hillDecreasingOrder R w i) := by
  let V : Fin n → ℝ := fun j => f (R j w)
  let σ := Fin.revPerm.trans (Tuple.sort V)
  let τ := Fin.revPerm.trans (Tuple.sort (fun j => R j w))
  have hσ : Antitone (V ∘ σ) := (hill_decreasing_order_data (fun j w => f (R j w))).1 w
  have hτ : Antitone (V ∘ τ) := hf.comp_antitone ((hill_decreasing_order_data R).1 w)
  exact congrFun (Tuple.unique_antitone hσ hτ) i

/-- For [an experiment](hyp:E), [a sample size](hyp:n), [an outcome](hyp:w), and [a rank](hyp:i), the [corresponding ordered radius equals the decreasing order statistic of raw radii](goal). -/
-- @node: hill_orderedRadius_eq_decreasing_order
lemma hill_orderedRadius_eq_decreasing_order {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) {n : ℕ} (w : E.Om) (i : Fin n) :
    orderedRadius E n w (i.val + 1) =
      hillDecreasingOrder (fun j : Fin n => fun w => l1Norm (E.Zraw j.val w).2.2.2) w i := by
  have hi : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ n := by omega
  simp only [orderedRadius, dif_pos hi, hillDecreasingOrder]
  congr 2

/-- If [the experiment has independent identically distributed observations](hyp:hiid), [the survival function is measurable](hyp:hS), and [its negative log transform is increasing](hyp:hmono), then [the raw log-survival coordinates are measurable and independent, and their decreasing order statistics are the transformed ordered radii](goal).
Here [the experiment](hyp:E), [the sample size](hyp:n), and [the survival function](hyp:S) define those coordinates. -/
-- @node: hill_raw_survival_coordinates_data
lemma hill_raw_survival_coordinates_data {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) {n : ℕ} (hiid : IIDSampling E n) (S : ℝ → ℝ)
    (hS : Measurable S) (hmono : Monotone (fun x => -Real.log (S x))) :
    let V := fun i : Fin n => fun w => -Real.log (S (l1Norm (E.Zraw i.val w).2.2.2))
    (∀ i, Measurable (V i)) ∧ iIndepFun V E.P ∧
      (∀ w i, hillDecreasingOrder V w i =
        -Real.log (S (orderedRadius E n w (i.val + 1)))) := by
  let f : Obs q d → ℝ := fun z => -Real.log (S (l1Norm z.2.2.2))
  have hf : Measurable f := by
    fun_prop
  refine ⟨fun i => hf.comp (E.measurable_raw i.val), hiid.1.comp (fun _ => f) (fun _ => hf), ?_⟩
  intro w i
  rw [hill_decreasing_order_comp_monotone _ _ hmono,
    ← hill_orderedRadius_eq_decreasing_order E w i]

/-- If [the tail index is positive](hyp:hv₀), [survival is decreasing](hyp:hS), [survival and quantile are reciprocal inverses on the tail](hyp:hInv), [the quantile covers the upper tail](hyp:hRange), [the initial quantile is positive](hyp:hQpos), [the selected rank is in the sample](hyp:hk), [the tail level is admissible](hyp:hv), and [the selected ordered radius lies above its quantile](hyp:htail), then [the selected radius is positive, the log-survival coordinates have the stated prefix ordering, the quantile reconstructs each prefix radius, and the selected coordinate exceeds the tail level](goal).
Here [the experiment](hyp:E), [the survival function and quantile](hyp:S,Q), [the outcome](hyp:w), [the sample size](hyp:n), and [the selected rank](hyp:k) define the prefix. -/
-- @node: hill_survival_coordinate_prefix
lemma hill_survival_coordinate_prefix {q d : ℕ} {M : ExtremeModel q d}
    (E : NeteExperiment M) (S Q : ℝ → ℝ) {v₀ v : ℝ} {n k : ℕ} (w : E.Om)
    (hv₀ : 0 < v₀) (hS : Antitone S)
    (hInv : ∀ v ≥ v₀, S (Q v) = v⁻¹)
    (hRange : ∀ x > Q v₀, ∃ v ≥ v₀, Q v = x)
    (hQpos : 0 < Q v₀) (hk : k < n) (hv : v₀ ≤ v)
    (htail : Q v ≤ orderedRadius E n w (k + 1)) :
    let Y := fun j => -Real.log (S (orderedRadius E n w j))
    0 < orderedRadius E n w (k + 1) ∧
      (∀ j ∈ Finset.Icc 1 k, Y (j + 1) ≤ Y j ∧ Y (k + 1) ≤ Y (j + 1)) ∧
      (∀ j ∈ Finset.Icc 1 (k + 1), orderedRadius E n w j = Q (Real.exp (Y j))) ∧
      v ≤ Real.exp (Y (k + 1)) := by
  dsimp only
  have hpos := hill_survival_positive_of_quantile_range S Q hv₀ hS hInv hRange
  have hmono := hill_log_survival_monotone S hS hpos
  have hQmono := hill_quantile_strictMonoOn_of_reciprocal_survival S Q hv₀ hS hInv
  have hbase : Q v₀ ≤ orderedRadius E n w (k + 1) :=
    (hQmono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hv) hv).trans htail
  refine ⟨hQpos.trans_le hbase, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
    constructor
    · exact hmono (orderedRadius_antitone_on_ranks E n w hj1 (by omega) (by omega))
    · exact hmono (orderedRadius_antitone_on_ranks E n w (by omega) (by omega) (by omega))
  · intro j hj
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
    exact (hill_quantile_recovers_log_survival S Q hv₀ hInv hRange
      (hbase.trans (orderedRadius_antitone_on_ranks E n w hj1 hjk (by omega)))).2.symm
  · exact hill_log_survival_above_quantile S Q hv₀ hS hpos hInv hv htail

end Papers.TbsExtremeEffects
