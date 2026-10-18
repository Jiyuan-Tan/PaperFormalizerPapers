module
public import Papers.TbsExtremeEffects.Helpers.Hill.Partition
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Marginal

/-! Coordinate-slice identities for the nominal radial density. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped ENNReal BigOperators

/-- [Positive tail shape](hyp:hb), [positive coordinate scales](hyp:ha), and [a positive radial threshold](hyp:hr) imply that [integrating the nominal partition integrand over radii and then coordinates equals integrating in the opposite order for the specified coordinate](goal). -/
-- @node: hill_nominal_partition_lintegral_swap
lemma hill_nominal_partition_lintegral_swap {m : ℕ} (a : Fin m → ℝ)
    {beta r : ℝ} (hb : 0 < beta) (ha : ∀ i, 0 < a i) (hr : 0 < r)
    (i : Fin m) :
    (∫⁻ x in Set.Ioi r, ENNReal.ofReal (∫ z,
      hillLargestSummandIntegrand a beta x (fun j => a j * z j) i
        ∂hillNominalComponentLaw beta m)) =
    ∫⁻ z, (∫⁻ x in Set.Ioi r,
      ENNReal.ofReal (hillLargestSummandIntegrand a beta x (fun j => a j * z j) i))
        ∂hillNominalComponentLaw beta m := by
  let := hill_nominal_probability hb m
  calc
    _ = ∫⁻ x in Set.Ioi r, ∫⁻ z,
        ENNReal.ofReal (hillLargestSummandIntegrand a beta x (fun j => a j * z j) i)
          ∂hillNominalComponentLaw beta m := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro x hx
      apply ofReal_integral_eq_lintegral_ofReal
      · exact hill_largest_summand_integrand_integrable _ a
          (fun j z => a j * z j) i hb (ha i) (hr.trans hx) (by intro j; fun_prop)
      · exact Eventually.of_forall (fun z =>
          (hill_largest_summand_integrand_bound a (fun j => a j * z j) i
            hb (ha i) (hr.trans hx)).1)
    _ = _ := lintegral_lintegral_swap (by
      apply Measurable.aemeasurable
      apply Measurable.ennreal_ofReal
      exact (hill_largest_summand_joint_measurable a beta i).comp
        (measurable_fst.prodMk (by fun_prop)))

/-- [The coordinate scales](hyp:a), [the fixed component values](hyp:W), [the tail shape](hyp:beta), [the radial threshold](hyp:r), and [the selected coordinate](hyp:i) determine [the equality that rewrites the radial integral as the residual-coordinate slice integral](goal). -/
-- @node: hill_partition_slice_translate
lemma hill_partition_slice_translate {m : ℕ} (a W : Fin m → ℝ)
    (beta r : ℝ) (i : Fin m) :
    (∫⁻ x in Set.Ioi r, ENNReal.ofReal (hillLargestSummandIntegrand a beta x W i)) =
    ∫⁻ y : ℝ, if r < y + ∑ j ∈ Finset.univ.erase i, W j ∧
        (∀ j ∈ Finset.univ.erase i, W j ≤ y) then
      ENNReal.ofReal (beta * (a i) ^ beta * (a i + y) ^ (-beta - 1)) else 0 := by
  classical
  rw [← lintegral_indicator measurableSet_Ioi]
  rw [← lintegral_add_right_eq_self _ (∑ j ∈ Finset.univ.erase i, W j)]
  apply lintegral_congr
  intro y
  simp only [Set.indicator, Set.mem_Ioi, hillLargestSummandIntegrand,
    add_sub_cancel_right]
  by_cases hr : r < y + ∑ j ∈ Finset.univ.erase i, W j
  · by_cases hm : ∀ j ∈ Finset.univ.erase i, W j ≤ y
    · rw [if_pos hr, if_pos hm]
      exact (if_pos ⟨hr, hm⟩).symm
    · simp only [hr, hm, and_false, if_true, if_false, ENNReal.ofReal_zero]
  · simp only [hr, false_and, if_false]

/-- [A positive scale](hyp:ha) and [a positive evaluation point](hyp:hy) imply [the scaled Pareto-II density identity](goal) for [the tail shape](hyp:beta). -/
-- @node: hill_scaled_paretoII_density_formula
lemma hill_scaled_paretoII_density_formula {a y : ℝ} (ha : 0 < a) (hy : 0 < y)
    (beta : ℝ) :
    a⁻¹ * paretoIIDensity beta (y / a) =
      beta * a ^ beta * (a + y) ^ (-beta - 1) := by
  rw [paretoIIDensity, if_pos (div_pos hy ha)]
  have hbase : 1 + y / a = (a + y) / a := by field_simp
  rw [hbase, Real.div_rpow (by positivity) ha.le]
  have hpow : a ^ (-(beta + 1)) = (a ^ beta * a)⁻¹ := by
    rw [Real.rpow_neg ha.le, Real.rpow_add ha beta 1, Real.rpow_one]
  rw [hpow]
  rw [show -(beta + 1) = -beta - 1 by ring]
  field_simp

/-- [A positive radial threshold](hyp:hr) and [a residual value that exceeds it while dominating every other component](hyp:h) imply [that the residual value is positive](goal). -/
-- @node: hill_slice_residual_pos
lemma hill_slice_residual_pos {m : ℕ} (W : Fin m → ℝ) (i : Fin m)
    {r y : ℝ} (hr : 0 < r)
    (h : r < y + ∑ j ∈ Finset.univ.erase i, W j ∧
      ∀ j ∈ Finset.univ.erase i, W j ≤ y) : 0 < y := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hmax : ∀ j ∈ Finset.univ.erase i,
      W j ≤ (y + ∑ j ∈ Finset.univ.erase i, W j) -
        ∑ j ∈ Finset.univ.erase i, W j := by
    simpa only [add_sub_cancel_right] using h.2
  have hres := hill_largest_summand_residual_ge W i hmax
  simp only [add_sub_cancel_right] at hres
  exact (div_pos (hr.trans h.1) hm).trans_le hres

/-- [A positive scale for the selected coordinate](hyp:ha) and [a positive radial threshold](hyp:hr) imply [that the partition slice integral equals the Pareto-II probability of the displayed slice event](goal), for [the coordinate scales](hyp:a), [the fixed component values](hyp:W), [the tail shape](hyp:beta), and [the selected coordinate](hyp:i). -/
-- @node: hill_partition_slice_pareto_law
lemma hill_partition_slice_pareto_law {m : ℕ} (a W : Fin m → ℝ)
    (beta : ℝ) (i : Fin m) {r : ℝ} (ha : 0 < a i) (hr : 0 < r) :
    (∫⁻ x in Set.Ioi r, ENNReal.ofReal (hillLargestSummandIntegrand a beta x W i)) =
      (volume.withDensity (fun s => ENNReal.ofReal (paretoIIDensity beta s)))
        {s | r < a i * s + ∑ j ∈ Finset.univ.erase i, W j ∧
          ∀ j ∈ Finset.univ.erase i, W j ≤ a i * s} := by
  classical
  let v := ∑ j ∈ Finset.univ.erase i, W j
  let F : ℝ → ℝ≥0∞ := fun y => if r < y + v ∧
      (∀ j ∈ Finset.univ.erase i, W j ≤ y) then
    ENNReal.ofReal (beta * (a i) ^ beta * (a i + y) ^ (-beta - 1)) else 0
  have hEvent : MeasurableSet {y : ℝ | r < y + v ∧
      ∀ j ∈ Finset.univ.erase i, W j ≤ y} := by
    change MeasurableSet ({y : ℝ | r < y + v} ∩
      {y | ∀ j ∈ Finset.univ.erase i, W j ≤ y})
    apply MeasurableSet.inter (measurableSet_lt measurable_const (by fun_prop))
    simpa only [Set.iInter_ofPred, id_eq] using
      (Finset.univ.erase i).measurableSet_biInter
        (fun j _ => measurableSet_le (measurable_const : Measurable (fun _ : ℝ => W j))
          measurable_id)
  have hF : Measurable F := by
    apply Measurable.ite hEvent
    · fun_prop
    · fun_prop
  rw [hill_partition_slice_translate]
  change (∫⁻ y, F y) = _
  calc
    _ = ENNReal.ofReal (a i) * ∫⁻ s : ℝ, F (a i * s) := by
      conv_lhs => rw [← Real.smul_map_volume_mul_left ha.ne']
      rw [lintegral_smul_measure, lintegral_map hF (by fun_prop),
        abs_of_pos ha, smul_eq_mul]
    _ = _ := by
      have hS : MeasurableSet {s : ℝ | r < a i * s + v ∧
          ∀ j ∈ Finset.univ.erase i, W j ≤ a i * s} :=
        hEvent.preimage (by fun_prop)
      rw [withDensity_apply _ hS, ← lintegral_indicator hS,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro s
      simp only [Set.indicator, Set.mem_ofPred_eq]
      by_cases hs : r < a i * s + v ∧ ∀ j ∈ Finset.univ.erase i, W j ≤ a i * s
      · have hy : 0 < a i * s := hill_slice_residual_pos W i hr hs
        have hd := hill_scaled_paretoII_density_formula ha hy beta
        rw [mul_div_cancel_left₀ _ ha.ne'] at hd
        have hcoef : a i * (beta * (a i) ^ beta *
            (a i + a i * s) ^ (-beta - 1)) = paretoIIDensity beta s := by
          rw [← hd]
          field_simp
        dsimp only [F]
        rw [if_pos hs, if_pos hs, ← ENNReal.ofReal_mul ha.le, hcoef]
      · dsimp only [F]
        rw [if_neg hs, if_neg hs, mul_zero]

/-- [A positive tail shape](hyp:hb), [a measurable integrand](hyp:f), [its measurability](hyp:hf), and [a selected coordinate](hyp:i) imply [that resampling that coordinate from its Pareto-II law leaves the nominal-law integral unchanged](goal). -/
-- @node: hill_nominal_resample_coordinate_lintegral
lemma hill_nominal_resample_coordinate_lintegral {m : ℕ} {beta : ℝ}
    (hb : 0 < beta) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) (i : Fin m) :
    (∫⁻ z, (∫⁻ s, f (Function.update z i s)
      ∂volume.withDensity (fun x => ENNReal.ofReal (paretoIIDensity beta x)))
        ∂hillNominalComponentLaw beta m) = ∫⁻ z, f z ∂hillNominalComponentLaw beta m := by
  classical
  let nu := volume.withDensity (fun x => ENNReal.ofReal (paretoIIDensity beta x))
  let := hill_paretoII_probability hb
  let mu : Fin m → Measure ℝ := fun _ => nu
  let g : (Fin m → ℝ) → ℝ≥0∞ := fun z => ∫⁻ s, f (Function.update z i s) ∂nu
  have hg : Measurable g := by
    simpa only [lmarginal_singleton] using (hf.lmarginal (μ := mu) (s := {i}))
  have hgg : lmarginal mu {i} g = g := by
    funext z
    rw [lmarginal_singleton]
    dsimp [g, mu]
    simp only [Function.update_idem]
    simp
  have hfg : lmarginal mu {i} f = lmarginal mu {i} g := by
    rw [hgg, lmarginal_singleton]
  rw [hill_nominal_law_eq_pi hb]
  exact (lintegral_eq_of_lmarginal_eq {i} hf hg hfg).symm

/-- [The coordinate scales](hyp:a), [a positive tail shape](hyp:hb), [positive coordinate scales](hyp:ha), [a positive radial threshold](hyp:hr), and [the selected coordinate](hyp:i) imply [that the nominal probability of its largest-summand partition cell equals the stated radial integral](goal). -/
-- @node: hill_nominal_partition_slice
lemma hill_nominal_partition_slice {m : ℕ} (a : Fin m → ℝ)
    {beta r : ℝ} (hb : 0 < beta) (ha : ∀ i, 0 < a i) (hr : 0 < r) (i : Fin m) :
    (hillNominalComponentLaw beta m)
      {z | r < ∑ j, a j * z j ∧ ∀ j, a j * z j ≤ a i * z i} =
      ∫⁻ x in Set.Ioi r, ENNReal.ofReal (∫ z,
        hillLargestSummandIntegrand a beta x (fun j => a j * z j) i
          ∂hillNominalComponentLaw beta m) := by
  classical
  let A : Set (Fin m → ℝ) :=
    {z | r < ∑ j, a j * z j ∧ ∀ j, a j * z j ≤ a i * z i}
  have hA : MeasurableSet A := by
    change MeasurableSet ({z : Fin m → ℝ | r < ∑ j, a j * z j} ∩
      {z | ∀ j, a j * z j ≤ a i * z i})
    apply MeasurableSet.inter (measurableSet_lt measurable_const (by fun_prop))
    simpa only [Set.iInter_ofPred] using MeasurableSet.iInter
      (fun j => measurableSet_le (by fun_prop) (by fun_prop))
  have hCoordinate : ∀ z : Fin m → ℝ,
      (∫⁻ s, A.indicator 1 (Function.update z i s)
        ∂volume.withDensity (fun x => ENNReal.ofReal (paretoIIDensity beta x))) =
      ∫⁻ x in Set.Ioi r, ENNReal.ofReal
        (hillLargestSummandIntegrand a beta x (fun j => a j * z j) i) := by
    intro z
    rw [hill_partition_slice_pareto_law a (fun j => a j * z j) beta i (ha i) hr]
    have hEvent : MeasurableSet {s : ℝ | r < a i * s +
        ∑ j ∈ Finset.univ.erase i, a j * z j ∧
        ∀ j ∈ Finset.univ.erase i, a j * z j ≤ a i * s} := by
      change MeasurableSet ({s : ℝ | r < a i * s +
        ∑ j ∈ Finset.univ.erase i, a j * z j} ∩
        {s | ∀ j ∈ Finset.univ.erase i, a j * z j ≤ a i * s})
      apply MeasurableSet.inter (measurableSet_lt measurable_const (by fun_prop))
      simpa only [Set.iInter_ofPred] using
        (Finset.univ.erase i).measurableSet_biInter
          (fun j _ => measurableSet_le (measurable_const :
            Measurable (fun _ : ℝ => a j * z j)) (by fun_prop))
    rw [← lintegral_indicator_one hEvent]
    apply lintegral_congr
    intro s
    have hsum : (∑ j, a j * Function.update z i s j) =
        a i * s + ∑ j ∈ Finset.univ.erase i, a j * z j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), Function.update_self]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hmax : (∀ j, a j * Function.update z i s j ≤ a i * s) ↔
        (∀ j ∈ Finset.univ.erase i, a j * z j ≤ a i * s) := by
      constructor
      · intro h j hj
        simpa only [Function.update_of_ne (Finset.ne_of_mem_erase hj)] using h j
      · intro h j
        by_cases hj : j = i
        · subst j; simp
        · rw [Function.update_of_ne hj]
          exact h j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    simp only [Set.indicator, A, Set.mem_ofPred_eq, Pi.one_apply,
      hsum, Function.update_self, hmax]
  calc
    _ = ∫⁻ z, A.indicator 1 z ∂hillNominalComponentLaw beta m :=
      (lintegral_indicator_one hA).symm
    _ = ∫⁻ z, (∫⁻ s, A.indicator 1 (Function.update z i s)
        ∂volume.withDensity (fun x => ENNReal.ofReal (paretoIIDensity beta x)))
          ∂hillNominalComponentLaw beta m :=
      (hill_nominal_resample_coordinate_lintegral hb _ (measurable_one.indicator hA) i).symm
    _ = ∫⁻ z, (∫⁻ x in Set.Ioi r, ENNReal.ofReal
        (hillLargestSummandIntegrand a beta x (fun j => a j * z j) i))
          ∂hillNominalComponentLaw beta m := lintegral_congr hCoordinate
    _ = _ := (hill_nominal_partition_lintegral_swap a hb ha hr i).symm

end Papers.TbsExtremeEffects
