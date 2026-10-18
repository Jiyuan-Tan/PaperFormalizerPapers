module
public import Papers.TbsExtremeEffects.Helpers.Hill.NominalProductLaw
public import Mathlib.MeasureTheory.Integral.Prod

/-! Measurability and continuity of the largest-summand density partition. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped Topology BigOperators

/-- For [a finite dimension](hyp:m), [component scales](hyp:a), [a tail exponent](hyp:beta), and [a selected component](hyp:i), [the largest-summand integrand is jointly measurable in the radius and component values](goal).
@node: hill_largest_summand_joint_measurable -/
@[fun_prop] lemma hill_largest_summand_joint_measurable {m : ℕ}
    (a : Fin m → ℝ) (beta : ℝ) (i : Fin m) :
    Measurable (fun p : ℝ × (Fin m → ℝ) =>
      hillLargestSummandIntegrand a beta p.1 p.2 i) := by
  classical
  unfold hillLargestSummandIntegrand
  apply Measurable.ite
  · have hV : Measurable (fun p : ℝ × (Fin m → ℝ) =>
        ∑ j ∈ Finset.univ.erase i, p.2 j) := by fun_prop
    simpa only [Set.iInter_ofPred, Function.comp_apply, Pi.sub_apply] using
      (Finset.univ.erase i).measurableSet_biInter (fun j _ =>
        measurableSet_le ((measurable_pi_apply j).comp measurable_snd)
          (measurable_fst.sub hV))
  · fun_prop
  · fun_prop

/-- For [a sigma-finite component-value measure](hyp:P), [component scales](hyp:a), [a tail exponent](hyp:beta), and [a selected component](hyp:i), [the largest-summand integral is measurable as a function of radius](goal).
@node: hill_largest_summand_integral_measurable -/
@[fun_prop] lemma hill_largest_summand_integral_measurable {m : ℕ}
    (P : Measure (Fin m → ℝ)) [SFinite P]
    (a : Fin m → ℝ) (beta : ℝ) (i : Fin m) :
    Measurable (fun r => ∫ W, hillLargestSummandIntegrand a beta r W i ∂P) := by
  exact (hill_largest_summand_joint_measurable a beta i).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

/-- For component scales and values, [a selected component](hyp:i), [a positive selected scale](hyp:ha), [a positive radius](hyp:hr), and [absence of every partition boundary at that radius](hyp:hboundary), [the largest-summand integrand is continuous at the radius](goal).
@node: hill_largest_summand_continuousAt_off_boundary -/
lemma hill_largest_summand_continuousAt_off_boundary {m : ℕ}
    (a W : Fin m → ℝ) (i : Fin m) {beta r : ℝ}
    (ha : 0 < a i) (hr : 0 < r)
    (hboundary : ∀ j ∈ Finset.univ.erase i,
      W j + ∑ l ∈ Finset.univ.erase i, W l ≠ r) :
    ContinuousAt (fun x => hillLargestSummandIntegrand a beta x W i) r := by
  classical
  let v := ∑ l ∈ Finset.univ.erase i, W l
  by_cases hmax : ∀ j ∈ Finset.univ.erase i, W j ≤ r - v
  · have hstrict : ∀ j ∈ Finset.univ.erase i, W j + v < r := by
      intro j hj
      have hne := hboundary j hj
      have hle := hmax j hj
      dsimp [v] at *
      exact lt_of_le_of_ne (by linarith) hne
    have hlocal : ∀ᶠ x in 𝓝 r, ∀ j ∈ Finset.univ.erase i, W j ≤ x - v := by
      apply (Finset.eventually_all (Finset.univ.erase i)).mpr
      intro j hj
      filter_upwards [Ioi_mem_nhds (hstrict j hj)] with x hx
      have hx : W j + v < x := hx
      exact (by linarith : W j ≤ x - v)
    have hbase : a i + (r - v) ≠ 0 := by
      have hres := hill_largest_summand_residual_ge W i hmax
      have hm : 0 < (m : ℝ) := by exact_mod_cast ((Nat.zero_le i.val).trans_lt i.isLt)
      have := div_pos hr hm
      dsimp [v]
      linarith
    have hc : ContinuousAt (fun x : ℝ =>
        beta * (a i) ^ beta * (a i + (x - v)) ^ (-beta - 1)) r := by
      exact (((continuousAt_id.sub continuousAt_const).const_add (a i)).rpow_const
        (Or.inl hbase)).const_mul (beta * (a i) ^ beta)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hlocal] with x hx
    simp only [hillLargestSummandIntegrand,
      show (∑ l ∈ Finset.univ.erase i, W l) = v from rfl, if_pos hx]
  · obtain ⟨j, hj, hnot⟩ := by simpa only [not_forall, Classical.not_imp] using hmax
    have hstrict : r < W j + v := by linarith [not_le.mp hnot]
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hstrict] with x hx
    have hx : x < W j + v := hx
    have hfail : ¬ ∀ j ∈ Finset.univ.erase i, W j ≤ x - v := by
      intro h
      have := h j hj
      linarith
    simp only [hillLargestSummandIntegrand,
      show (∑ l ∈ Finset.univ.erase i, W l) = v from rfl, if_neg hfail]

/-- For [a finite component measure](hyp:P), [component scales](hyp:a), [a selected component](hyp:i), [a positive tail exponent](hyp:hb), [a positive selected scale](hyp:ha), [a positive radius](hyp:hr), and [almost-sure absence of partition boundaries](hyp:hboundary), [the largest-summand integral is continuous at that radius](goal).
@node: hill_largest_summand_integral_continuousAt -/
lemma hill_largest_summand_integral_continuousAt {m : ℕ}
    (P : Measure (Fin m → ℝ)) [IsFiniteMeasure P]
    (a : Fin m → ℝ) (i : Fin m) {beta r : ℝ}
    (hb : 0 < beta) (ha : 0 < a i) (hr : 0 < r)
    (hboundary : ∀ᵐ W ∂P, ∀ j ∈ Finset.univ.erase i,
      W j + ∑ l ∈ Finset.univ.erase i, W l ≠ r) :
    ContinuousAt (fun x => ∫ W, hillLargestSummandIntegrand a beta x W i ∂P) r := by
  apply continuousAt_of_dominated
    (bound := fun _ => beta * (a i) ^ beta * ((r / 2) / m) ^ (-beta - 1))
  · exact Eventually.of_forall (fun x =>
      ((hill_largest_summand_joint_measurable a beta i).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  · filter_upwards [Ioi_mem_nhds (by linarith : r / 2 < r)] with x hx
    have hx : r / 2 < x := hx
    apply Eventually.of_forall
    intro W
    obtain ⟨hpos, hbound⟩ := hill_largest_summand_integrand_bound a W i hb ha
      (by linarith : 0 < x)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    apply hbound.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hm : 0 < (m : ℝ) := by exact_mod_cast ((Nat.zero_le i.val).trans_lt i.isLt)
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (div_le_div_of_nonneg_right hx.le hm.le) (by linarith)
  · exact integrable_const _
  · filter_upwards [hboundary] with W hW
    exact hill_largest_summand_continuousAt_off_boundary a W i ha hr hW

/-- For [a finite dimension](hyp:m), [linear coefficients](hyp:c), [a coordinate with nonzero coefficient](hyp:hc), and [a target value](hyp:r), [the corresponding linear sum differs from that value almost everywhere under volume](goal).
@node: hill_linear_sum_ne_ae_volume -/
lemma hill_linear_sum_ne_ae_volume {m : ℕ} (c : Fin m → ℝ)
    (j : Fin m) (hc : c j ≠ 0) (r : ℝ) :
    ∀ᵐ z : Fin m → ℝ ∂volume, (∑ l, c l * z l) ≠ r := by
  classical
  cases m with
  | zero => exact Fin.elim0 j
  | succ n =>
    let p : ℝ → (Fin n → ℝ) → Prop := fun x y =>
      c j * x + ∑ l, c (j.succAbove l) * y l ≠ r
    have hp : MeasurableSet {z : ℝ × (Fin n → ℝ) | p z.1 z.2} := by
      apply (measurableSet_eq_fun (by fun_prop) measurable_const).compl
    have hprod : ∀ᵐ z ∂(volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)),
        p z.1 z.2 := by
      rw [Measure.ae_prod_iff_ae_ae hp, Measure.ae_ae_comm hp]
      apply Eventually.of_forall
      intro y
      filter_upwards [Measure.ae_ne (volume : Measure ℝ)
        ((r - ∑ l, c (j.succAbove l) * y l) / c j)] with x hx
      dsimp [p]
      intro heq
      apply hx
      apply (eq_div_iff hc).mpr
      linarith
    have h := (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) j).quasiMeasurePreserving.ae hprod
    filter_upwards [h] with z hz
    change c j * z j + ∑ l, c (j.succAbove l) * z (j.succAbove l) ≠ r at hz
    rwa [Fin.sum_univ_succAbove _ j]

/-- For [component scales](hyp:a), [a tail exponent](hyp:beta), [positive component scales](hyp:ha), [a selected component](hyp:i), and [a radius](hyp:r), [the nominal component law almost surely avoids every selected partition boundary](goal).
@node: hill_nominal_partition_boundary_null -/
lemma hill_nominal_partition_boundary_null {m : ℕ} (a : Fin m → ℝ)
    {beta : ℝ} (ha : ∀ j, 0 < a j) (i : Fin m) (r : ℝ) :
    ∀ᵐ z ∂hillNominalComponentLaw beta m, ∀ j ∈ Finset.univ.erase i,
      a j * z j + ∑ l ∈ Finset.univ.erase i, a l * z l ≠ r := by
  classical
  rw [ae_all_iff]
  intro j
  by_cases hj : j ∈ Finset.univ.erase i
  · let c : Fin m → ℝ := fun l =>
      (if l = j then a l else 0) + (if l ≠ i then a l else 0)
    have hc : c j ≠ 0 := by
      simp only [c, ite_true, if_pos (Finset.mem_erase.mp hj).1]
      linarith [ha j]
    have hsum : ∀ z : Fin m → ℝ,
        (∑ l, c l * z l) = a j * z j + ∑ l ∈ Finset.univ.erase i, a l * z l := by
      intro z
      simp only [c, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq', ← Finset.sum_filter, Finset.filter_ne']
      simp
    have hvol := hill_linear_sum_ne_ae_volume c j hc r
    have hnom := (withDensity_absolutelyContinuous volume
      (fun z => ENNReal.ofReal (hillNominalComponentDensity beta z))).ae_le hvol
    filter_upwards [hnom] with z hz
    intro _
    rwa [hsum z] at hz
  · exact Eventually.of_forall (fun _ h => (hj h).elim)

/-- For [component scales](hyp:a), [a positive tail exponent](hyp:hb), [positive component scales](hyp:ha), [a positive radius](hyp:hr), and [a selected component](hyp:i), [the nominal largest-summand integral is continuous at that radius](goal).
@node: hill_nominal_partition_integral_continuousAt -/
lemma hill_nominal_partition_integral_continuousAt {m : ℕ} (a : Fin m → ℝ)
    {beta r : ℝ} (hb : 0 < beta) (ha : ∀ j, 0 < a j) (hr : 0 < r) (i : Fin m) :
    ContinuousAt (fun x => ∫ z,
      hillLargestSummandIntegrand a beta x (fun j => a j * z j) i
        ∂hillNominalComponentLaw beta m) r := by
  let P := hillNominalComponentLaw beta m
  let W : (Fin m → ℝ) → (Fin m → ℝ) := fun z j => a j * z j
  have hW : Measurable W := by fun_prop
  let := hill_nominal_probability hb m
  have hboundary : ∀ᵐ w ∂P.map W, ∀ j ∈ Finset.univ.erase i,
      w j + ∑ l ∈ Finset.univ.erase i, w l ≠ r := by
    rw [ae_map_iff hW.aemeasurable (by
      simpa only [Set.compl_ofPred, Set.iInter_ofPred] using
        (Finset.univ.erase i).measurableSet_biInter (fun j _ =>
          (measurableSet_eq_fun (by fun_prop : Measurable (fun w : Fin m → ℝ =>
            w j + ∑ l ∈ Finset.univ.erase i, w l))
            (measurable_const : Measurable (fun _ : Fin m → ℝ => r))).compl))]
    exact hill_nominal_partition_boundary_null a ha i r
  have hc := hill_largest_summand_integral_continuousAt (P.map W) a i hb (ha i) hr hboundary
  have heq : (fun x => ∫ w, hillLargestSummandIntegrand a beta x w i ∂P.map W) =
      (fun x => ∫ z, hillLargestSummandIntegrand a beta x (W z) i ∂P) := by
    funext x
    exact integral_map hW.aemeasurable
      (((hill_largest_summand_joint_measurable a beta i).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  rwa [heq] at hc

/-- For [component scales](hyp:a), [a tail exponent](hyp:beta), [a positive tail exponent assumption](hyp:hb), and [a selected component](hyp:i), [the nominal largest-summand integral is measurable in the radius](goal).
@node: hill_nominal_partition_integral_measurable -/
@[fun_prop] lemma hill_nominal_partition_integral_measurable {m : ℕ}
    (a : Fin m → ℝ) {beta : ℝ} (hb : 0 < beta) (i : Fin m) :
    Measurable (fun r => ∫ z,
      hillLargestSummandIntegrand a beta r (fun j => a j * z j) i
        ∂hillNominalComponentLaw beta m) := by
  let := hill_nominal_probability hb m
  have hjoint : Measurable (fun p : ℝ × (Fin m → ℝ) =>
      hillLargestSummandIntegrand a beta p.1 (fun j => a j * p.2 j) i) := by
    fun_prop
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

/-- For [component scales](hyp:a), [a tail exponent](hyp:beta), [a positive tail exponent assumption](hyp:hb), and [a prefactor](hyp:kappa), [the nominal partition density is measurable in the radius](goal).
@node: hill_nominal_partition_density_measurable -/
@[fun_prop] lemma hill_nominal_partition_density_measurable {m : ℕ}
    (a : Fin m → ℝ) {beta : ℝ} (hb : 0 < beta) (kappa : ℝ) :
    Measurable (fun r => kappa * ∑ i, ∫ z,
      hillLargestSummandIntegrand a beta r (fun j => a j * z j) i
        ∂hillNominalComponentLaw beta m) := by
  exact (Finset.measurable_sum Finset.univ (fun i _ =>
    hill_nominal_partition_integral_measurable a hb i)).const_mul kappa

/-- For [component scales](hyp:a), [a positive tail exponent](hyp:hb), [positive component scales](hyp:ha), [a positive radius](hyp:hr), and [a prefactor](hyp:kappa), [the nominal partition density is continuous at that radius](goal).
@node: hill_nominal_partition_density_continuousAt -/
lemma hill_nominal_partition_density_continuousAt {m : ℕ} (a : Fin m → ℝ)
    {beta r : ℝ} (hb : 0 < beta) (ha : ∀ j, 0 < a j) (hr : 0 < r) (kappa : ℝ) :
    ContinuousAt (fun x => kappa * ∑ i, ∫ z,
      hillLargestSummandIntegrand a beta x (fun j => a j * z j) i
        ∂hillNominalComponentLaw beta m) r := by
  exact (tendsto_finsetSum Finset.univ (fun i _ =>
    hill_nominal_partition_integral_continuousAt a hb ha hr i)).const_mul kappa

end Papers.TbsExtremeEffects
