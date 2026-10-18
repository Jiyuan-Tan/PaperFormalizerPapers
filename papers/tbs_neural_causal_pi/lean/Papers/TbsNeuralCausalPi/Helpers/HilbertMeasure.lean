module
public import Papers.TbsNeuralCausalPi.Helpers.HilbertGeometry
public import Papers.TbsNeuralCausalPi.Helpers.ComponentLaws
public import Papers.TbsNeuralCausalPi.Helpers.OneDimensionalCurve
public import Papers.TbsNeuralCausalPi.Helpers.HilbertReparameterization
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Analysis.SpecificLimits.Basic
/-! # Matched volumes of the Hilbert construction's dyadic cells

The parameter intervals and the traversal's cube cells have the same mass.
Cube boundaries are null, so the closed spatial cells form a measure partition.
Shrinking the mesh proves that the localized Hilbert curve preserves volume.
The first-hit lift and quantile time change then represent dominated cube laws.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction
open Causalean.Mathlib.Topology.SpaceFillingCurve

-- @node: hilbertCubeCell_eq_Icc
/-- For [a dyadic traversal](hyp:T), [a refinement level](hyp:n), and [a cell index](hyp:k),
[the spatial cell is the closed coordinate box whose lower bounds are its grid coordinates
divided by 2 to the refinement level and whose upper bounds are one grid step higher](goal). -/
lemma hilbertCubeCell_eq_Icc {d : ℕ} (T : DyadicTraversal d) (n : ℕ)
    (k : Fin (2 ^ (d * n))) :
    {x | dyadicCubeCell T n k x} =
      Set.Icc (fun j => ((T.cell n k j).val : ℝ) / (2 ^ n : ℝ))
        (fun j => (((T.cell n k j).val : ℝ) + 1) / (2 ^ n : ℝ)) := by
  ext x
  exact forall_and

-- @node: hilbertCubeCell_isCompact
/-- For [a dyadic traversal](hyp:T), [a refinement level](hyp:n), and [a cell index](hyp:k),
[the corresponding closed spatial cell is compact](goal). -/
lemma hilbertCubeCell_isCompact {d : ℕ} (T : DyadicTraversal d) (n : ℕ)
    (k : Fin (2 ^ (d * n))) : IsCompact {x | dyadicCubeCell T n k x} := by
  rw [hilbertCubeCell_eq_Icc]
  exact isCompact_Icc

-- @node: hilbertCubeCell_subset_unitCube
/-- For [a dyadic traversal](hyp:T), [a refinement level](hyp:n), and [a cell index](hyp:k),
[the corresponding spatial cell lies entirely in the unit cube](goal). -/
lemma hilbertCubeCell_subset_unitCube {d : ℕ} (T : DyadicTraversal d) (n : ℕ)
    (k : Fin (2 ^ (d * n))) :
    {x | dyadicCubeCell T n k x} ⊆ {x | InUnitCube x} := by
  intro x hx j
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hupper : ((T.cell n k j).val : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (T.cell n k j).isLt
  exact ⟨(div_nonneg (Nat.cast_nonneg _) hpow.le).trans (hx j).1,
    ((hx j).2).trans ((div_le_one hpow).2 hupper)⟩

-- @node: hilbertCubeCell_volume
/-- For [a dyadic traversal](hyp:T), [a refinement level n](hyp:n), and [a cell index](hyp:k),
[the spatial cell has Lebesgue volume 2 to the power minus d times n, where d is the dimension](goal). -/
lemma hilbertCubeCell_volume {d : ℕ} (T : DyadicTraversal d) (n : ℕ)
    (k : Fin (2 ^ (d * n))) :
    volume {x | dyadicCubeCell T n k x} = ENNReal.ofReal ((2 : ℝ) ^ (d * n))⁻¹ := by
  rw [hilbertCubeCell_eq_Icc, Real.volume_Icc_pi]
  have hedge (j : Fin d) :
      (((T.cell n k j).val : ℝ) + 1) / (2 ^ n : ℝ) -
        ((T.cell n k j).val : ℝ) / (2 ^ n : ℝ) = (2 ^ n : ℝ)⁻¹ := by ring
  simp_rw [hedge]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity)]
  have hp : ((2 ^ n : ℝ)⁻¹) ^ d = (2 ^ (d * n) : ℝ)⁻¹ := by
    rw [inv_pow, ← pow_mul, Nat.mul_comm n d]
  rw [hp, ENNReal.ofReal_inv_of_pos (by positivity)]

-- @node: hilbertCubeCell_boundary_null
/-- For [a dyadic traversal](hyp:T), [a refinement level](hyp:n), and [a cell index](hyp:k),
[the boundary of the spatial cell has zero Lebesgue volume](goal). -/
lemma hilbertCubeCell_boundary_null {d : ℕ} (T : DyadicTraversal d) (n : ℕ)
    (k : Fin (2 ^ (d * n))) :
    volume (frontier {x | dyadicCubeCell T n k x}) = 0 := by
  rw [hilbertCubeCell_eq_Icc]
  exact (convex_Icc _ _).addHaar_frontier (μ := volume)

-- @node: hilbertTimeCell_subset_interval
/-- In [dimension d](hyp:d), at [refinement level n](hyp:n),
[the time cell with index k](hyp:k) [is contained in the closed unit interval](goal). -/
lemma hilbertTimeCell_subset_interval (d n : ℕ) (k : Fin (2 ^ (d * n))) :
    dyadicTimeCell d n k ⊆ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  have hpow : (0 : ℝ) < 2 ^ (d * n) := by positivity
  have hupper : (k.val : ℝ) + 1 ≤ (2 : ℝ) ^ (d * n) := by
    exact_mod_cast k.isLt
  exact ⟨(div_nonneg (Nat.cast_nonneg _) hpow.le).trans ht.1,
    ht.2.trans ((div_le_one hpow).2 hupper)⟩

-- @node: hilbertTimeCell_volume
/-- In [dimension d](hyp:d), at [refinement level n](hyp:n),
[the time cell with index k](hyp:k) [has Lebesgue length 2 to the power minus d times n](goal). -/
lemma hilbertTimeCell_volume (d n : ℕ) (k : Fin (2 ^ (d * n))) :
    volume (dyadicTimeCell d n k) = ENNReal.ofReal ((2 : ℝ) ^ (d * n))⁻¹ := by
  change volume (Set.Icc ((k.val : ℝ) / (2 ^ (d * n) : ℝ))
    (((k.val : ℝ) + 1) / (2 ^ (d * n) : ℝ))) = _
  rw [Real.volume_Icc]
  have hedge : ((k.val : ℝ) + 1) / (2 ^ (d * n) : ℝ) -
      (k.val : ℝ) / (2 ^ (d * n) : ℝ) = (2 ^ (d * n) : ℝ)⁻¹ := by ring
  rw [hedge, ENNReal.ofReal_inv_of_pos (by positivity)]

-- @node: hilbertTimeCell_curveLebesgue
/-- In [dimension d](hyp:d), at [refinement level n](hyp:n),
[the time cell with index k](hyp:k) [has mass 2 to the power minus d times n
under Lebesgue measure restricted to the unit interval](goal). -/
lemma hilbertTimeCell_curveLebesgue (d n : ℕ) (k : Fin (2 ^ (d * n))) :
    curveLebesgue (dyadicTimeCell d n k) =
      ENNReal.ofReal ((2 : ℝ) ^ (d * n))⁻¹ := by
  change (volume.restrict (Set.Icc (0 : ℝ) 1)) _ = _
  rw [Measure.restrict_apply (show MeasurableSet (dyadicTimeCell d n k) from measurableSet_Icc),
    Set.inter_eq_left.mpr (hilbertTimeCell_subset_interval d n k),
    hilbertTimeCell_volume]

-- @node: hilbertCubeCell_cubeLebesgue
/-- For [a dyadic traversal](hyp:T), [a refinement level](hyp:n), and [a cell index](hyp:k),
[the spatial cell's mass under unit-cube Lebesgue measure equals the corresponding
time cell's mass under unit-interval Lebesgue measure](goal). -/
lemma hilbertCubeCell_cubeLebesgue {d : ℕ} (T : DyadicTraversal d) (n : ℕ)
    (k : Fin (2 ^ (d * n))) :
    cubeLebesgue d {x | dyadicCubeCell T n k x} =
      curveLebesgue (dyadicTimeCell d n k) := by
  rw [cubeLebesgue, Measure.restrict_apply (hilbertCubeCell_isCompact T n k).measurableSet,
    Set.inter_eq_left.mpr (show {x | dyadicCubeCell T n k x} ⊆
      {x | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1} from hilbertCubeCell_subset_unitCube T n k),
    hilbertCubeCell_volume, hilbertTimeCell_curveLebesgue]

-- @node: hilbertTimeCell_cover
/-- In [dimension d](hyp:d), at [any refinement level](hyp:n),
[the union of all time cells is exactly the closed unit interval](goal). -/
lemma hilbertTimeCell_cover (d n : ℕ) :
    (⋃ k : Fin (2 ^ (d * n)), dyadicTimeCell d n k) = Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (hilbertTimeCell_subset_interval d n)
  · intro t ht
    obtain ⟨k, l, hk, _⟩ := exists_neighboring_timeCells d n ht ht
      (by simp only [sub_self, abs_zero]; positivity)
    exact Set.mem_iUnion.mpr ⟨k, hk⟩

-- @node: hilbertTimeCell_aedisjoint
/-- In [dimension d](hyp:d), at [any refinement level](hyp:n),
[distinct time cells overlap only on sets of zero Lebesgue measure](goal). -/
lemma hilbertTimeCell_aedisjoint (d n : ℕ) :
    Pairwise (fun k l : Fin (2 ^ (d * n)) =>
      AEDisjoint volume (dyadicTimeCell d n k) (dyadicTimeCell d n l)) := by
  intro k l hkl
  have hpow : (0 : ℝ) < 2 ^ (d * n) := by positivity
  suffices h : ∀ a b : Fin (2 ^ (d * n)), a.val < b.val →
      volume (dyadicTimeCell d n a ∩ dyadicTimeCell d n b) = 0 by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with hlt | hgt
    · exact h k l hlt
    · rw [AEDisjoint, Set.inter_comm]
      exact h l k hgt
  intro a b hab
  apply measure_mono_null (t := {((a.val : ℝ) + 1) / (2 ^ (d * n) : ℝ)})
  · intro t ht
    have hstep : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast hab
    have hbound := (div_le_div_iff_of_pos_right hpow).2 hstep
    exact Set.mem_singleton_iff.mpr (le_antisymm ht.1.2 (hbound.trans ht.2.1))
  · exact measure_singleton _

-- @node: hilbertCubeCell_cover
/-- For [a dyadic traversal](hyp:T) and [any refinement level](hyp:n),
[the union of all spatial cells is exactly the unit cube](goal). -/
lemma hilbertCubeCell_cover {d : ℕ} (T : DyadicTraversal d) (n : ℕ) :
    (⋃ k : Fin (2 ^ (d * n)), {x | dyadicCubeCell T n k x}) =
      {x | InUnitCube x} := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (hilbertCubeCell_subset_unitCube T n)
  · intro x hx
    obtain ⟨k, hk⟩ := T.cubeCell_cover n x hx
    exact Set.mem_iUnion.mpr ⟨k, hk⟩

-- @node: hilbertCubeCell_aedisjoint
/-- For [a dyadic traversal](hyp:T) and [any refinement level](hyp:n),
[distinct spatial cells overlap only on sets of zero Lebesgue volume](goal). -/
lemma hilbertCubeCell_aedisjoint {d : ℕ} (T : DyadicTraversal d) (n : ℕ) :
    Pairwise (fun k l : Fin (2 ^ (d * n)) =>
      AEDisjoint volume {x | dyadicCubeCell T n k x} {x | dyadicCubeCell T n l x}) := by
  intro k l hkl
  have hne : T.cell n k ≠ T.cell n l := fun h => hkl ((T.bijective n).1 h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  suffices h : ∀ a b : Fin (2 ^ (d * n)), (T.cell n a j).val < (T.cell n b j).val →
      volume ({x | dyadicCubeCell T n a x} ∩ {x | dyadicCubeCell T n b x}) = 0 by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with hlt | hgt
    · exact h k l hlt
    · rw [AEDisjoint, Set.inter_comm]
      exact h l k hgt
  intro a b hab
  apply measure_mono_null (t := {x : Fin d → ℝ |
    x j = (((T.cell n a j).val : ℝ) + 1) / (2 ^ n : ℝ)})
  · intro x hx
    have hstep : ((T.cell n a j).val : ℝ) + 1 ≤ (T.cell n b j).val := by
      exact_mod_cast hab
    have hbound := (div_le_div_iff_of_pos_right hpow).2 hstep
    exact le_antisymm (hx.1 j).2 (hbound.trans (hx.2 j).1)
  · rw [volume_pi]
    exact Measure.pi_hyperplane (fun _ : Fin d => volume) j _

-- @node: hilbertTimeCell_partition
/-- In [dimension d](hyp:d), at [any refinement level](hyp:n),
[Lebesgue measure restricted to the unit interval equals the sum of Lebesgue
measures restricted to the individual time cells](goal). -/
lemma hilbertTimeCell_partition (d n : ℕ) :
    curveLebesgue = Measure.sum (fun k : Fin (2 ^ (d * n)) =>
      volume.restrict (dyadicTimeCell d n k)) := by
  change volume.restrict (Set.Icc (0 : ℝ) 1) = _
  rw [← hilbertTimeCell_cover d n]
  exact Measure.restrict_iUnion_ae (hilbertTimeCell_aedisjoint d n)
    (fun _ => measurableSet_Icc.nullMeasurableSet)

-- @node: hilbertCubeCell_partition
/-- For [a dyadic traversal](hyp:T) and [any refinement level](hyp:n),
[Lebesgue measure restricted to the unit cube equals the sum of Lebesgue
measures restricted to the individual spatial cells](goal). -/
lemma hilbertCubeCell_partition {d : ℕ} (T : DyadicTraversal d) (n : ℕ) :
    cubeLebesgue d = Measure.sum (fun k : Fin (2 ^ (d * n)) =>
      volume.restrict {x | dyadicCubeCell T n k x}) := by
  change volume.restrict {x | InUnitCube x} = _
  rw [← hilbertCubeCell_cover T n]
  exact Measure.restrict_iUnion_ae (hilbertCubeCell_aedisjoint T n)
    (fun k => (hilbertCubeCell_isCompact T n k).measurableSet.nullMeasurableSet)

-- @node: hilbertCubeCell_dist_le
/-- For [a dyadic traversal](hyp:T), [a refinement level n](hyp:n), and [a cell index](hyp:k),
if [x lies in that spatial cell](hyp:hx) and [y lies in the same cell](hyp:hy),
[their maximum coordinate distance is at most the reciprocal of 2 to the power n](goal). -/
lemma hilbertCubeCell_dist_le {d : ℕ} (T : DyadicTraversal d) (n : ℕ)
    (k : Fin (2 ^ (d * n))) {x y : Fin d → ℝ}
    (hx : dyadicCubeCell T n k x) (hy : dyadicCubeCell T n k y) :
    dist x y ≤ (2 ^ n : ℝ)⁻¹ := by
  apply (dist_pi_le_iff (by positivity)).2
  intro j
  rw [Real.dist_eq, abs_le]
  have hedge : (((T.cell n k j).val : ℝ) + 1) / (2 ^ n : ℝ) -
      ((T.cell n k j).val : ℝ) / (2 ^ n : ℝ) = (2 ^ n : ℝ)⁻¹ := by ring
  constructor <;> linarith [(hx j).1, (hx j).2, (hy j).1, (hy j).2]

-- @node: hilbert_matched_integral_bound
/-- Suppose [a real-valued function f](hyp:f) and [a real-valued function g](hyp:g) are [integrable under the first finite measure](hyp:hf)
and [under the second finite measure, respectively](hyp:hg), and [the two measures have equal total mass](hyp:hmass).
For [a common reference value c](hyp:c) and [an error bound eps](hyp:eps), if
[f differs from c by at most eps almost everywhere](hyp:hfclose) and
[g does likewise under its measure](hyp:hgclose), [their integrals differ in absolute value
by at most twice eps times the common total mass](goal). -/
lemma hilbert_matched_integral_bound {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {m : Measure X} {v : Measure Y}
    [IsFiniteMeasure m] [IsFiniteMeasure v]
    (f : X → ℝ) (g : Y → ℝ) (hf : Integrable f m) (hg : Integrable g v)
    (hmass : m Set.univ = v Set.univ) (c eps : ℝ)
    (hfclose : ∀ᵐ x ∂m, |f x - c| ≤ eps)
    (hgclose : ∀ᵐ y ∂v, |g y - c| ≤ eps) :
    |(∫ x, f x ∂m) - ∫ y, g y ∂v| ≤ 2 * eps * (m Set.univ).toReal := by
  have hmassreal : m.real Set.univ = v.real Set.univ := congrArg ENNReal.toReal hmass
  have hm : |(∫ x, f x ∂m) - m.real Set.univ * c| ≤ eps * m.real Set.univ := by
    have h := norm_integral_le_of_norm_le_const (f := fun x => f x - c) hfclose
    rw [integral_sub hf (integrable_const c), integral_const] at h
    simpa only [Real.norm_eq_abs, smul_eq_mul] using h
  have hv : |(∫ y, g y ∂v) - v.real Set.univ * c| ≤ eps * v.real Set.univ := by
    have h := norm_integral_le_of_norm_le_const (f := fun y => g y - c) hgclose
    rw [integral_sub hg (integrable_const c), integral_const] at h
    simpa only [Real.norm_eq_abs, smul_eq_mul] using h
  rw [← hmassreal] at hv
  have ht := abs_sub_le (∫ x, f x ∂m) (m.real Set.univ * c) (∫ y, g y ∂v)
  rw [abs_sub_comm (m.real Set.univ * c)] at ht
  change _ ≤ 2 * eps * m.real Set.univ
  linarith

-- @node: localizedHilbert_integral_comparison
/-- For [a localized cube curve](hyp:H) in [dimension at least two](hyp:hd),
[a bounded continuous real-valued function](hyp:phi), [a refinement level](hyp:n), and
[an error bound eps](hyp:eps), suppose [the function varies by at most eps between any
two points in each spatial cell](hyp:hosc). Then [its integral along the curve with
uniform time differs from its unit-cube integral by at most twice eps](goal). -/
lemma localizedHilbert_integral_comparison {d : ℕ} {T : DyadicTraversal d}
    (H : LocalizedCubeMap d T) (hd : 2 ≤ d) (phi : (Fin d → ℝ) →ᵇ ℝ)
    (n : ℕ) (eps : ℝ)
    (hosc : ∀ k : Fin (2 ^ (d * n)), ∀ x y,
      dyadicCubeCell T n k x → dyadicCubeCell T n k y → |phi x - phi y| ≤ eps) :
    |(∫ t, phi (H.toFun t) ∂curveLebesgue) - ∫ x, phi x ∂cubeLebesgue d| ≤
      2 * eps := by
  classical
  have hi : Integrable (fun t => phi (H.toFun t)) curveLebesgue :=
    (phi.continuous.comp_continuousOn (H.continuousOn hd)).integrableOn_compact isCompact_Icc
  have hcube : IsCompact {x : Fin d → ℝ | InUnitCube x} := by
    convert isCompact_univ_pi (fun _ : Fin d => isCompact_Icc (a := (0 : ℝ)) (b := 1)) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left, InUnitCube,
      Set.mem_Icc]
  have hj : Integrable (fun x => phi x) (cubeLebesgue d) :=
    phi.continuous.continuousOn.integrableOn_compact hcube
  have hmass : ∑ k : Fin (2 ^ (d * n)),
      (volume (dyadicTimeCell d n k)).toReal = 1 := by
    simp [hilbertTimeCell_volume]
  rw [hilbertTimeCell_partition d n] at hi ⊢
  rw [hilbertCubeCell_partition T n] at hj ⊢
  rw [integral_sum_measure hi, integral_sum_measure hj, tsum_fintype, tsum_fintype,
    ← Finset.sum_sub_distrib]
  calc
    |(∑ k, ((∫ t, phi (H.toFun t) ∂volume.restrict (dyadicTimeCell d n k)) -
        (∫ x, phi x ∂volume.restrict {x | dyadicCubeCell T n k x})))| ≤
      ∑ k, |(∫ t, phi (H.toFun t) ∂volume.restrict (dyadicTimeCell d n k)) -
        ∫ x, phi x ∂volume.restrict {x | dyadicCubeCell T n k x}| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin (2 ^ (d * n)), 2 * eps *
        (volume (dyadicTimeCell d n k)).toReal := by
      apply Finset.sum_le_sum
      intro k _
      let c := phi (H.toFun ((k.val : ℝ) / (2 ^ (d * n) : ℝ)))
      have htime : ((k.val : ℝ) / (2 ^ (d * n) : ℝ)) ∈ dyadicTimeCell d n k :=
        ⟨le_rfl, (div_le_div_iff_of_pos_right (by positivity)).2 (by linarith)⟩
      have href := H.localizes n k _ htime
      let m := volume.restrict (dyadicTimeCell d n k)
      let v := volume.restrict {x | dyadicCubeCell T n k x}
      let : IsFiniteMeasure m := isFiniteMeasure_restrict.mpr
        (show volume (dyadicTimeCell d n k) ≠ ∞ by
          rw [hilbertTimeCell_volume]
          exact ENNReal.ofReal_ne_top)
      let : IsFiniteMeasure v := isFiniteMeasure_restrict.mpr
        (show volume {x | dyadicCubeCell T n k x} ≠ ∞ by
          rw [hilbertCubeCell_volume]
          exact ENNReal.ofReal_ne_top)
      have hf := hi.mono_measure (Measure.le_sum _ k)
      have hg := hj.mono_measure (Measure.le_sum _ k)
      have hmv : m Set.univ = v Set.univ := by
        simp only [m, v, Measure.restrict_apply_univ,
          hilbertTimeCell_volume, hilbertCubeCell_volume]
      have he := hilbert_matched_integral_bound _ _ hf hg hmv c eps
        (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact hosc k _ _ (H.localizes n k t ht) href)
        (by
          filter_upwards [ae_restrict_mem (hilbertCubeCell_isCompact T n k).measurableSet]
            with x hx
          exact hosc k _ _ hx href)
      simpa only [m, Measure.restrict_apply_univ] using he
    _ = 2 * eps := by rw [← Finset.mul_sum, hmass, mul_one]

-- @node: localizedHilbert_map_cubeLebesgue
/-- For [a localized cube curve](hyp:H) in [dimension at least two](hyp:hd),
[the image of uniform unit-interval measure under the curve is unit-cube Lebesgue measure](goal). -/
lemma localizedHilbert_map_cubeLebesgue {d : ℕ} {T : DyadicTraversal d}
    (H : LocalizedCubeMap d T) (hd : 2 ≤ d) :
    curveLebesgue.map H.toFun = cubeLebesgue d := by
  let : IsFiniteMeasure curveLebesgue := by
    change IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1))
    infer_instance
  have hcompact : IsCompact {x : Fin d → ℝ | InUnitCube x} := by
    convert isCompact_univ_pi (fun _ : Fin d => isCompact_Icc (a := (0 : ℝ)) (b := 1)) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left, InUnitCube,
      Set.mem_Icc]
  let : IsFiniteMeasure (cubeLebesgue d) := isFiniteMeasure_restrict.mpr
    (show volume {x : Fin d → ℝ | InUnitCube x} ≠ ∞ from hcompact.measure_lt_top.ne)
  have hH : AEMeasurable H.toFun curveLebesgue := by
    first | fun_prop | exact (H.continuousOn hd).aemeasurable measurableSet_Icc
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro phi
  rw [integral_map hH phi.continuous.aestronglyMeasurable]
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm ?_ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨delta, hdelta, hosc⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous phi.continuous.continuousOn)
    (eps / 2) (by positivity)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hdelta (by norm_num : (1 / 2 : ℝ) < 1)
  have hmesh : (2 ^ n : ℝ)⁻¹ < delta := by
    simpa only [one_div, inv_pow] using hn
  have hbound := localizedHilbert_integral_comparison H hd phi n (eps / 2) (by
    intro k x y hx hy
    simpa only [Real.dist_eq] using (hosc x (hilbertCubeCell_subset_unitCube T n k hx)
      y (hilbertCubeCell_subset_unitCube T n k hy)
      ((hilbertCubeCell_dist_le T n k hx hy).trans_lt hmesh)).le)
  simpa only [zero_add, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hbound

-- @node: cubeLebesgue_map_toLp
/-- In [dimension d](hyp:d), [transporting unit-cube Lebesgue measure to the same
vectors equipped with the sum-of-absolute-coordinates norm equals transporting
product Lebesgue measure and then restricting it to the unit cube](goal). -/
lemma cubeLebesgue_map_toLp (d : ℕ) :
    (cubeLebesgue d).map (WithLp.toLp 1) =
      ((Measure.pi (fun _ : Fin d => volume)).map (WithLp.toLp 1)).restrict (unitCube d) := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  have hm : Measurable (WithLp.toLp 1 : (Fin d → ℝ) → L1Vec d) := by fun_prop
  have hc : MeasurableSet (unitCube d) := (unitCube_isCompact d).measurableSet
  rw [Measure.restrict_map hm hc, ← volume_pi]
  rfl

-- @node: exists_representing_holder_curve_on_of_uniform
/-- Let [C be a target set](hyp:C) that [is measurable](hyp:hC), and let [H be a curve](hyp:H)
with [nonnegative Hölder constant A and exponent r](hyp:A,r), where [r is positive](hyp:hr).
Suppose [H satisfies this Hölder bound on the unit interval](hyp:hH), [stays in C](hyp:hmem),
and [reaches every point of C there](hyp:hsurj). For [a probability law P](hyp:P)
[assigning mass one to C](hyp:hmass) and [a nonnegative constant c](hyp:c) that
[is positive](hyp:hc), if [P dominates c times the law of H at uniform time](hyp:hdom),
[there exists a continuous curve in C with uniform-time law P and Hölder exponent r
and constant A times c to the power minus r](goal). -/
lemma exists_representing_holder_curve_on_of_uniform {Y : Type*}
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (C : Set Y) (hC : MeasurableSet C) (H : ℝ → Y) (A r : ℝ≥0) (hr : 0 < r)
    (hH : HolderOnWith A r H (Set.Icc (0 : ℝ) 1))
    (hmem : Set.MapsTo H (Set.Icc (0 : ℝ) 1) C)
    (hsurj : ∀ x ∈ C, ∃ t ∈ Set.Icc (0 : ℝ) 1, H t = x)
    (P : Measure Y) [IsProbabilityMeasure P] (hmass : P C = 1)
    (c : ℝ≥0) (hc : 0 < c) (hdom : c • curveLebesgue.map H ≤ P) :
    ∃ gamma : ℝ → Y, ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
      Set.MapsTo gamma (Set.Icc (0 : ℝ) 1) C ∧ curveLebesgue.map gamma = P ∧
      HolderOnWith (A * c⁻¹ ^ (r : ℝ)) r gamma (Set.Icc (0 : ℝ) 1) := by
  classical
  let I := Set.Icc (0 : ℝ) 1
  have hzero : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  let h : ℝ → C := fun t => if ht : t ∈ I then ⟨H t, hmem ht⟩ else ⟨H 0, hmem hzero⟩
  have hh : HolderOnWith A r h I := by
    intro s hs t ht
    simpa only [h, dif_pos hs, dif_pos ht, Subtype.edist_eq] using hH s hs t ht
  have hhcont : ContinuousOn h I := hh.continuousOn hr
  have hhsurj : Function.Surjective (fun t : I => h t) := by
    intro x
    obtain ⟨t, ht, heq⟩ := hsurj x x.property
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    simpa only [h, I, dif_pos ht] using heq
  have hha : AEMeasurable h curveLebesgue := by
    first | fun_prop | exact hhcont.aemeasurable measurableSet_Icc
  have hmap : (curveLebesgue.map h).map ((↑) : C → Y) = curveLebesgue.map H := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_subtype_coe.aemeasurable hha]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [Function.comp_apply, h, I, dif_pos ht]
  let m := P.comap ((↑) : C → Y)
  let : IsProbabilityMeasure m := ⟨by
    rw [show m Set.univ = P (((↑) : C → Y) '' Set.univ) from
      (MeasurableEmbedding.subtype_coe hC).comap_apply P Set.univ,
      Set.image_univ, Subtype.range_coe, hmass]⟩
  have hm : m.map ((↑) : C → Y) = P := by
    rw [map_comap_subtype_coe hC]
    exact Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff_prob_eq_one hC).2 hmass)
  have hdomsub : c • curveLebesgue.map h ≤ m := by
    apply Measure.le_iff.mpr
    intro B hB
    have he := hdom (((↑) : C → Y) '' B)
    have him : MeasurableSet (((↑) : C → Y) '' B) :=
      (MeasurableEmbedding.subtype_coe hC).measurableSet_image.mpr hB
    rw [← hmap, Measure.smul_apply, (MeasurableEmbedding.subtype_coe hC).map_apply,
      Set.preimage_image_eq _ Subtype.coe_injective] at he
    simpa only [Measure.smul_apply, smul_eq_mul, m,
      (MeasurableEmbedding.subtype_coe hC).comap_apply] using he
  obtain ⟨gamma, hcont, hmaps, hpush, hholder⟩ :=
    exists_representing_holder_curve_of_uniform_curve h A r hr hh hhsurj m c hc hdomsub
  refine ⟨fun t => (gamma t).val, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp_continuousOn hcont
  · intro t ht
    exact (gamma t).property
  · have hga : AEMeasurable gamma curveLebesgue := by
      first | fun_prop | exact hcont.aemeasurable measurableSet_Icc
    change curveLebesgue.map gamma = m at hpush
    change curveLebesgue.map (((↑) : C → Y) ∘ gamma) = P
    rw [← AEMeasurable.map_map_of_aemeasurable measurable_subtype_coe.aemeasurable hga,
      hpush, hm]
  · intro s hs t ht
    exact hholder s hs t ht

-- @node: exists_uniform_holder_cube_curve
/-- For [dimension d](hyp:d) [at least two](hyp:hd), [there exists a curve on the unit
interval that stays in and covers the unit cube, has Hölder exponent 1/d and constant
4d for the sum-of-absolute-coordinates norm, and sends uniform time to product
Lebesgue measure restricted to the cube](goal). -/
lemma exists_uniform_holder_cube_curve (d : ℕ) (hd : 2 ≤ d) :
    ∃ H : ℝ → L1Vec d,
      HolderOnWith (4 * (d : ℝ≥0)) ((d : ℝ≥0)⁻¹) H (Set.Icc (0 : ℝ) 1) ∧
      Set.MapsTo H (Set.Icc (0 : ℝ) 1) (unitCube d) ∧
      (∀ x ∈ unitCube d, ∃ t ∈ Set.Icc (0 : ℝ) 1, H t = x) ∧
      curveLebesgue.map H =
        ((Measure.pi (fun _ : Fin d => volume)).map (WithLp.toLp 1)).restrict (unitCube d) := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  obtain ⟨T⟩ := exists_dyadicTraversal d (by omega)
  obtain ⟨H⟩ := exists_localizedCubeMap_of_traversal d T
  refine ⟨fun t => WithLp.toLp 1 (H.toFun t), localizedHilbert_holderOnWith H hd, ?_, ?_, ?_⟩
  · intro t ht j
    exact H.mapsToCube ht j
  · intro x hx
    obtain ⟨t, ht, heq⟩ := H.surjectiveOn x.ofLp hx
    refine ⟨t, ht, ?_⟩
    change WithLp.toLp 1 (H.toFun t) = x
    rw [heq, WithLp.toLp_ofLp]
  · have hHa : AEMeasurable H.toFun curveLebesgue := by
      first | fun_prop | exact (H.continuousOn hd).aemeasurable measurableSet_Icc
    have hm : Measurable (WithLp.toLp 1 : (Fin d → ℝ) → L1Vec d) := by fun_prop
    change curveLebesgue.map ((WithLp.toLp 1) ∘ H.toFun) = _
    rw [← AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hHa,
      localizedHilbert_map_cubeLebesgue H hd, cubeLebesgue_map_toLp]

-- @node: exists_component_pullback_holder_curve_ge_two
/-- In [dimension at least two](hyp:hd), let [mu be a probability law in the ambient
vector space](hyp:mu), [a chart identify the unit cube with a component K](hyp:chart),
and let [L be a nonnegative Lipschitz bound](hyp:L) and [Cf be a real density bound](hyp:Cf).
If [K is compact with mu-mass one, Cf is positive, the chart is L-Lipschitz,
and every measurable cube subset has chart-image mass at least Cf times its volume](hyp:hdom),
[there exists a curve staying in the unit cube, with Hölder exponent 1/d and some
nonnegative constant, whose uniform-time law is mu transported by the chart inverse](goal). -/
lemma exists_component_pullback_holder_curve_ge_two {D d : ℕ}
    (hd : 2 ≤ d) (mu : ProbabilityMeasure (L1Vec D)) {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube d) K) (L : ℝ≥0) (Cf : ℝ)
    (hdom : lowerBoundDominationAt (mu : Measure _) K chart L Cf) :
    ∃ gamma : ℝ → L1Vec d, ∃ A : ℝ≥0,
      HolderOnWith A ((d : ℝ≥0)⁻¹) gamma (Set.Icc (0 : ℝ) 1) ∧
      Set.MapsTo gamma (Set.Icc (0 : ℝ) 1) (unitCube d) ∧
      curveLebesgue.map gamma = (mu : Measure _).map (chartInverse chart) := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  let P := (mu : Measure _).map (chartInverse chart)
  let : IsProbabilityMeasure P :=
    Measure.isProbabilityMeasure_map (chartInverse_measurable chart hdom.1).aemeasurable
  obtain ⟨H, hH, hmem, hsurj, hmap⟩ := exists_uniform_holder_cube_curve d hd
  let c : ℝ≥0 := ⟨Cf, hdom.2.2.1.le⟩
  have hc : 0 < c := hdom.2.2.1
  have hdomP : c • curveLebesgue.map H ≤ P := by
    rw [hmap]
    have heq : ENNReal.ofReal Cf = (c : ℝ≥0∞) :=
      ENNReal.ofReal_eq_coe_nnreal hdom.2.2.1.le
    have hh := chartInverse_domination mu chart L Cf hdom
    rw [heq] at hh
    exact hh
  obtain ⟨gamma, hcont, hmaps, hpush, hholder⟩ :=
    exists_representing_holder_curve_on_of_uniform (unitCube d)
      (unitCube_isCompact d).measurableSet H (4 * (d : ℝ≥0)) ((d : ℝ≥0)⁻¹)
      (by positivity) hH hmem hsurj P
      (chartInverse_pullback_mass mu chart hdom.1 hdom.2.1) c hc hdomP
  exact ⟨gamma, _, hholder, hmaps, hpush⟩

end Papers.TbsNeuralCausalPi
