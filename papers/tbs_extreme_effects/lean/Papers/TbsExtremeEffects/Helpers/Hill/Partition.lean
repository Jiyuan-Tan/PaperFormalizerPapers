module
public import Papers.TbsExtremeEffects.Helpers.Hill.DensityContinuity

/-! The almost-sure largest-summand partition of the nominal radial law. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped BigOperators ENNReal

/-- If [all component weights are positive](hyp:ha), then [weighted nominal components have no ties almost surely](goal).

Their equality is a hyperplane with a nonzero coefficient. -/
-- @node: hill_nominal_weighted_ties_null
lemma hill_nominal_weighted_ties_null {m : ℕ} (a : Fin m → ℝ)
    (beta : ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᵐ z ∂hillNominalComponentLaw beta m, ∀ i j, i ≠ j → a i * z i ≠ a j * z j := by
  classical
  simp only [ae_all_iff]
  intro i j hij
  let c : Fin m → ℝ := fun l => (if l = i then a i else 0) -
    (if l = j then a j else 0)
  have hc : c i ≠ 0 := by simp [c, hij, (ha i).ne']
  have hvol := hill_linear_sum_ne_ae_volume c i hc 0
  have hnom := (withDensity_absolutelyContinuous volume
    (fun z => ENNReal.ofReal (hillNominalComponentDensity beta z))).ae_le hvol
  filter_upwards [hnom] with z hz
  intro heq
  apply hz
  simp only [c, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact sub_eq_zero.mpr heq

/-- If [the family is nonempty](hyp:hm) and [its values are pairwise distinct](hyp:hW), then [the sum of indicators selecting the unique largest value is the indicator that the total exceeds `r`](goal). -/
-- @node: hill_largest_summand_indicator_sum
lemma hill_largest_summand_indicator_sum {m : ℕ} (hm : 0 < m)
    (W : Fin m → ℝ) (hW : ∀ i j, i ≠ j → W i ≠ W j) (r : ℝ) :
    (∑ i : Fin m, if r < ∑ j, W j ∧ ∀ j, W j ≤ W i then (1 : ℝ≥0∞) else 0) =
      if r < ∑ j, W j then 1 else 0 := by
  classical
  by_cases hr : r < ∑ j, W j
  · obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ W
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    have himax : ∀ j, W j ≤ W i := fun j => hi j (Finset.mem_univ _)
    rw [if_pos hr, Finset.sum_eq_single i]
    · simp [hr, himax]
    · intro j _ hji
      have hj : ¬ ∀ l, W l ≤ W j := by
        intro hj
        exact hW j i hji (le_antisymm (himax j) (hj i))
      simp [hr, hj]
    · simp
  · simp [hr]

/-- If [there is at least one component](hyp:hm) and [every weight is positive](hyp:ha), then [the nominal probability that the weighted sum exceeds `r` is the sum of the probabilities of the events in which each component is uniquely largest](goal). -/
-- @node: hill_nominal_sum_tail_partition
lemma hill_nominal_sum_tail_partition {m : ℕ} (hm : 0 < m)
    (a : Fin m → ℝ) (beta : ℝ) (ha : ∀ i, 0 < a i) (r : ℝ) :
    (hillNominalComponentLaw beta m) {z | r < ∑ j, a j * z j} =
      ∑ i : Fin m, (hillNominalComponentLaw beta m)
        {z | r < ∑ j, a j * z j ∧ ∀ j, a j * z j ≤ a i * z i} := by
  classical
  have hmeas : ∀ i : Fin m, MeasurableSet
      {z : Fin m → ℝ | r < ∑ j, a j * z j ∧ ∀ j, a j * z j ≤ a i * z i} := by
    intro i
    change MeasurableSet ({z : Fin m → ℝ | r < ∑ j, a j * z j} ∩
      {z | ∀ j, a j * z j ≤ a i * z i})
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const (by fun_prop)
    · simpa only [Set.iInter_ofPred] using MeasurableSet.iInter
        (fun j => measurableSet_le (by fun_prop) (by fun_prop))
  have heq : (fun z : Fin m → ℝ =>
      if r < ∑ j, a j * z j then (1 : ℝ≥0∞) else 0) =ᵐ[hillNominalComponentLaw beta m]
      (fun z => ∑ i : Fin m,
        if r < ∑ j, a j * z j ∧ ∀ j, a j * z j ≤ a i * z i then 1 else 0) := by
    filter_upwards [hill_nominal_weighted_ties_null a beta ha] with z hz
    exact (hill_largest_summand_indicator_sum hm (fun i => a i * z i) hz r).symm
  have hInt := lintegral_congr_ae heq
  rw [lintegral_finsetSum Finset.univ (fun i _ =>
    Measurable.ite (hmeas i) measurable_const measurable_const)] at hInt
  have hmass : ∀ s : Set (Fin m → ℝ), MeasurableSet s →
      (∫⁻ z, if z ∈ s then (1 : ℝ≥0∞) else 0 ∂hillNominalComponentLaw beta m) =
        (hillNominalComponentLaw beta m) s := by
    intro s hs
    simpa only [Set.indicator, Pi.one_apply] using
      (lintegral_indicator_one (μ := hillNominalComponentLaw beta m) hs)
  calc
    _ = ∫⁻ z, if r < ∑ j, a j * z j then (1 : ℝ≥0∞) else 0
        ∂hillNominalComponentLaw beta m :=
      (hmass _ (measurableSet_lt measurable_const (by fun_prop))).symm
    _ = _ := hInt
    _ = ∑ i : Fin m, (hillNominalComponentLaw beta m)
        {z | r < ∑ j, a j * z j ∧ ∀ j, a j * z j ≤ a i * z i} := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Set.mem_setOf_eq] using hmass _ (hmeas i)

/-- If [there is at least one component](hyp:hm), [the tail-shape parameter is positive](hyp:hb), [the matrix has nonnegative entries](hyp:hA), and [each column has positive ℓ¹ norm](hyp:ha), then [the matrix-radius tail probability is partitioned by its unique largest weighted column component](goal). -/
-- @node: hill_nominal_radial_tail_partition
lemma hill_nominal_radial_tail_partition {d m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin d) (Fin m) ℝ) {beta : ℝ} (hb : 0 < beta)
    (hA : ∀ r i, 0 ≤ A r i) (ha : ∀ i, 0 < l1Norm (fun r => A r i)) (r : ℝ) :
    ((hillNominalComponentLaw beta m).map (fun z => l1Norm (A.mulVec z))) (Set.Ioi r) =
      ∑ i : Fin m, (hillNominalComponentLaw beta m)
        {z | r < ∑ j, l1Norm (fun r => A r j) * z j ∧
          ∀ j, l1Norm (fun r => A r j) * z j ≤ l1Norm (fun r => A r i) * z i} := by
  have hpos : ∀ᵐ z ∂hillNominalComponentLaw beta m, z ∈ nonnegativeOrthant := by
    simp only [nonnegativeOrthant, Set.mem_setOf_eq, ae_all_iff]
    intro j
    have hh := hill_scaled_paretoII_nonneg_ae (hillNominalComponentLaw beta m)
      (fun z => (1 : ℝ) * z j) (by norm_num : (0 : ℝ) < 1) (by fun_prop)
      (by simpa only [one_mul, div_one] using hill_nominal_coordinate_law hb j)
    simpa only [one_mul] using hh
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
  calc
    _ = (hillNominalComponentLaw beta m)
        {z | r < ∑ j, l1Norm (fun r => A r j) * z j} := by
      apply measure_congr
      filter_upwards [hpos] with z hz
      apply propext
      change (r < l1Norm (A.mulVec z)) ↔ r < ∑ j, l1Norm (fun r => A r j) * z j
      rw [hill_radial_matrix_sum A hA hz]
    _ = _ := hill_nominal_sum_tail_partition hm _ beta ha r

/-- If [there is at least one component](hyp:hm), [the tail-shape parameter is positive](hyp:hb), [the matrix has nonnegative entries](hyp:hA), [each column has positive ℓ¹ norm](hyp:ha), [the density multiplier is nonnegative](hyp:hkappa), [the threshold is positive](hyp:hr), and [each largest-component slice has its stated integral representation](hyp:hSlices), then [the scaled radial tail mass equals the tail mass under the stated slice density](goal). -/
-- @node: hill_nominal_density_tail_of_slices
lemma hill_nominal_density_tail_of_slices {d m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin d) (Fin m) ℝ) {beta : ℝ} (hb : 0 < beta)
    (hA : ∀ r i, 0 ≤ A r i) (ha : ∀ i, 0 < l1Norm (fun r => A r i))
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (r : ℝ) (hr : 0 < r)
    (hSlices : ∀ i : Fin m, (hillNominalComponentLaw beta m)
      {z | r < ∑ j, l1Norm (fun r => A r j) * z j ∧
        ∀ j, l1Norm (fun r => A r j) * z j ≤ l1Norm (fun r => A r i) * z i} =
      ∫⁻ x in Set.Ioi r, ENNReal.ofReal (∫ z,
        hillLargestSummandIntegrand (fun i => l1Norm (fun r => A r i)) beta x
          (fun j => l1Norm (fun r => A r j) * z j) i ∂hillNominalComponentLaw beta m)) :
    ENNReal.ofReal kappa *
        ((hillNominalComponentLaw beta m).map (fun z => l1Norm (A.mulVec z))) (Set.Ioi r) =
      (volume.withDensity (fun x => ENNReal.ofReal (kappa * ∑ i, ∫ z,
        hillLargestSummandIntegrand (fun i => l1Norm (fun r => A r i)) beta x
          (fun j => l1Norm (fun r => A r j) * z j) i ∂hillNominalComponentLaw beta m)))
        (Set.Ioi r) := by
  classical
  have hnonneg : ∀ x, r < x → ∀ i, 0 ≤ ∫ z,
      hillLargestSummandIntegrand (fun i => l1Norm (fun r => A r i)) beta x
        (fun j => l1Norm (fun r => A r j) * z j) i ∂hillNominalComponentLaw beta m := by
    intro x hx i
    apply integral_nonneg
    intro z
    change 0 ≤ hillLargestSummandIntegrand _ beta x _ i
    dsimp [hillLargestSummandIntegrand]
    split_ifs with hmax
    · have hres := hill_largest_summand_residual_ge
        (fun j => l1Norm (fun r => A r j) * z j) i hmax
      have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
      have hp : 0 < l1Norm (fun r => A r i) +
          (x - ∑ j ∈ Finset.univ.erase i, l1Norm (fun r => A r j) * z j) := by
        have := div_pos (hr.trans hx) hmR
        linarith [ha i]
      exact mul_nonneg (mul_nonneg hb.le (Real.rpow_nonneg (ha i).le _))
        (Real.rpow_nonneg hp.le _)
    · exact le_rfl
  rw [hill_nominal_radial_tail_partition hm A hb hA ha r]
  simp_rw [hSlices]
  rw [withDensity_apply _ measurableSet_Ioi]
  rw [← lintegral_finsetSum Finset.univ
    (fun i _ => (hill_nominal_partition_integral_measurable
      (fun i => l1Norm (fun r => A r i)) hb i).ennreal_ofReal),
    ← lintegral_const_mul' _ _ (by simp)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [ENNReal.ofReal_mul hkappa,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg x hx i)]


end Papers.TbsExtremeEffects
