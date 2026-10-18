module
public import Papers.TbsExtremeEffects.Helpers.TailSurvival
public import Mathlib.Tactic

/-! Transfer of the exact component tail to the full-input radial law.
The nominal density keeps the original nonnegative component support. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
variable {q d m : ℕ}
noncomputable section

open Classical in
/-- [The nominal component density](goal), for [tail-shape parameter `beta`](hyp:beta) and [component vector `z`](hyp:z), equals the product Pareto density on the nonnegative orthant and zero outside it. -/
-- @node: hillNominalComponentDensity
def hillNominalComponentDensity (beta : ℝ) (z : Fin m → ℝ) : ℝ :=
  if z ∈ nonnegativeOrthant then paretoProductDensity beta z else 0

/-- [The nominal component law](goal), for [tail-shape parameter `beta`](hyp:beta) and [number of components `m`](hyp:m), is the measure with the nominal component density. -/
-- @node: hillNominalComponentLaw
def hillNominalComponentLaw (beta : ℝ) (m : ℕ) : Measure (Fin m → ℝ) :=
  volume.withDensity (fun z => ENNReal.ofReal (hillNominalComponentDensity beta z))

/-- If [the matrix has nonnegative entries](hyp:hA) and [the component vector is nonnegative](hyp:hz), then [the ℓ¹ radius of its matrix image equals the weighted sum of component values, weighted by column ℓ¹ norms](goal). -/
-- @node: hill_radial_matrix_sum
lemma hill_radial_matrix_sum (A : Matrix (Fin d) (Fin m) ℝ)
    (hA : ∀ r i, 0 ≤ A r i) {z : Fin m → ℝ} (hz : z ∈ nonnegativeOrthant) :
    l1Norm (A.mulVec z) = ∑ i, l1Norm (fun r => A r i) * z i := by
  have hz' : ∀ i, 0 ≤ z i := hz
  unfold l1Norm Matrix.mulVec dotProduct
  simp_rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hA _ i) (hz' i))]
  simp_rw [abs_of_nonneg (hA _ _), Finset.sum_mul]
  exact Finset.sum_comm

/-- If [the matrix belongs to the prescribed matrix class](hyp:hA) and [the component vector is nonnegative](hyp:hz), then [the matrix-image radius is at most the upper class bound times the component radius](goal). -/
-- @node: hill_radial_matrix_le
lemma hill_radial_matrix_le (A : Matrix (Fin d) (Fin m) ℝ) (tp : TailParams)
    (hA : A ∈ matrixClass tp) {z : Fin m → ℝ} (hz : z ∈ nonnegativeOrthant) :
    l1Norm (A.mulVec z) ≤ tp.u * l1Norm z := by
  rw [hill_radial_matrix_sum A hA.1 hz]
  calc
    _ ≤ ∑ i, tp.u * z i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hA.2.1 i).2 (hz i)
    _ = _ := by
      unfold l1Norm
      simp_rw [abs_of_nonneg (hz _)]
      rw [Finset.mul_sum]

/-- If [the matrix belongs to the prescribed matrix class](hyp:hA) and [the component vector is nonnegative](hyp:hz), then [the matrix-image radius is at least the lower class bound times the component radius](goal). -/
-- @node: hill_radial_matrix_ge
lemma hill_radial_matrix_ge (A : Matrix (Fin d) (Fin m) ℝ) (tp : TailParams)
    (hA : A ∈ matrixClass tp) {z : Fin m → ℝ} (hz : z ∈ nonnegativeOrthant) :
    tp.l * l1Norm z ≤ l1Norm (A.mulVec z) := by
  rw [hill_radial_matrix_sum A hA.1 hz]
  calc
    _ = ∑ i, tp.l * z i := by
      unfold l1Norm
      simp_rw [abs_of_nonneg (hz _)]
      rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hA.2.1 i).1 (hz i)

/-- If [the multiplier is positive](hyp:hkappa), then [the leading radial coefficient obtained by summing the powered column norms is positive](goal). -/
-- @node: hill_radial_leading_constant_pos
lemma hill_radial_leading_constant_pos (M : ExtremeModel q d) (tp : TailParams)
    (model : ParetoTailModel M m tp) {kappa : ℝ} (hkappa : 0 < kappa) :
    0 < kappa * ∑ i : Fin m, (l1Norm (fun r => model.A r i)) ^ M.beta := by
  have hm : 0 < m := by
    obtain ⟨hd, hdm⟩ := model.constants.1
    omega
  have hi : ∀ i : Fin m, 0 < (l1Norm (fun r => model.A r i)) ^ M.beta := by
    intro i
    exact Real.rpow_pos_of_pos (model.constants.2.1.trans_le (model.matrix.2.1 i).1) _
  have hsum : 0 < ∑ i : Fin m, (l1Norm (fun r => model.A r i)) ^ M.beta := by
    exact Finset.sum_pos (fun i _ => hi i) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact mul_pos hkappa hsum

/-- If [the matrix belongs to the prescribed class](hyp:hA), [its upper bound is nonnegative](hyp:hu), [the density multiplier is positive](hyp:hkappa), [the component density vanishes outside the nonnegative orthant](hyp:hzero), [it equals the stated Pareto density sufficiently far out almost everywhere](hyp:hexact), [the event is measurable](hyp:hs), and [every point of that event lies beyond the radial cutoff](hyp:htail), then [the actual component mass of the event equals the nominal mass times the multiplier](goal). -/
-- @node: hill_component_tail_transfer
lemma hill_component_tail_transfer (A : Matrix (Fin d) (Fin m) ℝ) (tp : TailParams)
    (hA : A ∈ matrixClass tp) (hu : 0 ≤ tp.u) {beta cutoff kappa : ℝ} (hkappa : 0 < kappa)
    (h : (Fin m → ℝ) → ℝ)
    (hzero : ∀ z, z ∉ nonnegativeOrthant → h z = 0)
    (hexact : ∀ᵐ z ∂(volume : Measure (Fin m → ℝ)),
      z ∈ nonnegativeOrthant → cutoff < l1Norm z →
      h z = kappa * paretoProductDensity beta z)
    (s : Set (Fin m → ℝ)) (hs : MeasurableSet s)
    (htail : ∀ z ∈ s, tp.u * cutoff < l1Norm (A.mulVec z)) :
    (volume.withDensity (fun z => ENNReal.ofReal (h z))) s =
      ENNReal.ofReal kappa * hillNominalComponentLaw beta m s := by
  rw [hillNominalComponentLaw, withDensity_apply _ hs, withDensity_apply _ hs]
  calc
    _ = ∫⁻ z in s, ENNReal.ofReal kappa *
        ENNReal.ofReal (hillNominalComponentDensity beta z) := by
      apply lintegral_congr_ae
      apply (ae_restrict_iff' hs).2
      filter_upwards [hexact] with z hzexact
      intro hz
      by_cases horth : z ∈ nonnegativeOrthant
      · have hcut : cutoff < l1Norm z := by
          by_contra hc
          have hb := hill_radial_matrix_le A tp hA horth
          have hc' := mul_le_mul_of_nonneg_left (not_lt.mp hc) hu
          linarith [htail z hz]
        rw [hzexact horth hcut, ENNReal.ofReal_mul hkappa.le]
        simp [hillNominalComponentDensity, horth]
      · simp [hzero z horth, hillNominalComponentDensity, horth]
    _ = _ := lintegral_const_mul' _ _ (by simp)

/-- [There are a sample-size cutoff and positive multiplier such that, beyond the resulting radial threshold, the full radial law equals the nominal matrix-image law times that multiplier on every measurable event](goal). -/
-- @node: hill_radial_tail_transfer
lemma hill_radial_tail_transfer (M : ExtremeModel q d) (tp : TailParams)
    (model : ParetoTailModel M m tp) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ kappa : ℝ, 0 < kappa ∧
      ∀ s : Set ℝ, MeasurableSet s →
        s ⊆ Set.Ioi (tp.u * (tp.zeta * (k : ℝ) ^ ((1 - 2 * tp.s) / M.beta))) →
        (M.mu.map (radius M)) s = ENNReal.ofReal kappa *
          ((hillNominalComponentLaw M.beta m).map (fun z => l1Norm (model.A.mulVec z))) s := by
  obtain ⟨k, hk, nuZ, hclass, hlaw⟩ := model.density
  obtain ⟨_, h, hmeas, hnonneg, hzero, hdensity, hrelative, kappa, hkappa, hexact⟩ := hclass
  have hu : 0 ≤ tp.u := by
    have := model.constants.2.2.2.1
    linarith
  have hmat : Measurable (Matrix.mulVec model.A) := by
    fun_prop
  have hrad : Measurable (fun z => l1Norm (model.A.mulVec z)) := by
    fun_prop
  refine ⟨k, hk, kappa, hkappa, ?_⟩
  intro s hs htail
  have hpre : MeasurableSet ((fun z => l1Norm (model.A.mulVec z)) ⁻¹' s) := hrad hs
  have hmass := hill_component_tail_transfer model.A tp model.matrix hu hkappa h hzero
    hexact _ hpre (fun z hz => htail hz)
  have hmap : M.mu.map (radius M) = nuZ.map (fun z => l1Norm (model.A.mulVec z)) := by
    calc
      _ = (M.mu.map M.U).map l1Norm :=
        (Measure.map_map measurable_l1Norm M.measurable_U).symm
      _ = (nuZ.map (Matrix.mulVec model.A)).map l1Norm := by rw [hlaw]
      _ = _ := Measure.map_map measurable_l1Norm hmat
  rw [hmap, Measure.map_apply hrad hs, hdensity, Measure.map_apply hrad hs]
  exact hmass

/-- [There are a sample-size cutoff and positive multiplier such that, beyond the resulting radial threshold, the model survival probability equals that multiplier times the nominal matrix-image survival probability](goal). -/
-- @node: hill_radial_survival_transfer
lemma hill_radial_survival_transfer (M : ExtremeModel q d) (tp : TailParams)
    (model : ParetoTailModel M m tp) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ kappa : ℝ, 0 < kappa ∧
      ∀ r, tp.u * (tp.zeta * (k : ℝ) ^ ((1 - 2 * tp.s) / M.beta)) < r →
        tailProb M r = kappa *
          ((hillNominalComponentLaw M.beta m).map (fun z => l1Norm (model.A.mulVec z))).real
            (Set.Ioi r) := by
  obtain ⟨k, hk, kappa, hkappa, htransfer⟩ := hill_radial_tail_transfer M tp model
  refine ⟨k, hk, kappa, hkappa, ?_⟩
  intro r hr
  have hmass := htransfer (Set.Ioi r) measurableSet_Ioi
    (fun x hx => hr.trans hx)
  rw [Measure.map_apply (measurable_radius M) measurableSet_Ioi] at hmass
  change M.mu {w | r < radius M w} = _ at hmass
  unfold tailProb Measure.real
  rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal hkappa.le]

end
end Papers.TbsExtremeEffects
