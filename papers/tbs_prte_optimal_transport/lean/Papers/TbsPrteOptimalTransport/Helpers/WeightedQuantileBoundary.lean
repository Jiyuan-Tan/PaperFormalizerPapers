module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationDebiasedQuantileBoundary
/-! Weighted quadratic boundary cancellation for continuous product scores. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Bounded product-score weights may be signed. The L2 boundary error
-- supplies integrability; no separate weighted-remainder premise is needed.
-- @node: population_weighted_quantile_boundary_integrated_quadratic
/-- If [the two boundaries and the weight are measurable](hyp:ha,hb,hw),
[a nonnegative weight bound](hyp:hB) [holds almost everywhere](hyp:hwb), and
[the boundary displacement is square integrable](hyp:he), suppose
[treated interval masses near the original boundary are bounded by a density constant times interval length](hyp:hdensity)
for [a positive radius](hyp:hr) and [a nonnegative density constant](hyp:hC).
Then [the weighted, linearly corrected lower-tail boundary remainder is integrable, and its absolute population mean is at most the weight bound times the sum of the density constant and reciprocal radius times the mean squared displacement](goal). -/
lemma population_weighted_quantile_boundary_integrated_quadratic
    (L : LevelData Z X) (i : ℕ) (a b w : X → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hw : Measurable w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ᵐ x ∂xLaw M, |w x| ≤ B)
    (he : MemLp (fun x => b x - a x) 2 (xLaw M))
    (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    Integrable (fun x => w x * (∫ y, (b x - y) * indicator (y ≤ b x) -
      (a x - y) * indicator (y ≤ a x) -
      (b x - a x) * indicator (y ≤ a x) ∂treatedLaw M L i x)) (xLaw M) ∧
    |∫ x, w x * (∫ y, (b x - y) * indicator (y ≤ b x) -
      (a x - y) * indicator (y ≤ a x) -
      (b x - a x) * indicator (y ≤ a x) ∂treatedLaw M L i x) ∂xLaw M| ≤
      B * (C + 1 / r) * ∫ x, (b x - a x) ^ 2 ∂xLaw M := by
  let R := fun x => ∫ y, (b x - y) * indicator (y ≤ b x) -
    (a x - y) * indicator (y ≤ a x) -
    (b x - a x) * indicator (y ≤ a x) ∂treatedLaw M L i x
  have hm : Measurable (fun x => w x * R x) := by
    fun_prop
  have hbound : ∀ᵐ x ∂xLaw M,
      |w x * R x| ≤ (B * (C + 1 / r)) * (b x - a x) ^ 2 := by
    filter_upwards [hdensity, hwb] with x hx hwx
    let := treatedLaw_isFiniteMeasure M L i x
    have hq := debiased_quantile_boundary_global_quadratic
      (treatedLaw M L i x) (a x) (b x) r C hr hC hx
    have hmass := treatedLaw_mass_le_one M L i x
    have hR : |R x| ≤ (C + 1 / r) * (b x - a x) ^ 2 :=
      hq.trans (mul_le_mul_of_nonneg_right
        (add_le_add_right (div_le_div_of_nonneg_right hmass hr.le) C) (sq_nonneg _))
    rw [abs_mul]
    calc
      |w x| * |R x| ≤ B * ((C + 1 / r) * (b x - a x) ^ 2) :=
        mul_le_mul hwx hR (abs_nonneg _) hB
      _ = _ := by ring
  have hdom := he.integrable_sq.const_mul (B * (C + 1 / r))
  have hi : Integrable (fun x => w x * R x) (xLaw M) :=
    hdom.mono' hm.aestronglyMeasurable (by
      simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    |∫ x, w x * R x ∂xLaw M| ≤ ∫ x, |w x * R x| ∂xLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => w x * R x)
    _ ≤ ∫ x, (B * (C + 1 / r)) * (b x - a x) ^ 2 ∂xLaw M :=
      integral_mono_ae hi.abs hdom hbound
    _ = _ := integral_const_mul _ _

-- The weight itself may vary along the nuisance path. Uniform boundedness
-- is enough, since it multiplies an already quadratic boundary remainder.
-- @node: population_weighted_quantile_boundary_path_orthogonality
/-- If [the baseline boundary and perturbation direction are measurable](hyp:ha,hd),
[the direction is square integrable](hyp:hd2), [each path weight is measurable](hyp:hw), and
[a nonnegative constant](hyp:hB) [bounds all path weights almost everywhere](hyp:hwb),
while [treated interval masses near the boundary are bounded by a constant times interval length](hyp:hdensity)
for [a positive radius](hyp:hr) and [a nonnegative constant](hyp:hC), then
[the population weighted lower-tail boundary remainder, after subtracting its linear term, has derivative zero at zero along this path](goal). -/
lemma population_weighted_quantile_boundary_path_orthogonality
    (L : LevelData Z X) (i : ℕ) (a d : X → ℝ) (w : ℝ → X → ℝ)
    (ha : Measurable a) (hd : Measurable d) (hd2 : MemLp d 2 (xLaw M))
    (hw : ∀ t, Measurable (w t)) (B : ℝ) (hB : 0 ≤ B)
    (hwb : ∀ t, ∀ᵐ x ∂xLaw M, |w t x| ≤ B)
    (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    HasDerivAt (fun t : ℝ => ∫ x, w t x * (∫ y,
      (a x + t * d x - y) * indicator (y ≤ a x + t * d x) -
      (a x - y) * indicator (y ≤ a x) -
      (t * d x) * indicator (y ≤ a x) ∂treatedLaw M L i x) ∂xLaw M) 0 0 := by
  let F := fun t : ℝ => ∫ x, w t x * (∫ y,
    (a x + t * d x - y) * indicator (y ≤ a x + t * d x) -
    (a x - y) * indicator (y ≤ a x) -
    (t * d x) * indicator (y ≤ a x) ∂treatedLaw M L i x) ∂xLaw M
  have hbound (t : ℝ) : |F t| ≤
      ((B * (C + 1 / r)) * ∫ x, d x ^ 2 ∂xLaw M) * t ^ 2 := by
    have hb := (population_weighted_quantile_boundary_integrated_quadratic M L i
      a (fun x => a x + t * d x) (w t) ha (by fun_prop) (hw t) B hB (hwb t)
      (by simpa only [add_sub_cancel_left] using hd2.const_mul t)
      r C hr hC hdensity).2
    simp only [add_sub_cancel_left, mul_pow, integral_const_mul] at hb
    dsimp [F]
    convert hb using 1
    ring
  have hz : F 0 = 0 := by
    have hb := hbound 0
    exact abs_nonpos_iff.mp (by simpa using hb)
  have ho : F =O[nhds 0] (fun t : ℝ => t ^ 2) := by
    apply Asymptotics.IsBigO.of_bound ((B * (C + 1 / r)) * ∫ x, d x ^ 2 ∂xLaw M)
    exact Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using hbound t
  change HasDerivAt F 0 0
  apply HasDerivAt.of_isLittleO
  simpa only [hz, sub_zero, smul_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

-- @node: population_continuous_weighted_quantile_boundary_orthogonality
/-- Suppose [treated outcome densities are uniformly bounded near band boundaries](hyp:h),
[the baseline interval index is valid](hyp:hk), [the boundary index is at least one](hyp:hj)
and [does not exceed the number of bands](hyp:hjl), and
[the treated law is taken at the interval's upper level or its positive-index lower level](hyp:hi).
If [this boundary is measurable](hyp:ha), [the perturbation direction is measurable](hyp:hd)
and [square integrable](hyp:hd2), and [path weights are measurable](hyp:hw) with
[a nonnegative bound](hyp:hB) [holding almost everywhere for every path value](hyp:hwb), then
[the population weighted, linearly corrected boundary remainder has derivative zero at zero](goal). -/
lemma population_continuous_weighted_quantile_boundary_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j) (hjl : j ≤ L.l k)
    (i : ℕ) (hi : i = k + 1 ∨ (1 ≤ k ∧ i = k))
    (ha : Measurable (bandBoundary M L k j))
    (d : X → ℝ) (hd : Measurable d) (hd2 : MemLp d 2 (xLaw M))
    (w : ℝ → X → ℝ) (hw : ∀ t, Measurable (w t))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t, ∀ᵐ x ∂xLaw M, |w t x| ≤ B) :
    HasDerivAt (fun t : ℝ => ∫ x, w t x * (∫ y,
      (bandBoundary M L k j x + t * d x - y) *
        indicator (y ≤ bandBoundary M L k j x + t * d x) -
      (bandBoundary M L k j x - y) * indicator (y ≤ bandBoundary M L k j x) -
      (t * d x) * indicator (y ≤ bandBoundary M L k j x)
      ∂treatedLaw M L i x) ∂xLaw M) 0 0 := by
  obtain ⟨r, C, hr, hden⟩ := h
  apply population_weighted_quantile_boundary_path_orthogonality M L i
    (bandBoundary M L k j) d w ha hd hd2 hw B hB hwb r |C| hr (abs_nonneg C)
  filter_upwards [hden k hk j hj hjl i hi] with x hx
  intro u v hu huv hv
  exact (hx u v hu huv hv).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.mpr huv))

end Papers.TbsPrteOptimalTransport
