module
public import Papers.TbsPrteOptimalTransport.Helpers.DebiasedQuantileBoundary
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousResidual
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileIndicatorConvergence
/-! Integrated quadratic boundary cancellation under selected conditional outcome laws. -/
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

-- @node: population_debiased_quantile_boundary_measurable
/-- If [the original boundary](hyp:ha) and [the perturbed boundary](hyp:hb) are
measurable, [the treated-law expectation of the change in the positive boundary
shortfall, after subtracting the boundary change times the original lower-tail
indicator, is measurable in covariates](goal). -/
@[fun_prop] lemma population_debiased_quantile_boundary_measurable
    (L : LevelData Z X) (i : ℕ) (a b : X → ℝ)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => ∫ y, (b x - y) * indicator (y ≤ b x) -
      (a x - y) * indicator (y ≤ a x) -
      (b x - a x) * indicator (y ≤ a x) ∂treatedLaw M L i x) := by
  fun_prop

-- No separate integrability assumption is imposed on the remainder: the
-- finite conditional mass and the squared boundary error supply it.
-- @node: population_debiased_quantile_boundary_integrated_quadratic
/-- If [the original boundary](hyp:ha) and [the perturbed boundary](hyp:hb) are
measurable, [their difference is square-integrable](hyp:he), [the neighborhood
radius is positive](hyp:hr), [the density bound is nonnegative](hyp:hC), and
[almost every conditional treated law assigns each interval within that radius
of the original boundary mass at most the density bound times its
length](hyp:hdensity), [the debiased change in expected positive boundary
shortfall is integrable and the absolute value of its population mean is at most
the density bound plus the reciprocal radius, times the mean squared boundary
change](goal). -/
lemma population_debiased_quantile_boundary_integrated_quadratic
    (L : LevelData Z X) (i : ℕ) (a b : X → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (he : MemLp (fun x => b x - a x) 2 (xLaw M))
    (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    Integrable (fun x => ∫ y, (b x - y) * indicator (y ≤ b x) -
      (a x - y) * indicator (y ≤ a x) -
      (b x - a x) * indicator (y ≤ a x) ∂treatedLaw M L i x) (xLaw M) ∧
    |∫ x, (∫ y, (b x - y) * indicator (y ≤ b x) -
      (a x - y) * indicator (y ≤ a x) -
      (b x - a x) * indicator (y ≤ a x) ∂treatedLaw M L i x) ∂xLaw M| ≤
      (C + 1 / r) * ∫ x, (b x - a x) ^ 2 ∂xLaw M := by
  let R := fun x => ∫ y, (b x - y) * indicator (y ≤ b x) -
    (a x - y) * indicator (y ≤ a x) -
    (b x - a x) * indicator (y ≤ a x) ∂treatedLaw M L i x
  have hm : Measurable R :=
    population_debiased_quantile_boundary_measurable M L i a b ha hb
  have hbound : ∀ᵐ x ∂xLaw M, |R x| ≤ (C + 1 / r) * (b x - a x) ^ 2 := by
    filter_upwards [hdensity] with x hx
    let := treatedLaw_isFiniteMeasure M L i x
    have hq := debiased_quantile_boundary_global_quadratic
      (treatedLaw M L i x) (a x) (b x) r C hr hC hx
    have hmass := treatedLaw_mass_le_one M L i x
    exact hq.trans (mul_le_mul_of_nonneg_right
      (add_le_add_right (div_le_div_of_nonneg_right hmass hr.le) C) (sq_nonneg _))
  have hdom := he.integrable_sq.const_mul (C + 1 / r)
  have hi : Integrable R (xLaw M) := hdom.mono' hm.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hi, ?_⟩
  calc
    |∫ x, R x ∂xLaw M| ≤ ∫ x, |R x| ∂xLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ x, (C + 1 / r) * (b x - a x) ^ 2 ∂xLaw M :=
      integral_mono_ae hi.abs hdom hbound
    _ = _ := integral_const_mul _ _

-- The derivative is obtained from the integrated quadratic estimate. In
-- particular, differentiation under an integral of indicators is unnecessary.
-- @node: population_debiased_quantile_boundary_path_orthogonality
/-- If [the original boundary is measurable](hyp:ha), [the perturbation direction
is measurable](hyp:hd) and [square-integrable](hyp:hd2), [the neighborhood radius
is positive](hyp:hr), [the density bound is nonnegative](hyp:hC), and [almost
every conditional treated law bounds interval mass by the density bound times
length within that radius of the original boundary](hyp:hdensity), [the
population mean change in positive boundary shortfall, debiased by subtracting
the boundary displacement times the original lower-tail indicator, has derivative
zero at zero along the linear perturbation path](goal). -/
lemma population_debiased_quantile_boundary_path_orthogonality
    (L : LevelData Z X) (i : ℕ) (a d : X → ℝ)
    (ha : Measurable a) (hd : Measurable d) (hd2 : MemLp d 2 (xLaw M))
    (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    HasDerivAt (fun t : ℝ => ∫ x, (∫ y,
      (a x + t * d x - y) * indicator (y ≤ a x + t * d x) -
      (a x - y) * indicator (y ≤ a x) -
      (t * d x) * indicator (y ≤ a x) ∂treatedLaw M L i x) ∂xLaw M) 0 0 := by
  let F := fun t : ℝ => ∫ x, (∫ y,
    (a x + t * d x - y) * indicator (y ≤ a x + t * d x) -
    (a x - y) * indicator (y ≤ a x) -
    (t * d x) * indicator (y ≤ a x) ∂treatedLaw M L i x) ∂xLaw M
  have hbound (t : ℝ) : |F t| ≤
      ((C + 1 / r) * ∫ x, d x ^ 2 ∂xLaw M) * t ^ 2 := by
    have hb := (population_debiased_quantile_boundary_integrated_quadratic M L i
      a (fun x => a x + t * d x) ha (by fun_prop)
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
    apply Asymptotics.IsBigO.of_bound ((C + 1 / r) * ∫ x, d x ^ 2 ∂xLaw M)
    exact Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using hbound t
  change HasDerivAt F 0 0
  apply HasDerivAt.of_isLittleO
  simpa only [hz, sub_zero, smul_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

-- This instantiates the cancellation with the paper's density condition,
-- for both treated laws at every estimated interior boundary.
-- @node: population_continuous_quantile_boundary_orthogonality
/-- Under [bounded boundary densities](hyp:h), if [the level index is
valid](hyp:hk), [the boundary index is positive](hyp:hj) and [does not exceed the
number of bands](hyp:hjl), [the treated-law level is the next level or the current
positive level](hyp:hi), [the population boundary is measurable](hyp:ha), and
[the perturbation direction is measurable](hyp:hd) and
[square-integrable](hyp:hd2), [the population mean change in positive shortfall
about that boundary, debiased by its original lower-tail indicator, has derivative
zero at zero along the linear boundary perturbation](goal). -/
lemma population_continuous_quantile_boundary_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j) (hjl : j ≤ L.l k)
    (i : ℕ) (hi : i = k + 1 ∨ (1 ≤ k ∧ i = k))
    (ha : Measurable (bandBoundary M L k j))
    (d : X → ℝ) (hd : Measurable d) (hd2 : MemLp d 2 (xLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ x, (∫ y,
      (bandBoundary M L k j x + t * d x - y) *
        indicator (y ≤ bandBoundary M L k j x + t * d x) -
      (bandBoundary M L k j x - y) * indicator (y ≤ bandBoundary M L k j x) -
      (t * d x) * indicator (y ≤ bandBoundary M L k j x)
      ∂treatedLaw M L i x) ∂xLaw M) 0 0 := by
  obtain ⟨r, C, hr, hden⟩ := h
  apply population_debiased_quantile_boundary_path_orthogonality M L i
    (bandBoundary M L k j) d ha hd hd2 r |C| hr (abs_nonneg C)
  filter_upwards [hden k hk j hj hjl i hi] with x hx
  intro u v hu huv hv
  exact (hx u v hu huv hv).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.mpr huv))

end Papers.TbsPrteOptimalTransport
