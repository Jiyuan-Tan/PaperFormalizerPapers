module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandDirectionRegularity
/-! Quantile boundary cancellation with locally bounded fitted assignment weights. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Only a neighborhood of zero is relevant to the derivative. Extend the
-- weight by zero elsewhere to apply the global quadratic boundary estimate.
-- @node: population_weighted_quantile_boundary_local_path_orthogonality
/-- Suppose [the baseline boundary is measurable](hyp:ha), its direction is
[measurable](hyp:hd) and [square integrable](hyp:hd2), and [near zero the weights are measurable and almost surely bounded in absolute value by a common constant](hyp:hw)
that [is nonnegative](hyp:hB). If [the boundary neighborhood radius is positive](hyp:hr),
[the density bound is nonnegative](hyp:hC), and [selected treated outcome probabilities of intervals within that neighborhood are almost surely at most the density bound times interval length](hyp:hdensity),
[the expected weighted change in the lower-tail hinge, after subtracting its baseline linear term, has derivative zero at zero](goal). -/
lemma population_weighted_quantile_boundary_local_path_orthogonality
    (L : LevelData Z X) (i : ℕ) (a d : X → ℝ) (w : ℝ → X → ℝ)
    (ha : Measurable a) (hd : Measurable d) (hd2 : MemLp d 2 (xLaw M))
    (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ ∀ᵐ x ∂xLaw M, |w t x| ≤ B)
    (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    HasDerivAt (fun t : ℝ => ∫ x, w t x * (∫ y,
      (a x + t * d x - y) * indicator (y ≤ a x + t * d x) -
      (a x - y) * indicator (y ≤ a x) -
      (t * d x) * indicator (y ≤ a x) ∂treatedLaw M L i x) ∂xLaw M) 0 0 := by
  let good := fun t => Measurable (w t) ∧ ∀ᵐ x ∂xLaw M, |w t x| ≤ B
  let w' : ℝ → X → ℝ := fun t => if good t then w t else fun _ => 0
  have hwm (t : ℝ) : Measurable (w' t) := by
    dsimp only [w']
    split_ifs with ht
    · exact ht.1
    · fun_prop
  have hwb (t : ℝ) : ∀ᵐ x ∂xLaw M, |w' t x| ≤ B := by
    dsimp only [w']
    split_ifs with ht
    · exact ht.2
    · exact Eventually.of_forall fun _ => by simpa using hB
  apply (population_weighted_quantile_boundary_path_orthogonality M L i a d w'
    ha hd hd2 hwm B hB hwb r C hr hC hdensity).congr_of_eventuallyEq
  filter_upwards [hw] with t ht
  simp only [w', good, if_pos ht]

-- Clipped assignment probabilities and product weights yield an envelope
-- directly from admissibility and population overlap, including joint paths.
-- @node: continuous_regular_inverse_assignment_weight_local_regular
/-- Given [baseline assignment overlap with the specified positive lower bound](hyp:hov) and
[an admissible nuisance direction at the population nuisance collection](hyp:hd),
[near zero the ratio of any regular band weight to any assignment probability along the affine path is measurable and almost surely bounded in absolute value by two divided by the overlap bound](goal). -/
lemma continuous_regular_inverse_assignment_weight_local_regular
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a : RegularIndex L) (b : PositiveIndex L.K) :
    ∀ᶠ t : ℝ in 𝓝 0,
      Measurable (fun x => (trueNuisance M L + t • del).gamma a x /
        (trueNuisance M L + t • del).piLev b x) ∧
      ∀ᵐ x ∂xLaw M, |(trueNuisance M L + t • del).gamma a x /
        (trueNuisance M L + t • del).piLev b x| ≤ 2 / cpi := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
    continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht htr
  have had := hpath t htr
  rcases had with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm, _⟩
  refine ⟨by fun_prop, ?_⟩
  filter_upwards [hgb a, ht b] with x hgx hpx
  have hp : 0 < (trueNuisance M L + t • del).piLev b x :=
    lt_of_lt_of_le (div_pos hov.1 (by norm_num)) hpx
  rw [abs_div, abs_of_pos hp, abs_of_nonneg hgx.1]
  calc
    _ ≤ 1 / (cpi / 2) := div_le_div₀ (by norm_num) hgx.2
      (div_pos hov.1 (by norm_num)) hpx
    _ = 2 / cpi := by field_simp

-- The fitted gamma/pi ratio can multiply a fixed bounded population
-- coefficient. This is the boundary channel of the regular product score.
-- @node: population_continuous_fitted_weight_quantile_boundary_orthogonality
/-- Assume [bounded densities near the band boundaries](hyp:h), [baseline assignment overlap](hyp:hov),
and [an admissible nuisance direction at the population nuisance collection](hyp:hd).
If [the selected treatment level is the upper adjacent level or the positive lower adjacent level of the boundary's treatment interval](hyp:hi),
[the boundary is measurable](hyp:ha), and the additional coefficient is [measurable](hyp:hv) and
[almost surely bounded in absolute value](hyp:hvb) by [a nonnegative constant](hyp:hB),
[the expected boundary hinge remainder, weighted by that coefficient and the fitted band-weight-to-assignment ratio, has derivative zero at zero](goal). -/
lemma population_continuous_fitted_weight_quantile_boundary_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a : BoundaryIndex L) (g : RegularIndex L) (b : PositiveIndex L.K)
    (hi : b.val = a.val.1 + 1 ∨ (1 ≤ a.val.1 ∧ b.val = a.val.1))
    (ha : Measurable (bandBoundary M L a.val.1 a.val.2))
    (v : X → ℝ) (hv : Measurable v) (B : ℝ) (hB : 0 ≤ B)
    (hvb : ∀ᵐ x ∂xLaw M, |v x| ≤ B) :
    HasDerivAt (fun t : ℝ => ∫ x,
      ((trueNuisance M L + t • del).gamma g x /
        (trueNuisance M L + t • del).piLev b x) * v x * (∫ y,
      (bandBoundary M L a.val.1 a.val.2 x + t * del.nu a x - y) *
        indicator (y ≤ bandBoundary M L a.val.1 a.val.2 x + t * del.nu a x) -
      (bandBoundary M L a.val.1 a.val.2 x - y) *
        indicator (y ≤ bandBoundary M L a.val.1 a.val.2 x) -
      (t * del.nu a x) * indicator (y ≤ bandBoundary M L a.val.1 a.val.2 x)
      ∂treatedLaw M L b.val x) ∂xLaw M) 0 0 := by
  have hcpi : 0 < cpi := hov.1
  obtain ⟨r, C, hr, hden⟩ := h
  obtain ⟨_, _, hdir⟩ := continuous_quantile_direction_regular M L _ del hd
  apply population_weighted_quantile_boundary_local_path_orthogonality M L b.val
    (bandBoundary M L a.val.1 a.val.2) (del.nu a) _ ha (hdir a).1
    (continuous_quantile_direction_memLp M L _ del hd a)
    ((2 / cpi) * B) (by positivity) _ r |C| hr (abs_nonneg C)
  · filter_upwards [hden a.val.1 a.property.1 a.val.2 a.property.2.1 a.property.2.2 b.val hi]
      with x hx
    intro u v hu huv hv
    exact (hx u v hu huv hv).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.mpr huv))

  · filter_upwards [continuous_regular_inverse_assignment_weight_local_regular M L cpi hov del hd g b]
      with t ht
    have hm := ht.1
    refine ⟨by fun_prop, ?_⟩
    filter_upwards [ht.2, hvb] with x hx hvx
    rw [abs_mul]
    exact mul_le_mul hx hvx (abs_nonneg _) (by positivity)

-- Population treatment and assignment probabilities form the coefficient
-- in the conditional outcome boundary calculation. Their clipping and
-- measurability follow from the admissible path at zero.
-- @node: population_continuous_product_boundary_assignment_orthogonality
/-- Assume [bounded densities near the band boundaries](hyp:h), [baseline assignment overlap](hyp:hov),
and [an admissible nuisance direction at the population nuisance collection](hyp:hd).
If [the selected treatment level is the upper adjacent level or the positive lower adjacent level of the boundary's treatment interval](hyp:hi)
and [the boundary is measurable](hyp:ha),
[the expected boundary hinge remainder, weighted by the fitted band-weight-to-assignment ratio and the product of population treatment and assignment probabilities, has derivative zero at zero](goal). -/
lemma population_continuous_product_boundary_assignment_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a : BoundaryIndex L) (g : RegularIndex L) (b : PositiveIndex L.K)
    (hi : b.val = a.val.1 + 1 ∨ (1 ≤ a.val.1 ∧ b.val = a.val.1))
    (ha : Measurable (bandBoundary M L a.val.1 a.val.2)) :
    HasDerivAt (fun t : ℝ => ∫ x,
      ((trueNuisance M L + t • del).gamma g x /
        (trueNuisance M L + t • del).piLev b x) *
      ((trueNuisance M L).pLev b x * (trueNuisance M L).piLev b x) * (∫ y,
      (bandBoundary M L a.val.1 a.val.2 x + t * del.nu a x - y) *
        indicator (y ≤ bandBoundary M L a.val.1 a.val.2 x + t * del.nu a x) -
      (bandBoundary M L a.val.1 a.val.2 x - y) *
        indicator (y ≤ bandBoundary M L a.val.1 a.val.2 x) -
      (t * del.nu a x) * indicator (y ≤ bandBoundary M L a.val.1 a.val.2 x)
      ∂treatedLaw M L b.val x) ∂xLaw M) 0 0 := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hzero := hpath 0 (by simpa using hr)
  rcases hzero with ⟨_, _, hpb, hpm, hpib, hpim, _⟩
  have hpm0 : Measurable ((trueNuisance M L).pLev b) := by
    have hm := hpm b
    change Measurable (fun x => (trueNuisance M L).pLev b x + 0 * del.pLev b x) at hm
    simpa only [zero_mul, add_zero] using hm
  have hpim0 : Measurable ((trueNuisance M L).piLev b) := by
    have hm := hpim b
    change Measurable (fun x => (trueNuisance M L).piLev b x + 0 * del.piLev b x) at hm
    simpa only [zero_mul, add_zero] using hm
  apply population_continuous_fitted_weight_quantile_boundary_orthogonality M L h
    cpi hov del hd a g b hi ha
    (fun x => (trueNuisance M L).pLev b x * (trueNuisance M L).piLev b x)
    (by fun_prop) 1 (by norm_num)
  filter_upwards [hpb b, hpib b] with x hx hy
  change (trueNuisance M L).pLev b x + 0 * del.pLev b x ∈ Icc 0 1 at hx
  change (trueNuisance M L).piLev b x + 0 * del.piLev b x ∈ Icc 0 1 at hy
  simp only [zero_mul, add_zero] at hx hy
  rw [abs_mul, abs_of_nonneg hx.1, abs_of_nonneg hy.1]
  exact (mul_le_mul hx.2 hy.2 hy.1 (by norm_num)).trans_eq (by norm_num)

end Papers.TbsPrteOptimalTransport
