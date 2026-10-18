module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBounds
/-! Integrability and centering of boundary-CDF residuals with clipped denominators. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Selected averages are bounded even when the selected cell has mass zero.
-- @node: population_selected_integral_norm_le_of_global_bound
/-- If [the outcome function is measurable for each covariate value](hyp:hg) and
[every absolute function value is at most the bound](hyp:hb), where [the bound is nonnegative](hyp:hC),
[the absolute selected treated mean is at most that bound, even for a cell of zero mass](goal). -/
lemma population_selected_integral_norm_le_of_global_bound
    (L : LevelData Z X) (i : ℕ) (g : X → ℝ → ℝ)
    (hg : ∀ x, Measurable (g x)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x y, ‖g x y‖ ≤ C) (x : X) :
    ‖∫ y, g x y ∂treatedLaw M L i x‖ ≤ C := by
  unfold treatedLaw
  rw [normalized_selected_mean_eq_average _ _ _ (hg x)]
  exact selected_average_norm_le_of_bound _ _ C hC
    (Eventually.of_forall (fun a => hb x a.1))

-- An L1 covariate weight suffices; no assumption on the selected-cell mass
-- or on the outcome density is needed for this envelope.
-- @node: population_bounded_selected_residual_integrable
/-- Suppose [the outcome function is jointly measurable](hyp:hg) and
[uniformly bounded in absolute value](hyp:hb) by [a nonnegative constant](hyp:hC).
If [the denominator is measurable](hyp:hc) and [almost surely bounded below by the clipping constant](hyp:hcl),
which [is positive](hyp:hc0), and the covariate weight is [measurable](hyp:hw) and
[integrable](hyp:hwi), [the weighted selected treated residual, centered by its selected treated mean and divided by the denominator, is integrable under the observation distribution](goal). -/
lemma population_bounded_selected_residual_integrable
    (L : LevelData Z X) (i : ℕ) (g : X → ℝ → ℝ)
    (hg : Measurable (Function.uncurry g)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x y, ‖g x y‖ ≤ C)
    (c : X → ℝ) (hc : Measurable c) (c0 : ℝ) (hc0 : 0 < c0)
    (hcl : ∀ᵐ x ∂xLaw M, c0 ≤ c x)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 *
        (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L i o.1))) (observationLaw M) := by
  let r : Obs X Z → ℝ := fun o => indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 *
    (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L i o.1)
  have hm : Measurable r := by
    dsimp only [r]
    have hmean := population_treated_integral_measurable M L i g hg
    have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S i)) := by
      unfold indicator
      exact Measurable.ite ((L.S i).finite_toSet.measurableSet.preimage measurable_snd.fst)
        measurable_const measurable_const
    exact ((hi.mul measurable_snd.snd.fst).div (hc.comp measurable_fst)).mul
      ((hg.comp (measurable_fst.prodMk measurable_snd.snd.snd)).sub
        (hmean.comp measurable_fst))
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using Measure.map_map measurable_fst hobs
  have hwi' : Integrable (fun o : Obs X Z => w o.1) (observationLaw M) := by
    apply (integrable_map_measure hw.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [hmap]
  have ht : ∀ᵐ o : Obs X Z ∂observationLaw M, ‖o.2.2.1‖ ≤ 1 := by
    apply (ae_map_iff hobs.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall (fun s => by rcases M.rangeW s with hs | hs <;> simp [hs])
  have hr : ∀ᵐ o : Obs X Z ∂observationLaw M, ‖r o‖ ≤ (2 * C) / c0 := by
    filter_upwards [ht, observationLaw_covariate_ae M _ hcl] with o hto hco
    have hi : ‖indicator (o.2.1 ∈ L.S i)‖ ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    have hcpos : 0 < c o.1 := hc0.trans_le hco
    have hn : ‖g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L i o.1‖ ≤ 2 * C := by
      exact (norm_sub_le _ _).trans (by
        linarith [hb o.1 o.2.2.2,
          population_selected_integral_norm_le_of_global_bound M L i g
            (fun _ => hg.of_uncurry_left) C hC hb o.1])
    calc
      ‖r o‖ = (‖indicator (o.2.1 ∈ L.S i)‖ * ‖o.2.2.1‖) / c o.1 *
        ‖g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L i o.1‖ := by
          simp only [r, norm_mul, norm_div, Real.norm_eq_abs, abs_of_pos hcpos]
      _ ≤ (1 * 1) / c0 * (2 * C) := by gcongr
      _ = (2 * C) / c0 := by ring
  simpa only [r, mul_comm] using hwi'.bdd_mul hm.aestronglyMeasurable hr

-- @node: population_IFM_fitted_denominator_integrable
/-- Suppose [all fitted assignment denominators are measurable](hyp:hpi) and
[almost surely bounded below by a common clipping constant](hyp:hcl), which [is positive](hyp:hc0).
For [a valid treatment interval](hyp:hk) and [a boundary index no greater than its band count](hyp:hj),
if [the boundary is measurable](hyp:ha) and the covariate weight is [measurable](hyp:hw) and
[integrable](hyp:hwi), [the weighted boundary distribution residual with fitted assignment denominators is integrable, on either selected side](goal). -/
lemma population_IFM_fitted_denominator_integrable
    (L : LevelData Z X)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c0 : ℝ) (hc0 : 0 < c0) (hcl : ∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi a x)
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      IFM M L {trueNuisance M L with piLev := pi} plus k j o) (observationLaw M) := by
  let g : X → ℝ → ℝ := fun x y => indicator (y ≤ bandBoundary M L k j x)
  have hg : Measurable (Function.uncurry g) := by fun_prop
  have hgb x y : ‖g x y‖ ≤ 1 := by
    dsimp only [g, indicator]
    split_ifs <;> norm_num
  have hc i : Measurable (positiveValue pi i) := by
    unfold positiveValue
    split_ifs
    · exact hpi _
    · fun_prop
  have hcb i (hi : 1 ≤ i ∧ i ≤ L.K) :
      ∀ᵐ x ∂xLaw M, c0 ≤ positiveValue pi i x := by
    simpa only [positiveValue, dif_pos hi] using hcl ⟨i, hi⟩
  have hmean i x := continuous_boundary_indicator_integral_eq M L i k j x
  have hnu x : nuValue M {trueNuisance M L with piLev := pi} k j x =
      bandBoundary M L k j x := population_nuValue_eq_bandBoundary M L k j hk hj x
  cases plus
  · by_cases hk0 : k = 0
    · subst k
      simp [IFM]
    have hk1 : 1 ≤ k := by omega
    have heq : ∀ o : Obs X Z,
        IFM M L {trueNuisance M L with piLev := pi} false k j o =
        indicator (o.2.1 ∈ L.S k) * o.2.2.1 / positiveValue pi k o.1 *
          (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L k o.1) := by
      intro o
      simp only [IFM, Bool.not_false, true_and, hk0, if_false,
        Bool.false_eq_true, hnu o.1]
      simp [g, hmean, minusBoundaryValue, hk1, hk, hj, trueNuisance,
        boundaryIndicatorMean, hk0]
    simp_rw [heq]
    exact population_bounded_selected_residual_integrable M L k g hg 1 zero_le_one
      hgb _ (hc k) c0 hc0 (hcb k ⟨hk1, hk.le⟩) w hw hwi
  · have heq : ∀ o : Obs X Z,
        IFM M L {trueNuisance M L with piLev := pi} true k j o =
        indicator (o.2.1 ∈ L.S (k + 1)) * o.2.2.1 / positiveValue pi (k + 1) o.1 *
          (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L (k + 1) o.1) := by
      intro o
      simp only [IFM, Bool.not_true, Bool.false_eq_true, false_and, if_false,
        if_true, hnu o.1]
      simp [g, hmean, boundaryValue, hk, hj, trueNuisance, boundaryIndicatorMean]
    simp_rw [heq]
    exact population_bounded_selected_residual_integrable M L (k + 1) g hg 1 zero_le_one
      hgb _ (hc (k + 1)) c0 hc0 (hcb (k + 1) ⟨by omega, by omega⟩) w hw hwi

-- @node: population_IFM_weighted_centering_of_clipped_denominator
/-- If [the fitted assignment denominators are measurable](hyp:hpi) and
[almost surely bounded below by the clipping constant](hyp:hcl), which [is positive](hyp:hc0),
then for [a valid treatment interval](hyp:hk) and [a boundary index at most its band count](hyp:hj)
with [a measurable boundary](hyp:ha) and a [measurable](hyp:hw), [integrable covariate weight](hyp:hwi),
[the expected weighted boundary distribution residual with fitted denominators is zero on either selected side](goal). -/
lemma population_IFM_weighted_centering_of_clipped_denominator
    (L : LevelData Z X)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c0 : ℝ) (hc0 : 0 < c0) (hcl : ∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi a x)
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    (∫ o : Obs X Z, w o.1 * IFM M L {trueNuisance M L with piLev := pi}
      plus k j o ∂observationLaw M) = 0 := by
  exact population_IFM_fitted_denominator_weighted_zero M L pi hpi plus k j hk hj ha w hw
    (population_IFM_fitted_denominator_integrable M L pi hpi c0 hc0 hcl
      plus k j hk hj ha w hw hwi)

-- Only a neighborhood of zero is needed for admissible nuisance paths.
-- Coefficient changes also vanish because the selected residual is centered.
-- @node: population_IFM_clipped_local_path_orthogonality
/-- Let the clipping constant [be positive](hyp:hc0), and suppose
[near zero the assignment denominators are measurable and almost surely bounded below by that constant, while the covariate weights are measurable and integrable](hyp:hp).
For [a valid treatment interval](hyp:hk) and [a boundary index no greater than its band count](hyp:hj)
with [a measurable boundary](hyp:ha), [the expected weighted boundary distribution residual has derivative zero at zero along the joint denominator and weight path, on either selected side](goal). -/
lemma population_IFM_clipped_local_path_orthogonality
    (L : LevelData Z X) (pi : ℝ → PositiveIndex L.K → X → ℝ)
    (w : ℝ → X → ℝ) (c0 : ℝ) (hc0 : 0 < c0)
    (hp : ∀ᶠ t in 𝓝 (0 : ℝ), (∀ a, Measurable (pi t a)) ∧
      (∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi t a x) ∧
      Measurable (w t) ∧ Integrable (w t) (xLaw M))
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k j)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      IFM M L {trueNuisance M L with piLev := pi t} plus k j o
      ∂observationLaw M) 0 0 := by
  apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [hp] with t ht
  exact population_IFM_weighted_centering_of_clipped_denominator M L (pi t)
    ht.1 c0 hc0 ht.2.1 plus k j hk hj ha (w t) ht.2.2.1 ht.2.2.2

end Papers.TbsPrteOptimalTransport
