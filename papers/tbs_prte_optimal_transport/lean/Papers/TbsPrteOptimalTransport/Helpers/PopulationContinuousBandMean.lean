module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullMean
/-! Weighted band and boundary residuals stay centered with fitted assignment denominators. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuous_band_indicator_integral_eq
/-- [The treated-law expectation of the outcome times a band indicator equals the
outcome integral over that band, open at its lower boundary and closed at its upper boundary](goal). -/
lemma continuous_band_indicator_integral_eq (L : LevelData Z X) (i k j : ℕ) (x : X) :
    (∫ y, y * indicator (bandBoundary M L k j x < y ∧
      y ≤ bandBoundary M L k (j + 1) x) ∂treatedLaw M L i x) =
    ∫ y in Ioc (bandBoundary M L k j x) (bandBoundary M L k (j + 1) x),
      y ∂treatedLaw M L i x := by
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Ioc (bandBoundary M L k j x) (bandBoundary M L k (j + 1) x)
  <;> simp only [mem_Ioc] at hy
  <;> simp [indicator, Set.indicator, mem_Ioc, hy]

-- @node: continuous_boundary_indicator_integral_eq
/-- [The treated-law integral of the indicator that the outcome is at most a band
boundary equals the real-valued treated-law mass at or below that boundary](goal). -/
lemma continuous_boundary_indicator_integral_eq (L : LevelData Z X) (i k j : ℕ) (x : X) :
    (∫ y, indicator (y ≤ bandBoundary M L k j x) ∂treatedLaw M L i x) =
    (treatedLaw M L i x (Iic (bandBoundary M L k j x))).toReal := by
  have heq : (fun y => indicator (y ≤ bandBoundary M L k j x)) =
      (Iic (bandBoundary M L k j x)).indicator (fun _ => (1 : ℝ)) := by
    funext y
    simp [indicator, Set.indicator]
  rw [heq]
  exact integral_indicator_one measurableSet_Iic

-- @node: population_treated_band_mean_measurable
/-- If [the lower band boundary is measurable](hyp:ha) and
[the upper band boundary is measurable](hyp:hb),
[the treated-outcome band mean is measurable on either selected side](goal). -/
@[fun_prop] lemma population_treated_band_mean_measurable (L : LevelData Z X)
    (plus : Bool) (k j : ℕ)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1))) :
    Measurable (treatedBandMean M L plus false k j) := by
  first | fun_prop | skip
  have hg : Measurable (Function.uncurry (fun x y => y *
      indicator (bandBoundary M L k j x < y ∧ y ≤ bandBoundary M L k (j + 1) x))) := by
    fun_prop
  have hi := population_treated_integral_measurable M L (if plus then k + 1 else k) _ hg
  simp_rw [continuous_band_indicator_integral_eq] at hi
  change Measurable (fun x => treatedBandMean M L plus false k j x)
  by_cases hz : (!plus && k == 0) = true
  · simp only [treatedBandMean, if_pos hz]
    fun_prop
  · simpa only [treatedBandMean, if_neg hz, Bool.false_eq_true, if_false] using hi

-- @node: population_boundary_indicator_mean_measurable
/-- If [the band boundary is measurable](hyp:ha),
[the treated-outcome probability at or below that boundary is measurable on either selected side](goal). -/
@[fun_prop] lemma population_boundary_indicator_mean_measurable (L : LevelData Z X)
    (plus : Bool) (k j : ℕ) (ha : Measurable (bandBoundary M L k j)) :
    Measurable (boundaryIndicatorMean M L plus k j) := by
  first | fun_prop | skip
  have hg : Measurable (Function.uncurry (fun x y =>
      indicator (y ≤ bandBoundary M L k j x))) := by
    fun_prop
  have hi := population_treated_integral_measurable M L (if plus then k + 1 else k) _ hg
  simp_rw [continuous_boundary_indicator_integral_eq] at hi
  change Measurable (fun x => boundaryIndicatorMean M L plus k j x)
  by_cases hz : (!plus && k == 0) = true
  · simp only [boundaryIndicatorMean, if_pos hz]
    fun_prop
  · simpa only [boundaryIndicatorMean, if_neg hz] using hi

-- A denominator perturbation changes only a covariate weight. The selected
-- mean and the boundaries stay at their population values.
-- @node: population_IFJ_fitted_denominator_weighted_zero
/-- For [measurable fitted baseline-class probability denominators](hyp:hpi),
[a nonfinal bin](hyp:hk), [a band index below its policy-level count](hyp:hj),
[measurable lower](hyp:ha) and [upper band boundaries](hyp:hb), and
[a measurable covariate weight](hyp:hw), if
[the weighted treated-band residual using these denominators is integrable](hyp:hi),
[its population expectation is zero on either selected side](goal). -/
lemma population_IFJ_fitted_denominator_weighted_zero (L : LevelData Z X)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      IFJ M L {trueNuisance M L with piLev := pi} plus k j o) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 *
      IFJ M L {trueNuisance M L with piLev := pi} plus k j o ∂observationLaw M) = 0 := by
  let g : X → ℝ → ℝ := fun x y => y *
    indicator (bandBoundary M L k j x < y ∧ y ≤ bandBoundary M L k (j + 1) x)
  have hg : Measurable (Function.uncurry g) := by
    fun_prop
  have hc i : Measurable (positiveValue pi i) := by
    first | fun_prop | skip
    unfold positiveValue
    split_ifs
    · exact hpi _
    · fun_prop
  have hmean i x := continuous_band_indicator_integral_eq M L i k j x
  have hnu b (hbl : b ≤ L.l k) x :
      nuValue M {trueNuisance M L with piLev := pi} k b x = bandBoundary M L k b x :=
    population_nuValue_eq_bandBoundary M L k b hk hbl x
  cases plus
  · by_cases hk0 : k = 0
    · subst k
      simp [IFJ]
    have hk1 : 1 ≤ k := by omega
    have heq : ∀ o : Obs X Z,
        IFJ M L {trueNuisance M L with piLev := pi} false k j o =
        indicator (o.2.1 ∈ L.S k) * o.2.2.1 / positiveValue pi k o.1 *
          (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L k o.1) := by
      intro o
      simp only [IFJ, Bool.not_false, Bool.true_and, Bool.false_eq_true,
        beq_iff_eq, hk0, if_false, hnu j hj.le o.1,
        hnu (j + 1) (by omega) o.1]
      simp [g, hmean, minusMeanValue, hk1, hk, hj.le, trueNuisance,
        treatedBandMean, hk0]
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L k g hg _ w (hc k) hw hi
  · have heq : ∀ o : Obs X Z,
        IFJ M L {trueNuisance M L with piLev := pi} true k j o =
        indicator (o.2.1 ∈ L.S (k + 1)) * o.2.2.1 / positiveValue pi (k + 1) o.1 *
          (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L (k + 1) o.1) := by
      intro o
      simp only [IFJ, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false,
        if_true, hnu j hj.le o.1, hnu (j + 1) (by omega) o.1]
      simp [g, hmean, meanValue, hk, hj.le, trueNuisance, treatedBandMean]
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L (k + 1) g hg _ w
      (hc (k + 1)) hw hi

-- This includes the fixed boundary j = 0 and omits the structural-zero
-- minus residual. Terminal CDF values fixed at one have no regression direction.
-- @node: population_IFM_fitted_denominator_weighted_zero
/-- For [measurable fitted baseline-class probability denominators](hyp:hpi),
[a nonfinal bin](hyp:hk), [a boundary index no larger than its policy-level count](hyp:hj),
[a measurable boundary](hyp:ha), and [a measurable covariate weight](hyp:hw), if
[the weighted boundary-indicator residual using these denominators is integrable](hyp:hi),
[its population expectation is zero on either selected side](goal). -/
lemma population_IFM_fitted_denominator_weighted_zero (L : LevelData Z X)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      IFM M L {trueNuisance M L with piLev := pi} plus k j o) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 *
      IFM M L {trueNuisance M L with piLev := pi} plus k j o ∂observationLaw M) = 0 := by
  let g : X → ℝ → ℝ := fun x y => indicator (y ≤ bandBoundary M L k j x)
  have hg : Measurable (Function.uncurry g) := by
    fun_prop
  have hc i : Measurable (positiveValue pi i) := by
    first | fun_prop | skip
    unfold positiveValue
    split_ifs
    · exact hpi _
    · fun_prop
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
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L k g hg _ w (hc k) hw hi
  · have heq : ∀ o : Obs X Z,
        IFM M L {trueNuisance M L with piLev := pi} true k j o =
        indicator (o.2.1 ∈ L.S (k + 1)) * o.2.2.1 / positiveValue pi (k + 1) o.1 *
          (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L (k + 1) o.1) := by
      intro o
      simp only [IFM, Bool.not_true, Bool.false_eq_true, false_and, if_false,
        if_true, hnu o.1]
      simp [g, hmean, boundaryValue, hk, hj, trueNuisance, boundaryIndicatorMean]
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L (k + 1) g hg _ w
      (hc (k + 1)) hw hi

-- The whole expectation is zero along a measurable denominator path; this
-- avoids exchanging differentiation and integration or bounding inverse errors.
-- @node: population_IFJ_denominator_path_orthogonality
/-- Along [a path of measurable baseline-class probability denominators](hyp:hpi),
for [a nonfinal bin](hyp:hk), [a band index below its policy-level count](hyp:hj),
[measurable lower](hyp:ha) and [upper band boundaries](hyp:hb), and
[a measurable covariate weight](hyp:hw), if [the weighted treated-band residual is
integrable at every path value](hyp:hi), [its population expectation has derivative
zero at path value zero on either selected side](goal). -/
lemma population_IFJ_denominator_path_orthogonality (L : LevelData Z X)
    (pi : ℝ → PositiveIndex L.K → X → ℝ)
    (hpi : ∀ t a, Measurable (pi t a))
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (w : X → ℝ) (hw : Measurable w)
    (hi : ∀ t, Integrable (fun o : Obs X Z => w o.1 *
      IFJ M L {trueNuisance M L with piLev := pi t} plus k j o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w o.1 *
      IFJ M L {trueNuisance M L with piLev := pi t} plus k j o ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o : Obs X Z, w o.1 *
      IFJ M L {trueNuisance M L with piLev := pi t} plus k j o ∂observationLaw M) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact population_IFJ_fitted_denominator_weighted_zero M L (pi t) (hpi t)
      plus k j hk hj ha hb w hw (hi t)
  rw [heq]
  exact hasDerivAt_const 0 0

-- @node: population_IFM_denominator_path_orthogonality
/-- Along [a path of measurable baseline-class probability denominators](hyp:hpi),
for [a nonfinal bin](hyp:hk), [a boundary index no larger than its policy-level count](hyp:hj),
[a measurable boundary](hyp:ha), and [a measurable covariate weight](hyp:hw), if
[the weighted boundary-indicator residual is integrable at every path value](hyp:hi),
[its population expectation has derivative zero at path value zero on either selected side](goal). -/
lemma population_IFM_denominator_path_orthogonality (L : LevelData Z X)
    (pi : ℝ → PositiveIndex L.K → X → ℝ)
    (hpi : ∀ t a, Measurable (pi t a))
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (w : X → ℝ) (hw : Measurable w)
    (hi : ∀ t, Integrable (fun o : Obs X Z => w o.1 *
      IFM M L {trueNuisance M L with piLev := pi t} plus k j o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w o.1 *
      IFM M L {trueNuisance M L with piLev := pi t} plus k j o ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o : Obs X Z, w o.1 *
      IFM M L {trueNuisance M L with piLev := pi t} plus k j o ∂observationLaw M) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact population_IFM_fitted_denominator_weighted_zero M L (pi t) (hpi t)
      plus k j hk hj ha w hw (hi t)
  rw [heq]
  exact hasDerivAt_const 0 0

end Papers.TbsPrteOptimalTransport
