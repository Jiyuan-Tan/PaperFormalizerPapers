module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullRanges
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandRegressionBounds
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBoundaries
/-! Ranges, measurability and moments of the true continuous boundary nuisances.
The boundary support theorem supplies the known clipping interval. Selected
indicator and truncated outcome averages supply the remaining moment bounds. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_boundary_nuisance_range
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[covariate-invariant baseline and policy level ordering](hyp:hL),
[every indexed population boundary nuisance lies between the outcome endpoints for almost every covariate](goal). -/
lemma population_continuous_boundary_nuisance_range
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (a : BoundaryIndex L) :
    ∀ᵐ x ∂xLaw M, (trueNuisance M L).nu a x ∈ Icc M.yMin M.yMax := by
  filter_upwards [population_bandBoundary_supported M h he q L hL] with x hx
  have hy := hx a.val.1 a.property.1 a.val.2 a.property.2.2
  exact ⟨he.1.2 hy, he.2.2 hy⟩

-- @node: population_continuous_boundary_nuisance_measurable
/-- If [policy propensities are jointly measurable](hyp:hq),
[baseline and policy levels have covariate-invariant ordering](hyp:hL), and
[baseline levels are measurable](hyp:hlev), [each indexed population boundary nuisance is measurable](goal). -/
@[fun_prop] lemma population_continuous_boundary_nuisance_measurable
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (a : BoundaryIndex L) :
    Measurable ((trueNuisance M L).nu a) := by
  first | fun_prop | skip
  exact population_bandBoundary_measurable M q hq L hL hlev
    a.val.1 a.val.2 a.property.1 a.property.2.2

-- @node: population_continuous_boundary_nuisance_memLp
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[jointly measurable policy propensities](hyp:hq), [covariate-invariant level ordering](hyp:hL),
and [measurable baseline levels](hyp:hlev),
[each population boundary nuisance is measurable and square-integrable under the covariate law](goal). -/
lemma population_continuous_boundary_nuisance_memLp
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (a : BoundaryIndex L) :
    MemLp ((trueNuisance M L).nu a) 2 (xLaw M) := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hm : Measurable ((trueNuisance M L).nu a) := by
    first | fun_prop | exact population_continuous_boundary_nuisance_measurable M q hq L hL hlev a
  exact memLp_of_bounded
    (population_continuous_boundary_nuisance_range M h he q L hL a)
    hm.aestronglyMeasurable 2

-- @node: population_continuous_indicator_nuisance_memLp
/-- If [policy propensities are jointly measurable](hyp:hq),
[level ordering is invariant across covariates](hyp:hL), and [baseline levels are measurable](hyp:hlev),
[all plus-side and minus-side population boundary indicator means are measurable and square-integrable under the covariate law](goal). -/
lemma population_continuous_indicator_nuisance_memLp
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) :
    (∀ a, MemLp ((trueNuisance M L).Mplus a) 2 (xLaw M)) ∧
    (∀ a, MemLp ((trueNuisance M L).Mminus a) 2 (xLaw M)) := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  constructor
  · intro a
    have hb := population_bandBoundary_measurable M q hq L hL hlev
      a.val.1 a.val.2 a.property.1 a.property.2
    have hm : Measurable ((trueNuisance M L).Mplus a) := by
      first | fun_prop | exact population_boundary_indicator_mean_measurable M L true _ _ hb
    exact memLp_of_bounded
      (Eventually.of_forall (population_boundary_indicator_mean_range M L true _ _))
      hm.aestronglyMeasurable 2
  · intro a
    have hb := population_bandBoundary_measurable M q hq L hL hlev
      a.val.1 a.val.2 a.property.2.1 a.property.2.2
    have hm : Measurable ((trueNuisance M L).Mminus a) := by
      first | fun_prop | exact population_boundary_indicator_mean_measurable M L false _ _ hb
    exact memLp_of_bounded
      (Eventually.of_forall (population_boundary_indicator_mean_range M L false _ _))
      hm.aestronglyMeasurable 2

-- @node: population_treated_interior_band_mean_memLp
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[jointly measurable policy propensities](hyp:hq), [covariate-invariant level ordering](hyp:hL),
and [measurable baseline levels](hyp:hlev), for [a nonfinal bin](hyp:hk) and
[a band index strictly below its policy-level count](hyp:hj),
[the treated-outcome band mean on either selected side is measurable and square-integrable under the covariate law](goal). -/
lemma population_treated_interior_band_mean_memLp
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    MemLp (treatedBandMean M L plus false k j) 2 (xLaw M) := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have ha := population_bandBoundary_measurable M q hq L hL hlev k j hk hj.le
  have hb := population_bandBoundary_measurable M q hq L hL hlev k (j+1) hk (by omega)
  have hm : Measurable (treatedBandMean M L plus false k j) := by
    first | fun_prop | exact population_treated_band_mean_measurable M L plus k j ha hb
  exact memLp_of_bounded (population_treated_band_mean_range M h he L plus k j)
    hm.aestronglyMeasurable 2

end Papers.TbsPrteOptimalTransport
