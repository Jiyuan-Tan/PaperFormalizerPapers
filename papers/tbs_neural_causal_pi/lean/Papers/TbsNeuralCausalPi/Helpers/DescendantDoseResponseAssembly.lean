module
public import Papers.TbsNeuralCausalPi.Helpers.DescendantRegressionBounds
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseOverlap
/-! # Final integration of the descendant dose-response comparison

The analytic assembly uses domination of the actual non-descendant/treatment
law. Establishing this domination from parent overlap remains a separate
structural obligation at the caller.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
set_option linter.style.longLine false
set_option linter.unusedVariables false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [a scalar treatment](hyp:hT), [a scalar outcome](hyp:hY), and
[a common nonnegative regularity constant](hyp:L), assume [jointly independent
named latent inputs in the first model](hyp:hind) and [in the second](hyp:hindhat),
[no hidden confounding in their common graph](hyp:hnoconf), [continuous
mechanisms Lipschitz with that constant in the first model](hyp:hcont) and
[in the second](hyp:hconthat), [categorical propensities Lipschitz with that
constant in the first model](hyp:hprop) and [in the second](hyp:hprophat), and
[the given uniform bound on variables in the first model](hyp:hbound) and
[in the second](hyp:hboundhat). Then [the squared difference between the two
descendant means, evaluated at the observed joint vector and treatment,
is integrable under the first model's observational law](goal). -/
-- @node: descendant_regression_square_integrable
lemma descendant_regression_square_integrable
    (M Mhat : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hindhat : LatentBlocksIndependent Mhat.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hconthat : ContinuousMechanismsLipschitz Mhat.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hprophat : CategoricalPropensityLipschitz Mhat.toEuclideanSCM Mhat.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hboundhat : VariablesBoundedAt Mhat.toEuclideanSCM K) :
    Integrable (fun v => (descendantMean M T Y hY v (scalarOutcome T hT v) -
      descendantMean Mhat T Y hY v (scalarOutcome T hT v))^2)
      (observationalLaw M.toEuclideanSCM) := by
  letI := M.toEuclideanSCM.probability
  haveI : IsProbabilityMeasure (observationalLaw M.toEuclideanSCM) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M.toEuclideanSCM _ _).aemeasurable
  let B := K * (1 + 2 * (∑ i, valueDim (kind i)) * doseLip kind L)
  have hcarry : ∀ᵐ v ∂observationalLaw M.toEuclideanSCM,
      (∀ j, |v.ofLp j| ≤ K) ∧ admissibleJoint v :=
    (ae_mem_iff_measure_eq (admissibleJoint_box_isCompact (kind := kind) K).measurableSet.nullMeasurableSet).2
      (by simpa using observationalLaw_admissibleJoint_box M.toEuclideanSCM K hbound)
  apply Integrable.of_bound (by fun_prop [scalarOutcome]) ((2 * B)^2)
  filter_upwards [hcarry] with v hv
  have hm := descendant_regression_abs_le M T Y hT hY K L hind hnoconf hcont hprop hbound v hv.1 hv.2
  have hh := descendant_regression_abs_le Mhat T Y hT hY K L hindhat hnoconf hconthat hprophat hboundhat v hv.1 hv.2
  have hd : |descendantMean M T Y hY v (scalarOutcome T hT v) -
      descendantMean Mhat T Y hY v (scalarOutcome T hT v)| ≤ 2 * B :=
    (abs_sub _ _).trans (by dsimp [B]; linarith)
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
    pow_le_pow_left₀ (abs_nonneg _) hd 2

/-- For [a scalar treatment](hyp:hT) and [a scalar outcome](hyp:hY) that
[differs from the treatment](hyp:hne) and [is its descendant](hyp:hpath), assume
[a common nonnegative regularity constant](hyp:L), [independent named latent
inputs in the first model](hyp:hind) and [in the second](hyp:hindhat), [no hidden
confounding](hyp:hnoconf), [continuous mechanisms Lipschitz with that constant
in the first model](hyp:hcont) and [in the second](hyp:hconthat), [categorical
propensities Lipschitz with that constant in the first model](hyp:hprop) and
[in the second](hyp:hprophat), and [the given bound on variables in the first
model](hyp:hbound) and [in the second](hyp:hboundhat). If [the overlap constant
is positive](hyp:hdelta), [almost every dose in the chosen interval under the
given dose distribution is admissible](hyp:hadm), and [the first model's joint
observational treatment and non-descendant law dominates the overlap constant
times the product of the interval-restricted dose distribution and its
non-descendant law](hyp:hdom), then [the integrated squared difference of
interventional means on that interval is bounded by twice the dose contrast
constant divided by the overlap constant times the observational Wasserstein
distance, plus twice the squared dose Lipschitz constant times the squared
Wasserstein distance times the dose probability of the interval](goal). -/
-- @node: descendant_dose_response_bound_of_covariate_overlap
lemma descendant_dose_response_bound_of_covariate_overlap
    (M Mhat : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hT : valueDim (kind T) = 1) (hY : valueDim (kind Y) = 1)
    (hne : Y ≠ T) (hpath : dag.isAncestor T Y)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hindhat : LatentBlocksIndependent Mhat.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hconthat : ContinuousMechanismsLipschitz Mhat.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hprophat : CategoricalPropensityLipschitz Mhat.toEuclideanSCM Mhat.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hboundhat : VariablesBoundedAt Mhat.toEuclideanSCM K)
    (P : ProbabilityMeasure ℝ) (delta t1 t2 : ℝ) (hdelta : 0 < delta)
    (hadm : ∀ᵐ t ∂((P : Measure ℝ).restrict (Set.Icc t1 t2)),
      AdmissibleIntervention kind (singleIntervention T t))
    (hdom : ENNReal.ofReal delta •
        (((P : Measure ℝ).restrict (Set.Icc t1 t2)).prod
          ((observationalLaw M.toEuclideanSCM).map (nonDescendantProjection (dag := dag) T))) ≤
      (observationalLaw M.toEuclideanSCM).map (fun v =>
        (scalarOutcome T hT v, nonDescendantProjection (dag := dag) T v))) :
    (∫ t in Set.Icc t1 t2,
      (meanOutcome M.toEuclideanSCM T Y hY t - meanOutcome Mhat.toEuclideanSCM T Y hY t)^2
        ∂(P : Measure ℝ)) ≤
      2*doseCW kind L ⟨K, hbound.1.le⟩/delta *
        (wasserstein1 (observationalLaw Mhat.toEuclideanSCM) (observationalLaw M.toEuclideanSCM)).toReal +
      2*(doseLip kind L)^2 *
        (wasserstein1 (observationalLaw Mhat.toEuclideanSCM) (observationalLaw M.toEuclideanSCM)).toReal^2 *
        ((P : Measure ℝ) (Set.Icc t1 t2)).toReal := by
  letI := M.toEuclideanSCM.probability
  haveI : IsProbabilityMeasure (observationalLaw M.toEuclideanSCM) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M.toEuclideanSCM _ _).aemeasurable
  let nuA := (observationalLaw M.toEuclideanSCM).map (nonDescendantProjection (dag := dag) T)
  haveI : IsProbabilityMeasure nuA :=
    Measure.isProbabilityMeasure_map (nonDescendantProjection_measurable T).aemeasurable
  let rho := (P : Measure ℝ).restrict (Set.Icc t1 t2)
  let s := fun v : Joint kind => (scalarOutcome T hT v, nonDescendantProjection (dag := dag) T v)
  let eta := (observationalLaw M.toEuclideanSCM).map s
  let d := fun z : ℝ × Joint kind =>
    descendantMean M T Y hY z.2 z.1 - descendantMean Mhat T Y hY z.2 z.1
  let gap := fun t => meanOutcome M.toEuclideanSCM T Y hY t - meanOutcome Mhat.toEuclideanSCM T Y hY t
  let muA := (observationalLaw Mhat.toEuclideanSCM).map (nonDescendantProjection (dag := dag) T)
  let c := fun t => (∫ a, descendantMean Mhat T Y hY a t ∂nuA) -
    ∫ a, descendantMean Mhat T Y hY a t ∂muA
  have hs : Measurable s := by dsimp [s]; fun_prop [scalarOutcome]
  have hd : Measurable d := by dsimp [d]; fun_prop
  have heta : Integrable (fun z => (d z)^2) eta := by
    apply (integrable_map_measure (hd.pow_const 2).aestronglyMeasurable hs.aemeasurable).2
    simpa only [d, s, descendantMean_projection_eq, Function.comp_def] using
      descendant_regression_square_integrable M Mhat T Y hT hY K L hind hindhat hnoconf
        hcont hconthat hprop hprophat hbound hboundhat
  have heq : (∫ z, (d z)^2 ∂eta) =
      ∫ v, (descendantMean M T Y hY v (scalarOutcome T hT v) -
        descendantMean Mhat T Y hY v (scalarOutcome T hT v))^2
          ∂observationalLaw M.toEuclideanSCM := by
    rw [show eta = (observationalLaw M.toEuclideanSCM).map s from rfl,
      integral_map hs.aemeasurable (hd.pow_const 2).aestronglyMeasurable]
    simp only [d, s, descendantMean_projection_eq]
  have hreg := descendant_regression_gap_le_wasserstein M Mhat T Y hT hY hne hpath K L
    hind hindhat hnoconf hcont hconthat hprop hprophat hbound hboundhat
  rw [← heq] at hreg
  have hmean := overlap_regression_mean_square_le_of_integrable nuA rho eta d hd delta hdelta hdom heta
  have hdecomp : ∀ᵐ t ∂rho, gap t = (∫ a, d (t, a) ∂nuA) + c t := by
    filter_upwards [hadm] with t ht
    exact (descendant_dose_response_marginal_decomposition M Mhat T Y hY K L
      hind hindhat hnoconf hcont hconthat hprop hprophat hbound hboundhat t ht _
      (descendantMean_section_lipschitzOn Mhat T Y hT hY K L hindhat hnoconf
        hconthat hprophat hboundhat t ht)).2.1
  have hc : ∀ᵐ t ∂rho, |c t| ≤ doseLip kind L *
      (wasserstein1 (observationalLaw Mhat.toEuclideanSCM) (observationalLaw M.toEuclideanSCM)).toReal := by
    filter_upwards [hadm] with t ht
    exact (descendant_dose_response_marginal_decomposition M Mhat T Y hY K L
      hind hindhat hnoconf hcont hconthat hprop hprophat hbound hboundhat t ht _
      (descendantMean_section_lipschitzOn Mhat T Y hT hY K L hindhat hnoconf
        hconthat hprophat hboundhat t ht)).2.2
  have h := dose_response_integrated_decomposition_le rho gap
    (fun t => ∫ a, d (t, a) ∂nuA) c (by dsimp [gap]; fun_prop) hmean.1
    (doseLip kind L) _ (doseCW kind L ⟨K, hbound.1.le⟩) delta hdelta hdecomp hc
    (hmean.2.trans hreg)
  simpa only [rho, gap, Measure.restrict_apply_univ] using h

end
end Papers.TbsNeuralCausalPi
