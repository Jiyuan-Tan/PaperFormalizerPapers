module
public import Papers.TbsNeuralCausalPi.Helpers.DescendantDoseResponseAssembly
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseAveraging
public import Papers.TbsNeuralCausalPi.Helpers.DescendantRegressionVersion
public import Papers.TbsNeuralCausalPi.Helpers.DescendantAdjustment
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseMarginals
public import Papers.TbsNeuralCausalPi.Helpers.EvaluationNoise
public import Papers.TbsNeuralCausalPi.Helpers.TreatmentOverlapTransfer
/-! # Quantitative dose-response comparison -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

-- @node: prop:lip-ate
/-- For [reference and comparison canonical models](hyp:M,Mhat), with [a common
nonnegative Lipschitz bound](hyp:L), [a magnitude bound](hyp:K), [treatment and
outcome nodes](hyp:T,Y), and [a scalar outcome](hyp:hY), suppose [the reference
model has independent latent blocks](hyp:hind) and [the comparison model also
has independent latent blocks](hyp:hindhat),
[both models' continuous mechanisms obey that Lipschitz bound](hyp:hcont,hconthat),
[both models' categorical propensities obey that Lipschitz bound](hyp:hprop,hprophat), [their variables
are bounded by the common bound](hyp:hbound,hboundhat), and [both models
satisfy that observational and non-Gumbel latent coordinate bound](hyp:hboth).
Assume [no hidden confounding](hyp:hnoconf), [a scalar treatment node](hyp:hT),
[a treatment function](hyp:treatment) [equal to that node's scalar value](hyp:htreatment),
[a reference dose distribution](hyp:P), [a conditional density](hyp:p),
[an overlap bound](hyp:delta), [dose interval endpoints](hyp:t1,t2),
[a conditional treatment density relative to the reference dose
distribution](hyp:hdensity), [a positive overlap lower bound](hyp:hdelta), and
[that density at least the overlap bound throughout the dose interval for
almost every parent configuration](hyp:hoverlap). Then [the squared difference
of the two mean dose-response curves, integrated over that interval against
the reference dose distribution, is at most twice the dose comparison constant
divided by the overlap bound times observational Wasserstein distance, plus
twice the squared dose Lipschitz constant times squared observational
Wasserstein distance times the reference probability of the interval](goal). -/
theorem lipschitz_dose_response_gap (M Mhat : CanonicalSCM kind dims dag G C)
    (L : ℝ≥0) (K : ℝ) (T Y : Fin n) (hY : valueDim (kind Y) = 1)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hindhat : LatentBlocksIndependent Mhat.toEuclideanSCM)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hconthat : ContinuousMechanismsLipschitz Mhat.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hprophat : CategoricalPropensityLipschitz Mhat.toEuclideanSCM Mhat.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hboundhat : VariablesBoundedAt Mhat.toEuclideanSCM K)
    (hboth : AllVariablesNormBounded M.toEuclideanSCM Mhat.toEuclideanSCM K)
    (hnoconf : NoHiddenConfounding G) (P : ProbabilityMeasure ℝ)
    (treatment : Joint kind → ℝ)
    (hT : valueDim (kind T) = 1)
    (htreatment : treatment = scalarOutcome T hT)
    (p : ParentSpace M.toEuclideanSCM T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M.toEuclideanSCM T treatment P p)
    (hdelta : 0 < delta)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M.toEuclideanSCM).map
      (parentValues M.toEuclideanSCM T)), ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t)) :
    (∫ t in Set.Icc t1 t2,
      (meanOutcome M.toEuclideanSCM T Y hY t - meanOutcome Mhat.toEuclideanSCM T Y hY t)^2
        ∂(P : Measure ℝ)) ≤
      2*doseCW kind L ⟨K, le_of_lt hbound.1⟩/delta *
        (wasserstein1 (observationalLaw Mhat.toEuclideanSCM) (observationalLaw M.toEuclideanSCM)).toReal +
      2*(doseLip kind L)^2 *
        (wasserstein1 (observationalLaw Mhat.toEuclideanSCM) (observationalLaw M.toEuclideanSCM)).toReal^2 *
        ((P : Measure ℝ) (Set.Icc t1 t2)).toReal := by
  have hLy := one_le_doseLip (kind := kind) L
  have hCW := doseCW_nonneg (kind := kind) L ⟨K, le_of_lt hbound.1⟩
  have hfirst : 0 ≤ 2*doseCW kind L ⟨K, le_of_lt hbound.1⟩/delta *
      (wasserstein1 (observationalLaw Mhat.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM)).toReal := by positivity
  by_cases hsame : Y = T
  · subst Y
    simp_rw [meanOutcome_self_intervention]
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero]
    exact add_nonneg hfirst (by positivity)
  by_cases hpath : dag.isAncestor T Y
  · apply descendant_dose_response_bound_of_covariate_overlap M Mhat T Y hT hY hsame hpath
      K L hind hindhat hnoconf hcont hconthat hprop hprophat hbound hboundhat
      P delta t1 t2 hdelta
      (treatment_intervention_ae_admissible M.toEuclideanSCM T hT P treatment htreatment
        p delta t1 t2 hdensity hdelta hoverlap)
    exact treatment_reference_nonDescendant_product_le M T hT hind hnoconf
      P p delta t1 t2 (by simpa only [htreatment] using hdensity) hoverlap
  · have hgap := nonDescendant_dose_response_gap_le M Mhat K T Y hY
      hsame hpath hbound hboundhat P t1 t2
    refine hgap.trans ?_
    have hfactor : 1 ≤ 2*(doseLip kind L)^2 := by nlinarith [sq_nonneg (doseLip kind L - 1)]
    have hmass : 0 ≤ (wasserstein1 (observationalLaw Mhat.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM)).toReal^2 *
        ((P : Measure ℝ) (Set.Icc t1 t2)).toReal := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hmass]

end
end Papers.TbsNeuralCausalPi
