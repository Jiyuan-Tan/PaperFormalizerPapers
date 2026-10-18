module
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedBoundary
public import Papers.TbsPrteOptimalTransport.Helpers.FeasibleDisintegration
/-! TContinuousReduction statements. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
variable (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
-- @node: prop:continuous-reduction
/-- Assume [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), [common instrument support](hyp:hSupport),
[finitely many instrument components](hyp:hComponents), and [continuous propensity on each component](hyp:hContinuous).
For [an admissible policy](hyp:hPolicy), if [the instrument domain is connected](hyp:hConnected)
and [both observable bound integrands are integrable over instruments and covariates](hyp:hObservableIntegrable),
then [the covariate-averaged lower and upper bounds, and the corresponding transport bounds, equal the connected-instrument observable formulas](goal). -/
theorem continuous_reduction
    (hDomains : DomainsCompactBorel M) (hEndpoints : OutcomeEndpointsKnown M)
    (hPotential : PotentialSupport M) (hConsistency : Consistency M)
    (hExogeneity : InstrumentExogeneity M) (hThreshold : ThresholdCrossing M)
    (hUniform : UniformResistance M) (hSupport : CommonInstrumentSupport M)
    (hComponents : FiniteInstrumentComponents Z)
    (hContinuous : PropensityContinuousOnComponents M)

    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (hConnected : InstrumentConnectedReduction Z)
    -- Regularity bookkeeping for the outer expectations displayed in the proposition.
    (hObservableIntegrable : ∀ upper : Bool,
      Integrable (connectedInt M zeroLaw upper (policyProp phi M.prop)) (zxLaw M)) :
    covariateLowerValue M (policyWeight M (policyProp phi M.prop)) = connectedValue M zeroLaw false (policyProp phi M.prop) ∧
    covariateUpperValue M (policyWeight M (policyProp phi M.prop)) = connectedValue M zeroLaw true (policyProp phi M.prop) ∧
    thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop)) = connectedValue M zeroLaw false (policyProp phi M.prop) ∧
    thetaUpper1 (transportData M) (policyWeight M (policyProp phi M.prop)) = connectedValue M zeroLaw true (policyProp phi M.prop) := by
  have h : StructuralAssumptions M :=
    ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
  have hRegular := policyWeight_target_regular M hThreshold (policyProp phi M.prop)
    (policy_propensity_jointly_measurable M hThreshold phi hPolicy)
  have hValues (upper : Bool) :
      (∫ x, conditionalBoundIntegrand M upper
        (policyWeight M (policyProp phi M.prop)) x ∂xLaw M) =
      connectedValue M zeroLaw upper (policyProp phi M.prop) := by
    calc
      _ = ∫ x, (∫ z, connectedInt M zeroLaw upper (policyProp phi M.prop) (z, x)
          ∂M.instKernel x) ∂xLaw M :=
        integral_congr_ae (connected_conditional_formula M zeroLaw h hEndpoints
          hContinuous hComponents hConnected phi hPolicy upper)
      _ = _ := instrument_kernel_outer_integral M _ (hObservableIntegrable upper)
  have hSharp := conditional_sharp_bounds_assembly M h hEndpoints
    (policyWeight M (policyProp phi M.prop)) hRegular.1 hRegular.2 hContinuous hComponents
  have hLower : covariateLowerValue M (policyWeight M (policyProp phi M.prop)) =
      connectedValue M zeroLaw false (policyProp phi M.prop) := hValues false
  have hUpper : covariateUpperValue M (policyWeight M (policyProp phi M.prop)) =
      connectedValue M zeroLaw true (policyProp phi M.prop) := hValues true
  exact ⟨hLower, hUpper, hSharp.2.2.2.2.1.trans hLower, hSharp.2.2.2.2.2.trans hUpper⟩

end Papers.TbsPrteOptimalTransport
