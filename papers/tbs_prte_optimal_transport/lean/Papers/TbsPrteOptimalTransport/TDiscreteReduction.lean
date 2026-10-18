module
public import Papers.TbsPrteOptimalTransport.Helpers.DiscretePolicyAssembly
/-! TDiscreteReduction statements. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
variable [Fintype Z] [DecidableEq Z]
-- @node: prop:discrete-reduction
/-- Assume [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), and [common instrument support](hyp:hSupport).
For [an admissible policy](hyp:hPolicy), if [distinct baseline and policy propensity levels are separated](hyp:hGap),
[the level structure constructed at the reference covariate value has the same ordering at every covariate value](hyp:hOrder),
and [the instrument satisfies the finite-instrument reduction conditions](hyp:hFinite), then
[the covariate-averaged lower and upper bounds and the transport lower and upper bounds equal their discrete full-bin, band, and tail formulas](goal). -/
theorem discrete_reduction
    (hDomains : DomainsCompactBorel M) (hEndpoints : OutcomeEndpointsKnown M)
    (hPotential : PotentialSupport M) (hConsistency : Consistency M)
    (hExogeneity : InstrumentExogeneity M) (hThreshold : ThresholdCrossing M)
    (hUniform : UniformResistance M) (hSupport : CommonInstrumentSupport M)

    (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi) (x0 : X)
    (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hFinite : InstrumentFiniteReduction Z) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    covariateLowerValue M (policyWeight M (policyProp phi M.prop)) =
      discreteTarget M false L (policyProp phi M.prop) ∧
    covariateUpperValue M (policyWeight M (policyProp phi M.prop)) =
      discreteTarget M true L (policyProp phi M.prop) ∧
    thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop)) =
      discreteTarget M false L (policyProp phi M.prop) ∧
    thetaUpper1 (transportData M) (policyWeight M (policyProp phi M.prop)) =
      discreteTarget M true L (policyProp phi M.prop) := by
  let L := LevelStructure M.prop (policyProp phi M.prop) x0
  have h : StructuralAssumptions M :=
    ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
  have hRegular := policyWeight_target_regular M hThreshold (policyProp phi M.prop)
    (policy_propensity_jointly_measurable M hThreshold phi hPolicy)
  have hSharp := conditional_sharp_bounds_assembly M h hEndpoints
    (policyWeight M (policyProp phi M.prop)) hRegular.1 hRegular.2
    (finite_instrument_propensity_continuous M hFinite)
    (finite_instrument_components hFinite.1)
  -- Reflect the antitone weight quantile, assemble its observable slice integrals,
  -- and combine the separately identified tail with the sharp-bound theorem.
  have hInterior (upper : Bool) : ∀ᵐ x ∂xLaw M,
      (∑ k ∈ Finset.range L.K, (L.pLev (k + 1) x - L.pLev k x) *
        ∫ t in Ioo (0 : ℝ) 1,
          (conditionalIntervalQuantiles M (policyWeight M (policyProp phi M.prop)) x k).1 t *
          (conditionalIntervalQuantiles M (policyWeight M (policyProp phi M.prop)) x k).2
            (if upper then t else 1 - t)) =
      ∑ k ∈ Finset.range L.K, (gammaFull M L k x * Jfull M L k x +
        ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x * Jband M upper L k (j - 1) x) := by
    have hRewrite (x : X) :
        (∑ k ∈ Finset.range L.K, (L.pLev (k+1) x - L.pLev k x) *
          ∫ t in Ioo (0 : ℝ) 1,
            (conditionalIntervalQuantiles M (policyWeight M (policyProp phi M.prop)) x k).1 t *
            (conditionalIntervalQuantiles M (policyWeight M (policyProp phi M.prop)) x k).2
              (if upper then t else 1-t)) =
        ∑ k ∈ Finset.range L.K, (L.pLev (k+1) x - L.pLev k x) *
          ∫ t in Ioo (0 : ℝ) 1,
            (conditionalIntervalQuantiles M (policyWeight M (policyProp phi M.prop)) x k).1
              (if upper then 1-t else t) *
            policyWeight M (policyProp phi M.prop) x
              (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [finite_policy_quantile_product_integral M (policyProp phi M.prop) L hOrder x k
        (Finset.mem_range.mp hk)]
    suffices hAssembly : ∀ᵐ x ∂xLaw M,
        (∑ k ∈ Finset.range L.K, (L.pLev (k+1) x - L.pLev k x) *
          ∫ t in Ioo (0 : ℝ) 1,
            (conditionalIntervalQuantiles M (policyWeight M (policyProp phi M.prop)) x k).1
              (if upper then 1-t else t) *
            policyWeight M (policyProp phi M.prop) x
              (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t)) =
        ∑ k ∈ Finset.range L.K, (gammaFull M L k x * Jfull M L k x +
          ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x * Jband M upper L k (j-1) x) by
      filter_upwards [hAssembly] with x hx
      exact (hRewrite x).trans hx
    filter_upwards [finite_policy_observable_integral M h hEndpoints
      (policyProp phi M.prop) L hOrder upper] with x hx
    apply Finset.sum_congr rfl
    intro k hk
    exact hx k (Finset.mem_range.mp hk)
  have hConditional (upper : Bool) : ∀ᵐ x ∂xLaw M,
      conditionalBoundIntegrand M upper (policyWeight M (policyProp phi M.prop)) x =
      (∑ k ∈ Finset.range L.K, (gammaFull M L k x * Jfull M L k x +
        ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x * Jband M upper L k (j - 1) x)) +
      tailContribution M upper L (policyProp phi M.prop) x := by
    filter_upwards [hInterior upper] with x hx
    rw [finite_policy_conditional_bound_sum M hThreshold hFinite phi hPolicy L hOrder upper x, hx]
  have hlower : covariateLowerValue M (policyWeight M (policyProp phi M.prop)) =
      discreteTarget M false L (policyProp phi M.prop) := integral_congr_ae (hConditional false)
  have hupper : covariateUpperValue M (policyWeight M (policyProp phi M.prop)) =
      discreteTarget M true L (policyProp phi M.prop) := integral_congr_ae (hConditional true)
  exact ⟨hlower, hupper, hSharp.2.2.2.2.1.trans hlower, hSharp.2.2.2.2.2.trans hupper⟩

end Papers.TbsPrteOptimalTransport
