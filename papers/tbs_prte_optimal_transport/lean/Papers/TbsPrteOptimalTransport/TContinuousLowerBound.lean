module
public import Papers.TbsPrteOptimalTransport.TCovariateLowerBound
/-! TContinuousLowerBound statements. -/
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
-- @node: thm:continuous-lower-bound
/-- Assume [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold-crossing treatment](hyp:hThreshold),
[uniform resistance](hyp:hUniform), and [common instrument support](hyp:hSupport).
For [a rule assigning a covariate- and resistance-dependent target weight to each latent model](hyp:omOf),
if the target weight is [measurable](hyp:hMeasurable), [identified by the observed law](hyp:hIdentifiable),
and [integrable](hyp:hIntegrable), the instrument has [finitely many connected components](hyp:hComponents)
with [continuous propensity on each component](hyp:hContinuous), and [covariates are constant almost surely](hyp:hConstant),
then [at every almost-sure covariate value the conditional lower and upper formulas attain the minimum and maximum feasible treated values and equal the transport lower and upper bounds](goal). -/
theorem general_instrument_sharp_bounds
    (hDomains : DomainsCompactBorel M) (hEndpoints : OutcomeEndpointsKnown M)
    (hPotential : PotentialSupport M) (hConsistency : Consistency M)
    (hExogeneity : InstrumentExogeneity M) (hThreshold : ThresholdCrossing M)
    (hUniform : UniformResistance M) (hSupport : CommonInstrumentSupport M)
    (omOf : ∀ (A : Type u) [MeasurableSpace A], LatentIVModel A X Z → X → ℝ → ℝ)
    (hMeasurable : TargetWeightMeasurable (omOf Ω M))
    (hIdentifiable : TargetWeightIdentifiable omOf)
    (hIntegrable : TargetWeightIntegrable M (omOf Ω M))
    (hComponents : FiniteInstrumentComponents Z)
    (hContinuous : PropensityContinuousOnComponents M)

    (hConstant : CovariateConstant' M) :
    ∀ x0, (∀ᵐ a ∂M.law.toMeasure, M.Xv a = x0) →
      IsLeast (treatedValueSet (transportData M) (omOf Ω M))
        (conditionalBoundIntegrand M false (omOf Ω M) x0) ∧
      IsGreatest (treatedValueSet (transportData M) (omOf Ω M))
        (conditionalBoundIntegrand M true (omOf Ω M) x0) ∧
      thetaLower1 (transportData M) (omOf Ω M) = conditionalBoundIntegrand M false (omOf Ω M) x0 ∧
      thetaUpper1 (transportData M) (omOf Ω M) = conditionalBoundIntegrand M true (omOf Ω M) x0 := by
  intro x0 hX
  have hLaw : xLaw M = Measure.dirac x0 := by
    calc
      xLaw M = M.law.toMeasure.map (fun _ => x0) := Measure.map_congr hX
      _ = Measure.dirac x0 := by rw [Measure.map_const]; simp
  have hLower : covariateLowerValue M (omOf Ω M) =
      conditionalBoundIntegrand M false (omOf Ω M) x0 := by
    unfold covariateLowerValue
    rw [hLaw, integral_dirac]
  have hUpper : covariateUpperValue M (omOf Ω M) =
      conditionalBoundIntegrand M true (omOf Ω M) x0 := by
    unfold covariateUpperValue
    rw [hLaw, integral_dirac]
  obtain ⟨_, _, hLeast, hGreatest, hInf, hSup⟩ :=
    conditional_sharp_bounds M hDomains hEndpoints hPotential hConsistency
      hExogeneity hThreshold hUniform hSupport omOf hMeasurable hIdentifiable
      hIntegrable hComponents hContinuous
  exact ⟨hLower ▸ hLeast, hUpper ▸ hGreatest,
    hInf.trans hLower, hSup.trans hUpper⟩

end Papers.TbsPrteOptimalTransport
