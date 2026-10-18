module
public import Papers.TbsPrteOptimalTransport.Helpers.FeasibleDisintegration
/-! TCovariateLowerBound statements. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
set_option linter.style.haveILetI false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
-- @node: thm:covariate-continuous-lower-bound
/-- Under [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), and [common instrument support](hyp:hSupport), suppose
[a rule assigns a covariate- and resistance-dependent target weight to each latent model](hyp:omOf),
the target weight is [measurable](hyp:hMeasurable), [identified by the observed law](hyp:hIdentifiable),
and [integrable](hyp:hIntegrable), and the instrument has [finitely many connected components](hyp:hComponents)
with [continuous propensity on each component](hyp:hContinuous).
Then [both conditional bound integrands are integrable, their covariate averages attain the minimum and maximum feasible treated values, and these averages equal the transport lower and upper bounds](goal). -/
theorem conditional_sharp_bounds
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

    : Integrable (conditionalBoundIntegrand M false (omOf Ω M)) (xLaw M) ∧
      Integrable (conditionalBoundIntegrand M true (omOf Ω M)) (xLaw M) ∧
      IsLeast (treatedValueSet (transportData M) (omOf Ω M)) (covariateLowerValue M (omOf Ω M)) ∧
      IsGreatest (treatedValueSet (transportData M) (omOf Ω M)) (covariateUpperValue M (omOf Ω M)) ∧
      thetaLower1 (transportData M) (omOf Ω M) = covariateLowerValue M (omOf Ω M) ∧
      thetaUpper1 (transportData M) (omOf Ω M) = covariateUpperValue M (omOf Ω M) := by
  exact conditional_sharp_bounds_assembly M
    ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
    hEndpoints (omOf Ω M) hMeasurable hIntegrable hContinuous hComponents

-- @node: gap_extension_attains
/-- Under [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), and [common instrument support](hyp:hSupport), take
[a rule assigning a covariate- and resistance-dependent target weight to each latent model](hyp:omOf)
and let the target weight be
[measurable](hyp:hMeasurable), [identified by the observed law](hyp:hIdentifiable), and [integrable](hyp:hIntegrable).
If the instrument has [finitely many components](hyp:hComponents) with [continuous propensity on each](hyp:hContinuous),
and [the rank kernels extend the identified interval laws](hyp:hQ), then
[combining the completed attaining kernel with independent uniform resistance and the covariate law yields a feasible treated joint law whose weighted value equals the covariate lower bound](goal). -/
lemma gap_extension_attains
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

    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    IsFeasibleTreated (transportData M)
      (((Causalean.Stat.unifOI).prod (xLaw M)).bind (fun ux =>
        (completedAttainingKernel M (omOf Ω M) Q
          ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
          hEndpoints hMeasurable hContinuous hComponents hQ).val (ux.1, ux.2) |>.map (fun y => (ux,y)))) ∧
    thetaComp (omOf Ω M)
      (((Causalean.Stat.unifOI).prod (xLaw M)).bind (fun ux =>
        (completedAttainingKernel M (omOf Ω M) Q
          ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
          hEndpoints hMeasurable hContinuous hComponents hQ).val (ux.1, ux.2) |>.map (fun y => (ux,y)))) =
      covariateLowerValue M (omOf Ω M) := by
  let h : StructuralAssumptions M :=
    ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
  let K := completedAttainingKernel M (omOf Ω M) Q h hEndpoints hMeasurable
    hContinuous hComponents hQ
  letI := K.property.1
  constructor
  · refine ⟨supported_joint_probability M K.val,
      supported_joint_support M h K.val K.property.2.1,
      supported_joint_marginal M K.val, ?_⟩
    exact attaining_version_joint_compatible M h hContinuous hComponents
      (omOf Ω M) hMeasurable Q hQ K.val K.property
  · exact attaining_version_joint_cost M h hEndpoints hContinuous hComponents
      (omOf Ω M) hMeasurable hIntegrable Q hQ K.val K.property

end Papers.TbsPrteOptimalTransport
