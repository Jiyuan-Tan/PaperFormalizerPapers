module
public import Papers.TbsPrteOptimalTransport.Helpers.FiniteRangeReduction
/-! TDiscreteLowerBound statements. -/
@[expose] public section
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
/-- For [a latent instrument model](hyp:M), [a choice of upper or lower bound](hyp:upper),
[a target weight depending on covariates and resistance](hyp:om), and [a covariate value](hyp:x0),
the [finite-instrument bound value](goal) is obtained by [sorting the distinct propensity levels](step:1)
and [summing interval lengths times quantile-product integrals, using common ranks for the upper bound and opposite ranks for the lower bound, and adding the unsupported upper-tail contribution with outcome endpoints selected by the weight's sign](step:2). -/
noncomputable def finiteBoundValue (upper : Bool) (om : X → ℝ → ℝ) (x0 : X) :=
  let levels := finiteLevels (fun z => M.prop z x0)
  (∑ i ∈ Finset.range levels.length, (pLevel levels (i+1)-pLevel levels i) *
    ∫ t in Ioo (0:ℝ) 1, (conditionalIntervalQuantiles M om x0 i).1 t *
      (conditionalIntervalQuantiles M om x0 i).2 (if upper then t else 1-t)) +
  ∫ u in Ioc (pLevel levels levels.length) 1,
    (if upper then M.yMax else M.yMin) * max 0 (om x0 u) +
      (if upper then M.yMin else M.yMax) * min 0 (om x0 u)
-- @node: thm:discrete-lower-bound
/-- Under [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), and [common instrument support](hyp:hSupport), suppose
[a rule assigns a covariate- and resistance-dependent target weight to each latent model](hyp:omOf),
the target weight is [measurable](hyp:hMeasurable), [identified by the observed law](hyp:hIdentifiable),
and [integrable](hyp:hIntegrable), [the instrument is finite](hyp:hFinite), and
[covariates are constant almost surely](hyp:hConstant).
Then [at every almost-sure covariate value the finite interval-sum lower and upper formulas attain the minimum and maximum feasible treated values and equal the transport bounds](goal). -/
theorem finite_instrument_sharp_bounds
    (hDomains : DomainsCompactBorel M) (hEndpoints : OutcomeEndpointsKnown M)
    (hPotential : PotentialSupport M) (hConsistency : Consistency M)
    (hExogeneity : InstrumentExogeneity M) (hThreshold : ThresholdCrossing M)
    (hUniform : UniformResistance M) (hSupport : CommonInstrumentSupport M)
    (omOf : ∀ (A : Type u) [MeasurableSpace A], LatentIVModel A X Z → X → ℝ → ℝ)
    (hMeasurable : TargetWeightMeasurable (omOf Ω M))
    (hIdentifiable : TargetWeightIdentifiable omOf)
    (hIntegrable : TargetWeightIntegrable M (omOf Ω M))

    (hFinite : InstrumentFinite Z) (hConstant : CovariateConstant M) :
    ∀ x0, (∀ᵐ a ∂M.law.toMeasure, M.Xv a = x0) →
      IsLeast (treatedValueSet (transportData M) (omOf Ω M)) (finiteBoundValue M false (omOf Ω M) x0) ∧
      IsGreatest (treatedValueSet (transportData M) (omOf Ω M)) (finiteBoundValue M true (omOf Ω M) x0) ∧
      thetaLower1 (transportData M) (omOf Ω M) = finiteBoundValue M false (omOf Ω M) x0 ∧
      thetaUpper1 (transportData M) (omOf Ω M) = finiteBoundValue M true (omOf Ω M) x0 := by
  intro x0 hX
  have hLaw : xLaw M = Measure.dirac x0 := by
    calc
      xLaw M = M.law.toMeasure.map (fun _ => x0) := Measure.map_congr hX
      _ = Measure.dirac x0 := by rw [Measure.map_const]; simp
  have hFiniteValue (upper : Bool) :
      conditionalBoundIntegrand M upper (omOf Ω M) x0 =
        finiteBoundValue M upper (omOf Ω M) x0 := by
    exact finite_conditional_bound_eq_interval_sum M hFinite upper (omOf Ω M) x0
  have hLower : covariateLowerValue M (omOf Ω M) =
      finiteBoundValue M false (omOf Ω M) x0 := by
    unfold covariateLowerValue
    rw [hLaw, integral_dirac, hFiniteValue]
  have hUpper : covariateUpperValue M (omOf Ω M) =
      finiteBoundValue M true (omOf Ω M) x0 := by
    unfold covariateUpperValue
    rw [hLaw, integral_dirac, hFiniteValue]
  obtain ⟨_, _, hLeast, hGreatest, hInf, hSup⟩ :=
    conditional_sharp_bounds M hDomains hEndpoints hPotential hConsistency
      hExogeneity hThreshold hUniform hSupport omOf hMeasurable hIdentifiable
      hIntegrable (finite_instrument_components hFinite.1)
      (finite_instrument_propensity_continuous M hFinite)
  exact ⟨hLower ▸ hLeast, hUpper ▸ hGreatest,
    hInf.trans hLower, hSup.trans hUpper⟩

end Papers.TbsPrteOptimalTransport
