module
public import Papers.TbsPrteOptimalTransport.Helpers.SharpnessIdentification
/-! TSharpness statements. -/
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
-- @node: prop:sharpness
/-- Under [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), [common instrument support](hyp:hSupport), and
[generation of the observed law by the model](hyp:hGenerated),
[every candidate joint probability law of resistance, covariates, and both potential outcomes with feasible treatment-specific marginals admits a structural completion preserving that joint law, outcome support, propensity, and observed law; conversely, every structural model with the same outcome support and observed law has feasible treatment-specific marginals](goal). -/
theorem feasible_iff_structural
    (hDomains : DomainsCompactBorel M) (hEndpoints : OutcomeEndpointsKnown M)
    (hPotential : PotentialSupport M) (hConsistency : Consistency M)
    (hExogeneity : InstrumentExogeneity M) (hThreshold : ThresholdCrossing M)
    (hUniform : UniformResistance M) (hSupport : CommonInstrumentSupport M)

    (hGenerated : ObservedLawGenerated M (observedLaw M)) :
    (∀ piT : Measure ((ℝ × X) × (ℝ × ℝ)), IsProbabilityMeasure piT → -- @realizes \tilde{\pi}(joint candidate probability law on the latent carrier)
      IsFeasiblePair (transportData M) (piT.map (fun a => (a.1,a.2.1)))
        (piT.map (fun a => (a.1,a.2.2))) →
      ∃ N : LatentIVModel (((ℝ × X) × (ℝ × ℝ)) × Z) X Z,
        N.law.toMeasure.map (fun a => ((N.U a,N.Xv a),(N.Y0 a,N.Y1 a))) = piT ∧
        StructuralAssumptions N ∧ N.Yset = M.Yset ∧ N.prop = M.prop ∧ observedLaw N = observedLaw M) ∧
    (∀ (A : Type u) (mA : MeasurableSpace A) (N : @LatentIVModel A X Z mA _ _ _ _ _),
      StructuralAssumptions N → N.Yset = M.Yset → observedLaw N = observedLaw M →
        IsFeasiblePair (transportData M) (latentMarginal N false) (latentMarginal N true)) := by
  have hStructural : StructuralAssumptions M :=
    ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
  constructor
  · intro piT hpi hf
    letI : IsProbabilityMeasure piT := hpi
    obtain ⟨N, hj, hpot, hcon, hex, hu, hs, hd, hy, hp, hZX, hsel⟩ :=
      feasible_joint_exogenous_threshold_completion M hDomains hThreshold hSupport piT hf
    have hfeas : IsFeasiblePair (transportData M)
        (latentMarginal N false) (latentMarginal N true) := by
      rw [sharpness_prescribed_latent_marginal N piT hj false,
        sharpness_prescribed_latent_marginal N piT hj true]
      simpa only [latentJointMarginal, Bool.false_eq_true, ↓reduceIte] using hf
    have hmeas : Measurable (Function.uncurry N.prop) := by
      rw [hp]
      exact hThreshold.2.1
    have hobs := sharpness_identification_direct M hStructural N hcon hex hu hmeas
      (Filter.Eventually.of_forall hsel) hp hZX hfeas
    have hstruct : StructuralAssumptions N := by
      refine ⟨hpot, hcon, hex, ?_, hu, hs, hd⟩
      exact ⟨Filter.Eventually.of_forall hsel, hmeas, N.rangeProp,
        sharpness_observed_threshold_mean M N hThreshold hp hZX hobs⟩
    exact ⟨N, hj, hstruct, hy, hp, hobs⟩
  · intro A mA N hn hy hobs
    exact sharpness_identification_converse M hStructural N hn hy hobs

end Papers.TbsPrteOptimalTransport
