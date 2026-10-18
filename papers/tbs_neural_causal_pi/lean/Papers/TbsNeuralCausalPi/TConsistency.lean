module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.ConsistencyThresholds
public import Papers.TbsNeuralCausalPi.Helpers.ConvgOpt
public import Papers.TbsNeuralCausalPi.Helpers.EstimationFeasibility
public import Papers.TbsNeuralCausalPi.Helpers.DiscreteWasserstein
public import Papers.TbsNeuralCausalPi.Helpers.EstimationCompactness
public import Papers.TbsNeuralCausalPi.Helpers.EstimationSequential
public import Papers.TbsNeuralCausalPi.Helpers.ObjectiveRecovery
public import Papers.TbsNeuralCausalPi.Helpers.StructuralCompactness
public import Papers.TbsNeuralCausalPi.Helpers.ParameterConvergence
public import Papers.TbsNeuralCausalPi.Helpers.ParameterExtension
public import Papers.TbsNeuralCausalPi.Helpers.ParameterTransport
public import Papers.TbsNeuralCausalPi.Helpers.ParameterContinuity
public import Papers.TbsNeuralCausalPi.Helpers.ParameterDiscrepancy
public import Papers.TbsNeuralCausalPi.Helpers.ParameterLowerAssembly
public import Papers.TbsNeuralCausalPi.Helpers.ParameterRepresentatives
public import Papers.TbsNeuralCausalPi.Helpers.StructuralApprox
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalWasserstein
public import Papers.TbsNeuralCausalPi.Helpers.RobustCategoricalRace
public import Papers.TbsNeuralCausalPi.Helpers.SimulationShattering
public import Papers.TbsNeuralCausalPi.Helpers.SimulationActivationPolynomials
public import Papers.TbsNeuralCausalPi.Helpers.SimulationGeneratorPolynomials
public import Papers.TbsNeuralCausalPi.Helpers.SimulationGeneratorHistories
public import Papers.TbsNeuralCausalPi.Helpers.SimulationFiniteParameters
public import Papers.TbsNeuralCausalPi.Helpers.SimulationLayerPatterns
public import Papers.TbsNeuralCausalPi.Helpers.SimulationNetworkHistories
public import Papers.TbsNeuralCausalPi.Helpers.SimulationNetworkComparisons
public import Papers.TbsNeuralCausalPi.Helpers.SimulationNetworkShapes
public import Papers.TbsNeuralCausalPi.Helpers.SimulationGeneratorShapes
public import Papers.TbsNeuralCausalPi.Helpers.SimulationGeneratorGridPatterns
public import Papers.TbsNeuralCausalPi.Helpers.SimulationSamplingConcentration
public import Papers.TbsNeuralCausalPi.Helpers.SimulationMeshEntropy
public import Papers.TbsNeuralCausalPi.Helpers.SimulationSamplingMesh
public import Papers.TbsNeuralCausalPi.Helpers.SimulationTableAmbiguity
public import Papers.TbsNeuralCausalPi.Helpers.SimulationPrefixReadout
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalPushforwardSampling
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalRateExponents
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelStrata
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelPropensities
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelSelectorTables
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableApproximation
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableSampling
public import Papers.TbsNeuralCausalPi.Helpers.CausalTablePatterns
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableConcentration
public import Papers.TbsNeuralCausalPi.Helpers.CausalPropensityAlphabet
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableReadouts
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableGridPatterns
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableMeshConcentration
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableMeshSampling
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelPrefixCausality
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelCompactLatents
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelLatentCoordinates
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelZeroDimension
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalSamplingRate
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinSpace
public import Papers.TbsNeuralCausalPi.Helpers.CubeDimension
public import Papers.TbsNeuralCausalPi.Helpers.BoundedPopulationTransport
public import Papers.TbsNeuralCausalPi.Helpers.EstimationCandidateBounds
public import Papers.TbsNeuralCausalPi.Helpers.EstimationSamplingSupport
public import Papers.TbsNeuralCausalPi.Helpers.EstimationSamplingTolerance
public import Papers.TbsNeuralCausalPi.Helpers.EstimationCurrentClassSampling
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalCompactConcentration
/-! # Almost-sure bounds for empirical partial identification -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

variable {Omega : Type*} [MeasurableSpace Omega]

-- @node: consistency_positive_extension_mul_mono
/-- If [a is positive](hyp:ha) and [a is at most c](hyp:hac), then [for any real x, replacing a by c cannot decrease the rule that returns the product with x when that product is positive and returns one otherwise](goal). -/
lemma consistency_positive_extension_mul_mono {a c x : ℝ}
    (ha : 0 < a) (hac : a ≤ c) :
    (if 0 < a * x then a * x else 1) ≤
      (if 0 < c * x then c * x else 1) := by
  have hc : 0 < c := ha.trans_le hac
  by_cases hx : 0 < x
  · rw [if_pos (mul_pos ha hx), if_pos (mul_pos hc hx)]
    exact mul_le_mul_of_nonneg_right hac hx.le
  · have hax : ¬ 0 < a * x := not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hx))
    have hcx : ¬ 0 < c * x := not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt hx))
    rw [if_neg hax, if_neg hcx]

-- @node: consistency_epsN_mono_constant
/-- If [a is positive](hyp:ha) and [a is at most c](hyp:hac), then for [input and latent dimensions](hyp:din,dU) that [are respectively positive](hyp:hdin,hdU), [a width schedule and two depth schedules](hyp:W0,L1,L2), [a temperature schedule](hyp:tau), and [a sample index r](hyp:r), [the approximation tolerance computed with constant a is at most the tolerance computed with constant c](goal). -/
lemma consistency_epsN_mono_constant {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (din dU : ℕ) (hdin : 0 < din) (hdU : 0 < dU)
    (W0 L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ) :
    epsN a din dU hdin hdU W0 L1 L2 tau r ≤
      epsN c din dU hdin hdU W0 L1 L2 tau r := by
  exact consistency_positive_extension_mul_mono ha hac

-- @node: consistency_sN_mono_constant
/-- If [a is positive](hyp:ha) and [a is at most c](hyp:hac), then for [a total latent dimension](hyp:DU), [simulation-size and two depth schedules](hyp:m,L1,L2), [a regularization schedule](hyp:lam), and [a sample index r](hyp:r), [the sampling tolerance computed with constant a is at most the tolerance computed with constant c](goal). -/
lemma consistency_sN_mono_constant {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (DU : ℕ) (m L1 L2 : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) :
    sN a DU m L1 L2 lam r ≤ sN c DU m L1 L2 lam r := by
  exact consistency_positive_extension_mul_mono ha hac

-- @node: consistency_ae_eventually_feasible_of_thresholds
/-- For [a sampling measure](hyp:mu), [a true canonical causal model](hyp:M), [structural and generator classes indexed by sample size](hyp:F0,F1), [magnitude and Lipschitz bounds](hyp:K,L), [input, maximum latent, and total latent dimensions](hyp:din,dU,DU) with [positive input and maximum latent dimensions](hyp:hdin,hdU), [simulation-size, width, and two depth schedules](hyp:m,W0,L1,L2), [temperature and regularization schedules](hyp:tau,lam), [observation arrays](hyp:sample), and [simulation arrays](hyp:draws), take [approximation and sampling constants and a deviation prefactor](hyp:Ce,Cs,B) with [positive approximation and sampling constants](hyp:hCe,hCs). If [eventually a restricted candidate approximates the true observational law within the approximation tolerance](hyp:happrox), [the probability of any restricted candidate violating the two-sided comparison between its population Wasserstein error and empirical Sinkhorn discrepancy plus or minus the sampling tolerance is eventually at most the deviation prefactor divided by the squared sample size](hyp:hbad), [replacement constants ce and cs](hyp:ce,cs) [are at least the respective original constants](hyp:hce,hcs), and [a radius schedule](hyp:alpha) [eventually equals the sum of the approximation and sampling tolerances with these replacement constants](hyp:hradius), then [almost surely, at every sufficiently large sample size there is a restricted candidate with empirical Sinkhorn discrepancy at most the radius, and every such feasible candidate has observational Wasserstein error at most twice that radius](goal). -/
lemma consistency_ae_eventually_feasible_of_thresholds
    (mu : Measure Omega) {counts : Fin b → ℕ}
    (M : CanonicalSCM kind dims dag G C)
    (F0 : ℕ → StructuralClass kind dims dag C) (F1 : ℕ → GeneratorClass dims counts)
    (K L : ℝ≥0) (din dU DU : ℕ) (hdin : 0 < din) (hdU : 0 < dU)
    (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (Ce Cs B : ℝ) (hCe : 0 < Ce) (hCs : 0 < Cs)
    (happrox : ∀ᶠ r in atTop,
      ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM) ≤
          ENNReal.ofReal (epsN Ce din dU hdin hdU W0 L1 L2 tau r))
    (hbad : ∀ᶠ r in atTop,
      mu {w | ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        let e := sinkhornDivergence (lam r)
          (fun i => jointVector (ncmEval R (draws r i w)))
          (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
        let p := wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM)
        let s := sN Cs DU m L1 L2 lam r
        ¬ (p ≤ ENNReal.ofReal (e + s) ∧ ENNReal.ofReal (e - s) ≤ p)} ≤
          ENNReal.ofReal (B * (r : ℝ) ^ (-(2 : ℤ))))
    (ce cs : ℝ) (hce : Ce ≤ ce) (hcs : Cs ≤ cs) (alpha : ℕ → ℝ)
    (hradius : ∀ᶠ r in atTop, alpha r =
      consistencyRadius ce cs din dU DU m W0 L1 L2 hdin hdU tau lam r) :
    ∀ᵐ w ∂mu, ∀ᶠ r in atTop,
      (∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        sinkhornDivergence (lam r)
          (fun i => jointVector (ncmEval R (draws r i w)))
          (fun i => jointVector (sample r i w))
          (uniformWeights (m r)) (uniformWeights r) ≤ alpha r) ∧
      (∀ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R →
        sinkhornDivergence (lam r)
          (fun i => jointVector (ncmEval R (draws r i w)))
          (fun i => jointVector (sample r i w))
          (uniformWeights (m r)) (uniformWeights r) ≤ alpha r →
        wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal (2 * alpha r)) := by
  have hcontrol := estimation_ae_eventually_uniform_constraint_control mu
    (fun _ => restrictedCandidate K L)
    (fun _ R => wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM))
    (fun r R w => sinkhornDivergence (lam r)
      (fun i => jointVector (ncmEval R (draws r i w)))
      (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r))
    (sN Cs DU m L1 L2 lam) B hbad
  filter_upwards [hcontrol] with w hw
  filter_upwards [hw, happrox, hradius] with r hc ha hr
  have he : 0 ≤ epsN Ce din dU hdin hdU W0 L1 L2 tau r := by
    unfold epsN
    dsimp only
    split_ifs with h
    · exact h.le
    · norm_num
  have hemono := consistency_epsN_mono_constant hCe hce din dU hdin hdU W0 L1 L2 tau r
  have hsmono := consistency_sN_mono_constant hCs hcs DU m L1 L2 lam r
  have hrge : epsN Ce din dU hdin hdU W0 L1 L2 tau r + sN Cs DU m L1 L2 lam r ≤
      alpha r := by
    rw [hr, consistencyRadius]
    exact add_le_add hemono hsmono
  obtain ⟨R, hR, herr⟩ := ha
  constructor
  · exact ⟨R, hR,
      (estimation_feasible_of_population_approximation he herr (hc R hR).2).trans hrge⟩
  · intro R hR hfeas
    exact estimation_population_error_of_feasible (hc R hR).1 hfeas (by linarith)

-- @node: thm:consistency
/-- For [a sampling probability measure](hyp:mu), [a true canonical causal model](hyp:M), [nonnegative Lipschitz and magnitude bounds](hyp:L,K), [numbers of latent support components](hyp:counts), [the component sets](hyp:sets), [their intrinsic dimensions](hyp:dC), [a common chart Lipschitz bound](hyp:Lchart), [simulation-size, width, and two depth schedules](hyp:m,W0,L1,L2), and [temperature and Sinkhorn regularization schedules](hyp:tau,lam), assume [simulation sizes are positive](hyp:hm) and [regularization levels are positive](hyp:hlam); use [observation arrays](hyp:sample), [shared simulation arrays](hyp:draws), and [a rule assigning simulation arrays to candidate mechanisms and generators](hyp:candidateDraws). For [an intervention-index domain](hyp:domain), [an intervention family](hyp:t), [a probability measure over interventions](hyp:muT), and [a real outcome functional](hyp:F), assume [the functional is Lipschitz](hyp:hF), [its true intervention objective is integrable](hyp:htrueObjective), [its population candidate objectives are integrable](hyp:hpopulationObjective), [temperatures are positive](hyp:htau), and [observations are independent and identically distributed under the true observational law](hyp:hsample); also assume [independent latent blocks](hyp:hind), [a latent Gumbel decomposition](hyp:hdecomp), [categorical mechanisms given by Gumbel argmax](hyp:hcat), [L-Lipschitz continuous mechanisms](hyp:hcont), [L-Lipschitz categorical propensities](hyp:hprop), [the variable bound K](hyp:hbound), [the prescribed distinct connected components of each latent support](hyp:hsupp), [Lipschitz unit-cube charts for those components](hyp:hhomeo), [positive cube-Lebesgue lower bounds for their conditional laws in charts](hyp:hdom), [charts with zero inverse-transported boundary mass in positive dimension](hyp:hboundary), [generator regularity of all latent laws](hyp:hlatent), [the true model's deep-network premises, including unit-cube structural domains and positive maximum dimensions](hyp:hinherited), [L-Lipschitz structural functions on their full input domains](hyp:hstructural), [the consistency growth schedule for simulation sizes, network budgets, temperatures, and regularization](hyp:hgrowth), [positive maximum input and latent dimensions](hyp:hdin,hdU), [continuous structural outputs with norm at most K on their full domains](hyp:hcontinuousOutput), [independent identically distributed simulation inputs](hyp:hsim), [independence of simulation arrays from observation arrays](hyp:hsimind), [the quantized generation bound of Perekrestenko and coauthors](hyp:hPerekrestenko_of_gate), [Yarotsky's coordinate approximation bound](hyp:hYarotskyCoordinate_of_gate), [Yarotsky's structural approximation bound](hyp:hYarotskyStructural_of_gate), [the Anthony–Bartlett packing bound](hyp:hAnthonyBartlettPacking_of_gate), [the Anthony–Bartlett squared-loss concentration bound](hyp:hAnthonyBartlettSquaredLoss_of_gate), and [the Fournier–Guillin small-deviation bound](hyp:hFournierGuillin_of_gate). Then [there exist three positive integer architecture thresholds, certified by the approximation constructions, such that for every choice of architecture factors above these thresholds, if candidates use the shared simulation arrays and their empirical and parameter objectives are integrable, there exist positive approximation and sampling constants such that every larger pair of constants and every positive radius schedule eventually equal to the corresponding sum of tolerances yield the following result whenever both optimization classes and the intervention domain obey the common bound K: almost surely the lower limit of empirical partial-identification values is at least the population lower bound, and their upper limit is at most the true intervention objective](goal). -/
theorem consistency

    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0)

    (counts : Fin b → ℕ) (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)

    (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (hm : ∀ r, 0 < m r) (hlam : ∀ r, 0 < lam r) -- @realizes \lambda_n(strictly positive regularization at every sample index)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (candidateDraws : ∀ r, (∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i))) →
      (∀ j, ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j)) →
        Fin (m r) → Omega → SimulationInput kind counts)

    {I : Type*} [MeasurableSpace I] (domain : Set I) (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hF : ObjectiveLipschitz F)
    (htrueObjective : TrueObjectiveIntegrable M.toEuclideanSCM t muT F)
    (hpopulationObjective : PopulationObjectiveIntegrable M K (LhatF M.toEuclideanSCM L)
      t muT F) (htau : ∀ r, 0 < tau r)
    (hsample : ObservationalSampleIID mu M.toEuclideanSCM sample)

    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hdecomp : LatentGumbelDecomposition M.toEuclideanSCM)
    (hcat : CategoricalGumbelArgmax M.toEuclideanSCM M.f)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)

    (hsupp : ∀ j, SupportFiniteComponents (M.blockLaw j : Measure _) (sets j))
    (hhomeo : ∀ j, ComponentsLipschitzHomeomorphic (sets j) (dC j) Lchart)
    (hdom : ∀ j i, LowerBoundDomination (d := dC j i) (ProbabilityTheory.cond (M.blockLaw j : Measure _)
      (sets j i)) (sets j i) Lchart)
    (hboundary : ∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (sets j i)) (sets j i) Lchart)
    (hlatent : LatentLawsGeneratorRegular M)

    (hinherited : TrueSCMDeepNNPremises M L)
    (hstructural : TrueStructuralLipschitz M L K)
    (hgrowth : ConsistencyGrowthSchedule (maxLatentDim M.toEuclideanSCM) m W0 L1 L2 tau lam)
    (hdin : 0 < maxInDim M.toEuclideanSCM) (hdU : 0 < maxLatentDim M.toEuclideanSCM)
    (hcontinuousOutput : ∀ i d, kind i = Sum.inl d → ∀ x ∈ M.domain i none, ‖M.f i x‖ ≤ K)
    (hsim : SimulationDrawsIID mu m draws)
    (hsimind : SimulationIndependentOfSample mu m sample draws)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox)
    (hAnthonyBartlettPacking_of_gate : AnthonyBartlettPacking)
    (hAnthonyBartlettSquaredLoss_of_gate : AnthonyBartlettSquaredLoss)
    (hFournierGuillin_of_gate : FournierGuillinSmallDeviation)
 :
    ∃ a0 a1 a2 : ℕ,
      0 < a0 ∧ 0 < a1 ∧ 0 < a2 ∧
      ∃ hcert : ArchitectureConstructionThresholds M K (LhatF M.toEuclideanSCM L)
        counts dC a0 a1 a2,
      ∀ c0 c1 c2 : ℕ,
      (0 < a0 ∧ 0 < a1 ∧ 0 < a2 ∧ a0 ≤ c0 ∧ a1 ≤ c1 ∧ a2 ≤ c2) →
      ∀ (hcommon : CommonSimulationDraws (G := G)
        (fun r => structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
        (fun r => generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r) m draws candidateDraws),
      ∀ (hempiricalObjective : ∀ r, EmpiricalObjectiveIntegrable (G := G)
        (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
        (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r)
        (restrictedCandidate K (LhatF M.toEuclideanSCM L)) t muT F),
      ∀ (hparameterObjective : ParameterObjectiveIntegrable M
        (consistencyNeuralParameters (G := G) K (LhatF M.toEuclideanSCM L)
          (fun r => structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
          (fun r => generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r))
        t muT F),
      ∃ Ce Cs : ℝ, 0 < Ce ∧ 0 < Cs ∧
      ∀ ce : ℝ, Ce ≤ ce → ∀ cs : ℝ, Cs ≤ cs →
      ∀ alpha : ℕ → ℝ, -- @realizes \alpha_n(arbitrary positive finite prefix; prescribed constant multiples eventually)
      (∀ r, 0 < alpha r) →
      (∀ᶠ r in atTop, alpha r = consistencyRadius ce cs (maxInDim M.toEuclideanSCM)
        (maxLatentDim M.toEuclideanSCM) (∑ j, dims j) m W0 L1 L2 hdin hdU tau lam r) →
      ∀ (hclassBound : OptimizationClassBoundedByK K domain t muT
        (empiricalOptimizationModels (G := G)
          (fun r => structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
          (fun r => generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r)
          K (LhatF M.toEuclideanSCM L) m lam
          alpha
          sample draws)
        (populationOptimizationModels M K (LhatF M.toEuclideanSCM L))),
      (∀ᵐ w ∂mu,
        let values := fun r =>
          restrictedEmpiricalPIValue (G := G)
            (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
            (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r)
            K (LhatF M.toEuclideanSCM L) t muT F
            (fun i => sample r i w) (fun i => draws r i w)
            (lam r) (alpha r) (hempiricalObjective r)
        populationLowerBound M K (LhatF M.toEuclideanSCM L) t muT F hpopulationObjective ≤ liminf values atTop ∧
          limsup values atTop ≤ (trueObjective M.toEuclideanSCM t muT F htrueObjective : EReal)) := by
  obtain ⟨a0, a1, a2, hselection, hcert⟩ := exists_architecture_construction_thresholds
    M L K counts sets dC Lchart hinherited hstructural hbound hcontinuousOutput
    hsupp hhomeo hdom hboundary hPerekrestenko_of_gate hYarotskyCoordinate_of_gate
    hYarotskyStructural_of_gate
  refine ⟨a0, a1, a2, hselection.1, hselection.2.1, hselection.2.2.1, hcert, ?_⟩
  intro c0 c1 c2 hfactors hcommon hempiricalObjective hparameterObjective
  have hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart := by
    rcases hinherited with ⟨_, _, _, _, _, _, hregular, hdomain, hdims⟩
    exact ⟨hind, hdecomp, hcat, hbound, hregular, hdims, hdomain, hcont, hprop,
      hstructural, hcontinuousOutput, hsupp, hhomeo, hdom, hboundary⟩
  obtain ⟨thresholds, hCe, hCs, happrox, B, hB, hbad⟩ :=
    consistency_tolerance_thresholds_from_constructions mu M L K counts sets dC Lchart
      hmodel c0 c1 c2 hPerekrestenko_of_gate hYarotskyCoordinate_of_gate
      hYarotskyStructural_of_gate hAnthonyBartlettPacking_of_gate
      hAnthonyBartlettSquaredLoss_of_gate hFournierGuillin_of_gate
      a0 a1 a2 hcert hfactors m W0 L1 L2 tau lam hm htau hlam hgrowth
      sample draws hsample hsim hsimind hdin hdU
  obtain ⟨A, hA, hparameterApprox⟩ := consistencyGrowth_eventually_parameter_approximation
    M K (LhatF M.toEuclideanSCM L) counts dC a0 a1 a2 c0 c1 c2 hcert hfactors
    m W0 L1 L2 tau lam htau hgrowth hdin hdU
  have hK : 0 < K := by exact_mod_cast hbound.1
  obtain ⟨Q, hQ, hobjectiveRecovery⟩ := bounded_objective_recovery_bound
    (kind := kind) (dims := dims) (dag := dag) (G := G) (C := C) L K hK
  have hQA : 0 < (Q : ℝ) * A := mul_pos (by exact_mod_cast hQ) hA
  refine ⟨max thresholds.1 ((Q : ℝ) * A), thresholds.2,
    hCe.trans_le (le_max_left _ _), hCs, ?_⟩
  intro ce hce cs hcs alpha hpositive hradius hclassBound
  have hceOld : thresholds.1 ≤ ce := (le_max_left _ _).trans hce
  have hceRecovery : (Q : ℝ) * A ≤ ce := (le_max_right _ _).trans hce
  have hfeasible := consistency_ae_eventually_feasible_of_thresholds mu M
    (fun r => structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
    (fun r => generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM)
      c1 c2 L1 L2 tau r)
    K (LhatF M.toEuclideanSCM L) (maxInDim M.toEuclideanSCM)
    (maxLatentDim M.toEuclideanSCM) (∑ j, dims j) hdin hdU
    m W0 L1 L2 tau lam sample draws thresholds.1 thresholds.2 B hCe hCs
    happrox hbad ce cs hceOld hcs alpha hradius
  have halpha := (consistencyGrowth_eventually_small_radius
    (DU := ∑ j, dims j) hdin hdU (hCe.trans_le hceOld) (hCs.trans_le hcs)
    htau hlam hgrowth hradius).1
  obtain ⟨LF, hLF⟩ := hF
  have hclass : M ∈ canonicalClass (domainLipClass M L) := by
    intro i x hx y hy
    exact hstructural i hx hy
  let epsilon := epsN A (maxInDim M.toEuclideanSCM)
    (maxLatentDim M.toEuclideanSCM) hdin hdU W0 L1 L2 tau
  let upper := fun r => objectiveIntegral M.toEuclideanSCM t muT F +
    max (LF : ℝ) 1 * ((Q : ℝ) * epsilon r)
  have hepsilon : Tendsto epsilon atTop (𝓝 0) :=
    consistencyGrowth_epsN_tendsto_zero hdin hdU hA htau hgrowth
  have hupper : Tendsto upper atTop (𝓝 (objectiveIntegral M.toEuclideanSCM t muT F)) := by
    simpa only [upper, mul_zero, add_zero] using
      tendsto_const_nhds.add ((hepsilon.const_mul (Q : ℝ)).const_mul (max (LF : ℝ) 1))
  have hrecovery : ∀ᶠ r in atTop,
      ∃ R : NCMIn kind dims dag G C counts
        (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
        (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r),
      restrictedCandidate K (LhatF M.toEuclideanSCM L) R ∧
      wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM) ≤
          ENNReal.ofReal (epsN ce (maxInDim M.toEuclideanSCM)
            (maxLatentDim M.toEuclideanSCM) hdin hdU W0 L1 L2 tau r) ∧
      objectiveIntegral R.canonical.toEuclideanSCM t muT F ≤ upper r := by
    filter_upwards [hparameterApprox,
      hepsilon.eventually (gt_mem_nhds zero_lt_one)] with r hr hsmall
    obtain ⟨R, hR, herr⟩ := hr
    have henonneg : 0 ≤ epsilon r := by
      dsimp [epsilon, epsN]
      split_ifs with h
      · exact h.le
      · norm_num
    obtain ⟨hobs, hobj⟩ := hobjectiveRecovery M R.canonical hclass hind hdecomp hcat
      hcont hprop hbound
      (restrictedCandidate_variablesBoundedAt_original dC K (LhatF M.toEuclideanSCM L)
        hK hclassBound.2.2.1 (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r R hR)
      hcontinuousOutput
      (restrictedCandidate_continuous_output_bound K (LhatF M.toEuclideanSCM L) R hR)
      t muT domain hclassBound.2.2 F LF hLF htrueObjective
      (hempiricalObjective r R hR) (epsilon r) henonneg herr
    refine ⟨R, hR, ?_, ?_⟩
    · have hscale : (Q : ℝ) * epsilon r =
          epsN ((Q : ℝ) * A) (maxInDim M.toEuclideanSCM)
            (maxLatentDim M.toEuclideanSCM) hdin hdU W0 L1 L2 tau r := by
        exact positive_extension_scale_of_lt_one (by exact_mod_cast hQ) hsmall
      rw [hscale] at hobs
      exact hobs.trans (ENNReal.ofReal_le_ofReal
        (consistency_epsN_mono_constant hQA hceRecovery _ _ hdin hdU W0 L1 L2 tau r))
    · have h := (abs_le.mp hobj).2
      dsimp [upper]
      linarith
  have hcontrol := estimation_ae_eventually_uniform_constraint_control mu
    (fun _ => restrictedCandidate K (LhatF M.toEuclideanSCM L))
    (fun _ R => wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM))
    (fun r R w => sinkhornDivergence (lam r)
      (fun i => jointVector (ncmEval R (draws r i w)))
      (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r))
    (sN thresholds.2 (∑ j, dims j) m L1 L2 lam) B hbad
  filter_upwards [hfeasible, hcontrol] with w hw hc
  constructor
  · apply restrictedEmpiricalPIValue_liminf_ge_of_cube_representatives M hK hbound
      (fun r => structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
      (fun r => generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM)
        c1 c2 L1 L2 tau r)
      t muT domain hclassBound.2.2 F hLF hparameterObjective hpopulationObjective
      hempiricalObjective m (fun r i => sample r i w) (fun r i => draws r i w)
      lam alpha (fun r => 2 * alpha r)
      (by simpa using halpha.const_mul 2)
      (fun r => mul_nonneg (by norm_num) (hpositive r).le)
    · intro r R hR
      exact restrictedCandidate_populationRepresentation_of_latent_support R hR
        (ncm_generatorClassN_blockLaw_box dC K (maxLatentDim M.toEuclideanSCM)
          c1 c2 L1 L2 tau r R)
    · filter_upwards [hw] with r hr
      exact hr.2
  · apply restrictedEmpiricalPIValue_limsup_le_of_recovery
      (fun r => structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
      (fun r => generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM)
        c1 c2 L1 L2 tau r)
      K (LhatF M.toEuclideanSCM L) t muT F hempiricalObjective m
      (fun r i => sample r i w) (fun r i => draws r i w) lam alpha upper
      (objectiveIntegral M.toEuclideanSCM t muT F) hupper
    filter_upwards [hrecovery, hc, hradius] with r hr hcr hrad
    obtain ⟨R, hR, hpop, hobj⟩ := hr
    refine ⟨R, hR, ?_, hobj⟩
    have he : 0 ≤ epsN ce (maxInDim M.toEuclideanSCM)
        (maxLatentDim M.toEuclideanSCM) hdin hdU W0 L1 L2 tau r := by
      unfold epsN
      dsimp only
      split_ifs with h
      · exact h.le
      · norm_num
    apply (estimation_feasible_of_population_approximation he hpop (hcr R hR).2).trans
    rw [hrad, consistencyRadius]
    exact add_le_add le_rfl
      (consistency_sN_mono_constant hCs hcs _ m L1 L2 lam r)

end
end Papers.TbsNeuralCausalPi
