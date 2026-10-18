module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.TConsistency
public import Papers.TbsNeuralCausalPi.TLipAte
public import Papers.TbsNeuralCausalPi.Helpers.RateDoseResponse
public import Papers.TbsNeuralCausalPi.Helpers.RateSamplingAssembly
public import Papers.TbsNeuralCausalPi.Helpers.EstimationLimits
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Papers.TbsNeuralCausalPi.Helpers.CubeDimension
/-! # Probability and magnitude of the finite-sample error -/
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

-- Rate assembly from the construction thresholds and the causal-effect bound.
-- @node: thm:rate
/-- Under [a probability sampling law](hyp:mu), fix [a canonical causal
model](hyp:M), [nonnegative Lipschitz and magnitude bounds](hyp:L,K),
[latent component counts](hyp:counts), [component sets](hyp:sets), [component
dimensions](hyp:dC), [a chart Lipschitz bound](hyp:Lchart), [simulation-size,
structural-width, and two generator-depth schedules](hyp:m,W0,L1,L2),
[temperature and regularization schedules](hyp:tau,lam), [observation
arrays](hyp:sample), [simulation arrays](hyp:draws), and [candidate-dependent
simulation arrays](hyp:candidateDraws). Suppose [simulation sizes are positive
at every index](hyp:hm), [regularization levels are positive at every index](hyp:hlam), [latent blocks are
independent](hyp:hind), [noise admits the Gumbel decomposition](hyp:hdecomp),
[categorical mechanisms use Gumbel argmax](hyp:hcat), [continuous mechanisms
obey the Lipschitz bound](hyp:hcont), [categorical propensities obey the
Lipschitz bound](hyp:hprop), [variables
obey the magnitude bound](hyp:hbound), [block laws have the specified finite
support components](hyp:hsupp), [these components have Lipschitz cube
charts](hyp:hhomeo), [conditional component laws satisfy lower-bound
domination](hyp:hdom), [their pullbacks vanish on cube boundaries](hyp:hboundary),
and [latent laws are regular for generator approximation](hyp:hlatent).
Assume [the model also satisfies the deep-network premises, including unit-cube
structural domains](hyp:hinherited), [the budgets satisfy the consistency
growth schedule](hyp:hgrowth), [the maximum structural input dimension is
positive](hyp:hdin), [the maximum latent dimension is positive](hyp:hdU), [continuous mechanism
outputs obey the magnitude bound on their domains](hyp:hcontinuousOutput),
[simulation inputs are independent and identically distributed](hyp:hsim),
and [simulations are independent of observations](hyp:hsimind). Assume
[quantized generation](hyp:hPerekrestenko_of_gate), [coordinate approximation](hyp:hYarotskyCoordinate_of_gate),
[structural approximation](hyp:hYarotskyStructural_of_gate), [the packing
bound](hyp:hAnthonyBartlettPacking_of_gate), [the squared-loss bound](hyp:hAnthonyBartlettSquaredLoss_of_gate),
and [the small-deviation Wasserstein bound](hyp:hFournierGuillin_of_gate),
as well as [Lipschitz structural mechanisms on their full domains](hyp:hstructural)
and [positive temperatures](hyp:htemperature). For [treatment and outcome
nodes](hyp:T,Y), [a scalar outcome](hyp:hY), [dose interval endpoints](hyp:t1,t2)
[with the lower endpoint strictly below the upper](hyp:ht12), and [a tolerance parameter](hyp:epsilon)
[with positive value](hyp:hepsilon), take [a reference dose distribution](hyp:P),
[a treatment function](hyp:treatment), [a scalar treatment node](hyp:hT),
[that function equal to its scalar value](hyp:htreatment), [a conditional
density](hyp:p), and [an overlap constant](hyp:delta). Suppose [treatment
overlap holds on the interval](hyp:hoverlap), [the density represents the
conditional treatment law relative to the reference distribution](hyp:hdensity),
[there is no hidden confounding](hyp:hnoconf), [complete observations are
independent draws from the true observational law](hyp:hsample), [the outcome
objective is Lipschitz](hyp:hobjective), [the uniform intervention distribution
is absolutely continuous relative to the reference dose distribution](hyp:hac),
[its density has finite squared integral](hyp:hAT), [the true
intervention-averaged objective is integrable](hyp:htrueObjective), and
[population-candidate intervention-averaged objectives are integrable](hyp:hpopulationObjective).
Then [positive certified architecture thresholds
exist such that, for any larger architecture factors, common simulation draws,
and integrable empirical candidate objectives, positive approximation and
sampling constants exist with this property: for any larger constants and
positive tolerance schedule eventually equal to the corresponding consistency
radius, if the inherited rate premises hold, a positive error constant exists
such that, provided empirical and population optimization classes obey the
magnitude bound, at every sufficiently large observation count the empirical
partially identified value is finite and differs from the true objective by
at most that constant times the square root of tolerance, with probability at
least one minus that constant divided by observation count squared](goal). -/
theorem rate_of_convergence

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

    (hstructural : TrueStructuralLipschitz M L K)
    (htemperature : TemperaturesPositive tau)
    (T Y : Fin n) (hY : valueDim (kind Y) = 1)
    (t1 t2 epsilon : ℝ) (ht12 : t1 < t2)
    (hepsilon : 0 < epsilon)
    (P : ProbabilityMeasure ℝ) (treatment : Joint kind → ℝ)
    (hT : valueDim (kind T) = 1) (htreatment : treatment = scalarOutcome T hT)
    (p : ParentSpace M.toEuclideanSCM T × ℝ → ℝ≥0∞) (delta : ℝ)
    (hoverlap : TreatmentOverlap M.toEuclideanSCM T treatment P p delta t1 t2)
    (hdensity : TreatmentReferenceDensity M.toEuclideanSCM T treatment P p)
    (hnoconf : NoHiddenConfounding G)
    (hsample : ObservationalSampleCompleteIID mu M.toEuclideanSCM sample)
    (hobjective : ObjectiveLipschitz (rateObjective (scalarOutcome Y hY)))
    (hac : uniformIntervention t1 t2 ht12 ≪ (P : Measure ℝ))
    (hAT : (∫⁻ t in Set.Icc t1 t2,
      ((uniformIntervention t1 t2 ht12).rnDeriv (P : Measure ℝ) t)^2 ∂(P : Measure ℝ)) < ⊤)

    (htrueObjective : TrueObjectiveIntegrable M.toEuclideanSCM (singleLawIntervention T) (uniformIntervention t1 t2 ht12) (rateObjective (scalarOutcome Y hY)))
    (hpopulationObjective : PopulationObjectiveIntegrable M K (LhatF M.toEuclideanSCM L)
      (singleLawIntervention T) (uniformIntervention t1 t2 ht12) (rateObjective (scalarOutcome Y hY))) :
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
        (restrictedCandidate K (LhatF M.toEuclideanSCM L)) (singleLawIntervention T) (uniformIntervention t1 t2 ht12) (rateObjective (scalarOutcome Y hY))),
      ∃ Ce Cs : ℝ, 0 < Ce ∧ 0 < Cs ∧
      ∀ ce : ℝ, Ce ≤ ce → ∀ cs : ℝ, Cs ≤ cs →
      ∀ alpha : ℕ → ℝ, -- @realizes \alpha_n(arbitrary positive finite prefix; prescribed constant multiples eventually)
      (∀ r, 0 < alpha r) →
      (∀ᶠ r in atTop, alpha r = consistencyRadius ce cs (maxInDim M.toEuclideanSCM)
        (maxLatentDim M.toEuclideanSCM) (∑ j, dims j) m W0 L1 L2 hdin hdU tau lam r) →
      ∀ (hinheritRate : RatePremisesInherited mu M L K counts m W0 L1 L2 tau lam
        dC c0 c1 c2
        hPerekrestenko_of_gate hYarotskyCoordinate_of_gate hYarotskyStructural_of_gate hAnthonyBartlettPacking_of_gate hAnthonyBartlettSquaredLoss_of_gate
        (rateObjective (scalarOutcome Y hY)) sample draws candidateDraws
        T treatment P p delta t1 t2 (Set.Icc t1 t2)
        (singleLawIntervention T) (uniformIntervention t1 t2 ht12)
        alpha),
      ∃ A : ℝ, 0 < A ∧
      ∀ (hclassBound : RateOptimizationClassBoundedByK K (Set.Icc t1 t2) (singleLawIntervention T) (uniformIntervention t1 t2 ht12)
        (empiricalOptimizationModels (G := G)
          (fun r => structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
          (fun r => generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r)
          K (LhatF M.toEuclideanSCM L) m lam
          alpha
          sample draws)
        (populationOptimizationModels M K (LhatF M.toEuclideanSCM L))),
      ∀ᶠ r in atTop,
        mu {w | let v : EReal := (
          restrictedEmpiricalPIValue (G := G)
            (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
            (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r)
            K (LhatF M.toEuclideanSCM L) (singleLawIntervention T) (uniformIntervention t1 t2 ht12) (rateObjective (scalarOutcome Y hY))
            (fun i => sample r i w) (fun i => draws r i w)
            (lam r) (alpha r) (hempiricalObjective r));
          v ≠ ⊤ ∧ v ≠ ⊥ ∧ |v.toReal - trueObjective M.toEuclideanSCM
            (singleLawIntervention T) (uniformIntervention t1 t2 ht12)
              (rateObjective (scalarOutcome Y hY)) htrueObjective| ≤
            A * Real.sqrt (alpha r)} ≥
          ENNReal.ofReal (1-A*(r:ℝ)^(-(2:ℤ))) := by
  have hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart :=
    ⟨hind, hdecomp, hcat, hbound, hlatent, ⟨hdin, hdU⟩,
      hinherited.2.2.2.2.2.2.2.1, hcont, hprop, hstructural,
      hcontinuousOutput, hsupp, hhomeo, hdom, hboundary⟩
  obtain ⟨a0, a1, a2, hsel, hcert⟩ := exists_architecture_construction_thresholds
    M L K counts sets dC Lchart hinherited hstructural hbound hcontinuousOutput
    hsupp hhomeo hdom hboundary hPerekrestenko_of_gate
    hYarotskyCoordinate_of_gate hYarotskyStructural_of_gate
  refine ⟨a0, a1, a2, hsel.1, hsel.2.1, hsel.2.2.1, hcert, ?_⟩
  intro c0 c1 c2 hfactors hcommon hempiricalObjective
  obtain ⟨thresholds, hCe, hCs, happrox, B, hB, hbad⟩ :=
    consistency_tolerance_thresholds_from_constructions mu M L K counts sets dC Lchart
      hmodel c0 c1 c2 hPerekrestenko_of_gate hYarotskyCoordinate_of_gate
      hYarotskyStructural_of_gate hAnthonyBartlettPacking_of_gate
      hAnthonyBartlettSquaredLoss_of_gate hFournierGuillin_of_gate a0 a1 a2 hcert hfactors
      m W0 L1 L2 tau lam hm htemperature hlam hgrowth sample draws hsample hsim hsimind
      hdin hdU
  refine ⟨thresholds.1, thresholds.2, hCe, hCs, ?_⟩
  intro ce hce cs hcs alpha halpha hradius hinheritRate
  have hcepos := hCe.trans_le hce
  have hcspos := hCs.trans_le hcs
  have hmono (c d x : ℝ) (hc : 0 < c) (hcd : c ≤ d) :
      (if 0 < c * x then c * x else 1) ≤ (if 0 < d * x then d * x else 1) := by
    by_cases hx : 0 < x
    · rw [if_pos (mul_pos hc hx), if_pos (mul_pos (hc.trans_le hcd) hx)]
      exact mul_le_mul_of_nonneg_right hcd hx.le
    · rw [if_neg (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt hx))),
        if_neg (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
          (hc.trans_le hcd).le (le_of_not_gt hx)))]
  have hepsMono (r : ℕ) : epsN thresholds.1 _ _ hdin hdU W0 L1 L2 tau r ≤
      epsN ce _ _ hdin hdU W0 L1 L2 tau r := hmono _ _ _ hCe hce
  have hsMono (r : ℕ) : sN thresholds.2 (∑ j, dims j) m L1 L2 lam r ≤
      sN cs (∑ j, dims j) m L1 L2 lam r := hmono _ _ _ hCs hcs
  have hepsPos (r : ℕ) : 0 < epsN ce _ _ hdin hdU W0 L1 L2 tau r := by
    unfold epsN
    dsimp only
    split_ifs with h
    · exact h
    · norm_num
  have hsPos (r : ℕ) : 0 < sN cs (∑ j, dims j) m L1 L2 lam r := by
    unfold sN
    dsimp only
    split_ifs with h
    · exact h
    · norm_num
  have hsmall := (consistencyGrowth_eventually_small_radius hdin hdU hcepos hcspos
    htemperature hlam hgrowth hradius).2
  have hstructHat : ∀ i, LipschitzOnWith (LhatF M.toEuclideanSCM L) (M.f i) (M.domain i) := by
    intro i
    by_cases ho : 0 < outputDim (kind i)
    · exact (hstructural i).weaken (L_le_LhatF_of_positive_output M.toEuclideanSCM L hdin i ho)
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have he : M.f i x = M.f i y := by
        apply PiLp.ext
        intro j
        exact (ho (Nat.zero_lt_of_lt j.isLt)).elim
      rw [he, dist_self]
      positivity
  have hcontHat := canonical_continuousMechanismsLipschitz_of_structural M _ hstructHat
  have hpropHat := canonical_categoricalPropensityLipschitz_of_structural M _ hstructHat
  let muT := uniformIntervention t1 t2 ht12
  let : IsFiniteMeasure muT := ⟨by
    simp only [muT, uniformIntervention, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top⟩
  have hsupport : ∀ᵐ t ∂muT, t ∈ Set.Icc t1 t2 := by
    exact MeasureTheory.Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  let density : ℝ := Real.sqrt (∫⁻ t in Set.Icc t1 t2,
    (muT.rnDeriv (P : Measure ℝ) t)^2 ∂(P : Measure ℝ)).toReal
  let a : ℝ := 2 * doseCW kind (LhatF M.toEuclideanSCM L) K / delta
  let bb : ℝ := 2 * (doseLip kind (LhatF M.toEuclideanSCM L))^2 *
    ((P : Measure ℝ) (Set.Icc t1 t2)).toReal
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (mul_nonneg (by norm_num) (doseCW_nonneg _ _)) hoverlap.2.1.le
  have hbb : 0 ≤ bb := by dsimp [bb]; positivity
  let D := density * Real.sqrt (a * 2 + bb * 2^2)
  let A := max 1 (max B D)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBA : B ≤ A := (le_max_left B D).trans (le_max_right _ _)
  have hDA : D ≤ A := (le_max_right B D).trans (le_max_right _ _)
  refine ⟨A, hA, ?_⟩
  intro hclassBound
  filter_upwards [happrox, hbad, hradius, hsmall] with r happroxR hbadR hradiusR hsmallR
  have hbadLarge : mu {w | ∃ R : NCMIn kind dims dag G C counts
      (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
      (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r),
      restrictedCandidate K (LhatF M.toEuclideanSCM L) R ∧
      let e := sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i w)))
        (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
      let p := wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM)
      ¬ (p ≤ ENNReal.ofReal (e + sN cs (∑ j, dims j) m L1 L2 lam r) ∧
        ENNReal.ofReal (e - sN cs (∑ j, dims j) m L1 L2 lam r) ≤ p)} ≤
      ENNReal.ofReal (B * (r : ℝ)^(-(2 : ℤ))) := by
    apply le_trans (measure_mono ?_) hbadR
    rintro w ⟨R, hR, hfail⟩
    refine ⟨R, hR, ?_⟩
    dsimp only
    intro hgood
    apply hfail
    exact ⟨hgood.1.trans (ENNReal.ofReal_le_ofReal (add_le_add le_rfl (hsMono r))),
      (ENNReal.ofReal_le_ofReal (sub_le_sub_left (hsMono r) _)).trans hgood.2⟩
  apply (ENNReal.ofReal_le_ofReal (show 1 - A * (r : ℝ)^(-(2 : ℤ)) ≤
    1 - B * (r : ℝ)^(-(2 : ℤ)) from
    sub_le_sub_left (mul_le_mul_of_nonneg_right hBA (by positivity)) 1)).trans
  apply estimation_success_measure_of_bad_bound mu _ _ (by positivity) hbadLarge
  intro w hw
  have hcontrol : ∀ R : NCMIn kind dims dag G C counts
      (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
      (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r), restrictedCandidate K (LhatF M.toEuclideanSCM L) R →
      wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM) ≤ ENNReal.ofReal
          (sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i w)))
            (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r) +
              sN cs (∑ j, dims j) m L1 L2 lam r) ∧
      ENNReal.ofReal (sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i w)))
        (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r) -
          sN cs (∑ j, dims j) m L1 L2 lam r) ≤
      wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (observationalLaw M.toEuclideanSCM) := by
    intro R hR
    by_contra h
    exact hw ⟨R, hR, h⟩
  obtain ⟨R0, hR0, herr0⟩ := happroxR
  have hne : ∃ R : NCMIn kind dims dag G C counts
      (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
      (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r), restrictedCandidate K (LhatF M.toEuclideanSCM L) R ∧
      sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i w)))
        (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r) ≤ alpha r := by
    refine ⟨R0, hR0, ?_⟩
    rw [hradiusR]
    exact estimation_feasible_of_population_approximation (hepsPos r).le
      (herr0.trans (ENNReal.ofReal_le_ofReal (hepsMono r))) (hcontrol R0 hR0).2
  have hvalue := restrictedEmpiricalPIValue_error_of_quadratic_bound
    (structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r)
    (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r)
    K (LhatF M.toEuclideanSCM L) (singleLawIntervention T) muT
    (rateObjective (scalarOutcome Y hY)) (hempiricalObjective r) (fun i => sample r i w) (fun i => draws r i w)
    (lam r) (alpha r) (trueObjective M.toEuclideanSCM (singleLawIntervention T) muT
      (rateObjective (scalarOutcome Y hY)) htrueObjective) density a bb 2
    (fun R => (wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw M.toEuclideanSCM)).toReal)
    (Real.sqrt_nonneg _) ha hbb (by norm_num) (halpha r).le hsmallR hne ?_
  · exact ⟨hvalue.1, hvalue.2.1,
      hvalue.2.2.trans (mul_le_mul_of_nonneg_right hDA (Real.sqrt_nonneg _))⟩
  · intro R hR hf
    have hp := estimation_population_error_of_feasible (hcontrol R hR).1 hf (by
      rw [hradiusR]; exact le_add_of_nonneg_left (hepsPos r).le)
    have hpReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (halpha r).le : 0 ≤ 2 * alpha r)] at hpReal
    refine ⟨ENNReal.toReal_nonneg, hpReal, ?_⟩
    have hRbound := hclassBound.1 r R.canonical.toEuclideanSCM
      ⟨w, R, hR, hf, rfl⟩
    have hquad := restrictedCandidate_rateObjective_error_le_reference_square M R
      (LhatF M.toEuclideanSCM L) K hR T Y hY hind hcontHat hpropHat hbound hRbound
      hnoconf P treatment hT htreatment p delta t1 t2 hdensity hoverlap.2.1 hoverlap.2.2
      muT hac hsupport hAT htrueObjective (hempiricalObjective r R hR)
    have hK : (⟨(K : ℝ), le_of_lt hbound.1⟩ : ℝ≥0) = K := by
      apply Subtype.ext
      rfl
    rw [hK] at hquad
    simpa only [a, bb, density, mul_assoc, mul_left_comm, mul_comm,
      trueObjective, finiteIteratedObjective, objectiveIntegral] using hquad


end
end Papers.TbsNeuralCausalPi
