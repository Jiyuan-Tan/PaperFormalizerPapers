module
public import Papers.TbsNeuralCausalPi.Setup.Optimization
public import Papers.TbsNeuralCausalPi.Helpers.ArchitecturePremises
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Model
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Generators
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
/-! # Sampling and estimation assumptions -/
@[expose] public section
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
/-- For [the true causal model](hyp:M), [an intervention family](hyp:t),
[its averaging measure](hyp:muT), and [a real-valued outcome functional](hyp:F),
[both levels of the intervention-averaged expectation are integrable](goal). -/
-- @node: ass:bk-owner-4
def TrueObjectiveIntegrable (M : EuclideanSCM kind dims) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) (F : Joint kind → ℝ) : Prop :=
  objectiveDefined M t muT F

/-- For [a structural-function class](hyp:F0), [a generator class](hyp:F1), and
[a rule selecting admissible representations](hyp:admissible),
[every admitted candidate has both levels of its objective integrable](goal),
using [the intervention family](hyp:t), [the intervention averaging measure](hyp:muT),
and [the outcome functional](hyp:F). -/
-- @node: ass:bk-owner-5
def EmpiricalObjectiveIntegrable {counts : Fin b → ℕ}
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    (admissible : NCMIn kind dims dag G C counts F0 F1 → Prop)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) (F : Joint kind → ℝ) : Prop :=
  empiricalObjectivesDefined (G := G) F0 F1 admissible t muT F

/-- Relative to [a reference causal model](hyp:base), [a common magnitude bound](hyp:K),
and [a Lipschitz bound](hyp:L), [every population candidate with bounded Lipschitz
mechanisms, latent laws supported on the bounded cubes, and zero observational
Wasserstein discrepancy from the reference has both objective levels integrable](goal)
for [the intervention family](hyp:t),
[the averaging measure](hyp:muT), and [the outcome functional](hyp:F). -/
-- @node: ass:bk-owner-6
def PopulationObjectiveIntegrable (base : CanonicalSCM kind dims dag G C) (K L : ℝ≥0)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) (F : Joint kind → ℝ) : Prop :=
  populationObjectivesDefined base K L t muT F

/-- Using [a reference causal model](hyp:base) and [a sequence of parameter sets](hyp:Theta),
[both levels of the objective are integrable throughout the proof's parameter closure](goal)
for [the intervention family](hyp:t), [the averaging measure](hyp:muT),
and [the outcome functional](hyp:F). -/
-- @node: ass:bk-owner-7
def ParameterObjectiveIntegrable (base : CanonicalSCM kind dims dag G C) {K L : ℝ≥0}
    (Theta : ℕ → Set (ProofPopulationParam kind dims dag C K L))
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) (F : Joint kind → ℝ) : Prop :=
  parameterObjectivesDefined base Theta t muT F

-- @node: ass:thm-consistency-inherited
/-- For [a canonical causal model](hyp:M) and [a common Lipschitz bound](hyp:L),
[the deep-network premises](goal) require [independent latent blocks](step:1),
[a partition into non-Gumbel blocks and categorical noise](step:2),
[categorical mechanisms represented by Gumbel argmax](step:3),
[Lipschitz continuous mechanisms](step:4), [Lipschitz categorical propensities](step:5),
[a finite positive bound on observed and non-Gumbel latent coordinates](step:6),
[regular latent laws for generator approximation](step:7),
[unit-cube structural approximation domains](step:8), and
[positive maximum structural-input and latent-block dimensions](step:9). -/
def TrueSCMDeepNNPremises (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0) : Prop :=
  LatentBlocksIndependent M.toEuclideanSCM ∧
    LatentGumbelDecomposition M.toEuclideanSCM ∧
    CategoricalGumbelArgmax M.toEuclideanSCM M.f ∧
    ContinuousMechanismsLipschitz M.toEuclideanSCM L ∧
    CategoricalPropensityLipschitz M.toEuclideanSCM M.f L ∧
    (∃ K : ℝ, VariablesBoundedAt M.toEuclideanSCM K) ∧
    LatentLawsGeneratorRegular M ∧
    StructuralDomainsUnitCubes M.toEuclideanSCM ∧
    (0 < maxInDim M.toEuclideanSCM ∧ 0 < maxLatentDim M.toEuclideanSCM)
-- @node: ass:thm-consistency-structural-lipschitz
/-- For [a canonical causal model](hyp:M), [a Lipschitz constant](hyp:Lf), and
[a magnitude-bound parameter](hyp:K), [every structural mechanism is Lipschitz
with that constant on its full input domain](goal).

The magnitude-bound parameter does not restrict this predicate. -/
def TrueStructuralLipschitz (M : CanonicalSCM kind dims dag G C) (Lf K : ℝ≥0) : Prop :=
  ∀ i, LipschitzOnWith Lf (M.f i) (M.domain i none)
-- @node: ass:thm-consistency-objective-lipschitz
/-- [The outcome functional](hyp:F) [is globally Lipschitz with some finite
nonnegative constant](goal). -/
def ObjectiveLipschitz (F : Joint kind → ℝ) : Prop := ∃ L : ℝ≥0, LipschitzWith L F
-- @node: ass:thm-consistency-positive-temperature
/-- [The temperature schedule](hyp:tau) [is strictly positive at every index](goal). -/
def TemperaturesPositive (tau : ℕ → ℝ) : Prop := ∀ r, 0 < tau r
-- @node: ass:thm-consistency-growth
/-- For [latent dimension](hyp:dU), [simulation sizes](hyp:m), [width budgets](hyp:W0),
[two depth schedules](hyp:L1,L2), [temperatures](hyp:tau), and
[Sinkhorn regularization levels](hyp:lam), [the consistency growth schedule](goal)
requires [the observation count to be at most a constant times the simulation size eventually](step:1),
[the first depth to have the same asymptotic order as simulation size raised to
the latent dimension divided by twice that dimension plus four](step:2),
[the second depth to have that same asymptotic order](step:3), and
[the minimum of inverse temperature, width, and the reciprocal of the product of
regularization with the logarithm of observation count times simulation size
to diverge to infinity](step:4). -/
def ConsistencyGrowthSchedule (dU : ℕ) (m W0 L1 L2 : ℕ → ℕ)
    (tau lam : ℕ → ℝ) : Prop :=
  Asymptotics.IsBigO atTop (fun r : ℕ => (r : ℝ)) (fun r => (m r : ℝ)) ∧
  Asymptotics.IsTheta atTop (fun r => (L1 r : ℝ))
    (fun r => (m r : ℝ)^((dU : ℝ)/(2*dU+4))) ∧
  Asymptotics.IsTheta atTop (fun r => (L2 r : ℝ))
    (fun r => (m r : ℝ)^((dU : ℝ)/(2*dU+4))) ∧
  Tendsto (fun r => min (tau r)⁻¹ (min (W0 r : ℝ) (Real.log (r*m r) * lam r)⁻¹)) atTop atTop

/-- Under [the consistency growth schedule](hyp:h), [the simulation size tends
to infinity](goal). -/
-- @node: consistencyGrowth_simulation_tendsto
lemma consistencyGrowth_simulation_tendsto {dU : ℕ} {m W0 L1 L2 : ℕ → ℕ}
    {tau lam : ℕ → ℝ}
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    Tendsto (fun r => (m r : ℝ)) atTop atTop := by
  obtain ⟨c, hc, hbound⟩ := h.1.exists_pos
  have hdiv : Tendsto (fun r : ℕ => (r : ℝ) / c) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hc
  apply tendsto_atTop_mono' atTop _ hdiv
  filter_upwards [hbound.bound] with r hr
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)] at hr
  exact (div_le_iff₀ hc).mpr (by simpa [mul_comm] using hr)

/-- If [the latent dimension is positive](hyp:hdU) and [the consistency growth
schedule holds](hyp:h), [both network depth schedules tend to infinity](goal). -/
-- @node: consistencyGrowth_depths_tendsto
lemma consistencyGrowth_depths_tendsto {dU : ℕ} {m W0 L1 L2 : ℕ → ℕ}
    {tau lam : ℕ → ℝ} (hdU : 0 < dU)
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    Tendsto (fun r => (L1 r : ℝ)) atTop atTop ∧
      Tendsto (fun r => (L2 r : ℝ)) atTop atTop := by
  have hp : 0 < (dU : ℝ) / (2 * dU + 4) := by positivity
  have hpower := (tendsto_rpow_atTop hp).comp (consistencyGrowth_simulation_tendsto h)
  constructor
  · have hh := h.2.1.tendsto_norm_atTop_iff.mpr (by
      simpa only [Function.comp_def, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        using hpower)
    simpa only [Function.comp_def, Real.norm_of_nonneg (Nat.cast_nonneg _)] using hh
  · have hh := h.2.2.1.tendsto_norm_atTop_iff.mpr (by
      simpa only [Function.comp_def, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        using hpower)
    simpa only [Function.comp_def, Real.norm_of_nonneg (Nat.cast_nonneg _)] using hh

/-- Under [the consistency growth schedule](hyp:h), [the width tends to infinity,
the temperature tends to zero, and the product of log observation-count-times-simulation-size
with Sinkhorn regularization tends to zero](goal). -/
-- @node: consistencyGrowth_width_temperature_bias
lemma consistencyGrowth_width_temperature_bias {dU : ℕ} {m W0 L1 L2 : ℕ → ℕ}
    {tau lam : ℕ → ℝ}
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    Tendsto (fun r => (W0 r : ℝ)) atTop atTop ∧
      Tendsto tau atTop (𝓝 0) ∧
      Tendsto (fun r => Real.log (r * m r) * lam r) atTop (𝓝 0) := by
  have ht : Tendsto (fun r => (tau r)⁻¹) atTop atTop :=
    tendsto_atTop_mono (fun _ => min_le_left _ _) h.2.2.2
  have hw : Tendsto (fun r => (W0 r : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun _ => (min_le_right _ _).trans (min_le_left _ _)) h.2.2.2
  have hb : Tendsto (fun r => (Real.log (r * m r) * lam r)⁻¹) atTop atTop :=
    tendsto_atTop_mono (fun _ => (min_le_right _ _).trans (min_le_right _ _)) h.2.2.2
  refine ⟨hw, ht.inv_tendsto_atTop.congr' ?_, hb.inv_tendsto_atTop.congr' ?_⟩
  · exact Eventually.of_forall (fun r => inv_inv (tau r))
  · exact Eventually.of_forall (fun r => inv_inv (Real.log (r * m r) * lam r))

/-- If [the latent dimension is positive](hyp:hdU), [all temperatures are positive](hyp:htau),
[the consistency growth schedule holds](hyp:h), and [the temperature cutoff is positive](hyp:htau0),
then [eventually the width and both depths are at least any fixed construction budget,
and the temperature lies strictly between zero and the smaller of one and the cutoff](goal). -/
-- @node: consistencyGrowth_eventually_construction_budgets
lemma consistencyGrowth_eventually_construction_budgets
    {dU : ℕ} {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ}
    (hdU : 0 < dU) (htau : ∀ r, 0 < tau r)
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam)
    (B : ℕ) {tau0 : ℝ} (htau0 : 0 < tau0) :
    ∀ᶠ r in atTop, B ≤ W0 r ∧ B ≤ L1 r ∧ B ≤ L2 r ∧
      0 < tau r ∧ tau r < min 1 tau0 := by
  obtain ⟨hw, ht, _⟩ := consistencyGrowth_width_temperature_bias h
  obtain ⟨hL1, hL2⟩ := consistencyGrowth_depths_tendsto hdU h
  filter_upwards [hw.eventually (eventually_ge_atTop (B : ℝ)),
    hL1.eventually (eventually_ge_atTop (B : ℝ)),
    hL2.eventually (eventually_ge_atTop (B : ℝ)),
    ht.eventually (gt_mem_nhds (lt_min zero_lt_one htau0))] with r hr h1 h2 ht
  exact ⟨by exact_mod_cast hr, by exact_mod_cast h1, by exact_mod_cast h2, htau r, ht⟩
-- @node: ass:prop-lip-ate-bounded
/-- For [two causal models](hyp:M,Mhat) and [a common bound](hyp:K),
[common boundedness](goal) requires [the first model's observed and non-Gumbel latent
coordinates to be almost surely bounded in absolute value by this positive bound](step:1)
and [the same boundedness for the second model](step:2). -/
def AllVariablesNormBounded (M Mhat : EuclideanSCM kind dims) (K : ℝ) : Prop :=
  VariablesBoundedAt M K ∧ VariablesBoundedAt Mhat K
-- @node: ass:prop-lip-ate-no-confounding
/-- [The confounding graph](hyp:G) [has no edges between any pair of nodes](goal). -/
def NoHiddenConfounding (G : SimpleGraph (Fin n)) : Prop := ∀ i j, ¬ G.Adj i j

/-- For [a causal model](hyp:M), [a selected node](hyp:T), and [a joint observation](hyp:v),
[the parent-value vector](goal) collects all coordinates of that node's parents,
with the sum-of-absolute-values norm. -/
def parentValues (M : EuclideanSCM kind dims) (T : Fin n) (v : Joint kind) :
    WithLp 1 ((Σ p : {p // p ∈ M.dag.parents T}, Fin (valueDim (kind p))) → ℝ) :=
  WithLp.toLp 1 (fun ⟨p,j⟩ => v.ofLp ⟨p.val,j⟩)
/-- For [a causal model](hyp:M) and [a selected node](hyp:T), [the parent space](goal)
is the real coordinate space of that node's parents, with the sum-of-absolute-values norm. -/
abbrev ParentSpace (M : EuclideanSCM kind dims) (T : Fin n) :=
  WithLp 1 ((Σ p : {p // p ∈ M.dag.parents T}, Fin (valueDim (kind p))) → ℝ)
-- @node: observationalLaw_finite
/-- [The observational distribution of any causal model has finite total mass](goal). -/
lemma observationalLaw_finite (M : EuclideanSCM kind dims) :
    IsFiniteMeasure (observationalLaw M) := by
  let : IsProbabilityMeasure M.latentLaw := M.probability
  unfold observationalLaw interventionalLaw
  exact Measure.isFiniteMeasure_map M.latentLaw
    (intervenedEval M (noIntervention kind).val)
/-- For [a selected node](hyp:T) with [exactly one value coordinate](hyp:hT),
[the scalar node value](goal) extracts that coordinate from [a joint observation](hyp:v). -/
def scalarNode (T : Fin n) (hT : valueDim (kind T) = 1) (v : Joint kind) : ℝ :=
  v.ofLp ⟨T, Fin.cast hT.symm ⟨0, Nat.zero_lt_succ 0⟩⟩
-- @node: ass:pin-fix-19bccf89
/-- For [a causal model](hyp:M), [a treatment node](hyp:T), [a treatment readout](hyp:treatment),
[a fixed reference probability law](hyp:P), and [a proposed conditional density](hyp:p),
[the reference-density condition](goal) requires [the node to be scalar and the readout
to extract its value](step:1), [the readout to be measurable](step:2),
[the density to be measurable](step:3), and [the conditional treatment law given the
parents to equal the reference law weighted by this density for almost every parent vector](step:4). -/
def TreatmentReferenceDensity (M : EuclideanSCM kind dims) (T : Fin n) -- @realizes p_\nu(one measurable conditional density version relative to the fixed treatment law)
    (treatment : Joint kind → ℝ) (P : ProbabilityMeasure ℝ)
    (p : ParentSpace M T × ℝ → ℝ≥0∞) : Prop :=
  letI : IsFiniteMeasure (observationalLaw M) := observationalLaw_finite M
  (∃ hT : valueDim (kind T) = 1, treatment = scalarNode T hT) ∧
    Measurable treatment ∧ Measurable p ∧
    ∀ᵐ x ∂((observationalLaw M).map (parentValues M T)),
      ((observationalLaw M).map (fun v => (parentValues M T v, treatment v))).condKernel x =
        (P : Measure ℝ).withDensity (fun t => p (x,t))
-- @node: ass:prop-lip-ate-overlap
/-- For [a causal model](hyp:M), [a treatment node](hyp:T), [its scalar readout](hyp:treatment),
[a reference probability law](hyp:P), [a conditional density](hyp:p),
[a lower bound](hyp:delta), and [interval endpoints](hyp:t1,t2), [treatment overlap](goal)
requires [a measurable conditional density relative to the reference law](step:1),
[a strictly positive lower bound](step:2), and [that bound to hold at every point
of the closed interval for almost every parent vector](step:3). -/
def TreatmentOverlap (M : EuclideanSCM kind dims) (T : Fin n) -- @realizes t_1(positive lower density bound on the indicated interval for almost every parent vector) -- @realizes t_2(positive lower density bound on the indicated interval for almost every parent vector)
    (treatment : Joint kind → ℝ) (P : ProbabilityMeasure ℝ)
    (p : ParentSpace M T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ) : Prop :=
  TreatmentReferenceDensity M T treatment P p ∧
  0 < delta ∧ -- @realizes \delta(strictly positive overlap lower bound)
    ∀ᵐ x ∂((observationalLaw M).map (parentValues M T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t)
variable {Omega : Type*} [MeasurableSpace Omega]
-- @node: ass:pin-fix-09991de8
/-- Under [the sampling measure](hyp:mu), [the observation arrays](hyp:sample)
[form independent, identically distributed complete observations](goal) from
[the causal model](hyp:M): at every sample size, [the observations are mutually independent](step:1)
and [each is measurable with the model's observational distribution](step:2). -/
def ObservationalSampleIID (mu : Measure Omega) (M : EuclideanSCM kind dims)
    (sample : ∀ r, Fin r → Omega → Joint kind) : Prop :=
  ∀ r, ProbabilityTheory.iIndepFun (sample r) mu ∧
    ∀ i, Measurable (sample r i) ∧ mu.map (sample r i) = observationalLaw M
/-- For [a sampling measure](hyp:mu), [a causal model](hyp:M), and
[complete observation arrays](hyp:sample), [the Fournier--Guillin sampling condition](goal)
requires, at every sample size, [mutual independence of the observations](step:1)
and [measurability of each observation with distribution equal to the model's observational law](step:2).

The cited deviation bound itself remains independent of this model and sample. -/
-- @node: ass:bk-owner-9
def FournierObservationalSampleIID (mu : Measure Omega) (M : EuclideanSCM kind dims)
    (sample : ∀ r, Fin r → Omega → Joint kind) : Prop :=
  ∀ r, ProbabilityTheory.iIndepFun (sample r) mu ∧
    ∀ i, Measurable (sample r i) ∧ mu.map (sample r i) = observationalLaw M

-- @node: ass:pin-fix-91573abf
/-- For [a sampling measure](hyp:mu), [a causal model](hyp:M), and
[complete observation arrays](hyp:sample), [complete independent and identically distributed sampling](goal)
requires, at every sample size, [mutual independence of the observations](step:1)
and [measurability of each observation with distribution equal to the model's observational law](step:2). -/
def ObservationalSampleCompleteIID (mu : Measure Omega) (M : EuclideanSCM kind dims)
    (sample : ∀ r, Fin r → Omega → Joint kind) : Prop :=
  ∀ r, ProbabilityTheory.iIndepFun (sample r) mu ∧
    ∀ i, Measurable (sample r i) ∧ mu.map (sample r i) = observationalLaw M
-- @node: ass:pin-fix-59a01041
/-- For [structural-function classes](hyp:F0N), [generator classes](hyp:F1N),
[simulation sizes](hyp:m), [shared simulation arrays](hyp:draws), and
[a rule assigning simulation arrays to candidate mechanisms and generators](hyp:candidateDraws),
[every admitted candidate at every index receives exactly the shared simulation array](goal). -/
def CommonSimulationDraws {counts : Fin b → ℕ}
    (F0N : ℕ → StructuralClass kind dims dag C) (F1N : ℕ → GeneratorClass dims counts)
    (m : ℕ → ℕ)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (candidateDraws : ∀ r, (∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i))) →
      (∀ j, ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j)) →
        Fin (m r) → Omega → SimulationInput kind counts) : Prop :=
  ∀ r (R : NCMIn kind dims dag G C counts (F0N r) (F1N r)),
    candidateDraws r R.rawStructural R.generator = draws r
-- @node: ass:pin-fix-3b195d8d
/-- Under [a sampling measure](hyp:mu), for [simulation sizes](hyp:m) and
[simulation-input arrays](hyp:draws), [independent and identically distributed simulation](goal)
requires, at every index, [mutual independence of the draws](step:1) and
[each draw to be measurable with the prescribed simulation-input distribution](step:2). -/
def SimulationDrawsIID {counts : Fin b → ℕ} (mu : Measure Omega) (m : ℕ → ℕ)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts) : Prop :=
  ∀ r, ProbabilityTheory.iIndepFun (draws r) mu ∧
    ∀ i, Measurable (draws r i) ∧ mu.map (draws r i) = simulationInputLaw kind counts
-- @node: ass:pin-fix-30413b86
/-- Under [a sampling measure](hyp:mu), for [simulation sizes](hyp:m),
[observation arrays](hyp:sample), and [simulation arrays](hyp:draws),
[the full observation array and the full simulation array are independent at every index](goal). -/
def SimulationIndependentOfSample {counts : Fin b → ℕ} (mu : Measure Omega) (m : ℕ → ℕ)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts) : Prop :=
  ∀ r, ProbabilityTheory.IndepFun (fun w => fun i => sample r i w)
    (fun w => fun i => draws r i w) mu

/-- For [a common nonnegative bound](hyp:K), [an intervention-index domain](hyp:domain),
[an intervention family](hyp:t), [its averaging measure](hyp:muT),
[empirical feasible classes](hyp:empirical), and [a population feasible class](hyp:population),
[boundedness of the optimization classes](goal) requires [every empirical model's observed
and non-Gumbel latent coordinates to be almost surely bounded by the positive common bound](step:1),
[the same coordinate bounds to hold for every population model](step:2), and [category counts and intervention
coordinates on the domain to satisfy that bound, with the averaging measure concentrated on the domain](step:3). -/
-- @node: ass:bk-owner-1
def OptimizationClassBoundedByK (K : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (domain : Set I) (t : I → LawIntervention kind) (muT : Measure I)
    (empirical : ℕ → Set (EuclideanSCM kind dims))
    (population : Set (EuclideanSCM kind dims)) : Prop :=
  (∀ r M, M ∈ empirical r → VariablesBoundedAt M K) ∧
    (∀ M, M ∈ population → VariablesBoundedAt M K) ∧
    populationObjectiveDomain K domain t muT

-- @node: ass:bk-owner-2
/-- For [a common nonnegative bound](hyp:K), [an intervention-index domain](hyp:domain),
[an intervention family](hyp:t), [its averaging measure](hyp:muT),
[empirical feasible classes](hyp:empirical), and [a population feasible class](hyp:population),
[the rate theorem's boundedness condition](goal) requires all feasible models' observed
and non-Gumbel latent coordinates to obey the common positive bound, category counts
and intervention coordinates on the domain to obey it, and the averaging measure
to be concentrated on that domain. -/
def RateOptimizationClassBoundedByK (K : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (domain : Set I) (t : I → LawIntervention kind) (muT : Measure I)
    (empirical : ℕ → Set (EuclideanSCM kind dims))
    (population : Set (EuclideanSCM kind dims)) : Prop :=
  OptimizationClassBoundedByK K domain t muT empirical population

/-- Given [structural-function classes](hyp:F0N), [generator classes](hyp:F1N),
[a magnitude bound](hyp:K), [a Lipschitz bound](hyp:L), [simulation sizes](hyp:m),
[Sinkhorn regularization levels](hyp:lam), [discrepancy tolerances](hyp:alpha),
[observation arrays](hyp:sample), and [simulation arrays](hyp:draws),
[the empirical feasible model classes](goal) contain models admitting a representation
and a sample outcome such that [the representation satisfies the magnitude and Lipschitz restrictions](step:1),
[its simulated empirical law has Sinkhorn divergence from the observed empirical law
at most the tolerance, using uniform weights and the chosen regularization](step:2),
and [the model is the causal model induced by that representation](step:3). -/
def empiricalOptimizationModels {counts : Fin b → ℕ}
    (F0N : ℕ → StructuralClass kind dims dag C) (F1N : ℕ → GeneratorClass dims counts)
    (K L : ℝ≥0) (m : ℕ → ℕ) (lam alpha : ℕ → ℝ)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts) :
    ℕ → Set (EuclideanSCM kind dims) :=
  fun r => {M | ∃ (w : Omega) (R : NCMIn kind dims dag G C counts (F0N r) (F1N r)),
    restrictedCandidate K L R ∧
      sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i w)))
        (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r) ≤ alpha r ∧
      M = R.canonical.toEuclideanSCM}

/-- Relative to [a reference causal model](hyp:base), [a magnitude bound](hyp:K),
and [a Lipschitz bound](hyp:L), [the population feasible model class](goal) consists
of models represented by a canonical causal model such that [its mechanisms belong
to the bounded Lipschitz class](step:1), [each latent-block law gives full mass
to the bounded cube](step:2), [its observational law has zero Wasserstein distance
from the reference law](step:3), and [it induces the model in question](step:4). -/
def populationOptimizationModels (base : CanonicalSCM kind dims dag G C) (K L : ℝ≥0) :
    Set (EuclideanSCM kind dims) :=
  {M | ∃ N : CanonicalSCM kind dims dag G C,
    N ∈ canonicalClass (boundedLipClass K L) ∧
      (∀ j, (N.blockLaw j : Measure _) (boundedCube (dims j) K) = 1) ∧
      wasserstein1 (observationalLaw N.toEuclideanSCM)
        (observationalLaw base.toEuclideanSCM) = 0 ∧ M = N.toEuclideanSCM}

/-- For [a positive structural-input dimension](hyp:hdin) and [a positive latent
dimension](hyp:hdU), [the approximation prefactor times the sum of width raised
to minus one divided by the structural-input dimension, each depth raised to
minus two divided by the latent dimension, and temperature times one minus its
logarithm is bounded above by the positive extended approximation tolerance at every index](goal). -/
-- @node: approximation_rate_le_epsN
lemma approximation_rate_le_epsN (a : ℝ) (din dU : ℕ) (hdin : 0 < din) (hdU : 0 < dU)
    (W0 L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ) :
    a * ((W0 r : ℝ)^(-(1 : ℝ)/din) + (L1 r : ℝ)^(-(2 : ℝ)/dU) +
      (L2 r : ℝ)^(-(2 : ℝ)/dU) + tau r * (1 - Real.log (tau r))) ≤
      epsN a din dU hdin hdU W0 L1 L2 tau r := by
  unfold epsN
  dsimp only
  split_ifs with h
  · exact le_rfl
  · exact (le_of_not_gt h).trans zero_le_one

/-- If [the structural-input dimension is positive](hyp:hdin),
[the latent dimension is positive](hyp:hdU), [the approximation prefactor is positive](hyp:ha),
[every temperature is positive](hyp:htau), and [the consistency growth schedule holds](hyp:h),
[the positive extended approximation tolerance tends to zero](goal). -/
-- @node: consistencyGrowth_epsN_tendsto_zero
lemma consistencyGrowth_epsN_tendsto_zero {dU din : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ}
    (hdin : 0 < din) (hdU : 0 < dU) {a : ℝ} (ha : 0 < a)
    (htau : ∀ r, 0 < tau r)
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    Tendsto (epsN a din dU hdin hdU W0 L1 L2 tau) atTop (𝓝 0) := by
  obtain ⟨hw, ht, _⟩ := consistencyGrowth_width_temperature_bias h
  obtain ⟨h1, h2⟩ := consistencyGrowth_depths_tendsto hdU h
  have htpos : Tendsto tau atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall htau⟩
  have hlog : Tendsto (fun r => tau r * Real.log (tau r)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).comp htpos
  have hgumbel : Tendsto (fun r => tau r * (1 - Real.log (tau r))) atTop (𝓝 0) := by
    simpa only [mul_sub, mul_one, sub_zero] using ht.sub hlog
  have hwerr : Tendsto (fun r => (W0 r : ℝ)^(-(1 : ℝ) / din)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by positivity : 0 < (1 : ℝ) / din)).comp hw
  have h1err : Tendsto (fun r => (L1 r : ℝ)^(-(2 : ℝ) / dU)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by positivity : 0 < (2 : ℝ) / dU)).comp h1
  have h2err : Tendsto (fun r => (L2 r : ℝ)^(-(2 : ℝ) / dU)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by positivity : 0 < (2 : ℝ) / dU)).comp h2
  have hrate := (((hwerr.add h1err).add h2err).add hgumbel).const_mul a
  simp only [zero_add, mul_zero] at hrate
  apply hrate.congr'
  filter_upwards [hw.eventually (eventually_gt_atTop (0 : ℝ)),
    ht.eventually (gt_mem_nhds zero_lt_one)] with r hwr htr
  have hnonneg : 0 ≤ tau r * (1 - Real.log (tau r)) := by
    have hl := Real.log_nonpos (htau r).le htr.le
    exact mul_nonneg (htau r).le (by linarith)
  have hpositive : 0 < a * ((W0 r : ℝ)^(-(1 : ℝ)/din) +
      (L1 r : ℝ)^(-(2 : ℝ)/dU) + (L2 r : ℝ)^(-(2 : ℝ)/dU) +
      tau r * (1 - Real.log (tau r))) := by
    apply mul_pos ha
    have hp := Real.rpow_pos_of_pos hwr (-(1 : ℝ) / din)
    have h1p := Real.rpow_nonneg (Nat.cast_nonneg (L1 r) : (0 : ℝ) ≤ L1 r) (-(2 : ℝ)/dU)
    have h2p := Real.rpow_nonneg (Nat.cast_nonneg (L2 r) : (0 : ℝ) ≤ L2 r) (-(2 : ℝ)/dU)
    linarith
  simp only [epsN]
  rw [if_pos hpositive]

/-- For [a common magnitude bound](hyp:K), [a Lipschitz bound](hyp:L), and
[component dimensions for each latent generator](hyp:dC), assume
[the architecture construction thresholds hold](hyp:ha),
[the architecture factors satisfy the required selection inequalities](hyp:hfactors),
[all temperatures are positive](hyp:htau), [the consistency growth schedule holds](hyp:hgrowth),
[the maximum structural-input dimension is positive](hyp:hdin), and
[the maximum latent-block dimension is positive](hyp:hdU).
[There is a positive approximation prefactor such that, eventually, an admitted
neural representation satisfies the magnitude and Lipschitz restrictions and
has total structural uniform error plus latent-block Wasserstein error bounded
by the positive extended approximation tolerance](goal). -/
-- @node: consistencyGrowth_eventually_parameter_approximation
lemma consistencyGrowth_eventually_parameter_approximation
    (M : CanonicalSCM kind dims dag G C) (K L : ℝ≥0)
    (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
    (a0 a1 a2 c0 c1 c2 : ℕ)
    (ha : ArchitectureConstructionThresholds M K L counts dC a0 a1 a2)
    (hfactors : ArchitectureFactorSelection a0 a1 a2 c0 c1 c2)
    (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (htau : ∀ r, 0 < tau r)
    (hgrowth : ConsistencyGrowthSchedule (maxLatentDim M.toEuclideanSCM) m W0 L1 L2 tau lam)
    (hdin : 0 < maxInDim M.toEuclideanSCM) (hdU : 0 < maxLatentDim M.toEuclideanSCM) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ r in atTop,
      ∃ R : NCMIn kind dims dag G C counts
        (structuralClassN M K L W0 c0 r)
        (generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r),
        restrictedCandidate K L R ∧
        (∑ i, supDistOn (M.domain i (some (-(K : ℝ), K))) (M.f i) (R.canonical.f i)) +
          (∑ j, wasserstein1 (M.blockLaw j : Measure (L1Vec (dims j)))
            (R.canonical.blockLaw j : Measure (L1Vec (dims j)))) ≤
          ENNReal.ofReal (epsN A (maxInDim M.toEuclideanSCM)
            (maxLatentDim M.toEuclideanSCM) hdin hdU W0 L1 L2 tau r) := by
  obtain ⟨_, _, A, hA, B, tau0, htau0, hconstruct⟩ := ha
  refine ⟨A, hA, ?_⟩
  filter_upwards [consistencyGrowth_eventually_construction_budgets hdU htau hgrowth B htau0]
    with r hr
  obtain ⟨R, hR, herr⟩ := hconstruct c0 c1 c2 hfactors
    (W0 r) (L1 r) (L2 r) hr.1 hr.2.1 hr.2.2.1 (tau r) hr.2.2.2.1 hr.2.2.2.2
  exact ⟨R, hR, herr.trans (ENNReal.ofReal_le_ofReal
    (approximation_rate_le_epsN A _ _ hdin hdU W0 L1 L2 tau r))⟩

-- @node: ass:cor-rate-inherited
/-- For [a probability sampling measure](hyp:mu), [a canonical causal model](hyp:M),
[a structural Lipschitz bound](hyp:L), [a common magnitude bound](hyp:K),
[generator component counts](hyp:counts), [simulation sizes](hyp:m),
[structural widths](hyp:W0), [two generator depth schedules](hyp:L1,L2),
[temperatures](hyp:tau), [Sinkhorn regularization levels](hyp:lam),
[component dimensions](hyp:dC), and [three architecture factors](hyp:c0,c1,c2),
with certificates for [quantized latent generation](hyp:hPerekrestenko_of_gate),
[coordinate approximation](hyp:hYarotskyCoordinate_of_gate),
[structural approximation](hyp:hYarotskyStructural_of_gate),
[neural-network packing](hyp:hAnthonyBartlettPacking_of_gate), and
[squared-loss bounds](hyp:hAnthonyBartlettSquaredLoss_of_gate),
[the inherited rate premises](goal) concern [an outcome functional](hyp:F),
[observation arrays](hyp:sample), [simulation arrays](hyp:draws),
[candidate-specific simulation assignments](hyp:candidateDraws),
[a treatment node](hyp:T), [its readout](hyp:treatment), [a reference treatment law](hyp:P),
[a conditional treatment density](hyp:p), [an overlap lower bound](hyp:delta),
[overlap interval endpoints](hyp:t1,t2), [an intervention-index domain](hyp:domain),
[an intervention family](hyp:t), [its averaging measure](hyp:muT), and
[empirical discrepancy tolerances](hyp:alpha): form [the structural network classes
using the adjusted Lipschitz bound](step:1) and [the latent generator classes](step:2),
then require [the structural factor to be positive](step:3),
[the first generator factor to be positive](step:4), [the second generator factor to be positive](step:5),
[existence of latent component sets, a chart Lipschitz bound, architecture construction
premises, positive simulation sizes, temperatures and regularization levels, a consistency
growth schedule, complete independent observations, independent identically distributed
simulation draws, and independence between simulations and observations](step:6),
[the true model's deep-network premises](step:7), [Lipschitz continuous mechanisms](step:8),
[Lipschitz categorical propensities](step:9), [membership in the model's domain Lipschitz class](step:10),
[almost sure boundedness of observed and non-Gumbel latent coordinates](step:11),
[Lipschitz structural mechanisms on their full input domains](step:12),
[uniformly bounded continuous mechanism outputs on those domains](step:13),
[treatment overlap](step:14), [absence of confounding edges](step:15),
[positive temperatures](step:16), [positive regularization levels](step:17),
[positive simulation sizes](step:18), [the consistency growth schedule](step:19),
[complete independent and identically distributed observations](step:20),
[independent and identically distributed simulation draws](step:21),
[independence of simulations from observations](step:22),
[common draws for all candidates](step:23), [a Lipschitz outcome functional](step:24),
[common boundedness of empirical and population optimization classes and intervention coordinates](step:25),
[integrability of both objective levels at the true model](step:26),
[integrability at every restricted empirical representation](step:27),
[integrability throughout the population feasible class](step:28), and
[integrability throughout the closure of the neural parameter sets](step:29). -/
def RatePremisesInherited (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0)
    (counts : Fin b → ℕ) (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (dC : ∀ j, Fin (counts j) → ℕ) (c0 c1 c2 : ℕ)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox)
    (hAnthonyBartlettPacking_of_gate : AnthonyBartlettPacking)
    (hAnthonyBartlettSquaredLoss_of_gate : AnthonyBartlettSquaredLoss)
    (F : Joint kind → ℝ)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (candidateDraws : ∀ r, (∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i))) →
      (∀ j, ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j)) →
      Fin (m r) → Omega → SimulationInput kind counts)
    (T : Fin n) (treatment : Joint kind → ℝ) (P : ProbabilityMeasure ℝ)
    (p : ParentSpace M.toEuclideanSCM T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    {I : Type*} [MeasurableSpace I] (domain : Set I)
    (t : I → LawIntervention kind) (muT : Measure I)
    (alpha : ℕ → ℝ) : Prop :=
  let F0N := fun r => structuralClassN M K (LhatF M.toEuclideanSCM L) W0 c0 r
  let F1N := fun r => generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2 L1 L2 tau r
  0 < c0 ∧ 0 < c1 ∧ 0 < c2 ∧
  (∃ sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)), ∃ Lchart : ℝ≥0,
    ∃ hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart,
    ∃ hm : ∀ r, 0 < m r, ∃ htau : TemperaturesPositive tau, ∃ hlam : ∀ r, 0 < lam r,
    ∃ hgrowth : ConsistencyGrowthSchedule (maxLatentDim M.toEuclideanSCM) m W0 L1 L2 tau lam,
    ∃ hsample : ObservationalSampleCompleteIID mu M.toEuclideanSCM sample,
    SimulationDrawsIID mu m draws ∧ SimulationIndependentOfSample mu m sample draws) ∧
    TrueSCMDeepNNPremises M L ∧
    ContinuousMechanismsLipschitz M.toEuclideanSCM L ∧
    CategoricalPropensityLipschitz M.toEuclideanSCM M.f L ∧
    M ∈ canonicalClass (domainLipClass M L) ∧
    VariablesBoundedAt M.toEuclideanSCM K ∧ TrueStructuralLipschitz M L K ∧
    (∀ i d, kind i = Sum.inl d → ∀ x ∈ M.domain i none, ‖M.f i x‖ ≤ K) ∧ -- @realizes f_i(continuous uniform one-norm output bound on the full structural input domain)
    TreatmentOverlap M.toEuclideanSCM T treatment P p delta t1 t2 ∧
    NoHiddenConfounding G ∧ TemperaturesPositive tau ∧ (∀ r, 0 < lam r) ∧
    (∀ r, 0 < m r) ∧
    ConsistencyGrowthSchedule (maxLatentDim M.toEuclideanSCM) m W0 L1 L2 tau lam ∧
    ObservationalSampleCompleteIID mu M.toEuclideanSCM sample ∧
    SimulationDrawsIID mu m draws ∧ SimulationIndependentOfSample mu m sample draws ∧
    CommonSimulationDraws (G := G) F0N F1N m draws candidateDraws ∧ ObjectiveLipschitz F ∧
    RateOptimizationClassBoundedByK K domain t muT
      (empiricalOptimizationModels (G := G) F0N F1N K (LhatF M.toEuclideanSCM L)
        m lam alpha sample draws)
      (populationOptimizationModels M K (LhatF M.toEuclideanSCM L)) ∧
    TrueObjectiveIntegrable M.toEuclideanSCM t muT F ∧
    (∀ r, EmpiricalObjectiveIntegrable (G := G) (F0N r) (F1N r)
      (restrictedCandidate K (LhatF M.toEuclideanSCM L)) t muT F) ∧
    PopulationObjectiveIntegrable M K (LhatF M.toEuclideanSCM L) t muT F ∧
    ParameterObjectiveIntegrable M
      (consistencyNeuralParameters (G := G) K (LhatF M.toEuclideanSCM L) F0N F1N)
      t muT F

end
end Papers.TbsNeuralCausalPi
