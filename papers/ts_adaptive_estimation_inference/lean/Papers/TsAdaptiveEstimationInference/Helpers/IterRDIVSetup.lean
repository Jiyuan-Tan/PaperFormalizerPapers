module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSetup
public import Papers.TsAdaptiveEstimationInference.Helpers.IterBias
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVConcentration
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVSquaredLoss
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVLoss
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVFitting
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVJointFitting
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVBounded
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRadius
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVPilotStability
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVFinalCalibration
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVCalibratedEvent
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVAcceptance
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVFixedCenter
public import Mathlib.Analysis.Asymptotics.Defs
/-! Iterative RDIV scales, oracle domains, and recursive estimator assumptions.

Here δG, δH and δr denote raw confidence-parametric curves. Every calibration
wrapper at the prescribed positive t is definitionally RDIVIterationScaleCalibration
for rdivEvaluatedAccuracy δG/δH/δr with the fixed rdivPublicLogScale floor, by
rdivScaleCalibration_iff_public. In IterRDIVComparisonsOn the raw H value at
iterGridConfidence ρ ξ n t/4 is precisely the same public H value at η_(n,t).
The local stability proof constructs the preliminary, iteration-grid and final
calibration event using these budgets and preserves that event downstream. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  {pilotInputSupport : Set 𝒵}
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- For [a terminal propagation multiplier a](hyp:a), [the multiplier-domain
condition is that a is at least one](goal). -/
def IterRdivMultiplierDomain (a : ℝ) : Prop :=
  1 ≤ a -- @realizes a_t(deterministic multiplier bounded below by 1)
  -- @realizes s_{n,t}^{\mathrm R}(nonnegative multiplier domain)

/-- For [a propagation multiplier](hyp:a) and [an accuracy level](hyp:δ),
[the iterative RDIV scale is the multiplier times accuracy squared](goal). -/
noncomputable def iterRdivScale (a δ : ℝ) : ℝ :=
  a * δ ^ 2 -- @realizes s_{n,t}^{\mathrm R}(multiplier times the squared accuracy)

-- @node: def:iter-rdiv-scales
/-- For [a propagation multiplier](hyp:a), [an accuracy level](hyp:δ),
[a noise level](hyp:ν), and [a penalty](hyp:lam), [the iterative RDIV noise
budget is the multiplier times accuracy squared divided by the penalty,
plus noise squared](goal). -/
noncomputable def iterRdivNoiseLevel (a : ℝ) -- @realizes a_t(deterministic propagation multiplier)
    (δ ν lam : ℝ) : ℝ := iterRdivScale a δ / lam + ν ^ 2 -- @realizes A_{n,t}^{\mathrm R}(iterative RDIV noise level)
/-- For [a propagation multiplier](hyp:a), [an accuracy level](hyp:δ), and
[a penalty](hyp:lam), [the iterative RDIV stability scale is the multiplier
times accuracy squared divided by penalty squared](goal). -/
noncomputable def iterRdivStability (a δ lam : ℝ) : ℝ := iterRdivScale a δ / lam ^ 2 -- @realizes V_{n,t}^{\mathrm R}(iterative RDIV variance scale)

/-- In [an instrumental-variable model](hyp:V), with [a sampling law](hyp:P),
[an analysis sample](hyp:sample), [a sample split](hyp:split), [a covariate
integration measure](hyp:mu), [estimated density ratios](hyp:gHat), [a sample
size](hyp:n), [a positive horizon](hyp:t), and [a positive penalty](hyp:lam),
[the iterative RDIV recursion pairs the population iterate sequence with
the predicate requiring zero initialization and empirical minimizing steps
for the RDIV loss and fitting-block squared distance](goal). -/
-- @node: def:iter-population
noncomputable def iterativeRecursion (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (n : ℕ)
    (t : {j : ℕ // 1 ≤ j}) (lam : {r : ℝ // 0 < r}) :
    (ℕ → V.Hbar.toSubmodule) × ((ℕ → Ω → V.Hbar.toSubmodule) → Prop) :=
  genericIterativeRecursion V (rdivEmpiricalLoss V P sample split mu gHat n)
    (primalEmpDistanceSq V P sample split n) t lam
    -- @realizes h_{j,\lambda}^*(zero-initialized population recursion)
    -- @realizes \hat h_{j,\lambda}(actual RDIV empirical loss and fitting squared distance)

/-- In [an instrumental-variable model](hyp:V), for [a sampling law](hyp:P),
[an analysis sample](hyp:sample), [a sample split](hyp:split), [a covariate
integration measure](hyp:mu), [estimated density ratios](hyp:gHat), [a sample
size](hyp:n), [a horizon](hyp:t), [a penalty](hyp:lam), and [a candidate iterate
sequence](hyp:candidate), [being an iterative RDIV estimator means starting
at zero and minimizing the penalized empirical RDIV loss at every step
through the horizon](goal). -/
noncomputable def IsIterRDIVEstimator (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (n t : ℕ) (lam : ℝ)
    (candidate : ℕ → Ω → V.Hbar.toSubmodule) : Prop :=
  IsEmpiricalIterate V (rdivEmpiricalLoss V P sample split mu gHat n)
    (primalEmpDistanceSq V P sample split n) candidate t lam

/-- For [a radius constant](hyp:c), [a propagation multiplier](hyp:a), [a source
exponent](hyp:β), [an iteration horizon](hyp:t), [an accuracy curve](hyp:δ),
[a noise curve](hyp:ν), and [a sample size](hyp:n), [the oracle radius is the
radius constant times the larger of the inflated squared accuracy raised to
the reciprocal of one plus the qualification exponent and the noise raised
to twice the reciprocal of the qualification exponent](goal). -/
noncomputable def iterRdivOracleRadius (c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ) (n : ℕ) : ℝ :=
  c * max ((a * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))
    (ν n ^ (2 / qualificationExponent β t))

-- @node: def:iter-rdiv-oracle-point
/-- For [a grid ratio](hyp:ρ), [a radius constant](hyp:c), [a propagation
multiplier](hyp:a), [a source exponent](hyp:β), [a horizon](hyp:t), [an accuracy
curve](hyp:δ), [a noise curve](hyp:ν), and [a sample size](hyp:n), [the iterative
RDIV oracle point is the grid oracle point associated with the oracle radius](goal). -/
noncomputable def iterRdivOraclePoint (ρ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ) (n : ℕ) : ℝ := -- @realizes \lambda_{\mathrm{IR}}^\circ(first grid point below the iterative RDIV radius)
  oraclePoint ρ n (iterRdivOracleRadius c a β t δ ν n)

-- @node: ass:iter-realizability-rdiv
/-- For [an instrumental-variable model](hyp:V), [a grid ratio](hyp:ρ), [a radius
constant](hyp:c), [a propagation multiplier](hyp:a), [a source exponent](hyp:β),
[a horizon](hyp:t), [an accuracy curve](hyp:δ), and [a noise curve](hyp:ν),
[iterative RDIV realizability requires every positive-stage population iterate
through the horizon to belong to the hypothesis class at every grid penalty
between the oracle point and two, whenever the terminal grid point is below
the oracle radius](goal). -/
noncomputable def IterRealizableRDIV (ρ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ) : Prop :=
  ∀ n, gridValue ρ (terminalIndex ρ n) ≤ iterRdivOracleRadius c a β t δ ν n →
    ∀ j, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 → populationIterate V lam j ∈ V.H

-- @node: ass:iter-rdiv-minima
/-- For [an instrumental-variable model](hyp:V), [a sampling law](hyp:P),
[an analysis sample](hyp:sample), [a sample split](hyp:split), [a covariate
integration measure](hyp:mu), [estimated density ratios](hyp:gHat), [a grid
ratio](hyp:ρ), [a horizon](hyp:t), and [candidate iterates](hyp:candidate),
[attainment of iterative RDIV minima means that at every positive sample size
and grid penalty](goal), [the candidates form an empirical RDIV iterate
sequence](step:1) and [each stage through the horizon is measurable using only
the preliminary and fitting observations](step:2). -/
noncomputable def IterRDIVMinimaAttained (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (ρ : ℝ) (t : ℕ)
    (candidate : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ lam ∈ regGrid ρ n,
    IsIterRDIVEstimator V P sample split mu gHat n t lam (fun j => candidate n j lam) ∧
    ∀ j, j ≤ t →
      (@Measurable Ω V.Hbar.toSubmodule
        (⨆ i ∈ split.pre n ∪ split.fit n,
          MeasurableSpace.comap (sample.Z i) inferInstance)
        (borel _) (candidate n j lam)) -- @realizes \hat h_{j,\lambda}(preliminary/fitting-block measurable selected iterate)

-- @node: ass:iter-rdiv-rate-comparable-noise
/-- For [an accuracy curve](hyp:δ) and [a noise curve](hyp:ν), [comparable noise
means that the absolute noise is eventually bounded by a fixed constant times
the absolute accuracy](goal). -/
def ComparableNoise (δ ν : ℕ → ℝ) : Prop := Asymptotics.IsBigO atTop ν δ

-- @node: ass:iter-rdiv-rate-qualification
/-- For [a source exponent β](hyp:β) and [an iteration horizon](hyp:t), [RDIV
qualification means that β + 1 is at most twice the horizon](goal). -/
def IterQualificationRDIV (β : ℝ) (t : ℕ) : Prop := β + 1 ≤ 2 * (t : ℝ)

/-- For [an instrumental-variable model](hyp:V), [a grid ratio](hyp:ρ), [a radius
constant](hyp:c), [a propagation multiplier](hyp:a), [a source exponent](hyp:β),
[a horizon](hyp:t), [an accuracy curve](hyp:δ), [a noise curve](hyp:ν), and
[a sample size](hyp:n), [the zero-case oracle-segment condition says that a
zero minimum-norm solution implies the terminal grid point is no larger than
the oracle radius](goal). -/
noncomputable def IterRDIVZeroCaseOracleSegment (ρ c a β : ℝ) (t : ℕ)
    (δ ν : ℕ → ℝ) (n : ℕ) : Prop :=
  minNormSolution V = 0 →
    gridValue ρ (terminalIndex ρ n) ≤ iterRdivOracleRadius c a β t δ ν n

/-- For [a grid ratio](hyp:ρ), [a radius constant](hyp:c), [a propagation
multiplier](hyp:a), [a source exponent](hyp:β), [a horizon](hyp:t), [an accuracy
curve](hyp:δ), [a noise curve](hyp:ν), and [a sample size](hyp:n), [the stability
oracle segment exists when the terminal grid point is at most the oracle radius](goal). -/
noncomputable def IterRDIVOracleSegmentStability (ρ c a β : ℝ) (t : ℕ)
    (δ ν : ℕ → ℝ) (n : ℕ) : Prop :=
  gridValue ρ (terminalIndex ρ n) ≤ iterRdivOracleRadius c a β t δ ν n

/-- [The discrepancy oracle-segment condition is the stability oracle-segment
condition: the terminal grid point is at most the oracle radius](goal). -/
noncomputable def IterRDIVOracleSegmentDiscrepancy := IterRDIVOracleSegmentStability

/-- [The accepted oracle-segment condition is the stability oracle-segment
condition: the terminal grid point is at most the oracle radius](goal). -/
noncomputable def IterRDIVOracleSegmentAccepted := IterRDIVOracleSegmentStability

-- @node: def:iter-rdiv-oracle-scales
/-- For [a grid ratio](hyp:ρ), [a radius constant](hyp:c), [a propagation
multiplier](hyp:a), [a source exponent](hyp:β), [a horizon](hyp:t), [an accuracy
curve](hyp:δ), and [a noise curve](hyp:ν), [the oracle-scale condition requires
one positive constant such that eventually](goal) [the noise budget at the
oracle point is at most that constant times the sum of inflated accuracy
squared to the power q/(q + 1) and noise squared](step:1), and [the stability
scale there is at most that constant times inflated accuracy squared to the
power (q − 1)/(q + 1)](step:2), where q is the qualification exponent. -/
noncomputable def IterRDIVOracleScales (ρ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ n in atTop,
    iterRdivNoiseLevel a (δ n) (ν n) (iterRdivOraclePoint ρ c a β t δ ν n) ≤
      C * ((a * δ n ^ 2) ^ (qualificationExponent β t / (qualificationExponent β t + 1)) +
        ν n ^ 2) ∧
    iterRdivStability a (δ n) (iterRdivOraclePoint ρ c a β t δ ν n) ≤
      C * (a * δ n ^ 2) ^ ((qualificationExponent β t - 1) / (qualificationExponent β t + 1))

/-- In [an instrumental-variable model](hyp:V), with [a sampling law](hyp:P),
[an analysis sample](hyp:sample), [a sample split](hyp:split), [a covariate
integration measure](hyp:mu), [estimated density ratios](hyp:gHat), [estimated
reduced-form regressions](hyp:rHat), [a grid ratio](hyp:ρ), [a radius constant](hyp:c),
[a propagation multiplier](hyp:a), [a source exponent](hyp:β), [a horizon](hyp:t),
[an accuracy curve](hyp:δ), [a noise curve](hyp:ν), [a source element](hyp:w₀),
[candidate iterates](hyp:candidate), [a sample size](hyp:n), [an event](hyp:E),
and [a discrepancy constant C](hyp:C), [the discrepancy condition requires](goal)
[C to be positive](step:1) and [on the event, every grid penalty from the
oracle point to two to give a terminal calibration statistic at most its noise
budget plus C times the source norm squared times the penalty raised to the
qualification exponent](step:2). -/
noncomputable def IterRDIVDiscrepancyOn (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ) (w₀ : V.Hbar.toSubmodule)
    (candidate : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  0 < C ∧ ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
    lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
    rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n t lam ω) ≤
      iterRdivNoiseLevel a (δ n) (ν n) lam + C * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t

/-- In [an instrumental-variable model](hyp:V), with [a sampling law](hyp:P),
[an analysis sample](hyp:sample), [a sample split](hyp:split), [a covariate
integration measure](hyp:mu), [estimated density ratios](hyp:gHat), [estimated
reduced-form regressions](hyp:rHat), [a grid ratio](hyp:ρ), [a failure probability](hyp:ξ),
[a radius constant](hyp:c), [a propagation multiplier](hyp:a), [a source exponent](hyp:β),
[a horizon](hyp:t), [an accuracy curve](hyp:δ), [a noise curve](hyp:ν), [a source
element](hyp:w₀), [candidate iterates](hyp:candidate), [a sample size](hyp:n),
[an event](hyp:E), and [a discrepancy constant](hyp:C), [the discrepancy
envelope requires](goal) [the event to be measurable](step:1), [its probability
to be at least one minus the failure probability](step:2), and [the terminal
calibration statistic to satisfy the oracle-segment discrepancy bound with
a positive discrepancy constant throughout the event](step:3). -/
-- @node: def:iter-rdiv-discrepancy-bound
noncomputable def IterRDIVDiscrepancyEnvelope (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ ξ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ) (w₀ : V.Hbar.toSubmodule)
    (candidate : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
    IterRDIVDiscrepancyOn V P sample split mu gHat rHat
      ρ c a β t δ ν w₀ candidate n E C

/-- In [an instrumental-variable model](hyp:V), with [a sampling law](hyp:P),
[an analysis sample](hyp:sample), [a sample split](hyp:split), [a covariate
integration measure](hyp:mu), [a true density ratio](hyp:g₀), [estimated density
ratios](hyp:gHat), [estimated reduced-form regressions](hyp:rHat), [a failure
probability](hyp:ξ), [raw density, hypothesis, and regression accuracy curves](hyp:δG,δH,δr),
[a grid ratio](hyp:ρ), [a radius constant](hyp:c), [a propagation multiplier](hyp:a),
[a source exponent](hyp:β), [a horizon](hyp:t), [an accuracy curve](hyp:δ),
[a noise curve](hyp:ν), [empirical iterates](hyp:iter), [a sample size](hyp:n),
[an event](hyp:E), and [a comparison constant C](hyp:C), [the concentration
condition requires the following throughout the event](goal): [the preliminary
density and regression bounds hold](step:1); [at every stage through the
horizon and every oracle-segment grid penalty, the fixed-population-center
loss contrast and squared-distance contrast differ from their population
values by at most C times hypothesis accuracy times distance plus C times
hypothesis accuracy squared](step:2); and [the terminal calibration statistic
differs from squared projected error by at most C times noise times projected
error norm plus C times noise squared](step:3). -/
noncomputable def IterRDIVConcentrationOn (mu : Measure 𝒳)
    (g₀ : 𝒳 → 𝒵 → ℝ) (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ξ : ℝ) (δG δH δr : ℕ → ℝ → ℝ) (ρ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  ∀ ω ∈ E,
    RDIVPreliminaryOn V mu g₀ gHat rHat ξ δG δr n ω C ∧
    (∀ j, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
      ∀ h ∈ V.H,
      |blockAverage V P sample (split.fit n)
          (fun w => iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
            iterRdivFixedCenterLoss V mu (gHat n ω) lam j
              (populationIterate V lam j) w) ω -
        ∫ w, iterRdivFixedCenterLoss V mu (gHat n ω) lam j h w -
          iterRdivFixedCenterLoss V mu (gHat n ω) lam j
            (populationIterate V lam j) w ∂V.law| ≤
        C * (δH n (iterGridConfidence ρ ξ n t / 4) *
          ‖h - populationIterate V lam j‖ +
          δH n (iterGridConfidence ρ ξ n t / 4) ^ 2) ∧
      |primalEmpDistanceSq V P sample split n ω h (populationIterate V lam j) -
        ‖h - populationIterate V lam j‖ ^ 2| ≤
        C * (δH n (iterGridConfidence ρ ξ n t / 4) *
          ‖h - populationIterate V lam j‖ +
          δH n (iterGridConfidence ρ ξ n t / 4) ^ 2)) ∧
    ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
      |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) -
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2| ≤
        C * ν n * ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ + C * ν n ^ 2

/-- In [an instrumental-variable model](hyp:V), with [a sampling law](hyp:P),
[an analysis sample](hyp:sample), [a sample split](hyp:split), [a covariate
integration measure](hyp:mu), [a true density ratio](hyp:g₀), [estimated density
ratios](hyp:gHat), [estimated reduced-form regressions](hyp:rHat), [a failure
probability](hyp:ξ), [raw density, hypothesis, and regression accuracy curves](hyp:δG,δH,δr),
[a grid ratio](hyp:ρ), [a radius constant](hyp:c), [a propagation multiplier](hyp:a),
[a source exponent](hyp:β), [a horizon](hyp:t), [an accuracy curve](hyp:δ),
[a noise curve](hyp:ν), [empirical iterates](hyp:iter), [a sample size](hyp:n),
[an event](hyp:E), and [a stability and calibration constant C](hyp:C), [the
comparison condition requires a positive auxiliary data constant making the
following hold throughout the event](goal): [the preliminary bounds hold](step:1);
[fixed-population-center penalized loss contrasts differ between population
and sample by at most the data constant times hypothesis accuracy times
distance plus hypothesis accuracy squared](step:2); [each positive-stage
energy and squared norm error on the oracle grid are bounded by C times
inflated accuracy squared divided by the penalty and penalty squared,
respectively](step:3); and [terminal calibration differs from squared projected
error by at most C times noise times projected error norm plus C times noise
squared](step:4). -/
noncomputable def IterRDIVComparisonsOn (mu : Measure 𝒳)
    (g₀ : 𝒳 → 𝒵 → ℝ) (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ξ : ℝ) (δG δH δr : ℕ → ℝ → ℝ) (ρ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  ∃ Cdata > (0 : ℝ), ∀ ω ∈ E,
    RDIVPreliminaryOn V mu g₀ gHat rHat ξ δG δr n ω Cdata ∧
    (∀ j, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
      ∀ h ∈ V.H,
      |((conditionalPopulationLoss V mu gHat n ω h +
            lam * ‖h - populationIterate V lam (j - 1)‖ ^ 2) -
          (conditionalPopulationLoss V mu gHat n ω (populationIterate V lam j) +
            lam * ‖populationIterate V lam j - populationIterate V lam (j - 1)‖ ^ 2)) -
        ((rdivEmpiricalLoss V P sample split mu gHat n ω h +
            lam * primalEmpDistanceSq V P sample split n ω h
              (populationIterate V lam (j - 1))) -
          (rdivEmpiricalLoss V P sample split mu gHat n ω (populationIterate V lam j) +
            lam * primalEmpDistanceSq V P sample split n ω
              (populationIterate V lam j) (populationIterate V lam (j - 1))))| ≤
      Cdata * (δH n (iterGridConfidence ρ ξ n t / 4) * ‖h - populationIterate V lam j‖ +
        δH n (iterGridConfidence ρ ξ n t / 4) ^ 2)) ∧
    (∀ j, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
      lam * ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 +
        ‖projCondExpOp V (iter n j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          C * a * δ n ^ 2 / lam ∧
      ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 ≤ C * a * δ n ^ 2 / lam ^ 2) ∧
    ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
      |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) -
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2| ≤
      C * ν n * ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ + C * ν n ^ 2

/-- In [an instrumental-variable model](hyp:V), with [a sampling law](hyp:P),
[an analysis sample](hyp:sample), [a sample split](hyp:split), [a covariate
integration measure](hyp:mu), [estimated density ratios](hyp:gHat), [estimated
reduced-form regressions](hyp:rHat), [a grid ratio](hyp:ρ), [a radius constant](hyp:c),
[a source exponent](hyp:β), [a stagewise coefficient sequence](hyp:aSeq),
[a horizon](hyp:t), [an accuracy curve](hyp:δ), [a noise curve](hyp:ν), [empirical
iterates](hyp:iter), [a sample size](hyp:n), [an event](hyp:E), and [a calibration
constant C](hyp:C), [the stability condition requires throughout the event](goal)
[each positive-stage energy and squared norm error on the terminal-coefficient
oracle segment to be bounded by that stage's coefficient times accuracy
squared divided by the penalty and penalty squared, respectively](step:1),
and [terminal calibration to differ from squared projected error by at most
C times noise times projected error norm plus C times noise squared](step:2). -/
noncomputable def IterRDIVStabilityOn (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ c β : ℝ) (aSeq : ℕ → ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  ∀ ω ∈ E,
    (∀ j, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c (aSeq t) β t δ ν n) 2 →
      lam * ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 +
        ‖projCondExpOp V (iter n j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          aSeq j * δ n ^ 2 / lam ∧
      ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 ≤ aSeq j * δ n ^ 2 / lam ^ 2) ∧
    ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c (aSeq t) β t δ ν n) 2 →
      |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) -
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2| ≤
        C * ν n * ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ + C * ν n ^ 2

/-- If [the grid ratio lies in $[1/2,1)$](hyp:hρ), [the radius constant is
positive](hyp:hc), [the propagation multiplier is at least one](hyp:ha),
[the source exponent is positive](hyp:hβ), [the horizon is positive](hyp:ht),
[the failure probability lies strictly between zero and one](hyp:hξ),
[the accuracy and noise curves satisfy RDIV scale calibration for the raw
curves at this horizon](hyp:hCalibration), [both deterministic curves are
nonnegative](hyp:hNonneg), and [all raw accuracy curves are nonnegative at
positive sample sizes and confidence levels strictly between zero and one](hyp:hRates),
then [eventually the terminal grid point is at most the iterative RDIV oracle
radius, so the stability oracle segment exists](goal). -/
-- @node: iterRdivOracleExists
lemma iterRdivOracleExists (ρ c a β ξ : ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (δG δH δr : ℕ → ℝ → ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hc : 0 < c) (ha : 1 ≤ a)
    (hβ : 0 < β) (ht : 1 ≤ t) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hCalibration : RDIVScaleCalibration ρ ξ δ ν δG δH δr t)
    (hNonneg : CalibrationDeterministic δ ν)
    (hRates : ∀ n, 0 < n → ∀ η ∈ Set.Ioo (0 : ℝ) 1,
      0 ≤ δG n η ∧ 0 ≤ δH n η ∧ 0 ≤ δr n η) :
    ∀ᶠ n in atTop, IterRDIVOracleSegmentStability ρ c a β t δ ν n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ qualificationExponent β t := by
    unfold qualificationExponent
    exact le_min (by linarith) (by positivity)
  have hden : 0 < qualificationExponent β t + 1 := by linarith
  have hp : 0 ≤ 1 / (qualificationExponent β t + 1) := by positivity
  have hp1 : 1 / (qualificationExponent β t + 1) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  filter_upwards [eventually_ge_atTop
    (max 1 (max ⌈Real.log 2⌉₊ ⌈1 / (c * Real.log 2)⌉₊))] with n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnlog : Real.log 2 ≤ (n : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast ((le_max_left _ _).trans ((le_max_right _ _).trans hn)))
  have hcn : 1 / (c * Real.log 2) ≤ (n : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hbudget : iterGridConfidence ρ ξ n t / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    have hd : (1 : ℝ) ≤ (t * (terminalIndex ρ n + 1) : ℕ) := by
      have hm := Nat.mul_le_mul ht (Nat.succ_le_succ (Nat.zero_le (terminalIndex ρ n)))
      exact_mod_cast (show 1 ≤ t * (terminalIndex ρ n + 1) by simpa using hm)
    have hd0 : (0 : ℝ) < (t * (terminalIndex ρ n + 1) : ℕ) := by linarith
    unfold iterGridConfidence
    constructor
    · exact div_pos (div_pos hξ.1 hd0) (by norm_num)
    · have hh : ξ / (t * (terminalIndex ρ n + 1) : ℕ) ≤ ξ :=
        (div_le_iff₀ hd0).2 (by nlinarith [hξ.1])
      linarith [hξ.2]
  have hg := (hRates n hn0 (ξ / 4) hquarter).1
  have hh := (hRates n hn0 (iterGridConfidence ρ ξ n t / 4) hbudget).2.1
  have hcal := (hCalibration.2.1 n hn0).1
  change δG n (ξ / 4) + δH n (iterGridConfidence ρ ξ n t / 4) +
    rdivPublicLogScale ρ ξ n ≤ δ n at hcal
  have hfloor : rdivPublicLogScale ρ ξ n ≤ δ n := by linarith only [hg, hh, hcal]
  have hsq : Real.log 2 / n ≤ δ n ^ 2 :=
    (rdiv_public_log_square_floor ρ ξ hρ hξ n hn0).trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) hfloor 2)
  have hbase : Real.log 2 / n ≤ a * δ n ^ 2 := by
    nlinarith [sq_nonneg (δ n)]
  have hradius : c * (Real.log 2 / n) ≤ iterRdivOracleRadius c a β t δ ν n := by
    unfold iterRdivOracleRadius
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply le_trans _ (le_max_left _ _)
    calc
      Real.log 2 / n = (Real.log 2 / n) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log 2 / n) ^ (1 / (qualificationExponent β t + 1)) :=
        Real.rpow_le_rpow_of_exponent_ge (div_pos hlog hnpos)
          ((div_le_one hnpos).2 hnlog) hp1
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hbase hp
  have hsize : 1 ≤ c * Real.log 2 * n := by
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hc hlog)).1 hcn
  change gridValue ρ (terminalIndex ρ n) ≤ iterRdivOracleRadius c a β t δ ν n
  refine (terminalGrid_le ρ hρ n hn0).trans (le_trans ?_ hradius)
  apply (div_le_iff₀ (sq_pos_of_pos hnpos)).2
  have heq : c * (Real.log 2 / n) * (n : ℝ) ^ 2 = c * Real.log 2 * n := by
    field_simp
  rwa [heq]

open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  {pilotInputSupport : Set 𝒵}
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (δG δH δr tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
/-- In [an instrumental-variable model](hyp:V), with [a sampling law](hyp:P),
[an analysis sample](hyp:sample), [a sample split](hyp:split), [a covariate
integration measure](hyp:mu), [estimated density ratios](hyp:gHat), [estimated
reduced-form regressions](hyp:rHat), [a grid ratio](hyp:ρ), [a radius constant](hyp:c),
[a source exponent](hyp:β), [a stagewise coefficient sequence](hyp:aSeq),
[a horizon](hyp:t), [a public accuracy curve](hyp:δ), [a public noise curve](hyp:ν),
[empirical iterates](hyp:iter), [a sample size](hyp:n), [an event](hyp:E),
[a calibration constant C](hyp:C), and [an inflation divisor L](hyp:L),
[the preinflation condition requires throughout the event](goal) [each
positive-stage energy and squared norm error on the public oracle segment
to be bounded by the stage coefficient times squared accuracy divided by L
squared, further divided by the penalty and penalty squared, respectively](step:1),
and [terminal calibration to differ from squared projected error by at most
C times noise divided by L times projected error norm plus C times squared
noise divided by L squared](step:2). -/
noncomputable def IterRDIVPreinflationOn (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ c β : ℝ) (aSeq : ℕ → ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C L : ℝ) : Prop :=
  ∀ ω ∈ E,
    (∀ j, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c (aSeq t) β t δ ν n) 2 →
      lam * ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 +
        ‖projCondExpOp V (iter n j lam ω - populationIterate V lam j)‖ ^ 2 ≤
          aSeq j * (δ n / L) ^ 2 / lam ∧
      ‖iter n j lam ω - populationIterate V lam j‖ ^ 2 ≤
        aSeq j * (δ n / L) ^ 2 / lam ^ 2) ∧
    ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c (aSeq t) β t δ ν n) 2 →
      |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) -
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2| ≤
        C * (ν n / L) * ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ +
          C * (ν n / L) ^ 2


end Papers.TsAdaptiveEstimationInference
