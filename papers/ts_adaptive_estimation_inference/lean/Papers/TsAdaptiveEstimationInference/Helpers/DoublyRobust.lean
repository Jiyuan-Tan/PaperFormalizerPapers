module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real
/-! The constructed dual problem, independent evaluation, and inference assumptions. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵)
variable (hTarget : Continuous V.targetFunctional)
variable (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- For [an instrumental-variable model](hyp:V) whose [target functional is continuous](hyp:hTarget),
the [dual model](goal) exchanges the primal and dual closed spaces, covariates,
function classes, realizations, and moment maps, retaining the observation law and outcome. -/
def dualWorld : IVWorld 𝒲 𝒵 𝒳 where
  law := V.law
  probability := V.probability
  xOf := V.zOf
  zOf := V.xOf
  measurable_x := V.measurable_z
  measurable_z := V.measurable_x
  Hbar := V.Qbar
  Qbar := V.Hbar
  Hmeas := V.Qmeas
  Qmeas := V.Hmeas
  primalRealization := V.dualRealization
  dualRealization := V.primalRealization
  primal_measurable := V.dual_measurable
  dual_measurable := V.primal_measurable
  primal_coherent := V.dual_coherent
  dual_coherent := V.primal_coherent
  H := V.Q
  Q := V.H
  F := V.S
  S := V.F
  m := V.mt
  mt := V.m
  measurable_m := V.measurable_mt
  measurable_mt := V.measurable_m
  integrable_m := V.integrable_mt
  integrable_mt := V.integrable_m
  momentFunctional := ⟨V.targetFunctional, hTarget⟩
  targetFunctional := V.momentFunctional.toLinearMap
  momentFunctional_eq := V.targetFunctional_eq
  targetFunctional_eq := V.momentFunctional_eq
  Y := V.Y
  measurable_Y := V.measurable_Y

/-- In [the instrumental-variable model](hyp:V), [continuity of the target functional](hyp:hTarget)
determines its [Riesz representer in the primal closed space](goal): the unique element
whose inner product with any primal function equals that function's target value. -/
noncomputable def targetRepresenter : V.Hbar.toSubmodule := -- @realizes a_0(Riesz representer in the primal closed subspace)
  (InnerProductSpace.toDual ℝ V.Hbar.toSubmodule).symm
    (⟨V.targetFunctional, hTarget⟩ : StrongDual ℝ V.Hbar.toSubmodule)

-- @node: def:dual-problem
/-- For [the instrumental-variable model](hyp:V) with [a continuous target functional](hyp:hTarget),
the [dual minimum-norm solution](goal) is the minimum-norm inverse of the adjoint
conditional-expectation operator at the target's Riesz representer. -/
noncomputable def dualMinNormSolution : V.Qbar.toSubmodule := -- @realizes q_0(minimum-norm inverse of the adjoint)
  minimumNormInverse (adjointOp V) (targetRepresenter V hTarget)

-- @node: dualWorld_operator
/-- If the target functional is continuous, [the conditional-expectation
operator in the exchanged model equals the adjoint operator in the original model](goal). -/
lemma dualWorld_operator : projCondExpOp (dualWorld V hTarget) = adjointOp V := by
  apply ContinuousLinearMap.ext
  intro q
  change V.Qbar.toSubmodule at q
  change (projCondExpOp (dualWorld V hTarget) q : V.Hbar.toSubmodule) = adjointOp V q
  apply ext_inner_right ℝ
  intro h
  change V.Hbar.toSubmodule at h
  calc
    inner ℝ (projCondExpOp (dualWorld V hTarget) q) h =
        inner ℝ (q : Lp ℝ 2 V.law) (h : Lp ℝ 2 V.law) :=
      trae_operator_inner (dualWorld V hTarget) q h
    _ = inner ℝ (h : Lp ℝ 2 V.law) (q : Lp ℝ 2 V.law) := real_inner_comm _ _
    _ = inner ℝ (projCondExpOp V h) q := (trae_operator_inner V h q).symm
    _ = inner ℝ q (projCondExpOp V h) := real_inner_comm _ _
    _ = inner ℝ (adjointOp V q) h :=
      ((projCondExpOp V).adjoint_inner_left h q).symm

-- @node: dualWorld_solution
/-- If the target functional is continuous and [the exchanged moment
equation satisfies the range condition](hyp:hRange), [the exchanged model's
minimum-norm solution equals the dual minimum-norm solution](goal). -/
lemma dualWorld_solution (hRange : RangeCondition (dualWorld V hTarget)) :
    minNormSolution (dualWorld V hTarget) = dualMinNormSolution V hTarget := by
  unfold minNormSolution dualMinNormSolution
  rw [dualWorld_operator]
  rfl

/-- For [the instrumental-variable model](hyp:V), [the sampling law](hyp:P),
[the observation sequence](hyp:sample), and [the sample split](hyp:split), the
[empirical dual adversarial loss](goal) at [sample size](hyp:n), [sample realization](hyp:ω),
and [dual function](hyp:q) is the supremum over primal critics of the fitting-block
average of twice the target moment minus twice the primal-dual product minus the squared primal critic.

The loss uses only the known linear map and supplied representatives. The
extended-real supremum retains +∞ for an unbounded critic objective and −∞
for an empty test class, rather than the real conditional supremum's default. -/
noncomputable def dualEmpiricalLoss (n : ℕ) (ω : Ω) (q : V.Qbar.toSubmodule) : EReal := -- @realizes L_n(dual empirical adversarial loss with the original exchanged representatives)
  ⨆ h : V.S, (blockAverage V P sample (split.fit n)
    (fun w => 2 * V.mt h.1 w -
      2 * dualVersion V q (V.zOf w) * primalVersion V h.1 (V.xOf w) -
      primalVersion V h.1 (V.xOf w) ^ 2) ω : EReal)

/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P),
[observations](hyp:sample), [sample split](hyp:split), [grid ratio](hyp:ρ),
[candidate dual fits indexed by sample size and penalty](hyp:candidate), and
[sample size](hyp:n), the [dual grid minimizer condition](goal) requires, at every
grid penalty, [admissible candidates minimizing the dual empirical loss plus the
penalty times their empirical squared norm](step:1), [measurable candidate fits](step:2),
and [measurable empirical losses for every admissible dual function](step:3). -/
noncomputable def DualTRAEGridMinimizers (ρ : ℝ)
    (candidate : ℕ → ℝ → Ω → V.Qbar.toSubmodule) (n : ℕ) : Prop :=
  ∀ lam ∈ regGrid ρ n,
    (∀ ω, candidate n lam ω ∈ V.Q ∧ ∀ q ∈ V.Q,
      dualEmpiricalLoss V P sample split n ω (candidate n lam ω) +
        (lam * blockAverage V P sample (split.fit n)
          (fun w => dualVersion V (candidate n lam ω) (V.zOf w) ^ 2) ω : EReal) ≤
      dualEmpiricalLoss V P sample split n ω q +
        (lam * blockAverage V P sample (split.fit n)
          (fun w => dualVersion V q (V.zOf w) ^ 2) ω : EReal)) ∧
    (@Measurable Ω V.Qbar.toSubmodule inferInstance (borel _) (candidate n lam)) ∧
    (∀ q ∈ V.Q, Measurable (fun ω => dualEmpiricalLoss V P sample split n ω q))

/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P),
[observations](hyp:sample), [sample split](hyp:split), [grid ratio](hyp:ρ),
[noise-scale sequence](hyp:δ), [candidate dual fits](hyp:candidate), [sample size](hyp:n),
and [sample realization](hyp:ω), the [selected dual penalty](goal) is the first grid
penalty whose empirical dual loss is at most three halves of the squared noise scale,
or the terminal grid penalty if none qualifies; this uses [a decision rule for each
index's discrepancy test](step:1), [a decision rule for existence of a qualifying index](step:2),
and [the grid value at the first qualifying index or the terminal index](step:3). -/
noncomputable def dualSelectedPenalty (ρ : ℝ) (δ : ℕ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Qbar.toSubmodule) (n : ℕ) (ω : Ω) : ℝ :=
  letI : DecidablePred (fun k : ℕ => k ≤ terminalIndex ρ n ∧
    dualEmpiricalLoss V P sample split n ω (candidate n (gridValue ρ k) ω) ≤
      ((3 / 2 : ℝ) * traeNoiseLevel (δ n) (gridValue ρ k) : EReal)) :=
    Classical.decPred _
  letI : Decidable (∃ k, k ≤ terminalIndex ρ n ∧
    dualEmpiricalLoss V P sample split n ω (candidate n (gridValue ρ k) ω) ≤
      ((3 / 2 : ℝ) * traeNoiseLevel (δ n) (gridValue ρ k) : EReal)) :=
    Classical.propDecidable _
  gridValue ρ (if e : ∃ k, k ≤ terminalIndex ρ n ∧
        dualEmpiricalLoss V P sample split n ω (candidate n (gridValue ρ k) ω) ≤
          ((3 / 2 : ℝ) * traeNoiseLevel (δ n) (gridValue ρ k) : EReal)
      then Nat.find e else terminalIndex ρ n)

/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P),
[observations](hyp:sample), [sample split](hyp:split), [grid ratio](hyp:ρ),
[noise-scale sequence](hyp:δ), [candidate dual fits](hyp:candidate), [sample size](hyp:n),
and [sample realization](hyp:ω), the [selected dual estimator](goal) is the candidate
fit evaluated at the discrepancy-selected penalty. -/
noncomputable def dualSelectedEstimator (ρ : ℝ) (δ : ℕ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Qbar.toSubmodule) (n : ℕ) (ω : Ω) :
    V.Qbar.toSubmodule :=
  candidate n (dualSelectedPenalty V P sample split ρ δ candidate n ω) ω
  -- @realizes \hat q(discrepancy-selected dual empirical minimizer)

-- @node: def:dual-estimator
/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P),
[observations](hyp:sample), [sample split](hyp:split), [grid ratio](hyp:ρ),
[noise-scale sequence](hyp:δ), [candidate dual fits](hyp:candidate), [a proposed selected fit](hyp:selected),
and [sample size](hyp:n), the [dual TRAE estimator condition](goal) says that
[the candidates are measurable penalized grid minimizers](step:1) and
[the proposed fit equals their discrepancy-selected estimator](step:2). -/
noncomputable def IsDualTRAEEstimator (ρ : ℝ) (δ : ℕ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Qbar.toSubmodule)
    (selected : Ω → V.Qbar.toSubmodule) (n : ℕ) : Prop :=
  DualTRAEGridMinimizers V P sample split ρ candidate n ∧
  selected = dualSelectedEstimator V P sample split ρ δ candidate n

-- @node: def:dr-estimator
/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P),
[observations](hyp:sample), [sample split](hyp:split), [sample size](hyp:n),
[primal nuisance function](hyp:h), [dual nuisance function](hyp:q), and
[sample realization](hyp:ω), the [doubly robust estimator](goal) is the evaluation-block
average of the target moment plus the dual moment minus the product of the two nuisance functions. -/
noncomputable def drEstimator (n : ℕ) (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) -- @realizes \hat\theta(independent evaluation-block mean of the displayed score)
    (ω : Ω) : ℝ :=
  blockAverage V P sample (split.eval n)
    (fun w => V.mt h w + V.m q w - primalVersion V h (V.xOf w) * dualVersion V q (V.zOf w)) ω

-- @node: def:target
/-- For [the instrumental-variable model](hyp:V), the [population target value](goal)
is the expected target moment evaluated at the primal minimum-norm solution. -/
noncomputable def targetValue : ℝ := ∫ w, V.mt (minNormSolution V) w ∂V.law -- @realizes \theta_0(population expectation at the constructed primal solution)

/-- For [the instrumental-variable model](hyp:V) with [a continuous target functional](hyp:hTarget),
the [centered population score](goal) at [an observation](hyp:w) is the target moment
at the primal solution plus the moment at the dual solution, minus their realized
product and the population target value. -/
noncomputable def centeredScore (w : 𝒲) : ℝ := -- @realizes \psi_0(single centered population score)
  V.mt (minNormSolution V) w + V.m (dualMinNormSolution V hTarget) w -
    primalVersion V (minNormSolution V) (V.xOf w) *
      dualVersion V (dualMinNormSolution V hTarget) (V.zOf w) - targetValue V

/-- For [the instrumental-variable model](hyp:V) with [a continuous target functional](hyp:hTarget),
the [score variance](goal) is the population second moment of the centered population score. -/
noncomputable def scoreVariance : ℝ := ∫ w, centeredScore V hTarget w ^ 2 ∂V.law -- @realizes \sigma_0^2(second moment of the centered score)

-- @node: ass:normality-confidence
/-- A [confidence-level sequence](hyp:ξseq) is a [confidence sequence for these bounds](goal)
when it is [strictly positive at every sample size](step:1), [nonincreasing](step:2),
and [convergent to zero](step:3). -/
def ConfidenceSequence (ξseq : ℕ → ℝ) : Prop :=
  (∀ n, 0 < ξseq n) ∧ Antitone ξseq ∧ Tendsto ξseq atTop (𝓝 0) -- @realizes \xi_n(deterministic positive antitone confidence sequence tending to zero)

-- @node: ass:normality-source-parameters
/-- For [the instrumental-variable model](hyp:V) with [a continuous target functional](hyp:hTarget),
[sampling law](hyp:P), [observations](hyp:sample), [sample split](hyp:split),
[grid ratio](hyp:ρ), [envelope bound](hyp:B), [primal source exponent](hyp:βh),
[dual source exponent](hyp:βq), [primal source witness](hyp:wh), [dual source witness](hyp:wq),
[primal critical-radius bounds](hyp:tildeδh), [dual critical-radius bounds](hyp:tildeδq),
[calibrated noise scales](hyp:δ), [calibrated projected-error scales](hyp:ν),
[base noise scales](hyp:baseδ), [base projected-error scales](hyp:baseν),
[failure-level sequence](hyp:ξseq), [required multiplier threshold](hyp:required),
[population constants for calibration](hyp:c₀,CG,Cm), [multiplier policy](hyp:κ₀),
[primal candidate fits](hyp:hCandidate), and [dual candidate fits](hyp:qCandidate),
the [joint primal-dual TRAE assumptions](goal) first extract [the noise multiplier](step:1)
and [the projected-error multiplier](step:2) from that policy at the population bounds.
They require [the primal range condition](step:3), [the dual range condition](step:4),
[the primal source condition with its witness](step:5), [the dual source condition with its witness](step:6),
[primal solution membership in the hypothesis class](step:7), [dual solution membership in its hypothesis class](step:8),
[primal closeness](step:9), [dual closeness](step:10), [primal mean-square continuity](step:11),
[dual mean-square continuity](step:12), [primal boundedness and process measurability](step:13),
[dual boundedness and process measurability](step:14), [primal critical-radius control](step:15),
[dual critical-radius control](step:16), [measurable primal grid minimizers](step:17),
[measurable dual grid minimizers in the exchanged model](step:18),
[base noise-scale calibration for the primal radii at half the grid-adjusted failure budget](step:19),
[the corresponding calibration for the dual radii](step:20),
[valid calibrated multipliers and scaled base sequences](step:21), and
[nonnegative deterministic calibrated scales](step:22). -/
noncomputable def PrimalDualTRAEHypotheses (ρ B : ℝ)
    (βh : ℝ) -- @realizes \beta_h(primal source exponent, positive in the source clause)
    (βq : ℝ)
    (wh : V.Hbar.toSubmodule) (wq : V.Qbar.toSubmodule)
    (tildeδh tildeδq : ℕ → ℝ → ℝ)
    (δ ν baseδ baseν ξseq : ℕ → ℝ) (required c₀ CG Cm : ℝ)
    (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
    (hCandidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (qCandidate : ℕ → ℝ → Ω → V.Qbar.toSubmodule) : Prop :=
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  RangeCondition V ∧ RangeCondition (dualWorld V hTarget) ∧
  BetaSourceCondition V βh wh ∧ -- @realizes \beta_h(positive source exponent and primal witness)
  BetaSourceCondition (dualWorld V hTarget) βq wq ∧ -- @realizes \beta_q(positive source exponent and dual witness)
  H0MemHypothesisClass V ∧ H0MemHypothesisClass (dualWorld V hTarget) ∧
  ClosenessCondition V ∧ ClosenessCondition (dualWorld V hTarget) ∧
  MeanSquareContinuity V ∧ MeanSquareContinuity (dualWorld V hTarget) ∧
  TRAEBoundedness V B ∧ TRAEBoundedness (dualWorld V hTarget) B ∧
  TRAECriticalRadiusBound V tildeδh ∧ TRAECriticalRadiusBound (dualWorld V hTarget) tildeδq ∧
  TRAEMinimaAttained V P sample split ρ hCandidate ∧
  TRAEMinimaAttained (dualWorld V hTarget) P sample split ρ qCandidate ∧
  TRAEScaleCalibration baseδ tildeδh (fun n => gridConfidence ρ (ξseq n / 2) n) ∧
  TRAEScaleCalibration baseδ tildeδq (fun n => gridConfidence ρ (ξseq n / 2) n) ∧
  CalibratedValidBounds δ ν baseδ baseν κδ κν required ∧
  CalibrationDeterministic δ ν

-- @node: ass:normality-common-scale
/-- Given [a grid ratio](hyp:ρ), [a common noise-scale sequence](hyp:δ),
[a failure-level sequence](hyp:ξseq), [primal critical-radius bounds](hyp:tildeδh),
and [dual critical-radius bounds](hyp:tildeδq), the [common TRAE scale condition](goal)
requires [the common scale to tend to zero and dominate both the primal radius
and the inverse square root of sample size at half the grid-adjusted failure budget](step:1)
and [the same calibration for the dual radius](step:2). -/
noncomputable def CommonTRAEScale (ρ : ℝ) (δ ξseq : ℕ → ℝ)
    (tildeδh tildeδq : ℕ → ℝ → ℝ) : Prop :=
  TRAEScaleCalibration δ tildeδh (fun n => gridConfidence ρ (ξseq n / 2) n) ∧
  TRAEScaleCalibration δ tildeδq (fun n => gridConfidence ρ (ξseq n / 2) n)

-- @node: ass:normality-score-continuity
/-- For [the instrumental-variable model](hyp:V), [a continuity constant](hyp:C),
[a primal exponent](hyp:γh), and [a dual exponent](hyp:γq), the
[score Hölder continuity condition](goal) requires [a positive primal exponent](step:1),
[a positive dual exponent](step:2), [integrable squared target-moment differences
whose expectations are bounded by the constant times the primal distance raised
to the primal exponent, for all admissible primal pairs](step:3), and
[the analogous integrability and bound for dual moment differences and the dual exponent](step:4). -/
def ScoreHolderContinuity (C : ℝ)
    (γh : ℝ) -- @realizes \gamma_h(primal score exponent, positive in its domain clause)
    (γq : ℝ) : Prop :=
  0 < γh ∧ -- @realizes \gamma_h(positive primal score continuity exponent)
  0 < γq ∧ -- @realizes \gamma_q(positive dual score continuity exponent)
  (∀ h₁ ∈ V.H, ∀ h₂ ∈ V.H,
    Integrable (fun w => (V.mt h₁ w - V.mt h₂ w) ^ 2) V.law ∧
    (∫ w, (V.mt h₁ w - V.mt h₂ w) ^ 2 ∂V.law) ≤ C * ‖h₁ - h₂‖ ^ γh) ∧
  ∀ q₁ ∈ V.Q, ∀ q₂ ∈ V.Q,
    Integrable (fun w => (V.m q₁ w - V.m q₂ w) ^ 2) V.law ∧
    (∫ w, (V.m q₁ w - V.m q₂ w) ^ 2 ∂V.law) ≤ C * ‖q₁ - q₂‖ ^ γq

/-- For [a primal source exponent](hyp:βh) and [a dual source exponent](hyp:βq),
the [better source exponent](goal) is their maximum. -/
noncomputable def betterSource (βh βq : ℝ) : ℝ := max βh βq -- @realizes \beta_m(maximum of the two fixed source exponents)
/-- For [a primal source exponent](hyp:βh) and [a dual source exponent](hyp:βq),
the [doubly robust rate exponent](goal) is one plus the smaller of their maximum
and one, divided by two plus four times that same smaller value. -/
noncomputable def drRateExponent (βh βq : ℝ) : ℝ := -- @realizes \alpha_{\mathrm{dr}}(displayed exponent computed from the better source)
  (1 + min (betterSource βh βq) 1) / (2 + 4 * min (betterSource βh βq) 1)

/-- For [a primal source exponent](hyp:βh) and [a dual source exponent](hyp:βq),
the [source domain condition](goal) requires [the primal exponent to be positive](step:1)
and [the dual exponent to be positive](step:2). -/
def DRSourceDomain (βh βq : ℝ) : Prop :=
  0 < βh ∧ 0 < βq -- @realizes \beta_m(positive source inputs to the maximum)
  -- @realizes \alpha_{\mathrm{dr}}(positive source inputs, yielding an exponent strictly below one-half)

-- @node: ass:normality-rate
/-- For [a noise-scale sequence](hyp:δ), [a primal source exponent](hyp:βh),
and [a dual source exponent](hyp:βq), the [doubly robust rate condition](goal)
requires the noise scale to be negligible relative to sample size raised to
the negative doubly robust rate exponent. -/
noncomputable def DoublyRobustRateCondition (δ : ℕ → ℝ) (βh βq : ℝ) : Prop :=
  Asymptotics.IsLittleO atTop δ (fun n : ℕ => (n : ℝ) ^ (-drRateExponent βh βq))

/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P),
[observation sequence](hyp:sample), [sample split](hyp:split), and [sample size](hyp:n),
the [training sigma-field](goal) is generated by all preliminary, fitting, and calibration observations. -/
noncomputable abbrev trainingSigma (n : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ split.pre n ∪ split.fit n ∪ split.cal n,
    MeasurableSpace.comap (sample.Z i) inferInstance

-- @node: ass:normality-independent-evaluation
/-- For [the instrumental-variable model](hyp:V) with [a continuous target functional](hyp:hTarget),
[sampling law](hyp:P), [observations](hyp:sample), [sample split](hyp:split),
[training sigma-fields indexed by sample size](hyp:training), [fitted primal functions](hyp:hhat),
and [fitted dual functions](hyp:qhat), the [independent evaluation condition](goal)
uses [the ambient sigma-field](step:1) and requires, at every sample size,
[training information to be contained in the ambient information](step:2),
[all preliminary, fitting, and calibration observations to be included in training](step:3),
[independence between the whole training sigma-field and the evaluation sigma-field](step:4),
[jointly measurable primal and dual versions that almost surely agree with the fitted
functions both almost everywhere in the covariate laws and at every evaluation observation](step:5),
and [a jointly measurable version of the fitted-minus-population score difference
that almost surely agrees both population-almost-everywhere and at every evaluation observation](step:6).

Training may include independent randomness; independence applies to the whole
training sigma-field even if the fitted outputs are constant. -/
noncomputable def IndependentEvaluationSample
    (training : ℕ → MeasurableSpace Ω)
    (hhat : ℕ → Ω → V.Hbar.toSubmodule) (qhat : ℕ → Ω → V.Qbar.toSubmodule) : Prop :=
  let ambient : MeasurableSpace Ω := inferInstance
  ∀ n, training n ≤ ambient ∧ trainingSigma V P sample split n ≤ training n ∧
    (∀ A B : Set Ω, @MeasurableSet Ω (training n) A →
      @MeasurableSet Ω (⨆ i ∈ split.eval n,
        MeasurableSpace.comap (sample.Z i) inferInstance) B →
      P (A ∩ B) = P A * P B) ∧
    (∃ (hVersion : Ω → 𝒳 → ℝ) (qVersion : Ω → 𝒵 → ℝ),
      @Measurable (Ω × 𝒳) ℝ ((training n).prod inferInstance) inferInstance
        (fun p => hVersion p.1 p.2) ∧
      @Measurable (Ω × 𝒵) ℝ ((training n).prod inferInstance) inferInstance
        (fun p => qVersion p.1 p.2) ∧
      (∀ᵐ ω ∂P,
        hVersion ω =ᵐ[V.law.map V.xOf] primalVersion V (hhat n ω) ∧
        qVersion ω =ᵐ[V.law.map V.zOf] dualVersion V (qhat n ω)) ∧
      (∀ᵐ ω ∂P, ∀ i ∈ split.eval n,
        hVersion ω (V.xOf (sample.Z i ω)) =
          primalVersion V (hhat n ω) (V.xOf (sample.Z i ω)) ∧
        qVersion ω (V.zOf (sample.Z i ω)) =
          dualVersion V (qhat n ω) (V.zOf (sample.Z i ω)))) ∧
    ∃ dVersion : Ω → 𝒲 → ℝ,
      @Measurable (Ω × 𝒲) ℝ ((training n).prod inferInstance) inferInstance
        (Function.uncurry dVersion) ∧
      let score := fun (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) (w : 𝒲) =>
        V.mt h w + V.m q w - primalVersion V h (V.xOf w) * dualVersion V q (V.zOf w)
      let d := fun ω w => score (hhat n ω) (qhat n ω) w -
        score (minNormSolution V) (dualMinNormSolution V hTarget) w
      (∀ᵐ ω ∂P, dVersion ω =ᵐ[V.law] d ω) ∧
      (∀ᵐ ω ∂P, ∀ i ∈ split.eval n, dVersion ω (sample.Z i ω) = d ω (sample.Z i ω))

-- @node: drEstimator_congr_evaluation
/-- At [sample size](hyp:n), for [a fitted primal function](hyp:hhat), [a fitted dual function](hyp:qhat),
[a primal evaluation version](hyp:hVersion), and [a dual evaluation version](hyp:qVersion),
if [both versions almost surely agree with the fitted representatives at every
evaluation observation](hyp:hAgreement), [replacing the representatives by these
versions leaves the doubly robust evaluation estimator unchanged almost surely](goal). -/
lemma drEstimator_congr_evaluation (n : ℕ)
    (hhat : Ω → V.Hbar.toSubmodule) (qhat : Ω → V.Qbar.toSubmodule)
    (hVersion : Ω → 𝒳 → ℝ) (qVersion : Ω → 𝒵 → ℝ)
    (hAgreement : ∀ᵐ ω ∂P, ∀ i ∈ split.eval n,
      hVersion ω (V.xOf (sample.Z i ω)) =
        primalVersion V (hhat ω) (V.xOf (sample.Z i ω)) ∧
      qVersion ω (V.zOf (sample.Z i ω)) =
        dualVersion V (qhat ω) (V.zOf (sample.Z i ω))) :
    (fun ω => drEstimator V P sample split n (hhat ω) (qhat ω) ω) =ᵐ[P]
      (fun ω => blockAverage V P sample (split.eval n)
        (fun w => V.mt (hhat ω) w + V.m (qhat ω) w -
          hVersion ω (V.xOf w) * qVersion ω (V.zOf w)) ω) := by
  filter_upwards [hAgreement] with ω hω
  unfold drEstimator blockAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [(hω i hi).1, (hω i hi).2]

-- @node: ass:normality-variance
/-- For [the instrumental-variable model](hyp:V) with [a continuous target functional](hyp:hTarget),
the [positive score variance condition](goal) requires [a square-integrable centered
population score](step:1) and [a strictly positive population second moment](step:2). -/
def ScoreVariancePositive : Prop :=
  MemLp (centeredScore V hTarget) 2 V.law ∧
  0 < scoreVariance V hTarget -- @realizes \sigma_0^2(strictly positive finite second moment)

-- @node: drScore
/-- For [the instrumental-variable model](hyp:V), [a primal function](hyp:h),
[a dual function](hyp:q), and [an observation](hyp:w), the [uncentered doubly robust score](goal)
is the target moment of the primal function plus the moment of the dual function
minus the product of their realized values. -/
noncomputable def drScore (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule)
    (w : 𝒲) : ℝ :=
  V.mt h w + V.m q w - primalVersion V h (V.xOf w) * dualVersion V q (V.zOf w)

-- @node: dr_primal_memLp
/-- For [a function in the primal closed space](hyp:h), [its chosen representative
evaluated at the primal covariates is square-integrable under the observation law](goal). -/
lemma dr_primal_memLp (h : V.Hbar.toSubmodule) :
    MemLp (fun w => primalVersion V h (V.xOf w)) 2 V.law := by
  exact (memLp_congr_ae (V.primal_coherent h)).2 (Lp.memLp (h : Lp ℝ 2 V.law))

-- @node: dr_dual_memLp
/-- For [a function in the dual closed space](hyp:q), [its chosen representative
evaluated at the dual covariates is square-integrable under the observation law](goal). -/
lemma dr_dual_memLp (q : V.Qbar.toSubmodule) :
    MemLp (fun w => dualVersion V q (V.zOf w)) 2 V.law := by
  exact (memLp_congr_ae (V.dual_coherent q)).2 (Lp.memLp (q : Lp ℝ 2 V.law))

-- @node: dr_product_integrable
/-- For [a primal function](hyp:h) and [a dual function](hyp:q), [the product of
their chosen representatives evaluated at the corresponding covariates is integrable](goal). -/
lemma dr_product_integrable (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) :
    Integrable (fun w => primalVersion V h (V.xOf w) *
      dualVersion V q (V.zOf w)) V.law := by
  exact (dr_primal_memLp V h).integrable_mul (dr_dual_memLp V q)

-- @node: dr_product_mean
/-- For [a primal function](hyp:h) and [a dual function](hyp:q), [the population
mean of the product of their chosen representatives equals the inner product
of the projected conditional expectation of the primal function with the dual function](goal). -/
lemma dr_product_mean (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) :
    (∫ w, primalVersion V h (V.xOf w) * dualVersion V q (V.zOf w) ∂V.law) =
      inner ℝ (projCondExpOp V h) q := by
  rw [trae_operator_inner, L2.inner_def]
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm, Pi.mul_apply,
    primalVersion, dualVersion] using
    integral_congr_ae ((V.primal_coherent h).mul (V.dual_coherent q))

-- @node: drScore_integrable
/-- For [a primal function](hyp:h) and [a dual function](hyp:q), [their doubly
robust score is integrable under the population observation law](goal). -/
lemma drScore_integrable (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) :
    Integrable (drScore V h q) V.law := by
  exact ((V.integrable_mt h).add (V.integrable_m q)).sub
    (dr_product_integrable V h q)

-- @node: dr_dual_moment_mean
/-- If [the primal moment equation satisfies the range condition](hyp:hRange), then
for [any dual function](hyp:q), [its population moment equals its inner product
with the projected conditional expectation of the primal minimum-norm solution](goal). -/
lemma dr_dual_moment_mean (hRange : RangeCondition V) (q : V.Qbar.toSubmodule) :
    (∫ w, V.m q w ∂V.law) = inner ℝ (projCondExpOp V (minNormSolution V)) q := by
  rw [(minNormSolution_spec V hRange).1]
  exact (V.momentFunctional_eq q).symm.trans
    (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := q)
      (y := V.momentFunctional)).symm

-- @node: dr_primal_moment_mean
/-- If the target functional is continuous and [the exchanged moment
equation satisfies the range condition](hyp:hDualRange), then for [any primal function](hyp:h),
[its population target moment equals the inner product of its projected conditional
expectation with the dual minimum-norm solution](goal). -/
lemma dr_primal_moment_mean (hDualRange : RangeCondition (dualWorld V hTarget))
    (h : V.Hbar.toSubmodule) :
    (∫ w, V.mt h w ∂V.law) = inner ℝ (projCondExpOp V h) (dualMinNormSolution V hTarget) := by
  have heq : adjointOp V (dualMinNormSolution V hTarget) = targetRepresenter V hTarget := by
    have hs := (minNormSolution_spec (dualWorld V hTarget) hDualRange).1
    rw [dualWorld_operator, dualWorld_solution V hTarget hDualRange] at hs
    exact hs
  calc
    _ = inner ℝ (targetRepresenter V hTarget) h :=
      (V.targetFunctional_eq h).symm.trans
        (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := h)
          (y := (⟨V.targetFunctional, hTarget⟩ : StrongDual ℝ V.Hbar.toSubmodule))).symm
    _ = inner ℝ (adjointOp V (dualMinNormSolution V hTarget)) h := by rw [heq]
    _ = inner ℝ (dualMinNormSolution V hTarget) (projCondExpOp V h) :=
      (projCondExpOp V).adjoint_inner_left h (dualMinNormSolution V hTarget)
    _ = _ := real_inner_comm _ _

-- @node: drScore_bias_identity
/-- If the target functional is continuous, [the primal range
condition holds](hyp:hRange), and [the dual range condition holds](hyp:hDualRange),
then for [a primal nuisance function](hyp:h) and [a dual nuisance function](hyp:q),
[the mean doubly robust score minus the population target is the negative inner
product of the projected primal error with the dual error, each measured from
its minimum-norm solution](goal). -/
lemma drScore_bias_identity (hRange : RangeCondition V)
    (hDualRange : RangeCondition (dualWorld V hTarget))
    (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) :
    (∫ w, drScore V h q w ∂V.law) - targetValue V =
      -inner ℝ (projCondExpOp V (h - minNormSolution V)) (q - dualMinNormSolution V hTarget) := by
  have hs : (∫ w, drScore V h q w ∂V.law) =
      (∫ w, V.mt h w ∂V.law) + (∫ w, V.m q w ∂V.law) -
        ∫ w, primalVersion V h (V.xOf w) * dualVersion V q (V.zOf w) ∂V.law := by
    unfold drScore
    have hp := dr_product_integrable V h q
    have hh := V.integrable_mt h
    have hq := V.integrable_m q
    integral_linearity
  rw [hs, dr_primal_moment_mean V hTarget hDualRange, dr_dual_moment_mean V hRange,
    dr_product_mean, targetValue, dr_primal_moment_mean V hTarget hDualRange,
    map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
  ring

-- @node: centeredScore_mean_zero
/-- If the target functional is continuous, [the primal range
condition holds](hyp:hRange), and [the dual range condition holds](hyp:hDualRange),
[the centered population score has mean zero](goal). -/
lemma centeredScore_mean_zero (hRange : RangeCondition V)
    (hDualRange : RangeCondition (dualWorld V hTarget)) :
    (∫ w, centeredScore V hTarget w ∂V.law) = 0 := by
  have hs := drScore_bias_identity V hTarget hRange hDualRange
    (minNormSolution V) (dualMinNormSolution V hTarget)
  simp only [sub_self, map_zero, inner_zero_left, neg_zero] at hs
  change (∫ w, drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w -
    targetValue V ∂V.law) = 0
  rw [integral_sub (drScore_integrable V _ _) (integrable_const _)]
  simpa using hs

-- @node: drScore_bias_bounds
/-- If the target functional is continuous, [the primal range
condition holds](hyp:hRange), and [the dual range condition holds](hyp:hDualRange),
then for [a primal nuisance function](hyp:h) and [a dual nuisance function](hyp:q),
[the absolute score bias is bounded both by the primal error norm times the
adjoint-transformed dual error norm and by the dual error norm times the
projected primal error norm](goal).

Both bounds have constant one. Errors are relative to the corresponding minimum-norm solutions. -/
lemma drScore_bias_bounds (hRange : RangeCondition V)
    (hDualRange : RangeCondition (dualWorld V hTarget))
    (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) :
    |(∫ w, drScore V h q w ∂V.law) - targetValue V| ≤
        ‖h - minNormSolution V‖ * ‖adjointOp V (q - dualMinNormSolution V hTarget)‖ ∧
      |(∫ w, drScore V h q w ∂V.law) - targetValue V| ≤
        ‖q - dualMinNormSolution V hTarget‖ * ‖projCondExpOp V (h - minNormSolution V)‖ := by
  rw [drScore_bias_identity V hTarget hRange hDualRange, abs_neg]
  constructor
  · have heq : inner ℝ (projCondExpOp V (h - minNormSolution V))
          (q - dualMinNormSolution V hTarget) =
        inner ℝ (adjointOp V (q - dualMinNormSolution V hTarget)) (h - minNormSolution V) := by
      exact (real_inner_comm _ _).trans
        ((projCondExpOp V).adjoint_inner_left _ _).symm
    rw [heq]
    exact (abs_real_inner_le_norm _ _).trans_eq (mul_comm _ _)
  · exact (abs_real_inner_le_norm _ _).trans_eq (mul_comm _ _)

-- @node: dr_error_product_mean
/-- For [a primal nuisance function](hyp:h) and [a dual nuisance function](hyp:q),
if the target functional is continuous, [the mean product of their
representative errors relative to the minimum-norm solutions equals the inner
product of the projected primal error with the dual error](goal).

This does not require pointwise linearity of the chosen representatives. -/
lemma dr_error_product_mean (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) :
    (∫ w, (primalVersion V h (V.xOf w) -
        primalVersion V (minNormSolution V) (V.xOf w)) *
      (dualVersion V q (V.zOf w) -
        dualVersion V (dualMinNormSolution V hTarget) (V.zOf w)) ∂V.law) =
      inner ℝ (projCondExpOp V (h - minNormSolution V)) (q - dualMinNormSolution V hTarget) := by
  have h₁ := dr_product_integrable V h q
  have h₂ := dr_product_integrable V h (dualMinNormSolution V hTarget)
  have h₃ := dr_product_integrable V (minNormSolution V) q
  have h₄ := dr_product_integrable V (minNormSolution V) (dualMinNormSolution V hTarget)
  simp_rw [sub_mul, mul_sub]
  integral_linearity
  rw [dr_product_mean, dr_product_mean, dr_product_mean, dr_product_mean,
    map_sub, inner_sub_left, inner_sub_right, inner_sub_right]

-- @node: drScore_difference_mean
/-- If the target functional is continuous, [the primal range
condition holds](hyp:hRange), and [the dual range condition holds](hyp:hDualRange),
then for [a primal nuisance function](hyp:h) and [a dual nuisance function](hyp:q),
[the mean difference between their score and the score at the minimum-norm
solutions is the negative mean product of their representative errors](goal). -/
lemma drScore_difference_mean (hRange : RangeCondition V)
    (hDualRange : RangeCondition (dualWorld V hTarget))
    (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) :
    (∫ w, drScore V h q w -
      drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w ∂V.law) =
      -(∫ w, (primalVersion V h (V.xOf w) -
          primalVersion V (minNormSolution V) (V.xOf w)) *
        (dualVersion V q (V.zOf w) -
          dualVersion V (dualMinNormSolution V hTarget) (V.zOf w)) ∂V.law) := by
  rw [integral_sub (drScore_integrable V _ _) (drScore_integrable V _ _),
    dr_error_product_mean]
  have htrue := drScore_bias_identity V hTarget hRange hDualRange
    (minNormSolution V) (dualMinNormSolution V hTarget)
  simp only [sub_self, map_zero, inner_zero_left, neg_zero] at htrue
  rw [sub_eq_zero.mp htrue]
  exact drScore_bias_identity V hTarget hRange hDualRange h q

-- @node: drEstimator_remainder_decomposition
/-- With a continuous target functional, at sample size
that is [strictly positive](hyp:hn), for [a primal nuisance function](hyp:h),
[a dual nuisance function](hyp:q), and [a sample realization](hyp:ω), [the doubly
robust estimator minus the target and the evaluation average of the centered
population score equals the centered evaluation average of the nuisance-score
difference plus its population mean](goal). -/
lemma drEstimator_remainder_decomposition (n : ℕ) (hn : 0 < n)
    (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule) (ω : Ω) :
    drEstimator V P sample split n h q ω - targetValue V -
        blockAverage V P sample (split.eval n) (centeredScore V hTarget) ω =
      (blockAverage V P sample (split.eval n)
        (fun w => drScore V h q w -
          drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w) ω -
        ∫ w, drScore V h q w -
          drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w ∂V.law) +
      ∫ w, drScore V h q w -
        drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w ∂V.law := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (∑ _i ∈ split.eval n, targetValue V) = (n : ℝ) * targetValue V := by
    simp [split.card_eval]
  change blockAverage V P sample (split.eval n) (drScore V h q) ω -
    targetValue V - blockAverage V P sample (split.eval n)
      (fun w => drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w -
        targetValue V) ω = _
  simp only [blockAverage, Finset.sum_sub_distrib, hc, split.card_eval]
  field_simp
  ring


end Papers.TsAdaptiveEstimationInference
