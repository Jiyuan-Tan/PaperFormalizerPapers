module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIV
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAE
/-! Helpers — Selection for adaptive inverse problems. -/
@[expose] public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
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
/-- In [an instrumental-variable model](hyp:V) with [sampling law](hyp:P),
[analysis sample](hyp:sample), and [sample split](hyp:split), the [RDIV selected
penalty](goal) uses [the covariate integration measure](hyp:mu), [estimated density
ratios](hyp:gHat), and [estimated reduced-form responses](hyp:rHat) to evaluate the
calibration discrepancy of [the candidate estimator family](hyp:candidate) at
[sample size](hyp:n) and [sample realization](hyp:ω). It searches [the geometric
grid with ratio ρ](hyp:ρ) for the first discrepancy at most three halves of the
noise budget, formed from [the fitting scale sequence](hyp:δ) and [the calibration
scale sequence](hyp:ν) as fitting scale squared divided by the penalty plus
calibration scale squared, and returns the terminal grid penalty if none qualifies. -/
noncomputable def rdivSelected (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ : ℝ) (δ ν : ℕ → ℝ) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (ω : Ω) : ℝ :=
  selectedPenalty ρ n (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω))
    (rdivNoiseLevel (δ n) (ν n))

/-- In [an instrumental-variable model](hyp:V) with [sampling law](hyp:P),
[analysis sample](hyp:sample), and [sample split](hyp:split), the [TRAE selected
penalty](goal) searches [the geometric grid with ratio ρ](hyp:ρ) at [sample
size](hyp:n) and [sample realization](hyp:ω), using the empirical loss of
[the candidate estimator family](hyp:candidate). It returns the first grid penalty
whose loss is at most three halves of the squared value of [the accuracy
sequence](hyp:δ), or the terminal grid penalty if none qualifies. -/
noncomputable def traeSelected (ρ : ℝ) (δ : ℕ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule) (n : ℕ) (ω : Ω) : ℝ :=
  selectedPenalty ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω)) (traeNoiseLevel (δ n))

/-- In [an instrumental-variable model](hyp:V) with [sampling law](hyp:P),
[analysis sample](hyp:sample), and [sample split](hyp:split), the [iterative RDIV
selected penalty](goal) evaluates the calibration discrepancy using [the covariate
integration measure](hyp:mu), [estimated density ratios](hyp:gHat), and [estimated
reduced-form responses](hyp:rHat) for [the iterate family](hyp:iter) after
[the prescribed number of iterations](hyp:t), at [sample size](hyp:n) and [sample
realization](hyp:ω). It searches [the grid with ratio ρ](hyp:ρ) for the first
discrepancy at most three halves of the noise budget, which is [the propagation
multiplier](hyp:a) times [the fitting scale](hyp:δ) squared divided by the penalty
plus [the calibration scale](hyp:ν) squared, with the terminal penalty as fallback. -/
noncomputable def iterRdivSelected (mu : Measure 𝒳) -- @realizes \lambda_{\mathrm{dp},t}^{\mathrm R}(actual discrepancy search on the terminal RDIV iterate)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ a : ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (n : ℕ) (ω : Ω) : ℝ :=
  selectedPenalty ρ n (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω))
    (iterRdivNoiseLevel a (δ n) (ν n))

/-- In [an instrumental-variable model](hyp:V) with [sampling law](hyp:P),
[analysis sample](hyp:sample), and [sample split](hyp:split), the [iterative TRAE
selected penalty](goal) searches [the grid with ratio ρ](hyp:ρ) using the empirical
loss of [the iterate family](hyp:iter) after [the prescribed number of
iterations](hyp:t), at [sample size](hyp:n) and [sample realization](hyp:ω).
It returns the first penalty whose loss is at most three halves of the iterative
noise level determined by [the propagation multiplier](hyp:b) and [the accuracy
sequence](hyp:δ), or the terminal grid penalty if none qualifies. -/
noncomputable def iterTraeSelected (ρ b : ℝ) (t : ℕ) (δ : ℕ → ℝ) -- @realizes \lambda_{\mathrm{dp},t}^{\mathrm T}(actual discrepancy search on the terminal TRAE iterate)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (n : ℕ) (ω : Ω) : ℝ :=
  selectedPenalty ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (iter n t lam ω))
    (iterTraeNoiseLevel b (δ n))

/-- For [source smoothness β](hyp:β), [fitting accuracy δ](hyp:δ), and [calibration
accuracy ν](hyp:ν), the [RDIV oracle error scale](goal) is fitting accuracy raised
to twice the bias exponent divided by one plus that exponent, plus squared
calibration accuracy; the bias exponent is the smaller of β plus one and two. -/
noncomputable def rdivErrorScale (β δ ν : ℝ) : ℝ := -- @realizes \varepsilon_{n,\beta}(RDIV oracle error scale)
  δ ^ (2 * biasExponent β / (biasExponent β + 1)) + ν ^ 2

/-- For [source smoothness β](hyp:β), [propagation multiplier a](hyp:a), [fitting
accuracy δ](hyp:δ), [calibration accuracy ν](hyp:ν), and [iteration count t](hyp:t),
the [iterative RDIV oracle error scale](goal) is the product of the multiplier and squared fitting
accuracy, raised to the qualification exponent divided by one plus that exponent,
plus squared calibration accuracy. The qualification exponent is the smaller of
β plus one and twice the iteration count. -/
noncomputable def iterRdivErrorScale (β a δ ν : ℝ) (t : ℕ) : ℝ := -- @realizes \varepsilon_{n,t,\beta}^{\mathrm R}(iterative RDIV oracle error scale)
  (a * δ ^ 2) ^ (qualificationExponent β t / (qualificationExponent β t + 1)) + ν ^ 2

variable (ρ ξ B β c₀ CG Cm c a b κδ κν required : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
  (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ) (mu : Measure 𝒳)
  (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (t : ℕ)
-- @node: ass:pin-172
/-- For [an instrumental-variable model](hyp:V), [sampling law](hyp:P), [analysis
sample](hyp:sample), [sample split](hyp:split), [covariate integration measure](hyp:mu),
[true density ratio](hyp:g₀), [estimated density ratios](hyp:gHat), [estimated
reduced-form responses](hyp:rHat), and [candidate estimator family](hyp:candidate),
the [RDIV selection property on an event family](goal) requires that, at every sample
size above the threshold determined by [the outcome envelope](hyp:B), [the specified
events](hyp:events) are [measurable](step:1), [have probability at least one minus
the error budget](step:2) [ξ](hyp:ξ), and [support common RDIV comparisons with some
positive constant](step:3), using [the preliminary density, fitting, and response
error bounds](hyp:δG,δH,δr). At every realization in the event, the discrepancy search
on [the grid with ratio ρ](hyp:ρ), using [the fitting scale sequence](hyp:δ) and [the calibration
scale sequence](hyp:ν),
[accepts within the finite grid, accepts initially in the zero-source
case, and either accepts initially or has a positive index satisfying the adjacent
discrepancy relation](step:4). -/
noncomputable def PinExistLambdaDeepivOnEvent (events : ℕ → Set Ω) : Prop :=
  ∀ n, rdivMinSampleSize B ≤ n →
    MeasurableSet (events n) ∧ 1 - ξ ≤ P.real (events n) ∧
    (∃ C > 0, RDIVComparisonsOn V P sample split mu g₀ gHat rHat
      ρ ξ ν δG δH δr candidate n (events n) C) ∧
    ∀ ω ∈ events n,
      let D := fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
        (candidate n lam ω)
      let A := rdivNoiseLevel (δ n) (ν n)
      let k := discrepancyIndex ρ n D A
      Accepts ρ n D A ∧ k + 1 ≤ terminalIndex ρ n + 1 ∧
      (ZeroSolutionCase V → k = 0) ∧
      (k = 0 ∨ (0 < k ∧ AdjacentDiscrepancyRelation ρ
        (selectedPenalty ρ n D A) D A))

/-- For [an instrumental-variable model](hyp:V), [sampling law](hyp:P), [analysis
sample](hyp:sample), [sample split](hyp:split), [covariate integration measure](hyp:mu),
[true density ratio](hyp:g₀), [estimated density ratios](hyp:gHat), [estimated
reduced-form responses](hyp:rHat), [candidate estimators](hyp:candidate), [grid
ratio](hyp:ρ), [confidence-error budget](hyp:ξ), [source smoothness](hyp:β), [source
witness](hyp:w₀), [fitting and calibration scale sequences](hyp:δ,ν), and [preliminary
density, fitting, and response error bounds](hyp:δG,δH,δr), the [RDIV rate property](goal)
uses [the event from the specified family](hyp:events) [at the fixed sample size](hyp:n)
as [its common event](step:1). It requires [measurability, probability at least one
minus the confidence-error budget, common comparisons and a discrepancy envelope,
and joint error bounds using the constant](step:2) [C](hyp:C): the projected squared
error is bounded by C times the RDIV oracle scale; the squared function error is
bounded by C times the sum of the fitting-scale bias term and the interpolated
oracle scale; this last bound is at most twice C times the interpolated oracle
scale; and both errors are bounded by C times squared fitting accuracy in the
zero-source rate case.

All conclusions hold jointly on this one event at the fixed sample size. -/
noncomputable def RDIVRateOnEvent (events : ℕ → Set Ω) (n : ℕ) (C : ℝ) : Prop :=
  let E := events n
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν δG δH δr candidate n E C ∧
      RDIVDiscrepancyEnvelope V P sample split mu gHat rHat ρ β δ ν w₀ candidate n E C ∧
      ∀ ω ∈ E,
          ‖projCondExpOp V (candidate n (rdivSelected V P sample split mu gHat rHat ρ δ ν candidate n ω) ω - minNormSolution V)‖ ^ 2 ≤ C * (rdivErrorScale β (δ n) (ν n)) ∧
          ‖candidate n (rdivSelected V P sample split mu gHat rHat ρ δ ν candidate n ω) ω - minNormSolution V‖ ^ 2 ≤ C * ((δ n ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) + (rdivErrorScale β (δ n) (ν n)) ^ interpolationExponent β)) ∧
          C * ((δ n ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) + (rdivErrorScale β (δ n) (ν n)) ^ interpolationExponent β)) ≤ (2 * C) * (rdivErrorScale β (δ n) (ν n)) ^ interpolationExponent β ∧
          (ZeroSolutionCaseRate V → ‖projCondExpOp V (candidate n (rdivSelected V P sample split mu gHat rHat ρ δ ν candidate n ω) ω - minNormSolution V)‖ ^ 2 ≤ C * δ n ^ 2 ∧ ‖candidate n (rdivSelected V P sample split mu gHat rHat ρ δ ν candidate n ω) ω - minNormSolution V‖ ^ 2 ≤ C * δ n ^ 2)

/-- For [an instrumental-variable model](hyp:V), [sampling law](hyp:P), [analysis
sample](hyp:sample), [sample split](hyp:split), [covariate integration measure](hyp:mu),
[estimated density ratios](hyp:gHat), [estimated reduced-form responses](hyp:rHat),
[iterate family](hyp:iter), [iteration count](hyp:t), [grid ratio](hyp:ρ), [propagation
multiplier](hyp:a), [fitting and calibration scale sequences](hyp:δ,ν), and
[confidence-error budget](hyp:ξ), the [iterative RDIV selection property](goal)
takes [the event family](hyp:events) [at the fixed sample size](hyp:n) as [the common
event](step:1). It requires [that event to be measurable with probability at least
one minus the confidence-error budget and, on every realization in it, that the
terminal-iterate discrepancy search accepts with iteration count times the number
of searched grid points bounded by iteration count times the full grid size,
accepts initially in the zero-source case, and either accepts initially or satisfies
the adjacent discrepancy relation at a positive index](step:2).

All conclusions hold jointly on this one event at the fixed sample size. -/
noncomputable def IterRDIVSelectionOnEvent (events : ℕ → Set Ω) (n : ℕ) : Prop :=
  let E := events n
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
    let D := fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
      (iter n t lam ω)
    let A := iterRdivNoiseLevel a (δ n) (ν n)
    let k := discrepancyIndex ρ n D A
    Accepts ρ n D A ∧ t * (k + 1) ≤ t * (terminalIndex ρ n + 1) ∧
      (ZeroSolutionCase V → k = 0) ∧
      (k = 0 ∨ (0 < k ∧ AdjacentDiscrepancyRelation ρ
        (selectedPenalty ρ n D A) D A))

-- @node: ass:pin-205
/-- For [an instrumental-variable model](hyp:V), [sampling law](hyp:P), [analysis
sample](hyp:sample), [sample split](hyp:split), [covariate integration measure](hyp:mu),
[estimated density ratios](hyp:gHat), [estimated reduced-form responses](hyp:rHat),
[iterate family](hyp:iter), [iteration count](hyp:t), [grid ratio](hyp:ρ), [propagation
multiplier](hyp:a), [fitting and calibration scale sequences](hyp:δ,ν), and
[confidence-error budget](hyp:ξ), the [existence property for iterative RDIV selection
events](goal) requires that every sample size above the threshold determined by
[the outcome envelope](hyp:B) admit a measurable event of probability at least one
minus the confidence-error budget on which all iterative RDIV selection conclusions
hold, including initial acceptance in the zero-source case. -/
noncomputable def PinExistLambdaIterRdivOnEvent : Prop :=
  ∀ n : ℕ, rdivMinSampleSize B ≤ n → ∃ E : Set Ω,
    IterRDIVSelectionOnEvent (V := V) (P := P) (sample := sample) (split := split)
      (ρ := ρ) (ξ := ξ) (δ := δ) (ν := ν) (mu := mu) (gHat := gHat)
      (rHat := rHat) (iter := iter) (a := a) (t := t) (fun _ => E) n

/-- For [an instrumental-variable model](hyp:V), [sampling law](hyp:P), [analysis
sample](hyp:sample), [sample split](hyp:split), [covariate integration measure](hyp:mu),
[estimated density ratios](hyp:gHat), [estimated reduced-form responses](hyp:rHat),
[iterate family](hyp:iter), [iteration count](hyp:t), [grid ratio](hyp:ρ), [propagation
multiplier](hyp:a), [source smoothness](hyp:β), [fitting and calibration scale
sequences](hyp:δ,ν), and [confidence-error budget](hyp:ξ), the [iterative RDIV rate
property](goal) at [sample size](hyp:n) with [bound constant](hyp:C) C requires an
event that is [measurable](step:1), [has probability at least one minus the
confidence-error budget](step:2), and [jointly bounds the selected terminal
iterate's projected squared error by C times the iterative oracle scale and its
squared function error by C times the sum of the propagated fitting bias term
and the oracle scale raised to β divided by β plus one](step:3).

The event is chosen separately for this fixed sample size. -/
noncomputable def IterRDIVRateOnEvent (n : ℕ) (C : ℝ) : Prop :=
  ∃ E : Set Ω, -- @realizes \mathcal E_{n,t}^{\mathrm{IR}}(measurable error event for the fixed n and prescribed t)
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
          ‖projCondExpOp V (iter n t (iterRdivSelected V P sample split mu gHat rHat ρ a t δ ν iter n ω) ω - minNormSolution V)‖ ^ 2 ≤ C * (iterRdivErrorScale β a (δ n) (ν n) t) ∧
          ‖iter n t (iterRdivSelected V P sample split mu gHat rHat ρ a t δ ν iter n ω) ω - minNormSolution V‖ ^ 2 ≤ C * (((a * δ n ^ 2) ^ ((qualificationExponent β t - 1) / (qualificationExponent β t + 1)) + (iterRdivErrorScale β a (δ n) (ν n) t) ^ (β / (β + 1))))

/-- For [an instrumental-variable model](hyp:V), [sampling law](hyp:P), [analysis
sample](hyp:sample), [sample split](hyp:split), [candidate estimator family](hyp:candidate),
[grid ratio](hyp:ρ), [source smoothness](hyp:β), [source witness](hyp:w₀), [accuracy
sequence](hyp:δ), and [confidence-error budget](hyp:ξ), the [TRAE selection
property](goal) takes [the event family](hyp:events) [at sample size](hyp:n) n as
[the common event](step:1). With [comparison constant](hyp:C) C, it requires
[measurability, probability at least one minus the confidence-error budget, common
TRAE comparisons and a discrepancy envelope, and, on every realization in the event,
acceptance within the finite grid together with either initial acceptance or a
positive acceptance index satisfying the adjacent discrepancy relation](step:2).

All conclusions hold jointly on this one event at the fixed sample size. -/
noncomputable def TRAESelectionOnEvent (events : ℕ → Set Ω) (n : ℕ) (C : ℝ) : Prop :=
  let E := events n
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      TRAEComparisonsOn V P sample split δ n E C ∧
      TRAEDiscrepancyEnvelope V P sample split ρ β δ w₀ candidate n E C ∧ ∀ ω ∈ E,
          Accepts ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω)) (traeNoiseLevel (δ n)) ∧
          discrepancyIndex ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω)) (traeNoiseLevel (δ n)) + 1 ≤ terminalIndex ρ n + 1 ∧
          (discrepancyIndex ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω)) (traeNoiseLevel (δ n)) = 0 ∨
            (0 < discrepancyIndex ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω)) (traeNoiseLevel (δ n)) ∧ AdjacentDiscrepancyRelation ρ (selectedPenalty ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω)) (traeNoiseLevel (δ n))) (fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω)) (traeNoiseLevel (δ n))))

/-- For [an instrumental-variable model](hyp:V), [sampling law](hyp:P), [analysis
sample](hyp:sample), [sample split](hyp:split), [candidate estimator family](hyp:candidate),
[grid ratio](hyp:ρ), [source smoothness](hyp:β), [accuracy sequence](hyp:δ), and
[confidence-error budget](hyp:ξ), the [TRAE rate property](goal) takes [the event
family](hyp:events) [at sample size](hyp:n) n as [the common event](step:1). With
[bound constant](hyp:C) C, it requires [measurability, probability at least one minus
the confidence-error budget, and joint bounds on the selected estimator's projected
squared error by C times squared accuracy and on its squared function error by C
times accuracy raised to twice the source exponent truncated at one divided by
one plus that truncated exponent](step:2).

All conclusions hold jointly on this one event at the fixed sample size. -/
noncomputable def TRAERateOnEvent (events : ℕ → Set Ω) (n : ℕ) (C : ℝ) : Prop :=
  let E := events n
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      ∀ ω ∈ E,
          ‖projCondExpOp V (candidate n (traeSelected V P sample split ρ δ candidate n ω) ω - minNormSolution V)‖ ^ 2 ≤ C * (δ n ^ 2) ∧
          ‖candidate n (traeSelected V P sample split ρ δ candidate n ω) ω - minNormSolution V‖ ^ 2 ≤ C * (δ n ^ (2 * truncatedSource β / (1 + truncatedSource β)))

/-- For [an instrumental-variable model](hyp:V), [sampling law](hyp:P), [analysis
sample](hyp:sample), [sample split](hyp:split), [iterate family](hyp:iter), [iteration
count](hyp:t), [grid ratio](hyp:ρ), [propagation multiplier](hyp:b), [accuracy
sequence](hyp:δ), and [confidence-error budget](hyp:ξ), the [iterative TRAE selection
property](goal) takes [the event family](hyp:events) [at sample size](hyp:n) n as
[the common event](step:1). It requires [measurability, probability at least one
minus the confidence-error budget, and, on every realization in the event, acceptance
of the terminal iterate with iteration count times the number of searched grid
points bounded by iteration count times the full grid size, together with either
initial acceptance or a positive acceptance index satisfying the adjacent
discrepancy relation](step:2).

All conclusions hold jointly on this one event at the fixed sample size. -/
noncomputable def IterTRAESelectionOnEvent (events : ℕ → Set Ω) (n : ℕ) : Prop :=
  let E := events n
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
          Accepts ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (iter n t lam ω)) (iterTraeNoiseLevel b (δ n)) ∧
          t * (discrepancyIndex ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (iter n t lam ω)) (iterTraeNoiseLevel b (δ n)) + 1) ≤ t * (terminalIndex ρ n + 1) ∧
          (discrepancyIndex ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (iter n t lam ω)) (iterTraeNoiseLevel b (δ n)) = 0 ∨
            (0 < discrepancyIndex ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (iter n t lam ω)) (iterTraeNoiseLevel b (δ n)) ∧ AdjacentDiscrepancyRelation ρ (selectedPenalty ρ n (fun lam => traeEmpiricalLoss V P sample split n ω (iter n t lam ω)) (iterTraeNoiseLevel b (δ n))) (fun lam => traeEmpiricalLoss V P sample split n ω (iter n t lam ω)) (iterTraeNoiseLevel b (δ n))))

end Papers.TsAdaptiveEstimationInference
