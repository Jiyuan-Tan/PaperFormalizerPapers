module
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedIV
public import Mathlib.Algebra.Order.Floor.Ring
/-! Grid learners, selected-law target and transfer of learner rates. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z) (μ : Measure A)
variable (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
-- @node: def:local-linear-kernel
/-- For [a base kernel](hyp:K), [a bandwidth](hyp:h) [that is positive](hyp:_hh), and
[an evaluation point](hyp:t), the [scaled kernel](goal) evaluates the base kernel at the
point divided by the bandwidth and divides the result by the bandwidth. -/
noncomputable def scaledKernel (K : ℝ → ℝ) (h : ℝ) (_hh : 0 < h) (t : ℝ) := K (t/h) / h
  -- @realizes K_{h_n}(scaled base smoothing kernel)
  -- @realizes K(base smoothing kernel in the connected-instrument estimator)
/-- For [a grid size](hyp:N) [that is positive](hyp:_hN) and [an integer index](hyp:m),
the [grid level](goal) is the index divided by the grid size. -/
noncomputable def gridLevel (N : ℕ) (_hN : 0 < N) (m : ℕ) : ℝ := (m : ℝ) / N
-- @node: def:continuous-learners-clipped-grid
/-- Given [a latent instrumental-variable model](hyp:M) and [raw grid fits](hyp:raw),
the [clipped grid fit](goal) at [sample size](hyp:n), [sample realization](hyp:a),
[grid index](hyp:m), and [covariates](hyp:x) truncates the raw fit to the model's outcome endpoints. -/
noncomputable def clippedGrid (raw : ℕ → A → ℕ → X → ℝ) (n : ℕ) (a : A) (m : ℕ) (x : X) := -- @realizes \widetilde Q(raw grid-fit carrier)
  min M.yMax (max M.yMin (raw n a m x))
  -- @realizes \widetilde Q_m^c(raw grid fit clipped to known outcome endpoints)
/-- For [a model](hyp:M), [raw grid fits](hyp:raw), [grid size](hyp:N),
[sample size](hyp:n), [sample realization](hyp:a), and [covariates](hyp:x), the
[sorted grid](goal) lists the clipped fits at indices one through one less than the grid size
in increasing order. -/
noncomputable def sortedGrid (raw : ℕ → A → ℕ → X → ℝ) (N : ℕ) (n : ℕ) (a : A) (x : X) :=
  ((List.range (N-1)).map (fun i => clippedGrid M raw n a (i+1) x)).mergeSort (· ≤ ·)
-- @node: def:quantile-endpoint-convention
/-- For [a model](hyp:M), [raw quantile fits](hyp:raw), [a grid size](hyp:N)
[that is positive](hyp:hN), [a flag choosing known outcome endpoints](hyp:knownEndpoints),
and [at least two cells when that flag is false](hyp:hInterior), the
[interpolated quantile](goal) at [sample size](hyp:n), [sample realization](hyp:a),
[covariates](hyp:x), and [quantile level](hyp:t) uses [the sorted clipped interior fits](step:1),
[grid values with either known endpoints or the extreme interior fits at the boundaries](step:2),
and [linear interpolation of these grid values](step:3). -/
noncomputable def interpolatedQuantile (raw : ℕ → A → ℕ → X → ℝ) -- @realizes \widehat Q_{1,\underline p\mid x}(sorted clipped grid interpolant with either permitted endpoint convention)
    (N : ℕ) (hN : 0 < N) (knownEndpoints : Bool)
    (hInterior : knownEndpoints = false → 2 ≤ N) (n : ℕ) (a : A) (x : X) (t : ℝ) :=
  let vs := sortedGrid M raw N n a x
  let v := fun m => if m = 0 then (if knownEndpoints then M.yMin else vs.getD 0 M.yMin)
    else if N ≤ m then (if knownEndpoints then M.yMax else vs.getD (N-2) M.yMax)
    else vs.getD (m-1) M.yMin
  interpolate N hN v t

/-- For [a grid size](hyp:N) [that is positive](hyp:_hN), [a quantile function](hyp:Q),
and [a level](hyp:t), the [cell-average quantile](goal) first [selects the cell by rounding
the level times the grid size down, capped at the final cell](step:1), then
[averages the quantile function at the cell's two endpoints](step:2). -/
noncomputable def cellAverageQuantile (N : ℕ) (_hN : 0 < N) (Q : ℝ → ℝ) (t : ℝ) :=
  let m := min (N-1) (Nat.floor (t*N))
  (Q ((m:ℝ)/N) + Q (((m+1:ℕ):ℝ)/N)) / 2
-- @node: ass:pin-39
/-- For [a grid size](hyp:N) [that is positive](hyp:hN), [a quantile function](hyp:Q),
and [a candidate integrated quantile](hyp:C), the [integrated-quantile interpolation
condition](goal) requires [agreement with cumulative grid sums at every grid node](step:1)
and [agreement with their linear interpolant throughout the unit interval](step:2). -/
def IntegratedQuantileInterpolationReading (N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ) (C : ℝ → ℝ) : Prop :=
  (∀ m ≤ N, C ((m:ℝ)/N) = cumulativeGrid N hN Q m) ∧
  (∀ t ∈ Icc (0:ℝ) 1, C t = interpolate N hN (cumulativeGrid N hN Q) t)
-- @node: ass:pin-40
/-- For [two quantile functions](hyp:Q,Q'), [two fitted functions](hyp:fitted,fitted'),
and [a grid size](hyp:N) [of at least two](hyp:_hInterior), the [endpoint-convention
scope condition](goal) requires [that equality of the quantiles on the open unit interval
implies equality of their integrals there](step:1), and [that the fitted functions agree
on the unit interval outside its first and last closed grid cells](step:2). -/
def EndpointConventionScopeReading (Q Q' fitted fitted' : ℝ → ℝ)
    (N : ℕ) (_hInterior : 2 ≤ N) : Prop :=
  ((∀ t ∈ Ioo (0:ℝ) 1, Q t = Q' t) →
    (∫ t in Ioo (0:ℝ) 1, Q t) = ∫ t in Ioo (0:ℝ) 1, Q' t) ∧
  (∀ t ∈ Icc (0:ℝ) 1, t ∉ Icc 0 (N : ℝ)⁻¹ ∪ Icc (1-(N : ℝ)⁻¹) 1 →
    fitted t = fitted' t)
-- @node: ass:pin-42
/-- For [a model](hyp:M) and [raw grid fits](hyp:raw), the [clipped-grid interpretation](goal)
requires every clipped fit to equal the raw fit truncated to the model's outcome endpoints. -/
def ClippedGridSuperscriptReading (raw : ℕ → A → ℕ → X → ℝ) : Prop :=
  ∀ n a m x, clippedGrid M raw n a m x = min M.yMax (max M.yMin (raw n a m x))
-- @node: def:continuous-learners-interior-indices
/-- For [quantile grid sizes](hyp:MQ) [positive at every sample size](hyp:hMQ),
[trimming widths](hyp:eps), and [a sample size](hyp:n), the [interior index set](goal)
contains indices from one through one less than the grid size whose levels lie between
the trimming width and one minus that width, inclusively. -/
noncomputable def interiorIdx (MQ : ℕ → ℕ) (hMQ : ∀ n, 0 < MQ n) (eps : ℕ → ℝ) (n : ℕ) :=
  (Finset.Icc 1 (MQ n-1)).filter (fun m => eps n ≤ gridLevel (MQ n) (hMQ n) m ∧
    gridLevel (MQ n) (hMQ n) m ≤ 1-eps n) -- @realizes \mathcal J_{Q,n}(subset of indices 1 through M_Q-1 satisfying both trimming inequalities)
-- @node: def:continuous-learners-evaluation-indices
/-- For [a policy transformation](hyp:phi), [a propensity function](hyp:p),
[a choice between two indices](hyp:ell), [an instrument value](hyp:z), and
[covariates](hyp:x), the [evaluation index](goal) is the policy-transformed propensity
clamped to the conditional propensity range for the first choice, and the propensity
itself for the second. -/
noncomputable def evalIndex (phi : Z → X → ℝ → ℝ) (p : Z → X → ℝ) (ell : Fin 2) (z : Z) (x : X) := -- @realizes U_\ell(two population target indices) @realizes \hat U_\ell(same index construction on fitted propensities)
  if ell = 0 then clampPolicy p (policyProp phi p) z x else p z x


/-- For [a model](hyp:M), [covariates](hyp:x), and [an index](hyp:t), the
[support projection](goal) truncates the index to the conditional propensity's lower
and upper bounds. -/
noncomputable def supportProjection (x : X) (t : ℝ) := min (pHigh M.prop x) (max (pLow M.prop x) t) -- @realizes \Pi_x(projection onto conditional propensity support)

/-- For [a model](hyp:M) and [covariates](hyp:x), the [support interval](goal) is the
closed interval between the conditional propensity's lower and upper bounds. -/
noncomputable def supportInterval (x : X) := Icc (pLow M.prop x) (pHigh M.prop x) -- @realizes \mathcal S_x(conditional connected propensity support)

-- @node: def:continuous-learners-selected-law
/-- For [a model](hyp:M), [fallback outcome laws supported on its outcome set](hyp:zeroLaw),
[fitted propensities](hyp:pHat), [boundary-window widths](hyp:delta), [a sample size](hyp:n),
[a sample realization](hyp:a), and [covariates](hyp:x), the [selected outcome law](goal)
starts with [the conditional joint law of outcome, treatment, and instrument](step:1),
[restricts it to treated units whose fitted propensity is within the window of its
conditional lower bound](step:2), and [normalizes its outcome marginal, using the boundary
law if the selected mass is zero](step:3). -/
noncomputable def selLaw (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ)
    (n : ℕ) (a : A) (x : X) : Measure ℝ :=
  let joint := condDistrib (fun s => (M.Y s,M.W s,M.Zv s)) M.Xv M.law.toMeasure x
  let selected := joint.restrict {o | o.2.1 = 1 ∧ pHat n a o.2.2 x ≤ pLow (pHat n a) x + delta n}
  if selected univ = 0 then boundaryLaw M zeroLaw x else (selected univ)⁻¹ • selected.map Prod.fst
  -- @realizes \mu^{\mathrm{sel}}_{1,n\mid x}(training-fixed selected population law with zero-probability fallback)
/-- For [a model](hyp:M), [fallback outcome laws supported on its outcome set](hyp:zeroLaw),
[fitted propensities](hyp:pHat), [boundary-window widths](hyp:delta), [a sample size](hyp:n),
[a sample realization](hyp:a), and [covariates](hyp:x), the [selected quantile function](goal)
is the lower generalized inverse of the selected outcome law. -/
noncomputable def selQuantile (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ) (n : ℕ) (a : A) (x : X) :=
  Causalean.Stat.quantile (selLaw M zeroLaw pHat delta n a x)
  -- @realizes Q^{\mathrm{sel}}_{1,n\mid x}(single lower generalized inverse of selected law)
-- @node: ass:pin-41
/-- For [a model](hyp:M), [fallback outcome laws supported on its outcome set](hyp:zeroLaw),
[fitted propensities](hyp:pHat), and [boundary-window widths](hyp:delta), the
[selected lower-inverse condition](goal) requires, at every sample size and realization
and almost every covariate value, that each interior selected quantile be the infimum
of outcome thresholds whose selected probability below the threshold and within the
model's outcome set reaches the quantile level. -/
def SelectedQuantileLowerInverse' (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ) : Prop :=
  ∀ n a, ∀ᵐ x ∂xLaw M, ∀ t ∈ Ioo (0:ℝ) 1, selQuantile M zeroLaw pHat delta n a x t =
    sInf {y : ℝ | t ≤ (selLaw M zeroLaw pHat delta n a x (M.Yset ∩ Iic y)).toReal}
-- @node: ass:pin-55
/-- For [a model](hyp:M), [fallback outcome laws supported on its outcome set](hyp:zeroLaw),
[fitted propensities](hyp:pHat), and [boundary-window widths](hyp:delta), the
[range-restricted selected lower-inverse condition](goal) requires, at every sample size
and realization and almost every covariate value, that each interior selected quantile
be the infimum of thresholds between the outcome endpoints whose selected cumulative
probability reaches the quantile level. -/
def SelectedQuantileLowerInverseOnRange
    (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ) : Prop :=
  ∀ n a, ∀ᵐ x ∂xLaw M, ∀ t ∈ Ioo (0 : ℝ) 1,
    selQuantile M zeroLaw pHat delta n a x t =
      sInf {y : ℝ | y ∈ Icc M.yMin M.yMax ∧
        t ≤ (selLaw M zeroLaw pHat delta n a x (Iic y)).toReal}
/-- For [a model](hyp:M), [fitted propensities](hyp:pHat), [a sample size](hyp:n), and
[a sample realization](hyp:a), the [uniform first-stage error](goal) is the supremum,
over all instrument and covariate pairs, of the absolute fitted propensity error. -/
noncomputable def uniformFirstStageError (pHat : ℕ → A → Z → X → ℝ) (n : ℕ) (a : A) :=
  sSup (range (fun zx : Z × X => |pHat n a zx.1 zx.2 - M.prop zx.1 zx.2|))
-- @node: ass:continuous-learners-first-stage
/-- For [a model](hyp:M), [a sampling measure](hyp:μ), [fitted propensities](hyp:pHat),
and [a rate sequence](hyp:rp), the [uniform first-stage rate condition](goal) requires
the rate to be nonnegative and the supremum propensity error to be bounded in probability
at that rate under the sampling measure. -/
def FirstStageUniformRate (pHat : ℕ → A → Z → X → ℝ) (rp : ℕ → ℝ) : Prop := -- @realizes r_{p,n}(nonnegative uniform first-stage error rate)
  BoundedAtRate μ (uniformFirstStageError M pHat) rp

-- @node: ass:pin-26
/-- For [a model](hyp:M), [fitted propensities](hyp:pHat), and [an error process](hyp:error),
the [supremum-norm interpretation](goal) requires the error at every sample size and
realization to equal the supremum absolute propensity error over all instrument and covariate pairs. -/
def SupNormReading (pHat : ℕ → A → Z → X → ℝ) (error : ℕ → A → ℝ) : Prop :=
  ∀ n a, error n a = sSup (range (fun zx : Z × X => |pHat n a zx.1 zx.2 - M.prop zx.1 zx.2|))
-- @node: ass:continuous-learners-outcome
/-- For [a model](hyp:M), [a sampling measure](hyp:μ), [a policy transformation](hyp:phi),
[fitted propensities](hyp:pHat), [an outcome learner](hyp:gHat), and [a local error rate](hyp:rgloc),
the [outcome-learner rate condition](goal) requires, for each of the two evaluation indices,
the population average absolute difference between the fitted outcome regression at the fitted
index and the target regression at its support projection to be bounded in probability at that
rate, with the rate everywhere nonnegative. -/
def OutcomeLearnerRate (phi : Z → X → ℝ → ℝ) (pHat : ℕ → A → Z → X → ℝ) -- @realizes r_{g,\mathrm{loc},n}(nonnegative rate of the projected-index learner error)
    (gHat : ℕ → A → ℝ → X → ℝ) (rgloc : ℕ → ℝ) : Prop :=
  ∀ ell : Fin 2, BoundedAtRate μ (fun n a => ∫ zx,
    |gHat n a (evalIndex phi (pHat n a) ell zx.1 zx.2) zx.2 -
      g1 M (supportProjection M zx.2 (evalIndex phi (pHat n a) ell zx.1 zx.2)) zx.2| ∂zxLaw M) rgloc

-- @node: ass:pin-27
/-- For [a model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S),
[three sample splits](hyp:I), [a policy transformation](hyp:phi), [fitted propensities](hyp:pHat),
[an outcome learner](hyp:gHat), and [two error processes](hyp:error), the
[outcome-learner conditioning condition](goal) requires [a valid three-way partition](step:1),
[propensity fits measurable from the first split](step:2), [outcome predictions measurable
from the first split and the labeled second split](step:3), and [errors equal to the population
average absolute discrepancies from the target regression at the projected fitted indices](step:4). -/
def OutcomeLearnerConditioningReading (S : ObservedSample M μ)
    (I : Fin 3 → SampleSplit A) (phi : Z → X → ℝ → ℝ)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (error : Fin 2 → ℕ → A → ℝ) : Prop :=
  ThreeWayPartition M μ S I ∧
  TrainingPredictorMeasurable M S (I 0) (fun n a (zx : Z × X) => pHat n a zx.1 zx.2) ∧
  LabeledTrainingPredictorMeasurable M μ S (I 0) (I 1)
    (fun n a (tx : Icc (0 : ℝ) 1 × X) => gHat n a tx.1.val tx.2) ∧
  (∀ ell n a, error ell n a = ∫ zx,
    |gHat n a (evalIndex phi (pHat n a) ell zx.1 zx.2) zx.2 -
      g1 M (supportProjection M zx.2 (evalIndex phi (pHat n a) ell zx.1 zx.2)) zx.2| ∂zxLaw M)
-- @node: ass:continuous-learners-trimming
/-- For [trimming widths](hyp:eps) and [quantile grid sizes](hyp:MQ), the
[trimming-sequence condition](goal) requires [each width to be at least the reciprocal
grid size and strictly less than one half](step:1), and [the widths to converge to zero](step:2). -/
def TrimmingSequence (eps : ℕ → ℝ) (MQ : ℕ → ℕ) : Prop :=
  (∀ n, ((MQ n : ℝ))⁻¹ ≤ eps n ∧ eps n < 1/2) ∧ Tendsto eps atTop (𝓝 0)
  -- @realizes \varepsilon_n(vanishing trimming at least one grid-cell width)
-- @node: ass:continuous-learners-boundary-grid-rate
/-- For [a model](hyp:M), [a sampling measure](hyp:μ), [fallback supported outcome laws](hyp:zeroLaw),
[fitted propensities](hyp:pHat), [boundary-window widths](hyp:delta), [raw quantile fits](hyp:raw),
[quantile grid sizes](hyp:MQ) [positive at every sample size](hyp:hMQ), [trimming widths](hyp:eps),
and [an error rate](hyp:rQ), the [boundary-grid rate condition](goal) requires the sum over trimmed
interior grid points of the covariate-average absolute clipped-quantile error, weighted by the
population lower propensity and divided by the grid size, to be bounded in probability at that
rate, with the rate everywhere nonnegative. -/
def BoundaryGridRate (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ) -- @realizes r_{Q,n}(nonnegative rate of the weighted interior-grid learner error)
    (raw : ℕ → A → ℕ → X → ℝ) (MQ : ℕ → ℕ) (hMQ : ∀ n, 0 < MQ n)
    (eps rQ : ℕ → ℝ) : Prop :=
  BoundedAtRate μ (fun n a => (MQ n : ℝ)⁻¹ *
    ∑ m ∈ interiorIdx MQ hMQ eps n, ∫ x, pLow M.prop x *
      |clippedGrid M raw n a m x - selQuantile M zeroLaw pHat delta n a x (gridLevel (MQ n) (hMQ n) m)| ∂xLaw M) rQ

-- @node: ass:pin-28
/-- For [a model](hyp:M), [a sampling measure](hyp:μ), [fallback supported outcome laws](hyp:zeroLaw),
[an observed sample](hyp:S), [three sample splits](hyp:I), [fitted propensities](hyp:pHat),
[boundary-window widths](hyp:delta), [raw quantile fits](hyp:raw), [quantile grid sizes](hyp:MQ)
[positive at every sample size](hyp:hMQ), [trimming widths](hyp:eps), and [an error process](hyp:error),
the [boundary-grid conditioning condition](goal) requires [a valid three-way partition](step:1),
[propensity fits measurable from the first split](step:2), [each raw grid fit measurable from
the first split and the labeled second split](step:3), and [the error, almost surely at each
sample size, to equal the grid-size-normalized sum of covariate-average clipped-quantile errors
over trimmed indices, weighted by the lower population propensity](step:4). -/
def BoundaryGridConditioningReading (S : ObservedSample M μ)
    (I : Fin 3 → SampleSplit A) (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ)
    (raw : ℕ → A → ℕ → X → ℝ) (MQ : ℕ → ℕ) (hMQ : ∀ n, 0 < MQ n)
    (eps : ℕ → ℝ) (error : ℕ → A → ℝ) : Prop :=
  ThreeWayPartition M μ S I ∧
  TrainingPredictorMeasurable M S (I 0) (fun n a (zx : Z × X) => pHat n a zx.1 zx.2) ∧
  (∀ m, LabeledTrainingPredictorMeasurable M μ S (I 0) (I 1) (fun n a x => raw n a m x)) ∧
  (∀ n, ∀ᵐ a ∂μ, error n a = (MQ n : ℝ)⁻¹ *
    ∑ m ∈ interiorIdx MQ hMQ eps n, ∫ x, pLow M.prop x *
      |clippedGrid M raw n a m x - selQuantile M zeroLaw pHat delta n a x
        (gridLevel (MQ n) (hMQ n) m)| ∂xLaw M)
-- @node: ass:continuous-primitive-rate-policy-lipschitz
/-- For [a policy transformation](hyp:phi) and [a proposed Lipschitz bound](hyp:Lphi),
the [uniform policy Lipschitz condition](goal) requires [a nonnegative bound](step:1)
and [that, at every instrument and covariate value, changing a propensity within the unit
interval changes the policy value by at most the bound times the propensity change](step:2). -/
def PolicyLipschitz (phi : Z → X → ℝ → ℝ) (Lphi : ℝ) : Prop :=
  0 ≤ Lphi ∧ ∀ z x p p', p ∈ Icc (0:ℝ) 1 → p' ∈ Icc (0:ℝ) 1 → -- @realizes L_\phi(one uniform policy Lipschitz constant)
    |phi z x p' - phi z x p| ≤ Lphi * |p'-p|

-- @node: ass:continuous-primitive-rate-split
/-- For [a sampling measure](hyp:μ), [three sample splits](hyp:I), and [three target
proportions](hyp:rho), the [split-proportion condition](goal) requires positive target
proportions strictly between zero and one, split indices among the first sample-size
observations almost surely at each sample size, and almost-sure convergence of each
split's sample fraction to its target. -/
def SplitProportions' (I : Fin 3 → SampleSplit A) (rho : Fin 3 → ℝ) : Prop := SplitProportions μ I rho
-- @node: ass:continuous-primitive-rate-vanishing-tuning
/-- For [a first-stage rate](hyp:rp), [a local outcome rate](hyp:rgloc), [a boundary-quantile
rate](hyp:rQ), [localization widths](hyp:delta), [trimming widths](hyp:eps), and
[quantile grid sizes](hyp:MQ), the [vanishing-tuning condition](goal) requires each of the
five real sequences, and the reciprocal grid sizes, to be [everywhere nonnegative](step:1)
and [converge to zero](step:2). -/
def TuningVanishes (rp rgloc rQ delta eps : ℕ → ℝ) (MQ : ℕ → ℕ) : Prop :=
  ∀ r ∈ ({rp,rgloc,rQ,delta,eps,fun n => (MQ n : ℝ)⁻¹} : Set (ℕ → ℝ)),
    (∀ n, 0 ≤ r n) ∧ Tendsto r atTop (𝓝 0)
/-- For [a quantile level](hyp:tau) and [a residual](hyp:t), the [check loss](goal) is
the residual multiplied by the difference between the quantile level and the indicator
that the residual is negative. -/
noncomputable def checkLoss (tau t : ℝ) := t * (tau - indicator (t < 0))
  -- @realizes \rho_\tau(check-function loss)
/-- For [a model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S),
[a fitting split](hyp:I₁), [fitted propensities](hyp:pHat), [localization widths](hyp:delta),
[a sample size](hyp:n), and [a sample realization](hyp:a), the [localized index set](goal)
retains treated observations in that split whose fitted propensity is no more than the
localization width above its conditional lower bound. -/
noncomputable def localizedIndices (S : ObservedSample M μ) (I₁ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ) (n : ℕ) (a : A) :=
  (I₁ n a).filter (fun i => (S.Z i a).2.2.1 = 1 ∧
    pHat n a (S.Z i a).2.1 (S.Z i a).1 ≤ pLow (pHat n a) (S.Z i a).1 + delta n)
  -- @realizes \mathcal I_{\delta,1}(treated observations in fitted boundary window)
/-- For [a model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S),
[three sample splits](hyp:I), [a policy transformation](hyp:phi), [fitted propensities](hyp:pHat),
[an outcome learner](hyp:gHat), [raw quantile fits](hyp:raw), [regression-grid intercepts](hyp:gGrid),
[regression-grid slopes](hyp:beta), [regression grid sizes](hyp:MG), [quantile grid sizes](hyp:MQ)
[respectively positive at every sample size](hyp:hMG,hMQ), [an endpoint-convention flag](hyp:knownEndpoints),
[at least two quantile cells whenever known endpoints are not used](hyp:hInterior),
[bandwidths](hyp:h) and [localization widths](hyp:delta), [positive bandwidths at every sample
size](hyp:hh), [a kernel](hyp:K), [sample-size-dependent regression classes](hyp:Fn), and
[a fixed quantile regression class](hyp:FQ), the [continuous-learner fitting condition](goal)
requires [positive localization widths](step:1); [a valid three-way partition and the training
measurability, joint measurability, and range conditions for the propensity, regression, and
interpolated quantile, with nondecreasing interior quantiles](step:2); [grid intercepts and
slopes in the regression class jointly minimizing kernel-weighted squared residuals for
outcome times treatment on the second split](step:3); [an outcome learner equal to the linear
interpolant of the intercepts clipped between the smaller of zero and the lower outcome
endpoint and the larger of zero and the upper endpoint](step:4); and [interior raw quantile
fits minimizing check loss in the fixed class on localized treated observations, or equal
to the lower outcome endpoint if that sample is empty](step:5). -/
def ContinuousLearnerFit (S : ObservedSample M μ) (I : Fin 3 → SampleSplit A)
    (phi : Z → X → ℝ → ℝ) (pHat : ℕ → A → Z → X → ℝ)
    (gHat : ℕ → A → ℝ → X → ℝ) (raw gGrid beta : ℕ → A → ℕ → X → ℝ)
    (MG MQ : ℕ → ℕ) (hMG : ∀ n, 0 < MG n) (hMQ : ∀ n, 0 < MQ n) -- @realizes M_g(positive regression grid size) @realizes M_Q(positive quantile grid size)
    (knownEndpoints : Bool) (hInterior : knownEndpoints = false → ∀ n, 2 ≤ MQ n)
    (h delta : ℕ → ℝ) (hh : ∀ n, 0 < h n) (K : ℝ → ℝ) -- @realizes h_n(positive bandwidth) @realizes \delta_n(localization window carrier)
    (Fn : ℕ → Set (X → ℝ)) -- @realizes \mathcal F_n(sample-size-dependent local regression function class)
    (FQ : Set (X → ℝ)) : Prop := -- @realizes \mathcal F_Q(one fixed check-loss regression function class)
  (∀ n, 0 < delta n) ∧ -- @realizes \delta_n(positive localization windows)
  ConnectedFitScope M μ S I pHat gHat
    (fun n a x => interpolatedQuantile M raw (MQ n) (hMQ n) knownEndpoints (fun hk => hInterior hk n) n a x) ∧
  (∀ n a m, m ≤ MG n → gGrid n a m ∈ Fn n ∧ beta n a m ∈ Fn n ∧
    ∀ g ∈ Fn n, ∀ b ∈ Fn n,
      (∑ i ∈ I 1 n a, scaledKernel K (h n) (hh n)
        (pHat n a (S.Z i a).2.1 (S.Z i a).1 - gridLevel (MG n) (hMG n) m) *
        ((S.Z i a).2.2.2 * (S.Z i a).2.2.1 - gGrid n a m (S.Z i a).1 -
          beta n a m (S.Z i a).1 * (pHat n a (S.Z i a).2.1 (S.Z i a).1 - gridLevel (MG n) (hMG n) m))^2) ≤
      ∑ i ∈ I 1 n a, scaledKernel K (h n) (hh n)
        (pHat n a (S.Z i a).2.1 (S.Z i a).1 - gridLevel (MG n) (hMG n) m) *
        ((S.Z i a).2.2.2 * (S.Z i a).2.2.1 - g (S.Z i a).1 -
          b (S.Z i a).1 * (pHat n a (S.Z i a).2.1 (S.Z i a).1 - gridLevel (MG n) (hMG n) m))^2) ∧
  (∀ n a t x, gHat n a t x = min (max 0 M.yMax) (max (min 0 M.yMin)
    (interpolate (MG n) (hMG n) (fun m => gGrid n a m x) t))) ∧
  (∀ n a m, 1 ≤ m → m < MQ n →
    if (localizedIndices M μ S (I 1) pHat delta n a) = ∅ then raw n a m = fun _ => M.yMin
    else raw n a m ∈ FQ ∧ ∀ f ∈ FQ,
      (∑ i ∈ localizedIndices M μ S (I 1) pHat delta n a,
        checkLoss (gridLevel (MQ n) (hMQ n) m) ((S.Z i a).2.2.2 - raw n a m (S.Z i a).1)) ≤
      ∑ i ∈ localizedIndices M μ S (I 1) pHat delta n a,
        checkLoss (gridLevel (MQ n) (hMQ n) m) ((S.Z i a).2.2.2 - f (S.Z i a).1))
  -- @realizes \hat\beta_m(gridwise fitted local-linear slopes)
/-- For [a grid size](hyp:N) [that is positive](hyp:hN) and [an index from zero through
that size](hyp:m), the [regression grid point](goal) is the index divided by the grid size. -/
noncomputable def regressionGridPoint (N : ℕ) (hN : 0 < N) (m : Fin (N+1)) := gridLevel N hN m -- @realizes u_m(regression-grid points indexed by 0 through M_g)

/-- For [a grid size](hyp:N) [of at least two](hyp:hInterior) and [an index at least one
and strictly below that size](hyp:m), the [quantile grid point](goal) is the index divided
by the grid size. -/
noncomputable def quantileGridPoint (N : ℕ) (hInterior : 2 ≤ N)
    (m : {m : ℕ // 1 ≤ m ∧ m < N}) := (m.val : ℝ) / N
  -- @realizes \tau_m(interior quantile-grid points)
-- @node: regression_grid_range
/-- If [the grid size is positive](hyp:hN), then [every regression grid point, including
the two endpoint indices, lies in the closed unit interval](goal). -/
lemma regression_grid_range (N : ℕ) (hN : 0 < N) (m : Fin (N+1)) : -- @realizes u_m(grid-point range [0,1])
    regressionGridPoint N hN m ∈ Icc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  change (m : ℝ) / N ∈ Icc (0 : ℝ) 1
  refine ⟨div_nonneg (by positivity) hNr.le, (div_le_one hNr).mpr ?_⟩
  exact_mod_cast (Nat.le_of_lt_succ m.isLt)

-- @node: quantile_grid_range
/-- If [the grid size is at least two](hyp:hInterior), then for
[any index at least one and strictly below the grid size](hyp:m),
[the corresponding quantile grid point lies in the open unit interval](goal). -/
lemma quantile_grid_range (N : ℕ) (hInterior : 2 ≤ N)
    (m : {m : ℕ // 1 ≤ m ∧ m < N}) : quantileGridPoint N hInterior m ∈ Ioo (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  change (m.val : ℝ) / N ∈ Ioo (0 : ℝ) 1
  refine ⟨div_pos (by exact_mod_cast (show 0 < m.val by omega)) hNr,
    (div_lt_one hNr).mpr ?_⟩
  exact_mod_cast m.property.2
  -- @realizes \tau_m(interior grid-point range (0,1))

-- @node: def:continuous-instrument
/-- For [a model](hyp:M), [a sampling measure](hyp:μ), [an observed sample](hyp:S),
[three sample splits](hyp:I), [a policy transformation](hyp:phi), [fitted propensities](hyp:pHat),
[an outcome learner](hyp:gHat), [raw quantile fits](hyp:raw), [regression-grid intercepts](hyp:gGrid),
[regression-grid slopes](hyp:beta), [regression grid sizes](hyp:MG), [quantile grid sizes](hyp:MQ)
[respectively positive at every sample size](hyp:hMG,hMQ), [an endpoint-convention flag](hyp:knownEndpoints),
[at least two quantile cells when known endpoints are not used](hyp:hInterior),
[bandwidths](hyp:h), [localization widths](hyp:delta), [positive bandwidths at every sample size](hyp:hh),
[a kernel](hyp:K), [sample-size-dependent regression classes](hyp:Fn), [a fixed quantile
regression class](hyp:FQ), and [a first-stage rule using a labeled training view](hyp:firstStage),
the [continuous estimation procedure](goal) constructs [sorted, clipped, interpolated
quantiles](step:1), [their interpolated cumulative trapezoidal sums](step:2), [fitted lower
and upper bound contributions](step:3), and [their means on the third split, using zero
when it is empty](step:4). It [returns these four objects together with the requirement
that the learners satisfy the fitting condition, the policy is a valid policy map, and
the propensity is measurable from the first split and equals the first-stage rule
clipped to the unit interval](step:5). -/
noncomputable def continuousProcedure (S : ObservedSample M μ) (I : Fin 3 → SampleSplit A)
    (phi : Z → X → ℝ → ℝ) (pHat : ℕ → A → Z → X → ℝ)
    (gHat : ℕ → A → ℝ → X → ℝ) (raw gGrid beta : ℕ → A → ℕ → X → ℝ)
    (MG MQ : ℕ → ℕ) (hMG : ∀ n, 0 < MG n) (hMQ : ∀ n, 0 < MQ n)
    (knownEndpoints : Bool) (hInterior : knownEndpoints = false → ∀ n, 2 ≤ MQ n)
    (h delta : ℕ → ℝ) (hh : ∀ n, 0 < h n)
    (K : ℝ → ℝ) (Fn : ℕ → Set (X → ℝ)) (FQ : Set (X → ℝ))
    (firstStage : (n : ℕ) → (Finset ℕ × (Fin n → Unit ⊕ Obs X Z)) → Z → X → ℝ) :=
  let Q := fun n a x => interpolatedQuantile M raw (MQ n) (hMQ n) knownEndpoints (fun hk => hInterior hk n) n a x
  let C := fun n a x => interpCumQuantile (MQ n) (hMQ n) (Q n a x)
  let scores := fun upper n a => fittedInt M upper phi (pHat n a) (gHat n a) (C n a)
  let estimate := fun upper n a => if hSplit : (I 2 n a).Nonempty then
    splitMean M S (I 2) (fun n a => scores upper n a) n a hSplit else 0
  ((ContinuousLearnerFit M μ S I phi pHat gHat raw gGrid beta
      MG MQ hMG hMQ knownEndpoints hInterior h delta hh K Fn FQ ∧
    IsPolicyMap phi ∧
    TrainingPredictorMeasurable M S (I 0)
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2) ∧
    (∀ n a z x, pHat n a z x = min 1 (max 0
      (firstStage n (trainingView M S (I 0) n a) z x)))),
    Q, C, scores, estimate)
  -- @realizes \widehat C(trapezoidal cumulative grid and its linear off-grid interpolation)

-- @node: list_getD_interval
/-- If [the fallback value lies in a given closed interval](hyp:hd) and [every entry
of a list lies in that interval](hyp:hvs), then [looking up any index, using the fallback
when the index is absent, yields a value in the same interval](goal). -/
lemma list_getD_interval (vs : List ℝ) (lo hi d : ℝ) (hd : d ∈ Icc lo hi)
    (hvs : ∀ y ∈ vs, y ∈ Icc lo hi) (m : ℕ) : vs.getD m d ∈ Icc lo hi := by
  induction vs generalizing m with
  | nil => simpa using hd
  | cons y ys ih =>
    cases m with
    | zero => simpa using hvs y (by simp)
    | succ m =>
      simpa using ih (fun z hz => hvs z (by simp [hz])) m

-- @node: interpolate_interval
/-- If [the grid size is positive](hyp:hN) and [all grid values lie in a given closed
interval](hyp:hv), then [their linear interpolant, extended by endpoint values outside
the unit interval, lies in that closed interval at every evaluation point](goal). -/
lemma interpolate_interval (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ) (lo hi : ℝ)
    (hv : ∀ m, v m ∈ Icc lo hi) (t : ℝ) : interpolate N hN v t ∈ Icc lo hi := by
  unfold interpolate
  split_ifs with ht0 ht1
  · exact hv 0
  · exact hv N
  · have htpos : 0 < t := lt_of_not_ge ht0
    have htlt : t < 1 := lt_of_not_ge ht1
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have htn : 0 ≤ t * N := mul_nonneg htpos.le hNr.le
    have hfloor : Nat.floor (t * N) < N :=
      (Nat.floor_lt htn).mpr (by nlinarith)
    have hmin : min (N-1) (Nat.floor (t * N)) = Nat.floor (t * N) :=
      min_eq_right (by omega)
    rw [hmin]
    have ha0 : 0 ≤ t * N - (Nat.floor (t * N) : ℝ) :=
      sub_nonneg.mpr (Nat.floor_le htn)
    have ha1 : t * N - (Nat.floor (t * N) : ℝ) ≤ 1 := by
      linarith [Nat.lt_floor_add_one (t * N)]
    dsimp
    have h0 := hv (Nat.floor (t * N))
    have h1 := hv (Nat.floor (t * N) + 1)
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr h0.1),
        mul_nonneg ha0 (sub_nonneg.mpr h1.1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr h0.2),
        mul_nonneg ha0 (sub_nonneg.mpr h1.2)]

-- @node: interpolated_quantile_range
/-- If [the lower and upper outcome endpoints are respectively the least and greatest
elements of the model's outcome set](hyp:he),
[the grid size is positive](hyp:hN), and [there are at least two grid cells when the
endpoint convention uses extreme interior fits](hyp:hInterior), then [the sorted clipped
quantile interpolant lies between the outcome endpoints at every level, sample size,
sample realization, and covariate value](goal). -/
lemma interpolated_quantile_range (he : OutcomeEndpointsKnown M) -- @realizes \widehat Q_{1,\underline p\mid x}(clipped interpolant range with ordered outcome endpoints)
    (raw : ℕ → A → ℕ → X → ℝ) (N : ℕ) (hN : 0 < N)
    (knownEndpoints : Bool) (hInterior : knownEndpoints = false → 2 ≤ N) (n : ℕ) (a : A) (x : X) (t : ℝ) :
    interpolatedQuantile M raw N hN knownEndpoints hInterior n a x t ∈ Icc M.yMin M.yMax := by
  have horder : M.yMin ≤ M.yMax := he.1.2 he.2.1
  have hlo : M.yMin ∈ Icc M.yMin M.yMax := ⟨le_rfl, horder⟩
  have hhi : M.yMax ∈ Icc M.yMin M.yMax := ⟨horder, le_rfl⟩
  have hvs : ∀ y ∈ sortedGrid M raw N n a x, y ∈ Icc M.yMin M.yMax := by
    intro y hy
    have hmem : y ∈ (List.range (N-1)).map (fun i => clippedGrid M raw n a (i+1) x) :=
      (List.mergeSort_perm _ _).mem_iff.mp hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
    exact ⟨le_min horder (le_max_left _ _), min_le_left _ _⟩
  unfold interpolatedQuantile
  apply interpolate_interval
  intro m
  split_ifs <;> first
    | exact hlo
    | exact hhi
    | exact list_getD_interval _ _ _ _ hlo hvs _
    | exact list_getD_interval _ _ _ _ hhi hvs _

-- @node: support_projection_range
/-- At any covariate value and for any real index, [the conditional propensity support
interval is contained in the closed unit interval, and projecting the index onto that
support yields a point in the support interval](goal). -/
lemma support_projection_range (x : X) (t : ℝ) : -- @realizes \mathcal S_x(population support interval inside [0,1]) @realizes \Pi_x(projection takes values in the population support)
    supportInterval M x ⊆ Icc (0 : ℝ) 1 ∧
    supportProjection M x t ∈ supportInterval M x := by
  have he := propensity_support_endpoints M.prop M.rangeProp x
  constructor
  · intro u hu
    exact ⟨he.1.1.trans hu.1, hu.2.trans he.2.1.2⟩
  · exact ⟨le_min he.2.2 (le_max_left _ _), min_le_left _ _⟩


-- @node: evaluation_indices_range
/-- If [the propensity function takes values in the closed unit interval at every
instrument and covariate value](hyp:hp) and [the policy transformation is jointly
measurable on unit-interval propensities and maps them into the closed unit interval](hyp:hphi),
then [both the policy-transformed propensity clamped to the conditional propensity range
and the original propensity lie in the closed unit interval at every instrument and
covariate value](goal). -/
lemma evaluation_indices_range (phi : Z → X → ℝ → ℝ) (p : Z → X → ℝ) -- @realizes U_\ell(population evaluation-index range [0,1]) @realizes \hat U_\ell(fitted evaluation-index range [0,1])
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1) (hphi : IsPolicyMap phi) :
    ∀ ell z x, evalIndex phi p ell z x ∈ Icc (0 : ℝ) 1 := by
  intro ell z x
  have he := propensity_support_endpoints p hp x
  unfold evalIndex
  split_ifs
  · exact ⟨le_min he.2.1.1 (he.1.1.trans (le_max_left _ _)),
      (min_le_left _ _).trans he.2.1.2⟩
  · exact hp z x


-- @node: observed_outcome_supported
/-- Under [the model's structural assumptions on potential-outcome support, consistency,
instrument exogeneity, threshold crossing, uniform resistance, common instrument support,
and domain regularity](hyp:h), [the observed outcome belongs to the model's outcome
domain almost surely under the population law](goal). -/
lemma observed_outcome_supported (h : StructuralAssumptions M) :
    ∀ᵐ s ∂M.law.toMeasure, M.Y s ∈ M.Yset := by
  filter_upwards [h.1.1, h.1.2, h.2.1] with s h0 h1 hc
  rcases M.rangeW s with hw | hw
  · rw [hc, hw]
    simpa using h0
  · rw [hc, hw]
    simpa using h1

-- @node: conditional_observed_outcome_supported
/-- Under [the model's structural assumptions on potential-outcome support, consistency,
instrument exogeneity, threshold crossing, uniform resistance, common instrument support,
and domain regularity](hyp:h), [for almost every covariate value under the covariate
distribution, the conditional joint law of outcome, treatment, and instrument assigns
zero probability to outcomes outside the model's outcome domain](goal). -/
lemma conditional_observed_outcome_supported (h : StructuralAssumptions M) :
    ∀ᵐ x ∂xLaw M,
      condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
        {o | o.1 ∉ M.Yset} = 0 := by
  let V := fun s => (M.Y s, M.W s, M.Zv s)
  have hV : Measurable V := M.measY.prodMk (M.measW.prodMk M.measZ)
  have hS : MeasurableSet {o : ℝ × ℝ × Z | o.1 ∈ M.Yset} :=
    h.2.2.2.2.2.2.1.measurableSet.preimage measurable_fst
  have hj : ∀ᵐ a ∂M.law.toMeasure.map (fun s => (M.Xv s, V s)), a.2.1 ∈ M.Yset :=
    (ae_map_iff (M.measX.prodMk hV).aemeasurable
      (hS.preimage measurable_snd)).mpr (observed_outcome_supported M h)
  rw [← compProd_map_condDistrib hV.aemeasurable] at hj
  have hs := Measure.ae_ae_of_ae_compProd hj
  exact hs.mono fun x hx => ae_iff.mp hx

-- @node: selected_quantile_supported
/-- Under [the model's structural assumptions on potential-outcome support, consistency,
instrument exogeneity, threshold crossing, uniform resistance, common instrument support,
and domain regularity](hyp:h), if [the designated outcome endpoints are the least and
greatest elements of the outcome domain](hyp:he) and [the fitted propensities are jointly
measurable in sample realization, instrument, and covariates at every sample size](hyp:hp),
then [at every sample size and realization, for almost every covariate value under the
covariate distribution, every selected-outcome quantile at a level strictly between zero
and one belongs to the model's outcome domain](goal). -/
lemma selected_quantile_supported (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (pHat : ℕ → A → Z → X → ℝ) (delta : ℕ → ℝ)
    (hp : ∀ n, Measurable (fun ax : A × Z × X => pHat n ax.1 ax.2.1 ax.2.2)) :
    ∀ n a, ∀ᵐ x ∂xLaw M, ∀ t ∈ Ioo (0 : ℝ) 1,
      selQuantile M zeroLaw pHat delta n a x t ∈ M.Yset := by
  intro n a
  filter_upwards [conditional_observed_outcome_supported M h,
    canonical_submeasure_supported M h true, canonical_submeasure_mass M h true] with x hx hs hm
  let joint := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
  let selected := joint.restrict {o | o.2.1 = 1 ∧ pHat n a o.2.2 x ≤ pLow (pHat n a) x + delta n}
  have hprob : IsProbabilityMeasure (selLaw M zeroLaw pHat delta n a x) := by
    by_cases hz : selected univ = 0
    · change IsProbabilityMeasure (if selected univ = 0 then _ else _)
      rw [if_pos hz]
      by_cases hb : 0 < pLow M.prop x
      · constructor
        rw [boundaryLaw, if_pos hb, Measure.smul_apply,
          hm _ (population_support_endpoints M x).1]
        simp only [↓reduceIte, smul_eq_mul]
        exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hb) ENNReal.ofReal_ne_top
      · rw [boundaryLaw, if_neg hb]
        exact (zeroLaw x).val.property
    · change IsProbabilityMeasure (if selected univ = 0 then _ else _)
      rw [if_neg hz]
      constructor
      rw [Measure.smul_apply, Measure.map_apply measurable_fst MeasurableSet.univ,
        preimage_univ, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hz (measure_ne_top selected univ)
  have hsupport : selLaw M zeroLaw pHat delta n a x M.Ysetᶜ = 0 := by
    by_cases hz : selected univ = 0
    · change ((if selected univ = 0 then _ else _) : Measure ℝ) M.Ysetᶜ = 0
      rw [if_pos hz]
      by_cases hb : 0 < pLow M.prop x
      · rw [boundaryLaw, if_pos hb, Measure.smul_apply,
          hs _ (population_support_endpoints M x).1, smul_zero]
      · rw [boundaryLaw, if_neg hb]
        exact (zeroLaw x).property
    · change ((if selected univ = 0 then _ else _) : Measure ℝ) M.Ysetᶜ = 0
      rw [if_neg hz, Measure.smul_apply, Measure.map_apply measurable_fst
        h.2.2.2.2.2.2.1.measurableSet.compl]
      have hnull : selected (Prod.fst ⁻¹' M.Ysetᶜ) = 0 := by
        rw [Measure.restrict_apply (h.2.2.2.2.2.2.1.measurableSet.compl.preimage measurable_fst)]
        exact measure_mono_null inter_subset_left hx
      rw [hnull, smul_zero]
  intro t ht
  exact quantile_mem_closed_of_supported _ M.Yset h.2.2.2.2.2.2.1.isClosed hsupport t ht
  -- @realizes Q^{\mathrm{sel}}_{1,n\mid x}(one outcome-supported selected-law quantile)

end Papers.TbsPrteOptimalTransport
