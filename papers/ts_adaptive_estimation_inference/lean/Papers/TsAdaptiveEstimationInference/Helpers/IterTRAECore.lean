module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterEmpiricalCenter
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEClipping
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEIncrementNorms
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAE
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEVectorConcentration
/-! Iterative TRAE and the local curvature derivation separated from the cited comparisons. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 800000
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)


/-- In [the instrumental-variable model](hyp:V), with [clipping bound](hyp:B),
[grid ratio](hyp:ρ), [iteration horizon](hyp:t), and [oracle-radius sequence](hyp:oracleRadius),
[anchored-loss measurability](goal) requires both localized clipped excess-loss suprema
to be measurable at every population anchor through the horizon, for positive sample
sizes whose terminal grid point reaches the radius and grid penalties between the oracle point and two. -/
-- @node: ass:bk-12
noncomputable def IterTRAEAnchoredLossProcessesMeasurable (B ρ : ℝ) (t : ℕ)
    (oracleRadius : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → gridValue ρ (terminalIndex ρ n) ≤ oracleRadius n →
    ∀ j : ℕ, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
    lam ∈ Set.Icc (oraclePoint ρ n (oracleRadius n)) 2 →
    LocalizedSupremaMeasurableAt V.law (traeLossClass V)
      (iterTraePopulationAnchor V j lam) (traeClippedLoss B) n

/-- For [the instrumental-variable model](hyp:V), [clipping bound](hyp:B),
[grid ratio](hyp:ρ), [iteration horizon](hyp:t), and [oracle-radius sequence](hyp:oracleRadius),
[localized-process measurability](goal) requires [measurability of the anchored-loss
processes](step:1) and [measurability of the fixed-center processes](step:2). -/
noncomputable def IterTRAELocalizedProcessesMeasurable (B ρ : ℝ) (t : ℕ)
    (oracleRadius : ℕ → ℝ) : Prop :=
  IterTRAEAnchoredLossProcessesMeasurable V B ρ t oracleRadius ∧
    IterTRAEFixedCenterProcessesMeasurable V ρ t oracleRadius

-- @node: def:iter-trae-estimator
/-- For [the instrumental-variable model](hyp:V), [sampling measure](hyp:P),
[analysis sample](hyp:sample), [sample split](hyp:split), [sample size](hyp:n),
[iteration horizon](hyp:t), [penalty](hyp:lam), and [candidate sequence](hyp:candidate),
[being an iterative TRAE estimator](goal) means following the zero-initialized empirical
minimizer recursion with the empirical loss and squared empirical primal distance. -/
noncomputable def IsIterTRAEEstimator (n t : ℕ) (lam : ℝ) -- @realizes \hat h_{j,\lambda}(zero-initialized empirical minimizer recursion)
    (candidate : ℕ → Ω → V.Hbar.toSubmodule) : Prop :=
  IsEmpiricalIterate V (traeEmpiricalLoss V P sample split n)
    (primalEmpDistanceSq V P sample split n) candidate t lam

-- @node: ass:iter-trae-minima
/-- For [the instrumental-variable model](hyp:V), [sampling measure](hyp:P),
[analysis sample](hyp:sample), [sample split](hyp:split), [grid ratio](hyp:ρ),
[iteration horizon](hyp:t), and [candidate family](hyp:candidate),
[attainment of iterative TRAE minima](goal) requires, at every positive sample size
and grid penalty, [the empirical minimizer recursion](step:1) and
[measurability of every candidate iterate through the horizon](step:2). -/
noncomputable def IterTRAEMinimaAttained (ρ : ℝ) (t : ℕ)
    (candidate : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ lam ∈ regGrid ρ n,
    IsIterTRAEEstimator V P sample split n t lam (fun j => candidate n j lam) ∧
    ∀ j, j ≤ t →
      (@Measurable Ω V.Hbar.toSubmodule inferInstance (borel _) (candidate n j lam))

-- @node: ass:iter-mean-sq-continuity
/-- In [the instrumental-variable model](hyp:V), [iterative mean-square continuity](goal)
means that one real constant uniformly ensures [integrability of squared moment
differences between critic functions](step:1) and [bounds their expectations by that
constant times the squared distance between the critics](step:2). -/
def IterMeanSquareContinuity : Prop :=
  ∃ C : ℝ, ∀ f ∈ V.F, ∀ f' ∈ V.F,
    Integrable (fun w => V.m (f - f') w ^ 2) V.law ∧
    (∫ w, V.m (f - f') w ^ 2 ∂V.law) ≤ C * ‖f - f'‖ ^ 2

/-- For [a propagation multiplier](hyp:b), [the admissible multiplier condition](goal)
requires it to be at least two. -/
def IterTraeMultiplierDomain (b : ℝ) : Prop :=
  2 ≤ b -- @realizes V_{n,t}^{\mathrm T}(nonnegative propagation multiplier)
  -- @realizes b_t(deterministic multiplier bounded below by 2)
  -- @realizes s_{n,t}^{\mathrm T}(nonnegative multiplier domain)

/-- Given [a propagation multiplier](hyp:b) and [accuracy](hyp:δ),
[the iterative TRAE scale](goal) is the multiplier times the squared accuracy. -/
noncomputable def iterTraeScale (b δ : ℝ) : ℝ :=
  b * δ ^ 2 -- @realizes s_{n,t}^{\mathrm T}(multiplier times the squared accuracy)

-- @node: def:iter-trae-scales
/-- For [a propagation multiplier](hyp:b), [accuracy](hyp:δ), and [penalty](hyp:lam),
[the iterative TRAE noise level](goal) is squared accuracy plus the smaller of the
penalty and the iterative scale divided by the penalty. -/
noncomputable def iterTraeNoiseLevel (b : ℝ) -- @realizes b_t(deterministic propagation multiplier)
    (δ lam : ℝ) : ℝ := -- @realizes A_{n,t}^{\mathrm T}(delta squared plus minimum of lambda and s over lambda)
  δ ^ 2 + min lam (iterTraeScale b δ / lam)
/-- For [a propagation multiplier](hyp:b), [accuracy](hyp:δ), and [penalty](hyp:lam),
[the iterative TRAE stability factor](goal) is the multiplier times squared accuracy
divided by the squared penalty. -/
noncomputable def iterTraeStability (b δ lam : ℝ) : ℝ := iterTraeScale b δ / lam ^ 2 -- @realizes V_{n,t}^{\mathrm T}(s over lambda squared)

-- @node: def:iter-trae-oracle-point
/-- Given [a grid ratio](hyp:ρ), [balancing constant](hyp:c), [propagation multiplier](hyp:b),
[source exponent](hyp:β), [iteration horizon](hyp:t), [accuracy sequence](hyp:δ), and
[sample size](hyp:n), [the iterative TRAE oracle point](goal) is the first grid point
below the balancing constant times the iterative scale raised to the reciprocal of
one plus the qualification exponent. -/
noncomputable def iterTraeOraclePoint (ρ c b β : ℝ) (t : ℕ) (δ : ℕ → ℝ) (n : ℕ) : ℝ := -- @realizes \lambda_{\mathrm{IT}}^\circ(first grid point below the iterative TRAE radius)
  oraclePoint ρ n (c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))

/-- If [the grid ratio is admissible](hyp:hρ), [the balancing constant is positive](hyp:hc),
[the multiplier is at least two](hyp:hb), [the source exponent is positive](hyp:hβ),
[the horizon is at least one](hyp:ht), and [the accuracy and allocation sequences satisfy
the TRAE scale calibration](hyp:hScale), then [for all sufficiently large sample sizes
there is a first grid index, no later than the terminal index, whose value lies below
the iterative oracle radius, and the oracle point equals that grid value](goal). -/
-- @node: iterTraeOraclePoint_eventually
lemma iterTraeOraclePoint_eventually (ρ c b β : ℝ) (t : ℕ)
    (δ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ) (allocation : ℕ → ℝ)
    (hρ : GridDomain ρ) (hc : 0 < c) (hb : 2 ≤ b) (hβ : 0 < β) (ht : 1 ≤ t)
    (hScale : TRAEScaleCalibration δ tildeδ allocation) :
    ∀ᶠ n in atTop, ∃ k ≤ terminalIndex ρ n,
    gridValue ρ k ≤ c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) ∧
    (∀ j < k, c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) < gridValue ρ j) ∧
    iterTraeOraclePoint ρ c b β t δ n = gridValue ρ k := by
  have hq : 0 ≤ qualificationExponent β t := by
    unfold qualificationExponent
    exact le_min (by linarith) (by positivity)
  have hden : 0 < qualificationExponent β t + 1 := by linarith
  have ha : 0 ≤ 1 / (qualificationExponent β t + 1) := by positivity
  have ha1 : 1 / (qualificationExponent β t + 1) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  filter_upwards [eventually_ge_atTop (max 1 ⌈1 / c⌉₊)] with n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn0 : 0 < n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : 0 < (n : ℝ) := by positivity
  have hcn : 1 / c ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hn))
  have hcn' : 1 ≤ c * n := by
    have := (div_le_iff₀ hc).1 hcn
    nlinarith
  have hfloor := (le_max_right _ _).trans (hScale.1 n hn0)
  have hδ : 0 ≤ δ n := (Real.rpow_nonneg hnpos.le _).trans hfloor
  have hsq : 1 / (n : ℝ) ≤ δ n ^ 2 := by
    have hs := pow_le_pow_left₀ (Real.rpow_nonneg hnpos.le (-(1 / 2 : ℝ))) hfloor 2
    have heq : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num [Real.rpow_neg_one]
    rwa [heq] at hs
  have hbase : 1 / (n : ℝ) ≤ b * δ n ^ 2 := by
    nlinarith [sq_nonneg (δ n)]
  have hradius : c * (1 / (n : ℝ)) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    calc
      1 / (n : ℝ) = (1 / (n : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 / (n : ℝ)) ^ (1 / (qualificationExponent β t + 1)) :=
        Real.rpow_le_rpow_of_exponent_ge (by positivity)
          ((div_le_one hnpos).2 hn') ha1
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hbase ha
  have hterminal : gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) := by
    refine (terminalGrid_le ρ hρ n hn0).trans (le_trans ?_ hradius)
    apply (div_le_iff₀ (sq_pos_of_pos hnpos)).2
    have heq : c * (1 / (n : ℝ)) * (n : ℝ) ^ 2 = c * n := by
      field_simp
    rw [heq]
    exact hcn'
  exact oraclePoint_first_crossing ρ _ n hterminal

-- @node: def:iter-trae-minimum-size
/-- For [an envelope bound](hyp:B), [the minimum iterative TRAE sample size](goal)
is the larger of two and the natural-number ceiling of eight times the squared bound. -/
noncomputable def iterTraeMinSampleSize (B : ℝ) : ℕ := max 2 ⌈8 * B ^ 2⌉₊ -- @realizes N_{\mathrm{IT}}(B)(maximum of two and the ceiling of eight B squared)

-- @node: ass:iter-realizability-trae
/-- For [the instrumental-variable model](hyp:V), [grid ratio](hyp:ρ),
[balancing constant](hyp:c), [propagation multiplier](hyp:b), [source exponent](hyp:β),
[iteration horizon](hyp:t), and [accuracy sequence](hyp:δ), [iterative TRAE realizability](goal)
requires every population iterate from one through the horizon to belong to the
hypothesis class at grid penalties between the oracle point and two, whenever the
terminal grid point reaches the oracle radius. -/
noncomputable def IterRealizableTRAE (ρ c b β : ℝ) (t : ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ n, gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) →
    ∀ j, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 → populationIterate V lam j ∈ V.H

-- @node: ass:iter-trae-rate-qualification
/-- For [a source exponent](hyp:β) and [iteration horizon](hyp:t),
[the iterative TRAE qualification condition](goal) requires the source exponent plus
one to be at most twice the horizon. -/
def IterQualificationTRAE (β : ℝ) (t : ℕ) : Prop := β + 1 ≤ 2 * (t : ℝ)

-- @node: ass:iter-trae-accepted-stability-branch
/-- Given [a grid ratio](hyp:ρ), [balancing constant](hyp:c), [propagation multiplier](hyp:b),
[source exponent](hyp:β), [horizon](hyp:t), [accuracy sequence](hyp:δ), [sample size](hyp:n),
and [penalty](hyp:lam), [the stable branch condition](goal) requires [grid membership](step:1),
[a penalty between the oracle point and two](step:2), and [a penalty at least the square
root of the iterative scale](step:3). -/
noncomputable def IterTRAEStableBranch (ρ c b β : ℝ) (t : ℕ)
    (δ : ℕ → ℝ) (n : ℕ) (lam : ℝ) : Prop :=
  lam ∈ regGrid ρ n ∧ lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 ∧
    Real.sqrt (b * δ n ^ 2) ≤ lam

/-- For [the model](hyp:V), [sampling measure](hyp:P), [sample](hyp:sample),
[split](hyp:split), [grid ratio](hyp:ρ), [balancing constant](hyp:c), [multiplier](hyp:b),
[source exponent](hyp:β), [horizon](hyp:t), [accuracy sequence](hyp:δ),
[source witness](hyp:w₀), [candidate family](hyp:candidate), [sample size](hyp:n),
[event](hyp:E), and [bias coefficient](hyp:C), [the discrepancy bound on the event](goal)
requires [a positive bias coefficient](step:1) and [terminal empirical loss bounded
by the noise level plus the coefficient times the squared witness norm times the
penalty to the qualification exponent, throughout the oracle grid segment](step:2). -/
noncomputable def IterTRAEDiscrepancyOn (ρ c b β : ℝ) (t : ℕ) (δ : ℕ → ℝ)
    (w₀ : V.Hbar.toSubmodule) (candidate : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  0 < C ∧ ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
    lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
      traeEmpiricalLoss V P sample split n ω (candidate n t lam ω) ≤
        iterTraeNoiseLevel b (δ n) lam + C * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t

/-- For [the model](hyp:V), [sampling measure](hyp:P), [sample](hyp:sample),
[split](hyp:split), [grid ratio](hyp:ρ), [failure budget](hyp:ξ), [balancing constant](hyp:c),
[multiplier](hyp:b), [source exponent](hyp:β), [horizon](hyp:t), [accuracy sequence](hyp:δ),
[source witness](hyp:w₀), [candidate family](hyp:candidate), [sample size](hyp:n),
[event](hyp:E), and [bias coefficient](hyp:C), [the discrepancy envelope](goal) requires
[event measurability](step:1), [probability at least one minus the failure budget](step:2),
and [the iterative TRAE discrepancy bound on that event](step:3). -/
-- @node: def:iter-trae-discrepancy-bound
noncomputable def IterTRAEDiscrepancyEnvelope (ρ ξ c b β : ℝ) (t : ℕ) (δ : ℕ → ℝ)
    (w₀ : V.Hbar.toSubmodule) (candidate : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
    IterTRAEDiscrepancyOn V P sample split ρ c b β t δ w₀ candidate n E C

-- @node: def:iter-trae-oracle-scales
/-- For [a grid ratio](hyp:ρ), [balancing constant](hyp:c), [multiplier](hyp:b),
[source exponent](hyp:β), [horizon](hyp:t), and [accuracy sequence](hyp:δ),
[the oracle scale bounds](goal) assert that a positive constant eventually bounds
[the oracle noise level by the iterative scale to the qualification exponent divided
by one plus that exponent](step:1) and [the oracle stability factor by the scale to
the qualification exponent minus one, divided by one plus that exponent](step:2). -/
noncomputable def IterTRAEOracleScales (ρ c b β : ℝ) (t : ℕ) (δ : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ n in atTop,
    iterTraeNoiseLevel b (δ n) (iterTraeOraclePoint ρ c b β t δ n) ≤
      C * (b * δ n ^ 2) ^ (qualificationExponent β t / (qualificationExponent β t + 1)) ∧
    iterTraeStability b (δ n) (iterTraeOraclePoint ρ c b β t δ n) ≤
      C * (b * δ n ^ 2) ^ ((qualificationExponent β t - 1) / (qualificationExponent β t + 1))

/-- For [the model](hyp:V), [sampling measure](hyp:P), [sample](hyp:sample),
[split](hyp:split), [sample size](hyp:n), [iteration](hyp:j), [penalty](hyp:lam),
[candidate sequence](hyp:candidate), and [sample outcome](hyp:ω), [the empirical center
difference](goal) is the squared empirical distance from the population iterate to
the preceding candidate, minus that from the current candidate to the preceding candidate. -/
noncomputable def iterEmpiricalCenterDifference (n j : ℕ) (lam : ℝ)
    (candidate : ℕ → Ω → V.Hbar.toSubmodule) (ω : Ω) : ℝ :=
  primalEmpDistanceSq V P sample split n ω (populationIterate V lam j) (candidate (j - 1) ω) -
    primalEmpDistanceSq V P sample split n ω (candidate j ω) (candidate (j - 1) ω)

/-- For [the model](hyp:V), [iteration](hyp:j), [penalty](hyp:lam), and [comparison function](hyp:h),
[the population center difference](goal) is the squared distance from the current to
the preceding population iterate, minus the squared distance from the comparison
function to that preceding iterate. -/
noncomputable def iterPopulationCenterDifference (j : ℕ) (lam : ℝ)
    (h : V.Hbar.toSubmodule) : ℝ :=
  ‖populationIterate V lam j - populationIterate V lam (j - 1)‖ ^ 2 -
    ‖h - populationIterate V lam (j - 1)‖ ^ 2

/-- For [the model](hyp:V), [iteration](hyp:j), [penalty](hyp:lam), and [comparison function](hyp:h),
[the strong variance error](goal) is the norm of the difference between the comparison
function and the population iterate. -/
noncomputable def iterStrongVariance (j : ℕ) (lam : ℝ) (h : V.Hbar.toSubmodule) : ℝ :=
  ‖h - populationIterate V lam j‖
/-- For [the model](hyp:V), [iteration](hyp:j), [penalty](hyp:lam), and [comparison function](hyp:h),
[the weak variance error](goal) is the norm of the projected conditional expectation
of the difference between the comparison function and the population iterate. -/
noncomputable def iterWeakVariance (j : ℕ) (lam : ℝ) (h : V.Hbar.toSubmodule) : ℝ :=
  ‖projCondExpOp V (h - populationIterate V lam j)‖
/-- For [the model](hyp:V), [iteration](hyp:j), and [penalty](hyp:lam),
[the weak bias](goal) is the norm of the projected conditional expectation of the
population iterate minus the minimum-norm solution. -/
noncomputable def iterWeakBias (j : ℕ) (lam : ℝ) : ℝ :=
  ‖projCondExpOp V (populationIterate V lam j - minNormSolution V)‖
/-- For [the model](hyp:V), [iteration](hyp:j), and [penalty](hyp:lam),
[the critic infinity norm](goal) is the real-valued essential supremum norm, under
the instrument distribution, of the dual representative of the projected conditional
expectation of the minimum-norm solution minus the population iterate. -/
noncomputable def iterCriticInfinityNorm (j : ℕ) (lam : ℝ) : ℝ :=
  (eLpNorm (dualVersion V (projCondExpOp V (minNormSolution V - populationIterate V lam j)))
    ⊤ (V.law.map V.zOf)).toReal

/-- Assuming [localized TRAE concentration](hyp:hBennett_of_gate), [a positive constant
uniformly bounds the empirical iterate's excess population loss by the penalty times
the empirical center difference plus that constant times the sum of squared weak bias,
accuracy times weak variance, and squared accuracy, on a measurable event of probability
at least one minus half the allocation](goal). This holds under the range, realizability,
closeness, boundedness, common-null-set boundedness, both mean-square continuity, and
critical-radius conditions, for calibrated scales, positive sample size and penalty,
iteration at least one, allocation strictly between zero and one, a realizable population
iterate, and an empirical minimizer recursion. -/
-- @node: iter_trae_ordinary_excess_loss
lemma iter_trae_ordinary_excess_loss
    (hBennett_of_gate : TRAELocalizedConcentration V) [IsProbabilityMeasure P] :
  ∀ (B : ℝ) (tildeδ : ℕ → ℝ → ℝ), RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
  TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → MeanSquareContinuity V → IterMeanSquareContinuity V →
  TRAECriticalRadiusBound V tildeδ →
  ∃ C > 0, ∀ (δ allocation : ℕ → ℝ), TRAEScaleCalibration δ tildeδ allocation →
    ∀ (n j : ℕ) (lam : ℝ)
    (candidate : ℕ → Ω → V.Hbar.toSubmodule),
    0 < n → 1 ≤ j → 0 < lam → allocation n ∈ Set.Ioo (0 : ℝ) 1 → populationIterate V lam j ∈ V.H →
    IsIterTRAEEstimator V P sample split n j lam candidate →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧ ∀ ω ∈ E,
      traePopulationLoss V (candidate j ω) - traePopulationLoss V (populationIterate V lam j) ≤
        lam * iterEmpiricalCenterDifference V P sample split n j lam candidate ω +
        C * (iterWeakBias V j lam ^ 2 + δ n * iterWeakVariance V j lam (candidate j ω) + δ n ^ 2) := by
  intro B tildeδ hRange hRealizable hClose hBound hCommon hMSC hIterMSC hComplexity
  obtain ⟨D, hD, hdeviation⟩ := trae_calibrated_deviation_at_allocation
    V P sample split hBennett_of_gate B tildeδ hBound hCommon hMSC hComplexity
  let C := 4 * D + D ^ 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro δ allocation hScale n j lam candidate hn hj hlam hη hStar hEst
  obtain ⟨E, hE, hprob, hdev⟩ :=
    hdeviation δ allocation hRange hClose hScale n hn hη
  let r := δ n
  have hr : 0 ≤ r :=
    (Real.rpow_nonneg (by positivity) _).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  refine ⟨E, hE, hprob, ?_⟩
  intro ω hω
  let a := populationIterate V lam j
  let h := candidate j ω
  let residual := fun u : V.Hbar.toSubmodule => projCondExpOp V (minNormSolution V - u)
  have hh : h ∈ V.H := (hEst.2 j hj le_rfl ω).1
  have hquad (u : V.Hbar.toSubmodule) (f : V.Qbar.toSubmodule) :
      (∫ w, traeIntegrand V u f w ∂V.law) =
        2 * inner ℝ (residual u) f - ‖f‖ ^ 2 :=
    trae_integrand_mean V hRange u f
  have hpop (u : V.Hbar.toSubmodule) (hu : u ∈ V.H) :
      traePopulationLoss V u = ‖residual u‖ ^ 2 := by
    rw [traePopulationLoss_eq V hRange hClose u hu]
    have he : projCondExpOp V (u - minNormSolution V) = -residual u := by
      dsimp [residual]
      rw [← map_neg, neg_sub]
    rw [he, norm_neg]
  -- Complete the empirical critic square before taking its supremum.
  have hupper (u : V.Hbar.toSubmodule) (hu : u ∈ V.H) :
      traeEmpiricalLoss V P sample split n ω u ≤
        ‖residual u‖ ^ 2 + D * r * ‖residual u‖ + (D + D ^ 2 / 4) * r ^ 2 := by
    have : Nonempty V.F := ⟨⟨residual u, hClose u hu⟩⟩
    apply ciSup_le
    intro f
    have hd := (abs_le.mp (hdev ω hω u hu f f.property)).2
    rw [hquad] at hd
    have hi := real_inner_le_norm (residual u) (f : V.Qbar.toSubmodule)
    have hs := sq_nonneg (‖(f : V.Qbar.toSubmodule)‖ - ‖residual u‖ - D * r / 2)
    nlinarith only [hd, hi, hs]
  have hlower : traePopulationLoss V h ≤ traeEmpiricalLoss V P sample split n ω h +
      D * r * ‖residual h‖ + D * r ^ 2 := by
    have hd := (abs_le.mp (hdev ω hω h hh (residual h) (hClose h hh))).1
    rw [hquad, real_inner_self_eq_norm_sq] at hd
    have hbdd : BddAbove (Set.range (fun f : V.F =>
        blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω)) := by
      refine ⟨‖residual h‖ ^ 2 + D * r * ‖residual h‖ + (D + D ^ 2 / 4) * r ^ 2, ?_⟩
      rintro _ ⟨f, rfl⟩
      have hd' := (abs_le.mp (hdev ω hω h hh f f.property)).2
      rw [hquad] at hd'
      have hi := real_inner_le_norm (residual h) (f : V.Qbar.toSubmodule)
      have hs := sq_nonneg (‖(f : V.Qbar.toSubmodule)‖ - ‖residual h‖ - D * r / 2)
      exact (show blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω ≤
        ‖residual h‖ ^ 2 + D * r * ‖residual h‖ + (D + D ^ 2 / 4) * r ^ 2 by
          nlinarith only [hd', hi, hs])
    have hsup := le_ciSup hbdd (⟨residual h, hClose h hh⟩ : V.F)
    change blockAverage V P sample (split.fit n) (traeIntegrand V h (residual h)) ω ≤
      traeEmpiricalLoss V P sample split n ω h at hsup
    rw [hpop h hh]
    nlinarith only [hd, hsup]
  have hopt := (hEst.2 j hj le_rfl ω).2 a hStar
  have hcenter : traeEmpiricalLoss V P sample split n ω h ≤
      traeEmpiricalLoss V P sample split n ω a +
        lam * iterEmpiricalCenterDifference V P sample split n j lam candidate ω := by
    dsimp only [iterEmpiricalCenterDifference]
    change traeEmpiricalLoss V P sample split n ω h + _ ≤
      traeEmpiricalLoss V P sample split n ω a + _ at hopt
    linarith only [hopt]
  have htriangle : ‖residual h‖ ≤ iterWeakVariance V j lam h + iterWeakBias V j lam := by
    have he : residual h = residual a - projCondExpOp V (h - a) := by
      dsimp [residual]
      simp only [map_sub]
      abel
    rw [he]
    have hb : ‖residual a‖ = iterWeakBias V j lam := by
      have he' : residual a = -projCondExpOp V (a - minNormSolution V) := by
        dsimp [residual]
        rw [← map_neg, neg_sub]
      rw [he', norm_neg]
      rfl
    calc
      _ ≤ ‖residual a‖ + ‖projCondExpOp V (h - a)‖ := norm_sub_le _ _
      _ = _ := by rw [hb]; exact add_comm _ _
  have hbias : ‖residual a‖ = iterWeakBias V j lam := by
    have he : residual a = -projCondExpOp V (a - minNormSolution V) := by
      dsimp [residual]
      rw [← map_neg, neg_sub]
    rw [he, norm_neg]
    rfl
  have hu := hupper a hStar
  rw [← hpop a hStar, hbias] at hu
  have ht := mul_le_mul_of_nonneg_left htriangle (mul_nonneg hD.le hr)
  have hy := mul_le_mul_of_nonneg_left (sq_nonneg (iterWeakBias V j lam - r)) hD.le
  have hCb : D ≤ C := by dsimp [C]; nlinarith [sq_nonneg D]
  have hCr : 3 * D + D ^ 2 / 4 ≤ C := by dsimp [C]; nlinarith [sq_nonneg D]
  have hb := mul_le_mul_of_nonneg_right hCb (sq_nonneg (iterWeakBias V j lam))
  have hv := mul_le_mul_of_nonneg_right hCb
    (mul_nonneg hr (norm_nonneg (projCondExpOp V (h - a))))
  have hs := mul_le_mul_of_nonneg_right hCr (sq_nonneg r)
  change traePopulationLoss V h - traePopulationLoss V a ≤ _
  change D * (r * iterWeakVariance V j lam h) ≤
    C * (r * iterWeakVariance V j lam h) at hv
  nlinarith only [hlower, hcenter, hu, ht, hy, hb, hv, hs]


/-- Under [the range condition](hyp:hRange) and [closeness condition](hyp:hClose),
at [iteration at least one](hyp:hj) with [positive penalty](hyp:hlam), if [the population
iterate belongs to the hypothesis class](hyp:hStar) and [a comparison function](hyp:h)
[also belongs to that class](hyp:hh), then [its excess population loss equals squared weak
variance plus the penalty times squared strong variance plus the penalty times the
population center difference](goal). -/
-- @node: iter_trae_population_curvature
lemma iter_trae_population_curvature (hRange : RangeCondition V)
    (hClose : ClosenessCondition V) (j : ℕ) (hj : 1 ≤ j) (lam : ℝ) (hlam : 0 < lam)
    (hStar : populationIterate V lam j ∈ V.H) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
    traePopulationLoss V h - traePopulationLoss V (populationIterate V lam j) =
      iterWeakVariance V j lam h ^ 2 + lam * iterStrongVariance V j lam h ^ 2 +
        lam * iterPopulationCenterDifference V j lam h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  let a := populationIterate V lam (k + 1)
  let c := populationIterate V lam k
  have hnormal : normalOp V a + lam • a =
      adjointOp V (momentRepresenter V) + lam • c :=
    resolvent_normalEquation V lam hlam _
  have hcross : inner ℝ (projCondExpOp V a - momentRepresenter V)
      (projCondExpOp V (h - a)) + lam * inner ℝ (a - c) (h - a) = 0 := by
    have hi := congrArg (fun x => inner ℝ x (h - a)) hnormal
    have hia : inner ℝ (lam • a) (h - a) = lam * inner ℝ a (h - a) :=
      real_inner_smul_left a (h - a) lam
    have hic : inner ℝ (lam • c) (h - a) = lam * inner ℝ c (h - a) :=
      real_inner_smul_left c (h - a) lam
    simp only [inner_add_left, hia, hic] at hi
    simp only [normalOp, ContinuousLinearMap.comp_apply, adjointOp,
      ContinuousLinearMap.adjoint_inner_left, inner_sub_left] at hi ⊢
    linarith
  have hT : projCondExpOp V h - momentRepresenter V =
      (projCondExpOp V a - momentRepresenter V) + projCondExpOp V (h - a) := by
    rw [map_sub]
    abel
  have hc : h - c = (a - c) + (h - a) := by abel
  rw [traePopulationLoss_eq V hRange hClose h hh,
    traePopulationLoss_eq V hRange hClose _ hStar]
  have hsol := (minNormSolution_spec V hRange).1
  simp only [map_sub, hsol]
  change ‖projCondExpOp V h - momentRepresenter V‖ ^ 2 -
      ‖projCondExpOp V a - momentRepresenter V‖ ^ 2 =
    ‖projCondExpOp V (h - a)‖ ^ 2 + lam * ‖h - a‖ ^ 2 +
      lam * (‖a - c‖ ^ 2 - ‖h - c‖ ^ 2)
  rw [hT, hc, norm_add_sq_real, norm_add_sq_real]
  nlinarith only [hcross]

/-- Assume [localized TRAE concentration](hyp:hBennett_of_gate), [the range condition](hyp:hRange),
[closeness](hyp:hClose), [membership of the minimum-norm solution in the hypothesis class](hyp:hRealizable),
[mean-square continuity](hyp:hMSC0), [boundedness](hyp:hBounded), [boundedness outside a
common null set](hyp:hCommonBounded), [iterative mean-square continuity](hyp:hMSC), and
[the critical-radius bound](hyp:hComplexity). Then [a positive constant uniformly bounds
penalty-weighted squared strong variance plus squared weak variance by that constant
times squared weak bias, accuracy times weak variance, and squared accuracy, plus the
penalty times the empirical center difference minus the population center difference,
on a measurable event of probability at least one minus half the allocation](goal), for
calibrated scales, positive sample size and penalty, iteration at least one, allocation
strictly between zero and one, a realizable population iterate, and an empirical minimizer recursion. -/
-- @node: iter_trae_excess_loss_with_bias
lemma iter_trae_excess_loss_with_bias
    (hBennett_of_gate : TRAELocalizedConcentration V) [IsProbabilityMeasure P]
    (hRange : RangeCondition V) (hClose : ClosenessCondition V)
    (hRealizable : H0MemHypothesisClass V) (hMSC0 : MeanSquareContinuity V)
    (B : ℝ) (hBounded : TRAEBoundedness V B) (hCommonBounded : TRAECommonNullSetBoundedness V B) (hMSC : IterMeanSquareContinuity V)
    (tildeδ : ℕ → ℝ → ℝ) (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (δ allocation : ℕ → ℝ), TRAEScaleCalibration δ tildeδ allocation →
      ∀ (n j : ℕ) (lam : ℝ)
      (candidate : ℕ → Ω → V.Hbar.toSubmodule),
      0 < n → 1 ≤ j → 0 < lam → allocation n ∈ Set.Ioo (0 : ℝ) 1 → populationIterate V lam j ∈ V.H →
      IsIterTRAEEstimator V P sample split n j lam candidate →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧ ∀ ω ∈ E,
        lam * iterStrongVariance V j lam (candidate j ω) ^ 2 +
          iterWeakVariance V j lam (candidate j ω) ^ 2 ≤
        C * (iterWeakBias V j lam ^ 2 + δ n * iterWeakVariance V j lam (candidate j ω) + δ n ^ 2) +
          lam * (iterEmpiricalCenterDifference V P sample split n j lam candidate ω -
            iterPopulationCenterDifference V j lam (candidate j ω)) := by
  obtain ⟨C, hC, hbound⟩ := iter_trae_ordinary_excess_loss (hBennett_of_gate := hBennett_of_gate) V P sample split B tildeδ
    hRange hRealizable hClose hBounded hCommonBounded hMSC0 hMSC hComplexity
  refine ⟨C, hC, ?_⟩
  intro δ allocation hScale n j lam candidate hn hj hlam hη hStar hEst
  obtain ⟨E, hE, hprob, he⟩ :=
    hbound δ allocation hScale n j lam candidate hn hj hlam hη hStar hEst
  refine ⟨E, hE, hprob, ?_⟩
  intro ω hω
  have hh := (hEst.2 j hj le_rfl ω).1
  have hcurv := iter_trae_population_curvature V hRange hClose j hj lam hlam
    hStar (candidate j ω) hh
  have hexcess := he ω hω
  rw [hcurv] at hexcess
  nlinarith only [hexcess]

/-- For [the model](hyp:V), [sampling measure](hyp:P), [sample](hyp:sample),
[split](hyp:split), [grid ratio](hyp:ρ), [balancing constant](hyp:c), [multiplier](hyp:b),
[source exponent](hyp:β), [horizon](hyp:t), [oracle accuracy sequence](hyp:δ),
[base comparison accuracy](hyp:radius), [iterate family](hyp:iter), [sample size](hyp:n),
[event](hyp:E), and [comparison constant](hyp:C), [the concentration certificate](goal)
requires [the base TRAE comparisons on the event](step:1) and [uniform bounds on game
deviations, anchored game increments, and empirical minus population center differences
through the horizon on the oracle grid segment whenever the oracle radius is reached](step:2).

Game deviations scale with base accuracy times critic norm plus squared accuracy;
anchored increments additionally use strong distance times the anchor critic infinity
norm. Center deviations use the sum and product of successive strong errors. -/
noncomputable def IterTRAEConcentrationOn (ρ c b β : ℝ) (t : ℕ) (δ radius : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  TRAEComparisonsOn V P sample split radius n E C ∧
  ∀ (_hOracleDefined : gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))),
  ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
    lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
    ∀ j, 1 ≤ j → j ≤ t →
      (∀ h ∈ V.H, ∀ f ∈ V.F,
        |blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω -
          ∫ w, traeIntegrand V h f w ∂V.law| ≤ C * (radius n * ‖f‖ + radius n ^ 2)) ∧
      (∀ h ∈ V.H, ∀ f ∈ V.F,
        let g := populationIterate V lam j
        let k := projCondExpOp V (minNormSolution V - g)
        |blockAverage V P sample (split.fit n) (fun w => traeIntegrand V h f w - traeIntegrand V g k w) ω -
          ∫ w, traeIntegrand V h f w - traeIntegrand V g k w ∂V.law| ≤
        C * (radius n * ‖h - g‖ *
          (eLpNorm (dualVersion V k) ⊤ (V.law.map V.zOf)).toReal +
          radius n * ‖f - k‖ + radius n ^ 2)) ∧
      |iterEmpiricalCenterDifference V P sample split n j lam (fun k => iter n k lam) ω -
        iterPopulationCenterDifference V j lam (iter n j lam ω)| ≤
      C * (radius n * (‖iter n j lam ω - populationIterate V lam j‖ +
        ‖iter n (j - 1) lam ω - populationIterate V lam (j - 1)‖) + radius n ^ 2 +
        ‖iter n j lam ω - populationIterate V lam j‖ *
          ‖iter n (j - 1) lam ω - populationIterate V lam (j - 1)‖)

/-- For [a grid ratio](hyp:ρ), [sample size](hyp:n), [iteration horizon](hyp:t), and
[three component events at each iteration and grid index](hyp:component),
[the common event](goal) is the intersection of all those component events. -/
def iterTraeCommonEvent (ρ : ℝ) (n t : ℕ)
    (component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω) : Set Ω :=
  ⋂ j, ⋂ k, ⋂ a, component j k a
  -- @realizes \mathcal E_{n,t}^{\mathrm{IT}}(one finite intersection of the allocated comparison events)

/-- If [the iteration horizon is at least one](hyp:ht) and [every component event is
measurable with probability at least one minus a third of the per-grid confidence
allocation](hyp:hcomponent), then [their common intersection is measurable and has
probability at least one minus the total failure budget](goal). -/
-- @node: iterTraeCommonEvent_probability
lemma iterTraeCommonEvent_probability [IsProbabilityMeasure P]
    (ρ ξ : ℝ) (n t : ℕ) (ht : 1 ≤ t)
    (component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω)
    (hcomponent : ∀ j k a, MeasurableSet (component j k a) ∧
      1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) :
    MeasurableSet (iterTraeCommonEvent ρ n t component) ∧
      1 - ξ ≤ P.real (iterTraeCommonEvent ρ n t component) := by
  have hE : MeasurableSet (iterTraeCommonEvent ρ n t component) := by
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun a => (hcomponent j k a).1
  refine ⟨hE, ?_⟩
  have hc (j k a) : P.real (component j k a)ᶜ ≤ iterGridConfidence ρ ξ n t / 3 := by
    have hp := probReal_add_probReal_compl (μ := P) (hcomponent j k a).1
    linarith [(hcomponent j k a).2]
  have hbad : P.real (iterTraeCommonEvent ρ n t component)ᶜ ≤ ξ := by
    calc
      P.real (iterTraeCommonEvent ρ n t component)ᶜ =
          P.real (⋃ j, ⋃ k, ⋃ a, (component j k a)ᶜ) := by
        simp only [iterTraeCommonEvent, Set.compl_iInter]
      _ ≤ ∑ j, ∑ k, ∑ a, P.real (component j k a)ᶜ := by
        refine (measureReal_iUnion_fintype_le _).trans ?_
        apply Finset.sum_le_sum
        intro j _
        refine (measureReal_iUnion_fintype_le _).trans ?_
        apply Finset.sum_le_sum
        intro k _
        exact measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin t, ∑ _k : Fin (terminalIndex ρ n + 1),
          ∑ _a : Fin 3, iterGridConfidence ρ ξ n t / 3 := by
        exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
          Finset.sum_le_sum fun a _ => hc j k a
      _ = ξ := by
        have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
        have hk0 : (terminalIndex ρ n + 1 : ℝ) ≠ 0 := by positivity
        simp [iterGridConfidence, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp
  linarith [probReal_add_probReal_compl (μ := P) hE]

end Papers.TsAdaptiveEstimationInference
