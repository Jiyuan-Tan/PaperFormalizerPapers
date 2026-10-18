module
public import Papers.TbsPrteOptimalTransport.Helpers.ScoresBinary
public import Causalean.Stat.Sample
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.Limit.Modes
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
/-! Samples, random partitions, level recovery and the finite-instrument fitting procedure. -/
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
variable {μ : Measure A} {B : Type*}
variable (M : LatentIVModel Ω X Z)
/-- For [the latent instrumental-variable model](hyp:M), the [observation law](goal)
is the joint population distribution of covariates, instrument, treatment, and outcome. -/
noncomputable def observationLaw : Measure (Obs X Z) :=
  M.law.toMeasure.map (fun a => (M.Xv a, M.Zv a, M.W a, M.Y a))
-- @node: def:observations-and-nuisances
/-- Under [the model](hyp:M) and [the sampling measure](hyp:μ), an [observed sample](goal)
is an infinite sequence of independent, identically distributed observations with the model's observation law. -/
def ObservedSample (μ : Measure A) := Causalean.Stat.IIDSample A (Obs X Z) μ (observationLaw M)
  -- @realizes O(iid observed sample from the population law)
/-- On [a space of sampling outcomes](hyp:A), a [sample split](goal) assigns a finite set
of observation indices to every sample size and sampling outcome. -/
abbrev SampleSplit (A : Type s) := ℕ → A → Finset ℕ
/-- For [the model](hyp:M), [the sampling measure](hyp:μ), [an observed sample](hyp:S),
[a selection of indices](hyp:I), and [an observation-level function](hyp:f), the [split mean](goal)
at [sample size](hyp:n) and [sampling outcome](hyp:a) is the sum of the function over the selected
observations divided by their number, with [the selected set required to be nonempty](hyp:_h). -/
noncomputable def splitMean (S : ObservedSample M μ) (I : SampleSplit A)
    (f : ℕ → A → Obs X Z → ℝ) (n : ℕ) (a : A) (_h : (I n a).Nonempty) :=
  ((I n a).card : ℝ)⁻¹ * ∑ i ∈ I n a, f n a (S.Z i a)
-- @node: ass:dml-equal-split
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S), and
[two index selections](hyp:I₁,I₂), the [equal-half split condition](goal) requires, at every
even sample size of at least two, [almost surely disjoint halves covering all sample indices,
each containing half the observations](step:1), [measurability of the training selection](step:2)
and [evaluation selection](step:3), [a uniform distribution over training halves](step:4),
and [independence of the training selection from the observations in that sample](step:5). -/
def EqualHalfSplit (μ : Measure A) (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A) : Prop := -- @realizes I_1(uniform random training half) @realizes I_2(complementary evaluation half, independent of observations)
  ∀ n, 2 ≤ n → Even n →
    (∀ᵐ a ∂μ, Disjoint (I₁ n a) (I₂ n a) ∧ I₁ n a ∪ I₂ n a = Finset.range n ∧
      (I₁ n a).card = n / 2 ∧ (I₂ n a).card = n / 2) ∧
    Measurable (I₁ n) ∧ Measurable (I₂ n) ∧
    (∀ J ∈ (Finset.range n).powersetCard (n / 2),
      μ {a | I₁ n a = J} = (((Finset.range n).powersetCard (n / 2)).card : ℝ≥0∞)⁻¹) ∧
    IndepFun (I₁ n) (fun a => fun i : Fin n => S.Z i a) μ


  -- @realizes n(even sample size at least two)
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S), and
[training index selection](hyp:I), the [training view](goal) at [sample size](hyp:n) and
[sampling outcome](hyp:a) records the selected indices and the first sample-size-many observations,
with every observation outside the training selection replaced by a missing-value marker. -/
noncomputable def trainingView (S : ObservedSample M μ) (I : SampleSplit A) (n : ℕ) (a : A) :=
  (I n a, fun i : Fin n => if i.val ∈ I n a then (Sum.inr (S.Z i a) : Unit ⊕ Obs X Z) else Sum.inl ())
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S), and
[training selection](hyp:I), [training-predictor measurability](goal) means that
[the fitted predictor](hyp:f), at each sample size, is jointly measurable using only the training
view of the sampling outcome and the measurable predictor argument. -/
def TrainingPredictorMeasurable [MeasurableSpace B] (S : ObservedSample M μ) (I : SampleSplit A)
    (f : ℕ → A → B → ℝ) : Prop :=
  ∀ n, Measurable[MeasurableSpace.prod
    (MeasurableSpace.comap (trainingView M S I n) inferInstance) inferInstance]
    (Function.uncurry (f n))
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S),
[evaluation selection](hyp:I₂), and [fitted score](hyp:score), the [score average](goal)
at [sample size](hyp:n) and [sampling outcome](hyp:a) is the mean score over the evaluation
observations, assuming [the evaluation selection is nonempty](hyp:h). -/
noncomputable def scoreAverage (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (score : ℕ → A → Obs X Z → ℝ) (n : ℕ) (a : A) (h : (I₂ n a).Nonempty) :=
  splitMean M S I₂ score n a h
  -- @realizes \hat{\underline{\theta}}_{\omega,1}(evaluation-half score average)
  -- @realizes \hat\psi(fitted score including fitted recovered level sets)
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S),
[evaluation selection](hyp:I₂), and [fitted score](hyp:score), the [sample variance](goal)
at [sample size](hyp:n) and [sampling outcome](hyp:a) is the mean squared deviation of evaluation
scores from their evaluation mean, assuming [the evaluation selection is nonempty](hyp:h). -/
noncomputable def sampleVariance (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (score : ℕ → A → Obs X Z → ℝ) (n : ℕ) (a : A) (h : (I₂ n a).Nonempty) :=
  ((I₂ n a).card : ℝ)⁻¹ * ∑ i ∈ I₂ n a,
    (score n a (S.Z i a) - scoreAverage M S I₂ score n a h)^2
  -- @realizes \hat\sigma^2(sample analog of score variance)
-- @node: ass:dml-normality-finite
/-- For [an instrument domain](hyp:Z), the [finite-instrument DML condition](goal)
requires [finitely many instrument values](step:1) and [the discrete topology](step:2). -/
def InstrumentFiniteDML (Z : Type*) [TopologicalSpace Z] : Prop :=
  Finite Z ∧ DiscreteTopology Z -- @realizes \mathcal{Z}(finite instrument domain with its discrete topology)
-- @node: ass:bk-2
/-- For [a proposed number of baseline levels](hyp:K), the [positive-level-count condition](goal)
requires that this number be strictly positive. -/
def LevelCountPos' (K : ℕ) : Prop := LevelCountPos K
variable [Fintype Z] [DecidableEq Z]
/-- For [the instrument domain](hyp:Z) and [covariate domain](hyp:X), the [measurable structure
on level data](goal) is induced by jointly recording the level counts, baseline and policy
instrument sets, and baseline and policy level functions. -/
instance : MeasurableSpace (LevelData Z X) :=
  MeasurableSpace.comap (fun L => (L.K, L.l, L.S, L.T, L.pLev, L.qLev)) inferInstance
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S),
[evaluation selection](hyp:I₂), and [fitted propensity](hyp:pHat), the [averaged propensity](goal)
at [sample size](hyp:n), [sampling outcome](hyp:a), and [instrument value](hyp:z) averages the
fitted propensity over evaluation covariates, using zero when the selection is empty. -/
noncomputable def pBar (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (n : ℕ) (a : A) (z : Z) :=
  ((I₂ n a).card : ℝ)⁻¹ * ∑ i ∈ I₂ n a, pHat n a z (S.Z i a).1
  -- @realizes \bar p_2(average fitted baseline propensity over evaluation covariates)
  -- @realizes \bar q_2(same averaging operator applied to the fitted policy propensity)
/-- For [an instrument domain](hyp:Z), a [recovery vertex](goal) pairs an instrument value
with a flag distinguishing policy vertices from baseline vertices. -/
abbrev RecoveryVertex (Z : Type v) := Bool × Z
/-- Given [baseline propensities](hyp:pb), [policy propensities](hyp:qb), and
[a flagged instrument vertex](hyp:v), its [vertex value](goal) is the policy propensity
for a policy vertex and the baseline propensity otherwise. -/
noncomputable def vertexValue (pb qb : Z → ℝ) (v : RecoveryVertex Z) := if v.1 then qb v.2 else pb v.2
/-- Given [baseline propensities](hyp:pb) and [a zero threshold](hyp:rho), the
[active recovery vertices](goal) comprise every policy vertex and precisely the baseline
vertices whose propensity strictly exceeds the threshold. -/
noncomputable def recoveryActive (pb : Z → ℝ) (rho : ℝ) : Finset (RecoveryVertex Z) :=
  Finset.univ.filter (fun v => v.1 = true ∨ rho < pb v.2)
/-- For [baseline propensities](hyp:pb), [policy propensities](hyp:qb), [a zero threshold](hyp:rho),
[a separation scale](hyp:gap), and [two recovery vertices](hyp:a,b), a [recovery edge](goal)
requires [the first vertex to be active](step:1), [the second vertex to be active](step:2),
[distinct vertices](step:3), and [an absolute difference of their values strictly below half
the separation scale](step:4). -/
noncomputable def recoveryEdge (pb qb : Z → ℝ) (rho gap : ℝ) (a b : RecoveryVertex Z) : Prop :=
  a ∈ recoveryActive pb rho ∧ b ∈ recoveryActive pb rho ∧ a ≠ b ∧
    |vertexValue pb qb a - vertexValue pb qb b| < gap / 2
/-- Given [baseline propensities](hyp:pb), [policy propensities](hyp:qb), [a zero threshold](hyp:rho),
[a separation scale](hyp:gap), and [a starting vertex](hyp:a), its [recovery component](goal)
consists of active vertices reachable from the starting vertex by zero or more recovery edges. -/
noncomputable def recoveryComponent (pb qb : Z → ℝ) (rho gap : ℝ) (a : RecoveryVertex Z) :=
  (recoveryActive pb rho).filter (fun b => Relation.ReflTransGen (recoveryEdge pb qb rho gap) a b)
/-- Given [baseline propensities](hyp:pb), [policy propensities](hyp:qb), and
[a finite collection of recovery vertices](hyp:C), the [component average](goal) is the mean
of their vertex values, with zero assigned to an empty collection. -/
noncomputable def componentAverage (pb qb : Z → ℝ) (C : Finset (RecoveryVertex Z)) :=
  (C.card : ℝ)⁻¹ * ∑ v ∈ C, vertexValue pb qb v
/-- Given [baseline propensities](hyp:pb), [policy propensities](hyp:qb), [a zero threshold](hyp:rho),
and [a separation scale](hyp:gap), the [ordered recovery components](goal) are the distinct
components of active vertices, sorted by nondecreasing average vertex value. -/
noncomputable def recoveryComponents (pb qb : Z → ℝ) (rho gap : ℝ) :=
  ((recoveryActive pb rho).image (recoveryComponent pb qb rho gap)).toList.mergeSort
    (fun C D => componentAverage pb qb C ≤ componentAverage pb qb D)
/-- Given [baseline propensities](hyp:pb), [policy propensities](hyp:qb), [a zero threshold](hyp:rho),
and [a separation scale](hyp:gap), the [recovered level data](goal) use [the ordered recovery
components](step:1), [the sublist containing baseline vertices](step:2), [its length as the number
of positive baseline levels](step:3), [baseline levels equal to zero at index zero, component means
at positive indices up to that count, and one thereafter](step:4), and [policy-containing components
grouped between consecutive baseline levels, with the final upper bound one included](step:5).
[The resulting data record these counts, thresholded baseline sets, component instrument sets,
and constant component-average levels, with boundary and out-of-range conventions](step:6). -/
noncomputable def recoverLevelsAt (pb qb : Z → ℝ) (rho gap : ℝ) : LevelData Z X :=
  let Cs := recoveryComponents pb qb rho gap
  let Bs := Cs.filter (fun C => ∃ z, (false,z) ∈ C)
  let K := Bs.length
  let p := fun k => if k = 0 then 0 else if k ≤ K then componentAverage pb qb (Bs.getD (k-1) ∅) else 1
  let Qs := fun k => Cs.filter (fun C => (∃ z, (true,z) ∈ C) ∧ p k ≤ componentAverage pb qb C ∧
    (if k = K then componentAverage pb qb C ≤ 1 else componentAverage pb qb C < p (k+1)))
  { K := K, l := fun k => (Qs k).length,
    S := fun k => if k = 0 then Finset.univ.filter (fun z => pb z ≤ rho) else
      Finset.univ.filter (fun z => (false,z) ∈ Bs.getD (k-1) ∅),
    T := fun k j => if j = 0 ∨ (Qs k).length < j then ∅ else
      Finset.univ.filter (fun z => (true,z) ∈ (Qs k).getD (j-1) ∅),
    pLev := fun k _ => p k,
    qLev := fun k j _ => if j = 0 then p k else if j ≤ (Qs k).length then
      componentAverage pb qb ((Qs k).getD (j-1) ∅) else p (k+1) }
  -- @realizes \widehat S_k(ordered recovered baseline connected components)
  -- @realizes \widehat T_{j,k}(policy connected components indexed by recovered baseline bins)
-- @node: ass:pin-3
/-- For [baseline propensities](hyp:pb), [policy propensities](hyp:qb), [a zero threshold](hyp:rho),
and [a separation scale](hyp:gap), the [strict-edge condition](goal) says that any two distinct
active vertices share a recovery edge exactly when their values differ by strictly less than
half the separation scale. -/
def RecoveryEdgeStrict (pb qb : Z → ℝ) (rho gap : ℝ) : Prop :=
  ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho, a ≠ b →
    (recoveryEdge pb qb rho gap a b ↔ |vertexValue pb qb a - vertexValue pb qb b| < gap / 2)
/-- A [threshold sequence](hyp:rho) is [admissible for recovery](goal) if it is
[nonincreasing](step:1), [strictly positive at every index](step:2), [convergent to zero](step:3),
and [diverges to positive infinity after multiplication by the fourth root of its index](step:4). -/
def RecoveryThresholdAdmissible (rho : ℕ → ℝ) : Prop :=
  Antitone rho ∧ (∀ n, 0 < rho n) ∧ Tendsto rho atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ)^(1/4 : ℝ) * rho n) atTop atTop
-- @node: def:dml-level-recovery
/-- Given [sample-dependent baseline propensities](hyp:pb), [sample-dependent policy
propensities](hyp:qb), [a threshold sequence](hyp:rho) [admissible for recovery](hyp:_hThreshold),
and [a separation scale](hyp:gap) [that is strictly positive](hyp:_hGap), the [level recovery
procedure](goal) applies component-based recovery at each sample size and sampling outcome
using the threshold at that size. -/
noncomputable def recoverLevels (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (_hThreshold : RecoveryThresholdAdmissible rho) (gap : ℝ) (_hGap : 0 < gap) : ℕ → A → LevelData Z X :=
  fun n a => recoverLevelsAt (pb n a) (qb n a) (rho n) gap
-- @node: ass:pin-4
/-- For [a threshold sequence](hyp:rho), [sample-dependent baseline propensities](hyp:pb),
and [candidate structural-zero sets](hyp:S₀), the [structural-zero threshold condition](goal)
requires [each candidate set to contain exactly the instruments with propensity at most the
threshold](step:1), [nonincreasing thresholds](step:2), [strictly positive thresholds](step:3),
[convergence of thresholds to zero](step:4), and [divergence to positive infinity after
multiplication by the fourth root of sample size](step:5). -/
def StructuralZeroThreshold (rho : ℕ → ℝ) (pb : ℕ → A → Z → ℝ)
    (S₀ : ℕ → A → Finset Z) : Prop :=
  (∀ n a, S₀ n a = Finset.univ.filter (fun z => pb n a z ≤ rho n)) ∧
  Antitone rho ∧ (∀ n, 0 < rho n) ∧ Tendsto rho atTop (𝓝 0) ∧ -- @realizes \rho_n(deterministic positive decreasing sequence converging to zero)
    Tendsto (fun n : ℕ => (n : ℝ)^(1/4 : ℝ) * rho n) atTop atTop -- @realizes \rho_n(n to the one-quarter times rho diverges)
-- @node: ass:pin-43
/-- For [baseline propensities](hyp:pb), [policy propensities](hyp:qb), [a zero threshold](hyp:rho),
and [a separation scale](hyp:gap), the [recovered-bin convention](goal) forms [the ordered
components](step:1), [the baseline-containing sublist](step:2), [the count of that sublist](step:3),
[baseline levels given by zero, baseline component means, and then one](step:4), and [bins of
policy-containing components with means between consecutive baseline levels](step:5).
[For every bin index from zero through the baseline count, membership of a recovered component
is equivalent to containing a policy vertex and satisfying the lower-inclusive, upper-exclusive
bounds, with the final upper bound one included](step:6). -/
def RecoveredBinConventionReading (pb qb : Z → ℝ) (rho gap : ℝ) : Prop :=
  let Cs := recoveryComponents pb qb rho gap
  let Bs := Cs.filter (fun C => ∃ z, (false,z) ∈ C)
  let K := Bs.length
  let p := fun k => if k = 0 then 0 else if k ≤ K then
    componentAverage pb qb (Bs.getD (k-1) ∅) else 1
  let bins := fun k => Cs.filter (fun C => (∃ z, (true,z) ∈ C) ∧
    p k ≤ componentAverage pb qb C ∧
    (if k = K then componentAverage pb qb C ≤ 1 else componentAverage pb qb C < p (k+1)))
  ∀ k ≤ K, ∀ C ∈ Cs, (C ∈ bins k ↔ (∃ z, (true,z) ∈ C) ∧
    p k ≤ componentAverage pb qb C ∧
    (if k = K then componentAverage pb qb C ≤ 1 else componentAverage pb qb C < p (k+1)))
/-- Under [the model's covariate distribution](hyp:M), the [finite integral error](goal)
between [a function](hyp:f) and [a comparison function](hyp:g) is the square root of the
population integral of their squared difference.

The real-valued integral convention returns zero for a nonintegrable squared difference;
rate assumptions instead use the extended population error. -/
noncomputable def finiteL2Error (f g : X → ℝ) := Real.sqrt (∫ x, (f x - g x)^2 ∂xLaw M)
/-- Under [the model's covariate distribution](hyp:M), the [extended population L2 error](goal)
between [a function](hyp:f) and [a comparison function](hyp:g) is the population L2 seminorm
of their difference, allowing an infinite value. -/
noncomputable def l2Error (f g : X → ℝ) : ℝ≥0∞ :=
  eLpNorm (fun x => f x - g x) 2 (xLaw M)
-- @node: finiteL2Error_ofReal_le_l2Error
/-- For [a function](hyp:f) and [a comparison function](hyp:g), [the finite integral error,
viewed as a nonnegative extended real number, is no larger than the extended population
L2 error](goal). -/
lemma finiteL2Error_ofReal_le_l2Error (f g : X → ℝ) :
    ENNReal.ofReal (finiteL2Error M f g) ≤ l2Error M f g := by
  have hi : 0 ≤ ∫ x, (f x - g x)^2 ∂xLaw M :=
    integral_nonneg fun x => sq_nonneg _
  have h := enorm_integral_le_lintegral_enorm (μ := xLaw M)
    (fun x => (f x - g x)^2)
  rw [Real.enorm_eq_ofReal hi] at h
  have hpow (y : ℝ) : ‖y^2‖ₑ = ‖y‖ₑ ^ (2 : ℝ) := by
    rw [Real.enorm_eq_ofReal (sq_nonneg _), Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_two, sq_abs]
  unfold finiteL2Error l2Error
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hi (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow (by simpa only [hpow] using h) (by positivity)
-- @node: ass:pin-65
/-- For [the model](hyp:M), [componentwise fitted functions](hyp:fit), [their population
targets](hyp:truth), and [reported extended errors](hyp:error), the [population L2 interpretation](goal)
requires each reported error to equal the L2 seminorm of the fitted function minus its target,
integrating over the population covariate distribution while holding the fitted function fixed. -/
def NuisanceL2NormPopulationReading {C : Type*}
    (fit : ℕ → A → C → X → ℝ) (truth : C → X → ℝ)
    (error : ℕ → A → C → ℝ≥0∞) : Prop :=
  ∀ n a c, error n a c = eLpNorm (fun x => fit n a c x - truth c x) 2 (xLaw M)
/-- Under [a sampling measure](hyp:μ), [an extended nonnegative error sequence](hyp:error)
is [little-o in probability at a real rate sequence](goal) specified by [the rates](hyp:rate)
when, for every positive real multiplier, the measure of outcomes whose error is at least
that multiplier times the rate tends to zero, including outcomes with infinite error. -/
def ExtendedLittleOp (μ : Measure A) (error : ℕ → A → ℝ≥0∞) (rate : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => μ {a | ENNReal.ofReal (ε * rate n) ≤ error n a}) atTop (𝓝 0)
-- @node: ExtendedLittleOp.of_norm_le
/-- Under [a sampling measure](hyp:μ), for [extended errors](hyp:error), [a rate sequence](hyp:rate),
and [a real-valued random sequence](hyp:f), if [the extended errors are little-o in probability
at that rate](hyp:h) and [they bound the absolute value of the random sequence at every index
and outcome](hyp:hle), then [the random sequence is little-o in probability at the same rate](goal). -/
lemma ExtendedLittleOp.of_norm_le (μ : Measure A) (error : ℕ → A → ℝ≥0∞)
    (rate : ℕ → ℝ) (f : ℕ → A → ℝ) (h : ExtendedLittleOp μ error rate)
    (hle : ∀ n a, ENNReal.ofReal ‖f n a‖ ≤ error n a) :
    Causalean.Stat.IsLittleOp f rate μ := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
  · intro n
    exact bot_le
  · intro n
    exact measure_mono fun a ha => (ENNReal.ofReal_le_ofReal ha).trans (hle n a)
-- @node: ass:dml-normality-first-stage
/-- For [the model](hyp:M), [sampling measure](hyp:μ), and [fitted instrument-specific
propensities](hyp:pHat), the [first-stage rate condition](goal) requires the maximum extended
population L2 error across instruments to be little-o in probability relative to sample size
to the negative one-quarter power, along even sample sizes starting at two. -/
def FirstStageRate (μ : Measure A) (pHat : ℕ → A → Z → X → ℝ) : Prop :=
  ExtendedLittleOp μ (fun n a => Finset.univ.sup' Finset.univ_nonempty
    (fun z => l2Error M (pHat (2*(n+1)) a z) (M.prop z)))
    (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ))
-- @node: ass:dml-normality-nuisance-rates
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [componentwise fits](hyp:fit), and
[population targets](hyp:truth), the [nuisance rate condition](goal) requires each component's
extended population L2 error to be little-o in probability relative to sample size to the
negative one-quarter power, along even sample sizes starting at two. -/
def NuisanceRates {C : Type*} (μ : Measure A)
    (fit : ℕ → A → C → X → ℝ) (truth : C → X → ℝ) : Prop :=
  ∀ c, ExtendedLittleOp μ (fun n a => l2Error M (fit (2*(n+1)) a c) (truth c))
    (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ))
/-- For [the model](hyp:M), [sampling measure](hyp:μ), and [fitted instrument-specific
propensities](hyp:pHat), the [finite first-stage rate condition](goal) requires the maximum
finite integral error across instruments to be little-o in probability relative to sample size
to the negative one-quarter power, along even sample sizes starting at two. -/
def FiniteFirstStageRate (μ : Measure A) (pHat : ℕ → A → Z → X → ℝ) : Prop :=
  Causalean.Stat.IsLittleOp (fun n a => Finset.univ.sup' Finset.univ_nonempty
    (fun z => finiteL2Error M (pHat (2*(n+1)) a z) (M.prop z)))
    (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [componentwise fits](hyp:fit), and
[population targets](hyp:truth), the [finite nuisance rate condition](goal) requires each
component's finite integral error to be little-o in probability relative to sample size to
the negative one-quarter power, along even sample sizes starting at two. -/
def FiniteNuisanceRates {C : Type*} (μ : Measure A) (fit : ℕ → A → C → X → ℝ) (truth : C → X → ℝ) : Prop :=
  ∀ c, Causalean.Stat.IsLittleOp (fun n a => finiteL2Error M (fit (2*(n+1)) a c) (truth c))
    (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ
-- @node: FirstStageRate.finite
/-- For [a sampling measure](hyp:μ) and [fitted instrument-specific propensities](hyp:pHat),
[the first-stage rate condition using extended population L2 errors](hyp:h) implies
[the corresponding rate condition using finite integral errors](goal). -/
lemma FirstStageRate.finite (μ : Measure A) (pHat : ℕ → A → Z → X → ℝ)
    (h : FirstStageRate M μ pHat) : FiniteFirstStageRate M μ pHat := by
  apply ExtendedLittleOp.of_norm_le μ _ _ _ h
  intro n a
  obtain ⟨z, hz, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun z => finiteL2Error M (pHat (2*(n+1)) a z) (M.prop z))
  rw [hmax]
  simp only [finiteL2Error, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (finiteL2Error_ofReal_le_l2Error M _ _).trans
    (Finset.le_sup' (fun z => l2Error M (pHat (2*(n+1)) a z) (M.prop z)) hz)
-- @node: NuisanceRates.finite
/-- For [a sampling measure](hyp:μ), [componentwise fits](hyp:fit), and [population targets](hyp:truth),
[the componentwise rate conditions using extended population L2 errors](hyp:h) imply
[the corresponding componentwise rate conditions using finite integral errors](goal). -/
lemma NuisanceRates.finite {C : Type*} (μ : Measure A)
    (fit : ℕ → A → C → X → ℝ) (truth : C → X → ℝ)
    (h : NuisanceRates M μ fit truth) : FiniteNuisanceRates M μ fit truth := by
  intro c
  apply ExtendedLittleOp.of_norm_le μ _ _ _ (h c)
  intro n a
  simp only [finiteL2Error, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact finiteL2Error_ofReal_le_l2Error M _ _
-- @node: ass:pin-22
/-- For [the model](hyp:M), [sampling measure](hyp:μ), and [fitted propensities](hyp:pHat),
the [fresh-draw first-stage rate requirement](goal) is the first-stage rate condition: the
maximum population L2 error across instruments, integrating over fresh population covariates,
is little-o in probability relative to sample size to the negative one-quarter power along
even sample sizes starting at two. -/
def FirstStageRateFreshDrawReading (μ : Measure A) (pHat : ℕ → A → Z → X → ℝ) : Prop := FirstStageRate M μ pHat
-- @node: ass:pin-24
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S),
[training and evaluation selections](hyp:I₁,I₂), [componentwise fits](hyp:fit), [population
targets](hyp:truth), and [reported squared errors](hyp:squaredError), the [componentwise
nuisance-rate interpretation](goal) requires [a uniform equal-half split independent of the
observations](step:1), [each reported squared error to equal the squared extended population
L2 error with the fit held fixed](step:2), and [each component's extended L2 error to be little-o
in probability relative to sample size to the negative one-quarter power along even sample
sizes starting at two](step:3). -/
def NuisanceRatesComponentwiseReading {C : Type*} (μ : Measure A)
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (fit : ℕ → A → C → X → ℝ) (truth : C → X → ℝ)
    (squaredError : ℕ → A → C → ℝ≥0∞) : Prop :=
  EqualHalfSplit M μ S I₁ I₂ ∧
  (∀ n a c, squaredError n a c = (l2Error M (fit n a c) (truth c))^2) ∧
  NuisanceRates M μ fit truth
/-- For [the model](hyp:M), [level data](hyp:L), and [continuous-outcome nuisances](hyp:e),
the [continuous clipping requirement](goal) places [instrument propensities](step:1),
[baseline levels and baseline probabilities](step:2), [policy probabilities and policy weights](step:3),
and [instrument shares](step:4) in the unit interval, [full-interval weights in the interval from
minus one to one](step:5), and [the tail weight in the unit interval](step:6); it places
[band boundaries within the model's outcome bounds](step:7), [upper indicator regressions](step:8)
and [lower indicator regressions](step:9) in the unit interval, [upper truncated means](step:10)
and [lower truncated means](step:11) between the smaller of zero and the lower outcome bound
and the larger of zero and the upper bound, [upper full-interval means](step:12) and
[lower full-interval means](step:13) within the outcome bounds, and [both higher-policy and
higher-baseline probability fits in the unit interval](step:14), at every admissible index and covariate. -/
def ContClipping (L : LevelData Z X) (e : NuisanceCont L) : Prop := -- @realizes \hat\eta(fitted continuous nuisance carrier)
  (∀ z x, e.prop z x ∈ Icc (0:ℝ) 1) ∧ -- @realizes p(component range on this conjunct)
  (∀ k x, e.pLev k x ∈ Icc (0:ℝ) 1 ∧ e.piLev k x ∈ Icc (0:ℝ) 1) ∧ -- @realizes p_k(component range on this conjunct) @realizes \pi_k(component range on this conjunct)
  (∀ a x, e.tauLev a x ∈ Icc (0:ℝ) 1 ∧ e.gamma a x ∈ Icc (0:ℝ) 1) ∧ -- @realizes \tau_{j,k}(component range on this conjunct) @realizes \gamma_{j,k}(component range on this conjunct)
  (∀ a z x, e.share a z x ∈ Icc (0:ℝ) 1) ∧ -- @realizes a_{j,k}(component range on this conjunct)
  (∀ k x, e.gammaFull k x ∈ Icc (-1:ℝ) 1) ∧ (∀ x, e.gammaTail x ∈ Icc (0:ℝ) 1) ∧ -- @realizes \gamma_{\text{full},k}(component range on this conjunct) @realizes \gamma_K(component range on this conjunct)
  (∀ a x, e.nu a x ∈ Icc M.yMin M.yMax) ∧ -- @realizes \nu_{j,k}(component range on this conjunct)
  (∀ a x, e.Mplus a x ∈ Icc (0:ℝ) 1) ∧ -- @realizes M_{j,k}^{+}(component range on this conjunct)
  (∀ a x, e.Mminus a x ∈ Icc (0:ℝ) 1) ∧ -- @realizes M_{j,k}^{-}(component range on this conjunct)
  (∀ a x, e.Jplus a x ∈ Icc (min 0 M.yMin) (max 0 M.yMax)) ∧ -- @realizes J_{j,k}^{+}(component range on this conjunct)
  (∀ a x, e.Jminus a x ∈ Icc (min 0 M.yMin) (max 0 M.yMax)) ∧ -- @realizes J_{j,k}^{-}(component range on this conjunct)
  (∀ k x, e.JfullPlus k x ∈ Icc M.yMin M.yMax) ∧ -- @realizes J_{\text{full},k}^{+}(component range on this conjunct)
  (∀ k x, e.JfullMinus k x ∈ Icc M.yMin M.yMax) ∧ -- @realizes J_{\text{full},k}^{-}(component range on this conjunct)
  (∀ k x, e.higherPolicyFit k x ∈ Icc (0:ℝ) 1 ∧ e.higherBaselineFit k x ∈ Icc (0:ℝ) 1)
/-- For [level data](hyp:L) and [continuous-outcome nuisances](hyp:e), the
[probability clipping before differencing requirement](goal) requires [higher-policy and
higher-baseline fits in the unit interval](step:1), [full-interval weights equal to their
policy-minus-baseline differences](step:2), and unit-interval values for [baseline probabilities](step:3),
[policy probabilities](step:4), [the tail weight](step:5), [policy weights](step:6),
[instrument propensities](step:7), [baseline levels](step:8), [instrument shares](step:9),
[upper indicator regressions](step:10), and [lower indicator regressions](step:11), everywhere. -/
def ContProbabilitiesClippedBeforeDifference (L : LevelData Z X) (e : NuisanceCont L) : Prop :=
  (∀ k x, e.higherPolicyFit k x ∈ Icc (0:ℝ) 1 ∧ e.higherBaselineFit k x ∈ Icc (0:ℝ) 1) ∧
  (∀ k x, e.gammaFull k x = e.higherPolicyFit k x - e.higherBaselineFit k x) ∧
    (∀ k x, e.piLev k x ∈ Icc (0:ℝ) 1) ∧ (∀ k x, e.tauLev k x ∈ Icc (0:ℝ) 1) ∧ -- @realizes \pi_k(component range on this conjunct) @realizes \tau_{j,k}(component range on this conjunct)
    (∀ x, e.gammaTail x ∈ Icc (0:ℝ) 1) ∧ (∀ k x, e.gamma k x ∈ Icc (0:ℝ) 1) ∧ -- @realizes \gamma_K(component range on this conjunct) @realizes \gamma_{j,k}(component range on this conjunct)
  (∀ z x, e.prop z x ∈ Icc (0 : ℝ) 1) ∧
  (∀ k x, e.pLev k x ∈ Icc (0 : ℝ) 1) ∧
  (∀ a z x, e.share a z x ∈ Icc (0 : ℝ) 1) ∧
  (∀ a x, e.Mplus a x ∈ Icc (0 : ℝ) 1) ∧
  (∀ a x, e.Mminus a x ∈ Icc (0 : ℝ) 1)
/-- For [level data](hyp:L), [continuous-outcome nuisances](hyp:e), and [a denominator bound](hyp:cpi),
the [continuous denominator clipping requirement](goal) puts [all baseline probabilities](step:1)
and [policy probabilities with nonempty instrument sets](step:2) between half the bound and one,
at every covariate. -/
def ContDenominatorsClipped (L : LevelData Z X) (e : NuisanceCont L) (cpi : ℝ) : Prop :=
  (∀ k x, e.piLev k x ∈ Icc (cpi/2) 1) ∧ -- @realizes \hat\pi_k(fitted baseline denominators clipped away from zero)
  (∀ a x, (L.T a.val.1 a.val.2).Nonempty → e.tauLev a x ∈ Icc (cpi/2) 1) -- @realizes \hat\tau_{j,k}(fitted policy denominators clipped away from zero)
/-- For [level data](hyp:L) and [continuous-outcome nuisances](hyp:e), the [share simplex
requirement](goal) says that, for every policy index and covariate, [all instrument shares are
nonnegative](step:1) and [their sum over that policy instrument set is one](step:2). -/
def ContFittedSharesSimplex (L : LevelData Z X) (e : NuisanceCont L) : Prop :=
  ∀ a x, (∀ z, 0 ≤ e.share a z x) ∧ ∑ z ∈ L.T a.val.1 a.val.2, e.share a z x = 1
-- @node: ass:dml-normality-continuous-nuisances
/-- For [the model](hyp:M), [level data](hyp:L), and [population continuous nuisances](hyp:e₀),
the [boundary identification requirement](goal) says that each boundary regression equals the
corresponding model band boundary for almost every population covariate. -/
def ContinuousNuisanceList (L : LevelData Z X) (e₀ : NuisanceCont L) : Prop :=
  ∀ a, ∀ᵐ x ∂xLaw M, e₀.nu a x = bandBoundary M L a.val.1 a.val.2 x
-- @node: ass:dml-normality-boundary-densities
/-- For [the model](hyp:M) and [level data](hyp:L), the [bounded boundary density condition](goal)
requires a common radius and real constant such that [the radius is positive](step:1) and
[every interval inside that radius of any interior-bin policy boundary has treated-outcome
probability at most the constant times its length, for the next baseline level and also the
current level when positive, for almost every population covariate](step:2). -/
def BoundaryDensitiesBounded (L : LevelData Z X) : Prop :=
  ∃ r C : ℝ, 0 < r ∧ ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k →
    ∀ k', k' = k+1 ∨ (1 ≤ k ∧ k' = k) → ∀ᵐ x ∂xLaw M,
      ∀ a b, bandBoundary M L k j x - r ≤ a → a ≤ b →
        b ≤ bandBoundary M L k j x + r →
        (treatedLaw M L k' x (Ioc a b)).toReal ≤ C * (b-a)
-- @node: ass:dml-normality-no-lower-atom
/-- For [the model](hyp:M) and [level data](hyp:L), the [no lower-endpoint atom condition](goal)
requires zero treated-outcome mass at the lower outcome bound for almost every population
covariate, at the next baseline level of every nonfinal bin and also at its current level when positive. -/
def NoAtomAtLowerEndpoint (L : LevelData Z X) : Prop :=
  ∀ k < L.K, ∀ k', k' = k+1 ∨ (1 ≤ k ∧ k' = k) →
    ∀ᵐ x ∂xLaw M, treatedLaw M L k' x {M.yMin} = 0
-- @node: ass:dml-normality-binary
/-- For [the model](hyp:M), the [binary outcome condition](goal) requires the outcome to be
zero or one almost surely under the population law. -/
def OutcomeBinaryAE : Prop := ∀ᵐ a ∂M.law.toMeasure, M.Y a = 0 ∨ M.Y a = 1
-- @node: ass:pin-25
/-- For [the model](hyp:M), the [binary outcome interpretation](goal) requires the outcome
to equal zero or one almost surely under the population law. -/
def OutcomeBinaryAEReading : Prop := OutcomeBinaryAE M
-- @node: def:dml-binary-rearrangement
/-- For [level data](hyp:L) and [binary-outcome nuisances](hyp:e), the [rearranged nuisance
vector](goal) replaces the positive-level success regressions by their unit-interval-clipped
values sorted in nondecreasing order at each covariate, assigning the sorted values to successive
positive levels and using zero if an entry is missing; all other components are retained. -/
noncomputable def rearrangeP1 (L : LevelData Z X) (e : NuisanceBin L) : NuisanceBin L :=
  { e with P1 := fun k x =>
      ((List.range L.K).map (fun i => min 1 (max 0 (positiveValue e.P1 (i+1) x)))).mergeSort (· ≤ ·) |>.getD (k.val-1) 0 }
-- @node: ass:pin-47
/-- For [level data](hyp:L) and [binary-outcome nuisances](hyp:e), the [sorting interpretation](goal)
requires [the rearranged success regression at structural level zero to be zero](step:1) and
[each positive-level regression to equal the corresponding entry of the nondecreasing sort
of the clipped original positive-level values, with zero for a missing entry](step:2), at every covariate. -/
def RearrangementSortReading (L : LevelData Z X) (e : NuisanceBin L) : Prop :=
  (∀ x, positiveValue (rearrangeP1 L e).P1 0 x = 0) ∧
  (∀ k x, (rearrangeP1 L e).P1 k x =
    (((List.range L.K).map (fun i => min 1 (max 0 (positiveValue e.P1 (i+1) x)))).mergeSort (· ≤ ·)).getD (k.val-1) 0)
/-- For [level data](hyp:L) and [binary-outcome nuisances](hyp:e), the [binary clipping
requirement](goal) puts [instrument propensities](step:1), [baseline levels, success regressions,
and baseline probabilities](step:2), [policy probabilities and policy weights](step:3),
[instrument shares](step:4), and [the tail weight](step:5) in the unit interval everywhere,
and [requires full-interval weights to be differences of some unit-interval-valued policy
and baseline fits](step:6). -/
def BinClipping (L : LevelData Z X) (e : NuisanceBin L) : Prop :=
  (∀ z x, e.prop z x ∈ Icc (0:ℝ) 1) ∧ -- @realizes p(component range on this conjunct)
  (∀ k x, e.pLev k x ∈ Icc (0:ℝ) 1 ∧ e.P1 k x ∈ Icc (0:ℝ) 1 ∧ e.piLev k x ∈ Icc (0:ℝ) 1) ∧ -- @realizes p_k(component range on this conjunct) @realizes P_{1,k}(component range on this conjunct) @realizes \pi_k(component range on this conjunct)
  (∀ a x, e.tauLev a x ∈ Icc (0:ℝ) 1 ∧ e.gamma a x ∈ Icc (0:ℝ) 1) ∧ -- @realizes \tau_{j,k}(component range on this conjunct) @realizes \gamma_{j,k}(component range on this conjunct)
  (∀ a z x, e.share a z x ∈ Icc (0:ℝ) 1) ∧ -- @realizes a_{j,k}(component range on this conjunct)
  (∀ x, e.gammaTail x ∈ Icc (0:ℝ) 1) ∧ -- @realizes \gamma_K(component range on this conjunct)
  (∃ policyFit baselineFit : Fin L.K → X → ℝ,
    (∀ k x, policyFit k x ∈ Icc (0:ℝ) 1 ∧ baselineFit k x ∈ Icc (0:ℝ) 1) ∧
    ∀ k x, e.gammaFull k x = policyFit k x - baselineFit k x)

/-- For [level data](hyp:L) and [binary-outcome nuisances](hyp:e), if [the binary clipping
requirement holds](hyp:h), then [the full-interval weight lies between minus one and one](goal)
at [any full-interval index](hyp:k) and [any covariate](hyp:x). -/
lemma binClipping_full_range (L : LevelData Z X) (e : NuisanceBin L)
    (h : BinClipping L e) (k : Fin L.K) (x : X) : e.gammaFull k x ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨policyFit, baselineFit, hrange, hdiff⟩ := h.2.2.2.2.2
  have hp := (hrange k x).1
  have hb := (hrange k x).2
  rw [hdiff k x]
  constructor <;> linarith [hp.1, hp.2, hb.1, hb.2]

/-- For [level data](hyp:L), [binary-outcome nuisances](hyp:e), and [a denominator bound](hyp:cpi),
the [binary denominator clipping requirement](goal) puts [all baseline probabilities](step:1)
and [policy probabilities with nonempty instrument sets](step:2) between half the bound and one,
at every covariate. -/
def BinDenominatorsClipped (L : LevelData Z X) (e : NuisanceBin L) (cpi : ℝ) : Prop :=
  (∀ k x, e.piLev k x ∈ Icc (cpi/2) 1) ∧ -- @realizes \hat\pi_k(fitted baseline denominators clipped away from zero)
  (∀ a x, (L.T a.val.1 a.val.2).Nonempty → e.tauLev a x ∈ Icc (cpi/2) 1) -- @realizes \hat\tau_{j,k}(fitted policy denominators clipped away from zero)
/-- For [level data](hyp:L) and [binary-outcome nuisances](hyp:e), the [binary share simplex
requirement](goal) says that, at every policy index and covariate, [all instrument shares are
nonnegative](step:1) and [their sum over that policy instrument set is one](step:2). -/
def BinFittedSharesSimplex (L : LevelData Z X) (e : NuisanceBin L) : Prop :=
  ∀ a x, (∀ z, 0 ≤ e.share a z x) ∧ ∑ z ∈ L.T a.val.1 a.val.2, e.share a z x = 1


/-- For [level data](hyp:L) and [binary-outcome nuisances](hyp:e), the [binary score clipping
requirement](goal) puts [instrument propensities](step:1), [baseline levels, success regressions,
and baseline probabilities](step:2), [policy probabilities and policy weights](step:3),
and [instrument shares](step:4) in the unit interval, [full-interval weights between minus one
and one](step:5), and [the tail weight in the unit interval](step:6), everywhere. -/
def BinScoreClipped (L : LevelData Z X) (e : NuisanceBin L) : Prop :=
  (∀ z x, e.prop z x ∈ Icc (0:ℝ) 1) ∧ -- @realizes p(component range on this conjunct)
  (∀ k x, e.pLev k x ∈ Icc (0:ℝ) 1 ∧ e.P1 k x ∈ Icc (0:ℝ) 1 ∧ e.piLev k x ∈ Icc (0:ℝ) 1) ∧ -- @realizes p_k(component range on this conjunct) @realizes P_{1,k}(component range on this conjunct) @realizes \pi_k(component range on this conjunct)
  (∀ a x, e.tauLev a x ∈ Icc (0:ℝ) 1 ∧ e.gamma a x ∈ Icc (0:ℝ) 1) ∧ -- @realizes \tau_{j,k}(component range on this conjunct) @realizes \gamma_{j,k}(component range on this conjunct)
  (∀ a z x, e.share a z x ∈ Icc (0:ℝ) 1) ∧ -- @realizes a_{j,k}(component range on this conjunct)
  (∀ k x, e.gammaFull k x ∈ Icc (-1:ℝ) 1) ∧ (∀ x, e.gammaTail x ∈ Icc (0:ℝ) 1) -- @realizes \gamma_{\text{full},k}(component range on this conjunct) @realizes \gamma_K(component range on this conjunct)
-- @node: ass:dml-normality-score-clipping
/-- For [the model](hyp:M), [level data](hyp:L), and [nuisances from either outcome regime](hyp:e),
the [score clipping condition](goal) requires [continuous clipping for continuous-outcome
nuisances](step:1) or [binary score clipping for binary-outcome nuisances](step:2). -/
def ScoreNuisancesClipped (L : LevelData Z X) (e : NuisanceCont L ⊕ NuisanceBin L) : Prop :=
  match e with | .inl e => ContClipping M L e | .inr e => BinScoreClipped L e
-- @node: ass:pin-23
/-- For [the model](hyp:M), [level data](hyp:L), and [continuous or binary nuisances](hyp:e),
the [clipping range interpretation](goal) requires the score clipping ranges appropriate to
the outcome regime. -/
def ClippingRangesReading (L : LevelData Z X) (e : NuisanceCont L ⊕ NuisanceBin L) : Prop := ScoreNuisancesClipped M L e
-- @node: ass:dml-normality-probability-clipping
/-- For [level data](hyp:L) and [continuous or binary nuisances](hyp:e), the
[clipping before differencing condition](goal) requires [the continuous probability clipping
and difference identities in the continuous regime](step:1) or [binary clipping, including
a representation of full-interval weights as differences of unit-interval fits, in the binary regime](step:2). -/
def ProbabilitiesClippedBeforeDifference (L : LevelData Z X) (e : NuisanceCont L ⊕ NuisanceBin L) : Prop :=
  match e with | .inl e => ContProbabilitiesClippedBeforeDifference L e | .inr e => BinClipping L e
-- @node: ass:dml-normality-denominator-clipping
/-- For [level data](hyp:L), [continuous or binary nuisances](hyp:e), and [a denominator
bound](hyp:cpi), the [denominator clipping condition](goal) requires baseline probabilities
and policy probabilities with nonempty instrument sets to lie between half the bound and one,
using [the continuous condition in the continuous regime](step:1) and [the binary condition
in the binary regime](step:2). -/
def DenominatorsClipped (L : LevelData Z X) (e : NuisanceCont L ⊕ NuisanceBin L) (cpi : ℝ) : Prop :=
  match e with | .inl e => ContDenominatorsClipped L e cpi | .inr e => BinDenominatorsClipped L e cpi
-- @node: ass:dml-simplex-shares
/-- For [level data](hyp:L) and [continuous or binary nuisances](hyp:e), the [fitted share
simplex condition](goal) requires nonnegative shares summing to one within each policy instrument
set, using [the continuous share condition](step:1) or [the binary share condition](step:2)
according to the outcome regime. -/
def FittedSharesSimplex (L : LevelData Z X) (e : NuisanceCont L ⊕ NuisanceBin L) : Prop :=
  match e with | .inl e => ContFittedSharesSimplex L e | .inr e => BinFittedSharesSimplex L e
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S),
[training selection](hyp:I₁), [evaluation selection](hyp:I₂), [fitted propensities](hyp:pHat),
[a policy transformation](hyp:phi), [a threshold sequence](hyp:rho), and [a separation scale](hyp:gap),
the [recovered level data](goal) at [sample size](hyp:n) and [sampling outcome](hyp:a) apply
component-based recovery to evaluation averages of the baseline fits and their policy transforms,
using the threshold at that size. -/
noncomputable def recoveredData (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ) (n : ℕ) (a : A) : LevelData Z X :=
  recoverLevelsAt (pBar M S I₂ pHat n a) (pBar M S I₂ (fun n a => policyProp phi (pHat n a)) n a) (rho n) gap
/-- For [level data](hyp:L), the [recovery labels](goal) record the number of positive baseline
levels, the policy-level count in each bin, and the baseline and policy instrument sets. -/
noncomputable def recoveryLabels (L : LevelData Z X) := (L.K,L.l,L.S,L.T)
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S),
[training selection](hyp:I₁), [evaluation selection](hyp:I₂), [fitted propensities](hyp:pHat),
[a policy transformation](hyp:phi), [a threshold sequence](hyp:rho), and [a separation scale](hyp:gap),
the [recovered information view](goal) at [sample size](hyp:n) and [sampling outcome](hyp:a)
pairs the masked training observations and training indices with the labels recovered from
evaluation-averaged baseline and policy propensities. -/
noncomputable def recoveredView (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ) (n : ℕ) (a : A) :=
  (trainingView M S I₁ n a, recoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap n a))
/-- For [the model](hyp:M), [sampling measure](hyp:μ), [observed sample](hyp:S),
[training and evaluation selections](hyp:I₁,I₂), [fitted propensities](hyp:pHat),
[a policy transformation](hyp:phi), [a recovery threshold sequence](hyp:rho), [a separation scale](hyp:gap),
[continuous nuisance fits on the recovered levels](hyp:eHat), and [a denominator bound](hyp:cpi),
the [continuous fitting scope condition](goal) requires [joint measurability of propensity
fits using only the training view and predictor arguments](step:1), [unit-interval propensity
fits everywhere](step:2), [agreement of nuisance propensities with those fits](step:3),
[score clipping, probability clipping before differencing, denominator clipping, and share
simplex constraints at every size and outcome](step:4), and [joint measurability of the
boundary regressions using only the recovered information view and covariates](step:5). -/
def ContinuousFitScope (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoverLevelsAt (pBar M S I₂ pHat n a)
      (pBar M S I₂ (fun n a => policyProp phi (pHat n a)) n a) (rho n) gap : LevelData Z X))
    (cpi : ℝ) : Prop :=
  TrainingPredictorMeasurable M S I₁ (fun n a (zx : Z × X) => pHat n a zx.1 zx.2) ∧ (∀ n a z x, pHat n a z x ∈ Icc (0:ℝ) 1) ∧
  (∀ n a, (eHat n a).prop = pHat n a) ∧
  (∀ n a, ScoreNuisancesClipped M _ (.inl (eHat n a)) ∧
    ProbabilitiesClippedBeforeDifference _ (.inl (eHat n a)) ∧ DenominatorsClipped _ (.inl (eHat n a)) cpi ∧
    FittedSharesSimplex _ (.inl (eHat n a))) ∧
  (∀ n, Measurable[MeasurableSpace.prod
    (MeasurableSpace.comap (recoveredView M S I₁ I₂ pHat phi rho gap n) inferInstance) inferInstance]
    (fun ax : A × X => fun k j => nuValue M (eHat n ax.1) k j ax.2))

/-- For [the model](hyp:M), [level data](hyp:L), [continuous nuisances](hyp:e),
[a component code with baseline index, policy index, and instrument](hyp:c), and [a covariate](hyp:x),
the [selected continuous component](goal) extracts [the baseline index](step:1),
[the policy index](step:2), and [the instrument](step:3), then [uses the code to return,
in order from zero through thirteen, the instrument propensity, baseline level, baseline
probability, policy probability, within-set share, full-interval weight, policy weight, tail
weight, boundary, upper indicator regression, lower indicator regression, upper truncated
mean, lower truncated mean, or upper full-interval mean; all other codes return the lower
full-interval mean](step:4), with the component accessors' boundary conventions and zero
shares outside the policy instrument set. -/
noncomputable def contComponent (L : LevelData Z X) (e : NuisanceCont L)
    (c : ℕ × ℕ × ℕ × Z) (x : X) :=
  let k := c.2.1; let j := c.2.2.1; let z := c.2.2.2
  match c.1 with
  | 0 => e.prop z x
  | 1 => positiveValue e.pLev k x
  | 2 => positiveValue e.piLev k x
  | 3 => regularValue e.tauLev k j x
  | 4 => if z ∈ L.T k j then shareValue e k j z x else 0
  | 5 => fullValue e.gammaFull k x
  | 6 => regularValue e.gamma k j x
  | 7 => e.gammaTail x
  | 8 => nuValue M e k j x
  | 9 => boundaryValue e.Mplus k j x
  | 10 => minusBoundaryValue e.Mminus k j x
  | 11 => meanValue e.Jplus k j x
  | 12 => minusMeanValue e.Jminus k j x
  | 13 => fullValue e.JfullPlus k x
  | _ => minusFullValue e k x
/-- For [level data](hyp:L), [binary nuisances](hyp:e), [a component code with baseline
index, policy index, and instrument](hyp:c), and [a covariate](hyp:x), the [selected binary
component](goal) extracts [the baseline index](step:1), [the policy index](step:2), and
[the instrument](step:3), then [returns the instrument propensity, baseline level, success
regression, baseline probability, policy probability, within-set share, full-interval weight,
or policy weight for codes zero through seven, respectively, and the tail weight for all
other codes](step:4), using the component accessors' boundary conventions and returning zero
for shares with invalid policy indices or instruments outside the policy set. -/
noncomputable def binComponent (L : LevelData Z X) (e : NuisanceBin L)
    (c : ℕ × ℕ × ℕ × Z) (x : X) :=
  let k := c.2.1; let j := c.2.2.1; let z := c.2.2.2
  match c.1 with
  | 0 => e.prop z x
  | 1 => positiveValue e.pLev k x
  | 2 => positiveValue e.P1 k x
  | 3 => positiveValue e.piLev k x
  | 4 => regularValue e.tauLev k j x
  | 5 => if hc : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k then
      if z ∈ L.T k j then e.share ⟨(k,j),hc⟩ z x else 0
    else 0
  | 6 => fullValue e.gammaFull k x
  | 7 => regularValue e.gamma k j x
  | _ => e.gammaTail x

/-- For [a finite list of real errors](hyp:errors), the [error maximum](goal) is the largest
of zero and all list entries, hence zero for an empty list. -/
def maxErrors (errors : List ℝ) : ℝ := errors.foldr max 0

/-- For [level data](hyp:L), the [policy error indices](goal) list every bin from zero
through the final baseline bin, paired with each positive policy index up to that bin's
policy-level count, in increasing bin and policy order. -/
def policyErrorIndices (L : LevelData Z X) : List (ℕ × ℕ) :=
  (List.range (L.K + 1)).flatMap fun k =>
    (List.range (L.l k)).map fun j => (k, j + 1)

/-- For [the model](hyp:M), [a policy transformation](hyp:phi), [level data](hyp:L), and
[sample-dependent continuous nuisance fits](hyp:fit), the [finite continuous regression-error
magnitude](goal) at [sample size](hyp:n) and [sampling outcome](hyp:a) selects [the fitted
nuisance vector](step:1), [the population nuisance vector](step:2), and [an arbitrary instrument
for components that do not depend on instruments](step:3), then [takes the maximum of zero
and the population L2 integral errors for instrument propensities, positive baseline levels,
pooled policy propensities, interior-bin boundaries, upper and lower indicator and truncated-mean
regressions, and upper and lower full-interval means over the enumerated indices](step:4).

Each fitted function is held fixed while integrating over population covariates. -/
noncomputable def finiteRegressionErrorMagnitude (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (fit : ℕ → A → NuisanceCont L) (n : ℕ) (a : A) : ℝ :=
  let e := fit n a
  let truth := trueNuisance M L
  let z0 : Z := Classical.choice inferInstance
  maxErrors (
    (Finset.univ.toList.map fun z => finiteL2Error M (e.prop z) (truth.prop z)) ++
    ((List.range L.K).map fun k =>
      finiteL2Error M (positiveValue e.pLev (k+1)) (positiveValue truth.pLev (k+1))) ++
    ((policyErrorIndices L).map fun kj =>
      finiteL2Error M (pooledQ phi L e kj.1 kj.2) (pooledQ phi L truth kj.1 kj.2)) ++
    ((List.range L.K).flatMap fun k =>
      ((List.range (L.l k)).map fun j =>
        finiteL2Error M (nuValue M e k (j+1)) (nuValue M truth k (j+1))) ++
      ((List.range (L.l k+1)).flatMap fun j =>
        [9,10,11,12].map fun c =>
          finiteL2Error M (contComponent M L e (c,k,j,z0))
            (contComponent M L truth (c,k,j,z0))) ++
      ([13,14].map fun c =>
        finiteL2Error M (contComponent M L e (c,k,0,z0))
          (contComponent M L truth (c,k,0,z0)))))

/-- For [level data](hyp:L), the [weight error index list](goal) chooses [an arbitrary instrument
for components independent of instruments](step:1), then [lists baseline probabilities at
positive levels, policy probabilities and policy weights at every regular policy index,
shares only for instruments in their policy set, full-interval weights, and a tail-weight
index, using the continuous component codes](step:2). -/
noncomputable def weightErrorIndices (L : LevelData Z X) : List (ℕ × ℕ × ℕ × Z) :=
  let z0 : Z := Classical.choice inferInstance
  ((List.range L.K).map fun k => (2,k+1,0,z0)) ++
  ((policyErrorIndices L).flatMap fun kj =>
    [(3,kj.1,kj.2,z0), (6,kj.1,kj.2,z0)] ++
    ((L.T kj.1 kj.2).toList.map fun z => (4,kj.1,kj.2,z))) ++
  ((List.range L.K).map fun k => (5,k,0,z0)) ++ [(7,L.K,1,z0)]

/-- For [the model](hyp:M), [level data](hyp:L), [continuous or binary nuisances](hyp:e),
and [a weight component code with level indices and instrument](hyp:c), the [weight component
function](goal) uses [the continuous component selector in the continuous regime](step:1)
or [the binary selector after translating codes two through six to baseline probability,
policy probability, share, full-interval weight, and policy weight, with every other code
selecting the tail weight](step:2). -/
noncomputable def weightComponent (L : LevelData Z X)
    (e : NuisanceCont L ⊕ NuisanceBin L) (c : ℕ × ℕ × ℕ × Z) : X → ℝ :=
  match e with
  | .inl e => contComponent M L e c
  | .inr e =>
    let code := match c.1 with
      | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | _ => 8
    binComponent L e (code,c.2)

/-- For [the model](hyp:M), [level data](hyp:L), and [sample-dependent continuous or binary
nuisance fits](hyp:fit), the [finite weight-error magnitude](goal) at [sample size](hyp:n)
and [sampling outcome](hyp:a) selects [the fitted vector](step:1), [the population nuisance
vector in the same outcome regime](step:2), and [the maximum of zero and all population L2
integral errors between fitted and population weight components over the weight error index list](step:3). -/
noncomputable def finiteWeightErrorMagnitude (L : LevelData Z X)
    (fit : ℕ → A → NuisanceCont L ⊕ NuisanceBin L) (n : ℕ) (a : A) : ℝ :=
  let e := fit n a
  let truth := match e with
    | .inl _ => Sum.inl (trueNuisance M L)
    | .inr _ => Sum.inr (eta0Bin M L)
  maxErrors ((weightErrorIndices L).map fun c =>
    finiteL2Error M (weightComponent M L e c) (weightComponent M L truth c))

/-- For [the model](hyp:M), [a policy transformation](hyp:phi), [level data](hyp:L), and
[sample-dependent binary nuisance fits](hyp:fit), the [finite binary core-error magnitude](goal)
at [sample size](hyp:n) and [sampling outcome](hyp:a) uses [the fitted vector with clipped
and sorted positive-level success regressions](step:1), [the population binary nuisance
vector](step:2), and [the maximum of zero and the population L2 integral errors for all
instrument propensities, baseline levels and success regressions from structural level zero
through the final baseline level, and pooled policy propensities at every regular policy index](step:3). -/
noncomputable def finiteBinaryCoreErrorMagnitude (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (fit : ℕ → A → NuisanceBin L) (n : ℕ) (a : A) : ℝ :=
  let e := rearrangeP1 L (fit n a)
  let truth := eta0Bin M L
  maxErrors (
    (Finset.univ.toList.map fun z => finiteL2Error M (e.prop z) (truth.prop z)) ++
    ((List.range (L.K+1)).flatMap fun k =>
      [finiteL2Error M (positiveValue e.pLev k) (positiveValue truth.pLev k),
       finiteL2Error M (positiveValue e.P1 k) (positiveValue truth.P1 k)]) ++
    ((policyErrorIndices L).map fun kj =>
      finiteL2Error M (pooledQBin phi L e kj.1 kj.2) (pooledQBin phi L truth kj.1 kj.2)))



end Papers.TbsPrteOptimalTransport
