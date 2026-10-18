module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLErrorFiniteness
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
variable [Fintype Z] [DecidableEq Z]
-- @node: maxErrors_nonneg
/-- [The maximum of any finite list of errors, with zero included, is nonnegative](goal). -/
lemma maxErrors_nonneg (errors : List ℝ) : 0 ≤ maxErrors errors := by
  induction errors with
  | nil => exact le_refl 0
  | cons e errors ih =>
    change 0 ≤ max e (maxErrors errors)
    exact ih.trans (le_max_right e (maxErrors errors))

-- @node: regressionErrorMagnitude_nonneg
/-- [The finite regression error magnitude is nonnegative for every continuous nuisance fit, policy rule, sample size, and sample realization](goal). -/
lemma regressionErrorMagnitude_nonneg (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (fit : ℕ → A → NuisanceCont L) (n : ℕ) (a : A) :
    0 ≤ finiteRegressionErrorMagnitude M phi L fit n a := by
  unfold finiteRegressionErrorMagnitude
  exact maxErrors_nonneg _

-- @node: weightErrorMagnitude_nonneg
/-- [The finite weight error magnitude is nonnegative for every continuous or binary nuisance fit, sample size, and sample realization](goal). -/
lemma weightErrorMagnitude_nonneg (L : LevelData Z X)
    (fit : ℕ → A → NuisanceCont L ⊕ NuisanceBin L) (n : ℕ) (a : A) :
    0 ≤ finiteWeightErrorMagnitude M L fit n a := by
  unfold finiteWeightErrorMagnitude
  exact maxErrors_nonneg _

-- @node: binaryCoreErrorMagnitude_nonneg
/-- [The finite binary core error magnitude is nonnegative for every binary nuisance fit, policy rule, sample size, and sample realization](goal). -/
lemma binaryCoreErrorMagnitude_nonneg (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (fit : ℕ → A → NuisanceBin L) (n : ℕ) (a : A) :
    0 ≤ finiteBinaryCoreErrorMagnitude M phi L fit n a := by
  unfold finiteBinaryCoreErrorMagnitude
  exact maxErrors_nonneg _

/-- For [the latent instrumental-variable model](hyp:M), [observed sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂), [estimated propensities](hyp:pHat), [policy rule](hyp:phi), [recovery thresholds](hyp:rho), [separation gap](hyp:gap), [continuous nuisance estimates on recovered levels](hyp:eHat), and [denominator clipping constant](hyp:cpi), [dynamic continuous fitting](goal) requires [an equal half split](step:1), [admissible recovery thresholds](step:2), [the continuous fitting scope conditions](step:3), [component measurability relative to recovered information and covariates](step:4), [joint measurability of the higher policy and baseline fits relative to that information](step:5), and [joint measurability of all components in the original sample and covariates](step:6). -/
def DynamicContFit (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a)) (cpi : ℝ) : Prop :=
  EqualHalfSplit M μ S I₁ I₂ ∧
  RecoveryThresholdAdmissible rho ∧
  ContinuousFitScope M S I₁ I₂ pHat phi rho gap eHat cpi ∧
  (∀ n c, Measurable[MeasurableSpace.prod
    (MeasurableSpace.comap (recoveredView M S I₁ I₂ pHat phi rho gap n) inferInstance) inferInstance]
    (fun ax : A × X => contComponent M _ (eHat n ax.1) c ax.2)) ∧
  (∀ n, Measurable[MeasurableSpace.prod
    (MeasurableSpace.comap (recoveredView M S I₁ I₂ pHat phi rho gap n) inferInstance) inferInstance]
    (fun ax : A × X => (fun k => fullValue (eHat n ax.1).higherPolicyFit k ax.2,
      fun k => fullValue (eHat n ax.1).higherBaselineFit k ax.2))) ∧
  (∀ n, Measurable (fun ax : A × X => fun c => contComponent M _ (eHat n ax.1) c ax.2))

/-- For [the model](hyp:M), [sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂), [propensity estimates](hyp:pHat), [policy rule](hyp:phi), [recovery thresholds](hyp:rho), [separation gap](hyp:gap), [binary nuisance fits on recovered levels](hyp:eHat), and [denominator floor constant](hyp:cpi), [dynamic binary fitting](goal) requires [an equal half split](step:1), [admissible thresholds](step:2), [a training-measurable propensity predictor](step:3), [propensities between zero and one](step:4), [agreement of fitted propensities with that predictor, binary clipping, clipped denominators, and simplex shares](step:5), [component measurability relative to recovered information and covariates](step:6), and [joint component measurability in the original sample and covariates](step:7). -/
def DynamicBinFit (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a)) (cpi : ℝ) : Prop :=
  EqualHalfSplit M μ S I₁ I₂ ∧ RecoveryThresholdAdmissible rho ∧
  TrainingPredictorMeasurable M S I₁ (fun n a (zx : Z × X) => pHat n a zx.1 zx.2) ∧ (∀ n a z x, pHat n a z x ∈ Icc (0:ℝ) 1) ∧
  (∀ n a, (eHat n a).prop = pHat n a ∧ BinClipping _ (eHat n a) ∧
    DenominatorsClipped _ (.inr (eHat n a)) cpi ∧ FittedSharesSimplex _ (.inr (eHat n a))) ∧
  (∀ n c, Measurable[MeasurableSpace.prod
    (MeasurableSpace.comap (recoveredView M S I₁ I₂ pHat phi rho gap n) inferInstance) inferInstance]
    (fun ax : A × X => binComponent _ (eHat n ax.1) c ax.2)) ∧
  (∀ n, Measurable (fun ax : A × X => fun c => binComponent _ (eHat n ax.1) c ax.2))

/-- For [the model](hyp:M), [sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂), [propensity predictor](hyp:pHat), [policy rule](hyp:phi), [policy derivative](hyp:dphi), [recovery thresholds](hyp:rho), [separation gap](hyp:gap), [continuous nuisance fits](hyp:eHat), [sample size](hyp:n), [sample realization](hyp:a), and [observation to score](hyp:o), [the fitted continuous score](goal) first [recovers the level structure](step:1), then [uses the continuous orthogonal score when the level count is positive and the common tail score otherwise](step:2). -/
noncomputable def fittedContScore (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (n : ℕ) (a : A) (o : Obs X Z) :=
  let L := recoveredData M S I₁ I₂ pHat phi rho gap n a
  if h : LevelCountPos L.K then psiCont M phi dphi L h o (eHat n a) else
    commonTailScore M phi dphi L (eHat n a).prop (eHat n a).pLev (eHat n a).piLev (eHat n a).gammaTail o
/-- For [the model](hyp:M), [sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂), [propensity predictor](hyp:pHat), [policy rule](hyp:phi), [policy derivative](hyp:dphi), [recovery thresholds](hyp:rho), [separation gap](hyp:gap), [binary nuisance fits](hyp:eHat), [sample size](hyp:n), [sample realization](hyp:a), and [observation to score](hyp:o), [the fitted binary score](goal) first [recovers the level structure](step:1), then [uses the binary orthogonal score with rearranged fitted probabilities when the level count is positive and the common tail score otherwise](step:2). -/
noncomputable def fittedBinScore (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (n : ℕ) (a : A) (o : Obs X Z) :=
  let L := recoveredData M S I₁ I₂ pHat phi rho gap n a
  if h : LevelCountPos L.K then psiBin M phi dphi L h o (rearrangeP1 L (eHat n a)) else
    commonTailScore M phi dphi L (eHat n a).prop (eHat n a).pLev (eHat n a).piLev (eHat n a).gammaTail o
/-- For [the model](hyp:M), [observed sample](hyp:S), [evaluation split](hyp:I₂), [sample-dependent score](hyp:score), [sample size](hyp:n), and [sample realization](hyp:a), [the DML random variable](goal) is the evaluation-sample score average if that split is nonempty, and zero otherwise. -/
noncomputable def dmlRV (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (score : ℕ → A → Obs X Z → ℝ) (n : ℕ) (a : A) :=
  if h : (I₂ n a).Nonempty then scoreAverage M S I₂ score n a h else 0
/-- For [the model](hyp:M), [observed sample](hyp:S), [evaluation split](hyp:I₂), [sample-dependent score](hyp:score), [sample size](hyp:n), and [sample realization](hyp:a), [the variance random variable](goal) is the evaluation-sample score variance if that split is nonempty, and zero otherwise. -/
noncomputable def varianceRV (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (score : ℕ → A → Obs X Z → ℝ) (n : ℕ) (a : A) :=
  if h : (I₂ n a).Nonempty then sampleVariance M S I₂ score n a h else 0
/-- For [the model](hyp:M), [sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂), [propensity predictor](hyp:pHat), [policy rule](hyp:phi), [recovery thresholds](hyp:rho), [separation gap](hyp:gap), [population level structure](hyp:L), and [sample size](hyp:n), [the exact recovery event](goal) consists of realizations for which [the recovered structure is formed](step:1) and [its level count, subgroup counts, level sets, and ordered subgroup sets agree with the population structure at every valid index](step:2). -/
noncomputable def recoveryEvent (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ)
    (L : LevelData Z X) (n : ℕ) : Set A :=
  {a | let H := recoveredData M S I₁ I₂ pHat phi rho gap n a
    H.K = L.K ∧ (∀ k ≤ L.K, H.l k = L.l k ∧ H.S k = L.S k ∧
      ∀ j ≤ L.l k, H.T k j = L.T k j)}
  -- @realizes \mathcal E_n(event of exact recovery of the population level sets and their order)
-- @node: def:estimator-dml
/-- For [the model](hyp:M), [sample](hyp:S), [evaluation split](hyp:I₂), [policy rule](hyp:phi), [policy derivative](hyp:dphi), [sample-dependent level structures](hyp:L), [continuous or binary nuisance fits](hyp:fit), [sample size](hyp:n), and [sample realization](hyp:a), with [a nonempty evaluation split](hyp:hSplit), [the DML estimator](goal) averages the corresponding fitted orthogonal score over that split, using the common tail score when the level count is zero and rearranging probabilities in the binary case. -/
noncomputable def dmlEstimator (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (phi dphi : Z → X → ℝ → ℝ) (L : ℕ → A → LevelData Z X)
    (fit : ∀ n a, NuisanceCont (L n a) ⊕ NuisanceBin (L n a))
    (n : ℕ) (a : A) (hSplit : (I₂ n a).Nonempty) :=
  splitMean M S I₂ (fun _ _ o => match fit n a with
    | .inl e => if hK : LevelCountPos (L n a).K then psiCont M phi dphi (L n a) hK o e
      else commonTailScore M phi dphi (L n a) e.prop e.pLev e.piLev e.gammaTail o
    | .inr e => if hK : LevelCountPos (L n a).K then psiBin M phi dphi (L n a) hK o (rearrangeP1 (L n a) e)
      else commonTailScore M phi dphi (L n a) e.prop e.pLev e.piLev e.gammaTail o) n a hSplit
  -- @realizes \hat{\underline{\theta}}_{\omega,1}(prescribed recovered-data orthogonal-score mean)
  -- @realizes \hat\psi(continuous or binary prescribed fitted orthogonal score)
/-- Given [a policy rule](hyp:phi), [level structure](hyp:L), [continuous nuisance fit](hyp:e), [level index](hyp:k), [boundary index within the level](hyp:j), [observation](hyp:o), and [candidate outcome threshold](hyp:y), [the quantile moment response](goal) is the inverse-share-weighted treated outcome indicator in the next level minus its current-level counterpart, with the latter set to zero at level zero, minus the difference between the pooled policy probability and fitted level propensity. -/
noncomputable def quantileMomentResponse (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) (y : ℝ) :=
  indicator (o.2.1 ∈ L.S (k+1)) * o.2.2.1 * indicator (o.2.2.2 ≤ y) /
    positiveValue e.piLev (k+1) o.1 -
  (if k = 0 then 0 else indicator (o.2.1 ∈ L.S k) * o.2.2.1 *
    indicator (o.2.2.2 ≤ y) / positiveValue e.piLev k o.1) -
  (pooledQ phi L e k j o.1 - positiveValue e.pLev k o.1)
/-- For [the model](hyp:M), [observed sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂), [propensity estimates](hyp:pHat), [policy rule](hyp:phi), [recovery thresholds](hyp:rho), [separation gap](hyp:gap), [denominator clipping constant](hyp:cpi), [continuous nuisance fits](hyp:eHat), [first-stage learner](hyp:firstStage), [conditional regression learner](hyp:regression), [multinomial share learner](hyp:multinomial), and [quantile moment learner](hyp:moment), [the DML learning-step specification](goal) requires [propensity estimates to equal the first-stage predictions clipped to the unit interval](step:1) and [all nuisance coordinates to equal their prescribed training-sample regressions, share predictions, or moment predictions with the specified conditioning, responses, and clipping](step:2).

Flexible learners receive all training observations, the recovered sets, and the conditioning and response rules. Pooling and tuning may use the entire training sample. Their quality is asserted separately by the rate assumptions. -/
def DMLLearningSteps (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap cpi : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (firstStage : ℕ → List (Obs X Z) → Z → X → ℝ)
    (regression : ℕ → (ℕ × ℕ × ℕ) → List (Obs X Z) → LevelData Z X →
      (Obs X Z → Prop) → (Obs X Z → ℝ) → X → ℝ)
    (multinomial : ℕ → List (Obs X Z) → LevelData Z X → Finset Z → X → Z → ℝ)
    (moment : ℕ → List (Obs X Z) → LevelData Z X →
      (Obs X Z → ℝ → ℝ) → X → ℝ) : Prop :=
  (∀ n a z x,
    let observations := ((I₁ n a).sort (· ≤ ·)).map (fun i => S.Z i a)
    pHat n a z x = min 1 (max 0 (firstStage n observations z x))) ∧
  ∀ n a,
    let L := recoveredData M S I₁ I₂ pHat phi rho gap n a
    let e := eHat n a
    let observations := ((I₁ n a).sort (· ≤ ·)).map (fun i => S.Z i a)
    let fit := fun token selected response x =>
      regression n token observations L selected response x
    let clipProb := fun t => min 1 (max 0 t)
    let clipDenom := fun t => min 1 (max (cpi/2) t)
    let clipOutcome := fun t => min M.yMax (max M.yMin t)
    let clipBand := fun t => min (max 0 M.yMax) (max (min 0 M.yMin) t)
    (∀ k x, e.pLev k x = clipProb (fit (0,k,0)
      (fun o => o.2.1 ∈ L.S k) (fun o => o.2.2.1) x)) ∧
    (∀ k x, e.piLev k x = clipDenom (fit (1,k,0)
      (fun _ => True) (fun o => indicator (o.2.1 ∈ L.S k)) x)) ∧
    (∀ b x, e.tauLev b x = clipDenom (fit (2,b.val.1,b.val.2)
      (fun _ => True) (fun o => indicator (o.2.1 ∈ L.T b.val.1 b.val.2)) x)) ∧
    (∀ k x, e.higherPolicyFit k x = clipProb (fit (3,k,0)
      (fun _ => True) (fun o => indicator (o.2.1 ∈ higherPolicy L k)) x) ∧
      e.higherBaselineFit k x = clipProb (fit (4,k,0)
        (fun _ => True) (fun o => indicator (o.2.1 ∈ higherBaseline L k)) x)) ∧
    (∀ b x, e.gamma b x = clipProb (fit (5,b.val.1,b.val.2)
      (fun _ => True) (fun o => indicator (o.2.1 ∈ policyUnion L b.val.1 b.val.2)) x)) ∧
    (∀ x, e.gammaTail x = clipProb (fit (6,L.K,1)
      (fun _ => True) (fun o => indicator (o.2.1 ∈ policyUnion L L.K 1)) x)) ∧
    (∀ b z x, e.share b z x = multinomial n observations L
      (L.T b.val.1 b.val.2) x z) ∧
    (∀ b x, e.nu b x = clipOutcome (moment n observations L
      (quantileMomentResponse phi L e b.val.1 b.val.2) x)) ∧
    (∀ b x, e.Mplus b x = clipProb (fit (7,b.val.1,b.val.2)
      (fun o => o.2.1 ∈ L.S (b.val.1+1) ∧ o.2.2.1 = 1)
      (fun o => indicator (o.2.2.2 ≤ nuValue M e b.val.1 b.val.2 o.1)) x)) ∧
    (∀ b x, e.Mminus b x = clipProb (fit (8,b.val.1,b.val.2)
      (fun o => o.2.1 ∈ L.S b.val.1 ∧ o.2.2.1 = 1)
      (fun o => indicator (o.2.2.2 ≤ nuValue M e b.val.1 b.val.2 o.1)) x)) ∧
    (∀ b x, e.Jplus b x = clipBand (fit (9,b.val.1,b.val.2)
      (fun o => o.2.1 ∈ L.S (b.val.1+1) ∧ o.2.2.1 = 1)
      (fun o => o.2.2.2 * indicator (nuValue M e b.val.1 b.val.2 o.1 < o.2.2.2 ∧
        o.2.2.2 ≤ nuValue M e b.val.1 (b.val.2+1) o.1)) x)) ∧
    (∀ b x, e.Jminus b x = clipBand (fit (10,b.val.1,b.val.2)
      (fun o => o.2.1 ∈ L.S b.val.1 ∧ o.2.2.1 = 1)
      (fun o => o.2.2.2 * indicator (nuValue M e b.val.1 b.val.2 o.1 < o.2.2.2 ∧
        o.2.2.2 ≤ nuValue M e b.val.1 (b.val.2+1) o.1)) x)) ∧
    (∀ k x, e.JfullPlus k x = clipOutcome (fit (11,k,0)
      (fun o => o.2.1 ∈ L.S (k+1) ∧ o.2.2.1 = 1) (fun o => o.2.2.2) x)) ∧
    (∀ k x, e.JfullMinus k x = clipOutcome (fit (12,k,0)
      (fun o => o.2.1 ∈ L.S k ∧ o.2.2.1 = 1) (fun o => o.2.2.2) x))

-- @node: def:dml-continuous-outcome-algorithm
/-- For [the model](hyp:M), [sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂), [propensity predictor](hyp:pHat), [policy rule](hyp:phi), [policy derivative](hyp:dphi), [threshold sequence](hyp:rho), [separation gap](hyp:gap), [continuous nuisance fits](hyp:eHat), [first-stage learner](hyp:firstStage), [regression learner](hyp:regression), [multinomial learner](hyp:multinomial), [moment learner](hyp:moment), [denominator floor constant](hyp:cpi), [estimator sequence](hyp:theta), and [variance sequence](hyp:variance), [being a continuous-outcome DML algorithm](goal) means [the policy has the specified derivative](step:1), [the gap is positive](step:2), [the denominator floor constant is positive](step:3), [dynamic continuous fitting holds](step:4), [the prescribed learning steps hold](step:5), [the estimator equals the fitted continuous score average](step:6), and [the variance equals its sample variance](step:7). -/
def IsDMLContinuousAlgorithm (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (firstStage : ℕ → List (Obs X Z) → Z → X → ℝ)
    (regression : ℕ → (ℕ × ℕ × ℕ) → List (Obs X Z) → LevelData Z X →
      (Obs X Z → Prop) → (Obs X Z → ℝ) → X → ℝ)
    (multinomial : ℕ → List (Obs X Z) → LevelData Z X → Finset Z → X → Z → ℝ)
    (moment : ℕ → List (Obs X Z) → LevelData Z X →
      (Obs X Z → ℝ → ℝ) → X → ℝ)
    (cpi : ℝ) (theta variance : ℕ → A → ℝ) : Prop :=
  PolicyDifferentiable phi dphi ∧ 0 < gap ∧ 0 < cpi ∧
  DynamicContFit M S I₁ I₂ pHat phi rho gap eHat cpi ∧
  DMLLearningSteps M S I₁ I₂ pHat phi rho gap cpi eHat firstStage regression multinomial moment ∧
  (∀ n a, theta n a = dmlRV M S I₂
    (fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat) n a) ∧
  (∀ n a, variance n a = varianceRV M S I₂
    (fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat) n a)
-- @node: def:dml-estimation-procedure
/-- For [the model](hyp:M), [sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂), [propensity predictor](hyp:pHat), [policy rule](hyp:phi), [policy derivative](hyp:dphi), [threshold sequence](hyp:rho), [separation gap](hyp:gap), [continuous nuisance fits](hyp:eHat), [first-stage learner](hyp:firstStage), [regression learner](hyp:regression), [multinomial learner](hyp:multinomial), [moment learner](hyp:moment), [denominator floor constant](hyp:cpi), and [estimator sequence](hyp:theta), [being a DML procedure](goal) means [the policy has the specified derivative](step:1), [the gap is positive](step:2), [the denominator floor constant is positive](step:3), [dynamic continuous fitting holds](step:4), [the prescribed learning steps hold](step:5), and [the estimator equals the fitted continuous score average at every sample size and realization](step:6). -/
def IsDMLProcedure (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (rho : ℕ → ℝ) (gap : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (firstStage : ℕ → List (Obs X Z) → Z → X → ℝ)
    (regression : ℕ → (ℕ × ℕ × ℕ) → List (Obs X Z) → LevelData Z X →
      (Obs X Z → Prop) → (Obs X Z → ℝ) → X → ℝ)
    (multinomial : ℕ → List (Obs X Z) → LevelData Z X → Finset Z → X → Z → ℝ)
    (moment : ℕ → List (Obs X Z) → LevelData Z X →
      (Obs X Z → ℝ → ℝ) → X → ℝ)
    (cpi : ℝ) (theta : ℕ → A → ℝ) : Prop :=
  PolicyDifferentiable phi dphi ∧ 0 < gap ∧ 0 < cpi ∧
  DynamicContFit M S I₁ I₂ pHat phi rho gap eHat cpi ∧
  DMLLearningSteps M S I₁ I₂ pHat phi rho gap cpi eHat firstStage regression multinomial moment ∧
  ∀ n a, theta n a = dmlRV M S I₂
    (fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat) n a
-- @node: sampleVariance_nonneg
/-- If [the evaluation split is nonempty](hyp:h), [the sample variance of any score on that split is nonnegative](goal). -/
lemma sampleVariance_nonneg (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (score : ℕ → A → Obs X Z → ℝ) (n : ℕ) (a : A) (h : (I₂ n a).Nonempty) :
    0 ≤ sampleVariance M S I₂ score n a h := by
  unfold sampleVariance
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => sq_nonneg _)
  -- @realizes \hat\sigma^2(nonnegative sample variance)

-- @node: finite_unit_average_range
/-- If [every value on a finite index set lies between zero and one](hyp:hf), [its sum divided by the number of indices also lies between zero and one, with value zero for the empty set](goal). -/
lemma finite_unit_average_range {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ I, f i ∈ Icc (0 : ℝ) 1) :
    (I.card : ℝ)⁻¹ * ∑ i ∈ I, f i ∈ Icc (0 : ℝ) 1 := by
  have hs0 : 0 ≤ ∑ i ∈ I, f i := Finset.sum_nonneg fun i hi => (hf i hi).1
  have hs1 : ∑ i ∈ I, f i ≤ (I.card : ℝ) := by
    calc
      ∑ i ∈ I, f i ≤ ∑ _i ∈ I, (1 : ℝ) :=
        Finset.sum_le_sum fun i hi => (hf i hi).2
      _ = (I.card : ℝ) := by simp
  refine ⟨mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hs0, ?_⟩
  by_cases hI : I.card = 0
  · simp [hI]
  · calc
      (I.card : ℝ)⁻¹ * ∑ i ∈ I, f i ≤ (I.card : ℝ)⁻¹ * (I.card : ℝ) :=
        mul_le_mul_of_nonneg_left hs1 (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hI)

-- @node: recovery_averages_range
/-- If [all fitted propensities lie between zero and one](hyp:hp) and [the policy rule is admissible and preserves that interval](hyp:hphi), [the evaluation-sample averages of both baseline and policy-transformed fitted propensities lie between zero and one for every sample size, realization, and instrument value](goal). -/
lemma recovery_averages_range (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ) (phi : Z → X → ℝ → ℝ)
    (hp : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1) (hphi : IsPolicyMap phi) :
    ∀ n a z, pBar M S I₂ pHat n a z ∈ Icc (0 : ℝ) 1 ∧
      pBar M S I₂ (fun n a => policyProp phi (pHat n a)) n a z ∈ Icc (0 : ℝ) 1 := by
  intro n a z
  constructor
  · exact finite_unit_average_range (I₂ n a) _ fun i _ => hp n a z (S.Z i a).1
  · exact finite_unit_average_range (I₂ n a) _ fun i _ =>
      hphi.2 z (S.Z i a).1 _ (hp n a z (S.Z i a).1)
  -- @realizes \bar p_2(averaged clipped baseline propensities in [0,1])
  -- @realizes \bar q_2(averaged fitted policy propensities in [0,1])

end Papers.TbsPrteOptimalTransport
