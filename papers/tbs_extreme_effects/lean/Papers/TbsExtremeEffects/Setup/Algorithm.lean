module
public import Papers.TbsExtremeEffects.Setup.Model
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Powerset

/-! Random split, training-measurable fits, score averages and full-input adaptive Hill selection.
Indices are zero-based. All fits are shared across thresholds. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open scoped BigOperators ENNReal Topology Classical
noncomputable section

-- @env: S3
variable {q d : ℕ} {M : ExtremeModel q d}

/-- [The relabelled observation](goal) at a given [sample size](hyp:n), [world](hyp:w), and [index](hyp:i) puts the observations selected by the [training-index rule](hyp:train) first and obtains their values from the [raw observation stream](hyp:raw). -/
def relabelledObs {W : Type} (raw : ℕ → W → Obs q d)
    (train : (n : ℕ) → W → Finset (Fin n)) (n : ℕ) (w : W) (i : Fin n) : Obs q d :=
  raw (((train n w).sort (· ≤ ·) ++ ((train n w)ᶜ).sort (· ≤ ·)).map Fin.val |>.getD i.val i.val) w

/-- [The training-data map](goal) packages relabelled data from the [raw observation stream](hyp:raw), the [training-index rule](hyp:train), and the [auxiliary information](hyp:aux) for a [sample size](hyp:n) and [world](hyp:w). -/
abbrev trainingMap {W Aux : Type} (raw : ℕ → W → Obs q d)
    (train : (n : ℕ) → W → Finset (Fin n)) (aux : W → Aux) (n : ℕ) (w : W) :=
  ((fun i : Fin n => if i.val < n / 2 then relabelledObs raw train n w i else (0, false, 0, 0)),
    train n w, aux w)

/-- [An even sample size](goal) is a [sample size n](hyp:n) that is [positive](step:1) and [even](step:2). -/
-- @node: ass:pin-fix-9567640d
def EvenSampleSize (n : ℕ) : Prop := 0 < n ∧ Even n

/-- [A uniform random split](goal) under probability measure [P](hyp:P) assigns the [training set](hyp:train) a half-sample uniformly and independently of the [raw indexed observations](hyp:raw). -/
-- @node: ass:pin-45
def RandomSplitUniform {W : Type} [MeasurableSpace W] {n : ℕ}
    (P : Measure W) (train : W → Finset (Fin n)) (raw : W → Fin n → Obs q d) : Prop :=
  (∀ w, (train w).card = n / 2) ∧ -- @realizes \mathcal{D}_1(equal training half)
  (∀ A : Finset (Fin n), A.card = n / 2 →
    P {w | train w = A} = (n.choose (n / 2) : ℝ≥0∞)⁻¹) ∧
  IndepFun train raw P

/-- Experiment data with the uniform independent split design built into the world. -/
structure NeteExperiment (M : ExtremeModel q d) where
  Om : Type
  measurableSpace : MeasurableSpace Om
  P : @Measure Om measurableSpace
  probability : @IsProbabilityMeasure Om measurableSpace P
  Aux : Type
  auxSpace : MeasurableSpace Aux
  aux : Om → Aux
  Zraw : ℕ → Om → Obs q d -- @realizes N(raw stream restricted to first N observations)
  trainSet : (n : ℕ) → Om → Finset (Fin n) -- @realizes \mathcal{D}_1(raw training indices before relabelling)
  measurable_raw : ∀ i, @Measurable Om _ measurableSpace inferInstance (Zraw i)
  measurable_train : ∀ n, @Measurable Om _ measurableSpace inferInstance (trainSet n)
  measurable_aux : @Measurable Om Aux measurableSpace auxSpace aux
  randomSplit : ∀ n, EvenSampleSize n →
    @RandomSplitUniform q d Om measurableSpace n P (trainSet n) (fun w i => Zraw i.val w)
  split_aux_independent : ∀ n, EvenSampleSize n →
    @IndepFun Om (Finset (Fin n) × Aux) (Fin n → Obs q d) measurableSpace
      (@Prod.instMeasurableSpace _ _ inferInstance auxSpace) inferInstance
      (fun w => (trainSet n w, aux w)) (fun w i => Zraw i.val w) P
  aux_split_independent : ∀ n, EvenSampleSize n →
    @IndepFun Om Aux (Finset (Fin n)) measurableSpace auxSpace inferInstance
      aux (trainSet n) P
  pHat : ℕ → Om → (Fin q → ℝ) → ℝ -- @realizes \hat{p}(one fitted propensity per sample size)
  gHat : ℕ → Om → (Fin q → ℝ) → Bool → (Fin d → ℝ) → ℝ -- @realizes \hat{g}(one fitted regression per sample size)
  alphaHat : ℕ → Om → ℝ -- @realizes \hat{\alpha}_n(supplied fitted exponent)
  pHat_training : ∀ n,
    @Measurable (Om × (Fin q → ℝ)) ℝ
      ((MeasurableSpace.comap (trainingMap Zraw trainSet aux n)
        (@Prod.instMeasurableSpace _ _ inferInstance
          (@Prod.instMeasurableSpace _ _ inferInstance auxSpace))).prod inferInstance)
      inferInstance (fun z => pHat n z.1 z.2)
  -- Regression fitting uses the training data and the supplied exponent as an input.
  gHat_training : ∀ n,
    @Measurable (Om × ((Fin q → ℝ) × Bool × (Fin d → ℝ))) ℝ
      ((MeasurableSpace.comap (fun w => (trainingMap Zraw trainSet aux n w, alphaHat n w))
        (@Prod.instMeasurableSpace _ _
          (@Prod.instMeasurableSpace _ _ inferInstance
            (@Prod.instMeasurableSpace _ _ inferInstance auxSpace)) inferInstance)).prod inferInstance)
      inferInstance (fun z => gHat n z.1 z.2.1 z.2.2.1 z.2.2.2)

attribute [instance] NeteExperiment.measurableSpace NeteExperiment.probability NeteExperiment.auxSpace

/-- [The relabelled sample](goal) consists of observations from experiment [E](hyp:E) at [sample size](hyp:n).

@realizes \mathcal{D}(n relabelled observed tuples)
@realizes n(full-input sample size)
@realizes i(zero-based Fin n index) -/
def obs (E : NeteExperiment M) (n : ℕ) := relabelledObs E.Zraw E.trainSet n
/-- [The sample covariate](goal) is the covariate of observation [i](hyp:i) in experiment [E](hyp:E), at [sample size](hyp:n) and [world](hyp:w).

@realizes X_i(covariate coordinate of relabelled tuple) -/
def sampleX (E : NeteExperiment M) (n : ℕ) (w : E.Om) (i : Fin n) := (obs E n w i).1
/-- [The sample treatment indicator](goal) is the treatment coordinate of observation [i](hyp:i) in experiment [E](hyp:E), at [sample size](hyp:n) and [world](hyp:w).

@realizes D_i(binary treatment coordinate of relabelled tuple) -/
def sampleD (E : NeteExperiment M) (n : ℕ) (w : E.Om) (i : Fin n) := (obs E n w i).2.1
/-- [The sample outcome](goal) is the outcome coordinate of observation [i](hyp:i) in experiment [E](hyp:E), at [sample size](hyp:n) and [world](hyp:w).

@realizes Y_i(real outcome coordinate of relabelled tuple) -/
def sampleY (E : NeteExperiment M) (n : ℕ) (w : E.Om) (i : Fin n) := (obs E n w i).2.2.1
/-- [The sample noise vector](goal) is the noise coordinate of observation [i](hyp:i) in experiment [E](hyp:E), at [sample size](hyp:n) and [world](hyp:w).

@realizes U_i(noise coordinate of relabelled tuple; nonnegativity inherited from population law) -/
def sampleU (E : NeteExperiment M) (n : ℕ) (w : E.Om) (i : Fin n) := (obs E n w i).2.2.2
/-- [The training indices](goal) are the first half of a [sample of size n](hyp:n).

@realizes \mathcal{D}_1(first n/2 relabelled indices) -/
def trainIndices (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < n / 2)
/-- [The evaluation indices](goal) are the second half of a [sample of size n](hyp:n).

@realizes \mathcal{D}_2(remaining relabelled indices) -/
def evalIndices (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => n / 2 ≤ i.val)
/-- [The training sigma-field](goal) records the information in experiment [E](hyp:E) available from its training portion at [sample size](hyp:n). -/
abbrev trainSigma (E : NeteExperiment M) (n : ℕ) :=
  MeasurableSpace.comap (trainingMap E.Zraw E.trainSet E.aux n) inferInstance

/-- [Independent and identically distributed sampling](goal) for experiment [E](hyp:E) and [sample size](hyp:N) means that [all raw observations are mutually independent](step:1) and [each has the model's observation distribution](step:2). -/
-- @node: ass:iid-sampling
def IIDSampling (E : NeteExperiment M) (N : ℕ) : Prop :=
  iIndepFun (fun i : Fin N => E.Zraw i.val) E.P ∧
  ∀ i : Fin N, E.P.map (E.Zraw i.val) = M.mu.map (observation M)

/-- [Training measurability of the fitted exponent](goal) says that experiment [E](hyp:E)'s fitted exponent at [sample size](hyp:n) depends only on training information. -/
def ExponentTraining (E : NeteExperiment M) (n : ℕ) : Prop :=
  Measurable[trainSigma E n] (E.alphaHat n)

/-- [Equal split sizes](goal) for [sample size n](hyp:n) means that [the sample size is positive and even](step:1), [the training split has half the observations](step:2), and [the evaluation split has half the observations](step:3). -/
-- @node: ass:pin-fix-0b814294
def EqualSplitSizes (n : ℕ) : Prop :=
  EvenSampleSize n ∧ (trainIndices n).card = n / 2 ∧ (evalIndices n).card = n / 2

/-- [Deterministic overlap with constant $c$](goal) for experiment [E](hyp:E) and [constant $c$](hyp:c) requires [that constant to be strictly between zero and one half](step:1) and [all fitted propensities on the covariate domain to lie between it and one minus it](step:2). -/
-- @node: ass:pin-owner-4
def OverlapConstantDeterministic (E : NeteExperiment M) (c : ℝ) : Prop :=
  0 < c ∧ c < 1 / 2 ∧ -- @realizes c(estimated-propensity overlap constant)
  ∀ n, EvenSampleSize n → ∀ w x, x ∈ M.covariateDomain →
    c ≤ E.pHat n w x ∧ E.pHat n w x ≤ 1 - c -- @realizes \hat{p}(range [c,1-c] on 𝒳)

/-- [Estimated overlap](goal) for experiment [E](hyp:E) with constant [c](hyp:c) is deterministic fitted-propensity overlap. -/
-- @node: ass:overlap
def EstimatedOverlap (E : NeteExperiment M) (c : ℝ) : Prop :=
  OverlapConstantDeterministic E c

/-- [The training exceedance count](goal) counts training observations in experiment [E](hyp:E), of [sample size](hyp:n), whose noise radius exceeds [threshold](hyp:t) in [world](hyp:w).

@realizes n_t(training exceedance count, including zero) -/
def trainCount (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) : ℕ :=
  ((trainIndices n).filter (fun i => t < l1Norm (sampleU E n w i))).card
/-- [The evaluation exceedance set](goal) contains evaluation indices in experiment [E](hyp:E), of [sample size](hyp:n), whose noise radius exceeds [threshold](hyp:t) in [world](hyp:w).

@realizes \mathcal{I}(evaluation indices strictly exceeding t) -/
def evalSet (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) :=
  (evalIndices n).filter (fun i => t < l1Norm (sampleU E n w i))
/-- [The evaluation exceedance count](goal) is the number of evaluation observations in experiment [E](hyp:E), of [sample size](hyp:n), above [threshold](hyp:t) in [world](hyp:w).

@realizes M(cardinality of evaluation exceedances) -/
def evalCount (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) := (evalSet E n t w).card
/-- [The sample direction](goal) normalizes the noise vector of observation [i](hyp:i) in experiment [E](hyp:E), at [sample size](hyp:n) and [world](hyp:w), by its radius.

@realizes S_i(noise divided by its l1 radius on positive exceedances) -/
def sampleDirection (E : NeteExperiment M) (n : ℕ) (w : E.Om) (i : Fin n) :=
  fun j => sampleU E n w i j / l1Norm (sampleU E n w i)

/-- [The training-count condition](goal) says that the training exceedance count for experiment [E](hyp:E), [sample size](hyp:n), [threshold](hyp:t), and [world](hyp:w) equals the direct count of first-half observations exceeding that threshold. -/
-- @node: ass:pin-fix-c90a58f3
def TrainCountIsTrainingExceedances (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) : Prop :=
  trainCount E n t w =
    (Finset.univ.filter (fun i : Fin n => i.val < n / 2 ∧ t < l1Norm (sampleU E n w i))).card

/-- [The observation tail law](goal) for model [M](hyp:M) at [threshold](hyp:t) is the distribution of an observation conditional on its noise radius exceeding that threshold. -/
def obsTailLaw (M : ExtremeModel q d) (t : ℝ) : Measure (Obs q d) :=
  cond (M.mu.map (observation M)) {z | t < l1Norm z.2.2.2}
/-- If [the sample size is positive and even](hyp:hn) and [the fitted propensity has deterministic overlap](hyp:hOverlap), then under the observation-tail law at [threshold](hyp:t) in [world](hyp:w) of experiment [E](hyp:E), [the fitted propensity lies between the overlap constant and one minus it almost surely](goal). -/
-- @node: estimatedOverlap_obsTailLaw
lemma estimatedOverlap_obsTailLaw (E : NeteExperiment M) {n : ℕ}
    (hn : EvenSampleSize n) {c : ℝ} (hOverlap : EstimatedOverlap E c)
    (t : ℝ) (w : E.Om) :
    ∀ᵐ z ∂obsTailLaw M t, c ≤ E.pHat n w z.1 ∧ E.pHat n w z.1 ≤ 1 - c := by
  have hp : Measurable (fun z : Obs q d => E.pHat n w z.1) := by
    first
    | fun_prop
    | exact (E.pHat_training n).comp (measurable_const.prodMk measurable_fst)
  have hobs : Measurable (observation M) := by
    first
    | fun_prop
    | exact M.measurable_X.prodMk
        (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  apply cond_absolutelyContinuous.ae_le
  apply (ae_map_iff hobs.aemeasurable
    ((measurableSet_le measurable_const hp).inter
      (measurableSet_le hp measurable_const))).mpr
  exact Filter.Eventually.of_forall fun v =>
    hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)

/-- [The observation direction](goal) normalizes the noise vector in [observation](hyp:z) by its radius. -/
def obsDirection (z : Obs q d) := fun i => z.2.2.2 i / l1Norm z.2.2.2

/-- [The pseudo-outcome](goal) for experiment [E](hyp:E), [sample size](hyp:n), [world](hyp:w), and [observation](hyp:z) divides that observation's outcome by its noise radius raised to the fitted exponent. -/
def pseudoOutcome (E : NeteExperiment M) (n : ℕ) (w : E.Om) (z : Obs q d) :=
  z.2.2.1 / l1Norm z.2.2.2 ^ E.alphaHat n w

/-- The fitted pseudo-outcome has [a finite absolute mean under the observation-tail law](goal) for almost every [world in set G](hyp:G), using experiment [E](hyp:E)'s exponent at [sample size](hyp:n) and [threshold](hyp:t). -/
def FittedPseudoOutcomeIntegrable (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (G : Set E.Om) : Prop :=
  ∀ᵐ w ∂E.P, w ∈ G →
    Integrable (fun z : Obs q d => |z.2.2.1| / l1Norm z.2.2.2 ^ E.alphaHat n w)
      (obsTailLaw M t)

/-- [The inverse-probability-weighted score](goal) for experiment [E](hyp:E), [sample size](hyp:n), [world](hyp:w), and [observation](hyp:z) weights its pseudo-outcome by the fitted treatment propensity. -/
def ipwScore (E : NeteExperiment M) (n : ℕ) (w : E.Om) (z : Obs q d) : ℝ :=
  pseudoOutcome E n w z *
    ((if z.2.1 then 1 else 0) / E.pHat n w z.1 -
      (if z.2.1 then 0 else 1) / (1 - E.pHat n w z.1))
/-- [The doubly robust score](goal) for experiment [E](hyp:E), [sample size](hyp:n), [world](hyp:w), and [observation](hyp:z) combines fitted treated and untreated regressions with a propensity-weighted pseudo-outcome residual. -/
def drScore (E : NeteExperiment M) (n : ℕ) (w : E.Om) (z : Obs q d) : ℝ :=
  E.gHat n w z.1 true (obsDirection z) - E.gHat n w z.1 false (obsDirection z) +
    ((if z.2.1 then 1 else 0) - E.pHat n w z.1) /
      (E.pHat n w z.1 * (1 - E.pHat n w z.1)) *
    (pseudoOutcome E n w z - E.gHat n w z.1 z.2.1 (obsDirection z))

/-- [The IPW evaluation average](goal) for experiment [E](hyp:E), [sample size](hyp:n), [threshold](hyp:t), and [world](hyp:w) averages inverse-probability-weighted scores over evaluation exceedances, [returning zero when there are none](step:1) and [otherwise returning their average](step:2).

@realizes \hat{\eta}_{n,t}^{\text{IPW}}(evaluation IPW average; zero for empty set) -/
def etaIPW (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) : ℝ :=
  if evalCount E n t w = 0 then 0 else
    (evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w, ipwScore E n w (obs E n w i)
/-- [The doubly robust evaluation average](goal) for experiment [E](hyp:E), [sample size](hyp:n), [threshold](hyp:t), and [world](hyp:w) averages doubly robust scores over evaluation exceedances, [returning zero when there are none](step:1) and [otherwise returning their average](step:2).

@realizes \hat{\eta}_{n,t}^{\tmop{DR}}(evaluation DR average; zero for empty set) -/
def etaDR (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) : ℝ :=
  if evalCount E n t w = 0 then 0 else
    (evalCount E n t w : ℝ)⁻¹ * ∑ i ∈ evalSet E n t w, drScore E n w (obs E n w i)

/-- [The ordered radius](goal) in experiment [E](hyp:E), for [sample size](hyp:n), [world](hyp:w), and [rank](hyp:j), is [the j-th largest raw noise radius when the rank is valid](step:1), [and is zero otherwise](step:2).

@realizes U_{(j)}(decreasing full-input radius; only valid ranks are accessed)
@realizes j(one-based radial rank) -/
def orderedRadius (E : NeteExperiment M) (n : ℕ) (w : E.Om) (j : ℕ) : ℝ :=
  if hj : 1 ≤ j ∧ j ≤ n then
    let radii := fun i : Fin n => l1Norm (E.Zraw i.val w).2.2.2
    radii (Tuple.sort radii ⟨n - j, Nat.sub_lt (Nat.lt_of_lt_of_le hj.1 hj.2) hj.1⟩)
  else 0
/-- [The Hill statistic](goal) for experiment [E](hyp:E), [sample size](hyp:n), [number of top ranks](hyp:k), and [world](hyp:w) is [zero when its reference radius vanishes](step:1), and [otherwise the average log ratio to that reference radius](step:2).

@realizes \hat{\gamma}_i(common-denominator Hill statistic on all n raw radii) -/
def hillStat (E : NeteExperiment M) (n k : ℕ) (w : E.Om) : ℝ :=
  if orderedRadius E n w (k + 1) = 0 then 0 else
    (k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k,
      Real.log (orderedRadius E n w j / orderedRadius E n w (k + 1))

/-- If [rank i is at least one](hyp:hi), [rank i is no greater than rank j](hyp:hij), and [rank j is within the sample](hyp:hj), then in experiment [E](hyp:E), at [sample size](hyp:n) and [world](hyp:w), [the radius at rank j is no greater than the radius at rank i](goal). -/
-- @node: orderedRadius_antitone_on_ranks
lemma orderedRadius_antitone_on_ranks (E : NeteExperiment M) (n : ℕ) (w : E.Om)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n) :
    orderedRadius E n w j ≤ orderedRadius E n w i := by
  have hj1 : 1 ≤ j := hi.trans hij
  have hin : i ≤ n := hij.trans hj
  have hi' : 1 ≤ i ∧ i ≤ n := ⟨hi, hin⟩
  have hj' : 1 ≤ j ∧ j ≤ n := ⟨hj1, hj⟩
  simp only [orderedRadius, dif_pos hi', dif_pos hj']
  apply Tuple.monotone_sort (fun i : Fin n => l1Norm (E.Zraw i.val w).2.2.2)
  change n - j ≤ n - i
  omega

/-- For any [real-valued sequence](hyp:f) and [nonnegative endpoint](hyp:k), [the sum of differences from its endpoint equals the rank-weighted sum of adjacent differences](goal). -/
-- @node: hill_weighted_telescoping
lemma hill_weighted_telescoping (f : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.Icc 1 k, (f j - f (k + 1))) =
      ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (f j - f (j + 1)) := by
  have hsum : ∀ k : ℕ,
      (∑ j ∈ Finset.Icc 1 k, (j : ℝ) * (f j - f (j + 1))) =
        (∑ j ∈ Finset.Icc 1 k, f j) - (k : ℝ) * f (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  rw [hsum, Finset.sum_sub_distrib]
  simp

/-- If [at least one top rank is used](hyp:hk), [that number is below the sample size](hyp:hkn), and [the reference radius is positive](hyp:hpos), then for experiment [E](hyp:E), [sample size](hyp:n), [number of top ranks](hyp:k), and [world](hyp:w), [the Hill statistic equals its rank-weighted adjacent log-spacing form](goal). -/
-- @node: hillStat_eq_weighted_spacings
lemma hillStat_eq_weighted_spacings (E : NeteExperiment M) (n k : ℕ) (w : E.Om)
    (hk : 1 ≤ k) (hkn : k < n) (hpos : 0 < orderedRadius E n w (k + 1)) :
    hillStat E n k w = (k : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 k,
      (j : ℝ) * Real.log (orderedRadius E n w j / orderedRadius E n w (j + 1)) := by
  have hpositive (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) :
      0 < orderedRadius E n w j :=
    hpos.trans_le (orderedRadius_antitone_on_ranks E n w hj1 hjk (by omega))
  rw [hillStat, if_neg (ne_of_gt hpos)]
  congr 1
  calc
    _ = ∑ j ∈ Finset.Icc 1 k,
        (Real.log (orderedRadius E n w j) - Real.log (orderedRadius E n w (k + 1))) := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
      exact Real.log_div (ne_of_gt (hpositive j hj1 (by omega))) (ne_of_gt hpos)
    _ = ∑ j ∈ Finset.Icc 1 k, (j : ℝ) *
        (Real.log (orderedRadius E n w j) - Real.log (orderedRadius E n w (j + 1))) :=
      hill_weighted_telescoping _ k
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
      rw [Real.log_div (ne_of_gt (hpositive j hj1 (by omega)))
        (ne_of_gt (hpositive (j + 1) (by omega) (by omega)))]

/-- [The algorithm's value conventions](goal) for experiment [E](hyp:E) require [both evaluation averages to be zero for an empty evaluation exceedance set](step:1) and [the Hill statistic to be zero when its reference radius vanishes](step:2). -/
-- @node: ass:pin-owner-3
def AlgorithmValueConventions (E : NeteExperiment M) : Prop :=
  (∀ n t w, evalCount E n t w = 0 → etaIPW E n t w = 0 ∧ etaDR E n t w = 0) ∧
  (∀ n k w, orderedRadius E n w (k + 1) = 0 → hillStat E n k w = 0)

/-- For experiment [E](hyp:E), [both evaluation averages vanish when their evaluation exceedance set is empty, and the Hill statistic vanishes when its reference radius is zero](goal). -/
lemma algorithmValueConventions (E : NeteExperiment M) : AlgorithmValueConventions E := by
  constructor
  · intro n t w h
    simp only [etaIPW, etaDR, if_pos h, and_self]
  · intro n k w h
    simp only [hillStat, if_pos h]

/-- [The lower Hill-rank bound](goal) for [sample size](hyp:n) is the smaller of one less than the sample size and the ceiling of 100 times its logarithm.

@realizes l_n(minimum of n-1 and ceil(100 log n)) -/
def hillLower (n : ℕ) : ℕ := min (n - 1) ⌈100 * Real.log n⌉₊
/-- [The Hill grid size](goal) for [sample size](hyp:n) is one plus the ceiling of its base-two logarithm. -/
def hillGridSize (n : ℕ) : ℕ := 1 + ⌈Real.log n / Real.log 2⌉₊
/-- For [sample size](hyp:n) and [confidence level](hyp:delta), [the Hill logarithmic budget](goal) is the logarithm of four times the grid size divided by the confidence level. -/
def hillLogBudget (n : ℕ) (delta : ℝ) := Real.log (4 * (hillGridSize n : ℝ) / delta)
/-- For [sample size](hyp:n) and [confidence level](hyp:delta), [the Hill deviation bound](goal) combines twice the square root of the logarithmic budget with that budget divided by the square root of the lower rank bound. -/
def hillDeviation (n : ℕ) (delta : ℝ) :=
  2 * Real.sqrt (hillLogBudget n delta) + hillLogBudget n delta / Real.sqrt (hillLower n)
/-- For [a real confidence level](hyp:delta), [the confidence domain](goal) requires it to lie strictly between zero and one.

@realizes \delta(confidence domain (0,1)) -/
def ConfidenceDomain (delta : ℝ) : Prop := 0 < delta ∧ delta < 1

/-- For [sample size](hyp:n) and [confidence level](hyp:delta), [the Hill tolerance](goal) is sixteen times the Hill deviation.

@realizes r_n(deterministic tolerance 16 c_n(delta)) -/
def hillTol (n : ℕ) (delta : ℝ) := 16 * hillDeviation n delta
/-- For [experiment](hyp:E) [E], [sample size](hyp:n), [confidence level](hyp:delta), and [world](hyp:w), [the selected Hill index](goal) is the largest candidate rank whose Hill estimate is sufficiently close to every estimate from the lower rank through that candidate.

@realizes k(largest candidate meeting every comparison from L_n through k) -/
def hillIndex (E : NeteExperiment M) (n : ℕ) (delta : ℝ) (w : E.Om) : ℕ :=
  ((Finset.Icc (hillLower n) (n - 1)).filter (fun k =>
    ∀ i ∈ Finset.Icc (hillLower n) k,
      |hillStat E n i w - hillStat E n k w| ≤
        hillStat E n i w * hillTol n delta / Real.sqrt i)).sup id
/-- For [experiment](hyp:E) [E], [sample size](hyp:n), [confidence level](hyp:delta), and [world](hyp:w), [the adaptive Hill estimate](goal) is the Hill statistic evaluated at the selected Hill index.

@realizes \hat{\gamma}_n(full-input adaptive Hill output) -/
def hillAdaptive (E : NeteExperiment M) (n : ℕ) (delta : ℝ) (w : E.Om) :=
  hillStat E n (hillIndex E n delta w) w
/-- For [experiment](hyp:E) [E], [sample size](hyp:n), [confidence level](hyp:delta), and [world](hyp:w), [the radial-tail estimate](goal) is the reciprocal of one minus the fitted tail index times the adaptive Hill estimate, and is zero if that denominator is zero.

@realizes \hat{\mu}_n(reciprocal radial estimate; zero when denominator vanishes) -/
def muHat (E : NeteExperiment M) (n : ℕ) (delta : ℝ) (w : E.Om) :=
  let den := 1 - E.alphaHat n w * hillAdaptive E n delta w
  if den = 0 then 0 else den⁻¹

/-- [The estimator kind](goal) distinguishes the [inverse-probability-weighted option](hyp:ipw) and [doubly robust option](hyp:dr).

@realizes \mathrm{estimator}(IPW or DR option) -/
inductive EstimatorKind | ipw | dr
-- @node: def:nete-algorithm
/-- For [experiment](hyp:E) [E], [estimator choice](hyp:kind), [sample size](hyp:n), [threshold and confidence level](hyp:t,delta), and [world](hyp:w), [the NETE estimator](goal) multiplies the chosen IPW or doubly robust average by the radial-tail estimate.

@realizes \widehat{\theta}_{n,t}^{\mathrm{estimator}}(first-factor average times radial estimate) -/
def neteEstimator (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t delta : ℝ) (w : E.Om) :=
  (match kind with | .ipw => etaIPW E n t w | .dr => etaDR E n t w) * muHat E n delta w
/-- For [experiment](hyp:E) [E], [the IPW NETE estimator](goal) is the NETE estimator with the inverse-probability-weighted option.

@realizes \widehat{\theta}_{n,t}^{\text{IPW}}(IPW NETE product) -/
abbrev thetaHatIPW (E : NeteExperiment M) := neteEstimator E .ipw
/-- For [experiment](hyp:E) [E], [the doubly robust NETE estimator](goal) is the NETE estimator with the doubly robust option.

@realizes \widehat{\theta}_{n,t}^{\text{DR}}(DR NETE product) -/
abbrev thetaHatDR (E : NeteExperiment M) := neteEstimator E .dr

/-- For [extreme-value model](hyp:M) [M] and [threshold](hyp:t), [the covariate-direction law](goal) is the tail law mapped to each observation's covariates and direction. -/
def covariateDirectionLaw (M : ExtremeModel q d) (t : ℝ) :=
  (tailLaw M t).map (fun w => (M.X w, direction M w))

/-- For [extreme-value model](hyp:M) [M], [threshold](hyp:t), [sign choice](hyp:negative), and [truncation level](hyp:k), [the tail-regression part](goal) is a fixed measurable conditional-regression version of the corresponding bounded signed pseudo-outcome. -/
def tailRegressionPart (M : ExtremeModel q d) (t : ℝ) (negative : Bool) (k : ℕ) :
    ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ :=
  Classical.choose (stronglyMeasurable_condExp
    (μ := tailLaw M t)
    (f := fun w => min (max (if negative then -(M.Y w / radius M w ^ M.alpha)
      else M.Y w / radius M w ^ M.alpha) 0) (k : ℝ))
    (m := MeasurableSpace.comap (fun w => (M.X w, M.D w, direction M w)) inferInstance)
      |>.exists_eq_measurable_comp)

/-- For [extreme-value model](hyp:M) [M], [threshold](hyp:t), and [regressor tuple](hyp:z), [the tail-regression version](goal) is the limit of the nonnegative truncated regression parts minus the limit of the negative truncated regression parts.

Definedness below rules out using limUnder's fallback as an actual regression. -/
def tailRegressionVersion (M : ExtremeModel q d) (t : ℝ)
    (z : (Fin q → ℝ) × Bool × (Fin d → ℝ)) : ℝ :=
  limUnder atTop (fun k => tailRegressionPart M t false k z) -
    limUnder atTop (fun k => tailRegressionPart M t true k z)

-- @node: measurable_tailRegressionVersion
/-- For [extreme-value model](hyp:M) [M] and [threshold](hyp:t), [the tail-regression version is measurable](goal). -/
@[fun_prop]
lemma measurable_tailRegressionVersion (M : ExtremeModel q d) (t : ℝ) :
    Measurable (tailRegressionVersion M t) := by
  unfold tailRegressionVersion
  first | fun_prop | skip
  have hpart (negative : Bool) (k : ℕ) :
      StronglyMeasurable (tailRegressionPart M t negative k) := by
    exact (Classical.choose_spec (stronglyMeasurable_condExp
      (μ := tailLaw M t)
      (f := fun w => min (max (if negative then -(M.Y w / radius M w ^ M.alpha)
        else M.Y w / radius M w ^ M.alpha) 0) (k : ℝ))
      (m := MeasurableSpace.comap (fun w => (M.X w, M.D w, direction M w)) inferInstance)
        |>.exists_eq_measurable_comp)).1
  exact (StronglyMeasurable.limUnder (hpart false)).measurable.sub
    (StronglyMeasurable.limUnder (hpart true)).measurable

/-- For [extreme-value model](hyp:M) [M] and [threshold](hyp:t), [tail-regression definedness](goal) requires that, almost surely under the tail law, both signed truncated-regression sequences converge at the observation's regressor tuple. -/
def TailRegressionDefined (M : ExtremeModel q d) (t : ℝ) : Prop :=
  ∀ᵐ w ∂(tailLaw M t),
    (∃ lp : ℝ, Tendsto (fun k => tailRegressionPart M t false k
      (M.X w, M.D w, direction M w)) atTop (𝓝 lp)) ∧
    (∃ ln : ℝ, Tendsto (fun k => tailRegressionPart M t true k
      (M.X w, M.D w, direction M w)) atTop (𝓝 ln))

/-- For [extreme-value model](hyp:M) [M], [threshold](hyp:t), and [candidate regression](hyp:reg), [being a tail-regression version](goal) means the candidate is measurable, the limiting construction is defined, and it agrees almost surely with that construction under the tail law. -/
def IsTailRegressionVersion (M : ExtremeModel q d) (t : ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) : Prop :=
  Measurable reg ∧ TailRegressionDefined M t ∧
  (fun w => reg (M.X w, M.D w, direction M w)) =ᵐ[tailLaw M t]
    fun w => tailRegressionVersion M t (M.X w, M.D w, direction M w)

/-- For [experiment](hyp:E) [E], [sample size](hyp:n), [threshold and error tolerance](hyp:t,eps), [the three error-rate functions](hyp:Rp,Rg,Ralpha), [regression](hyp:reg), and [world](hyp:w), [the nuisance conditions at that world](goal) bound the tail-index, propensity-score, and regression estimation errors by their respective rates. -/
def NuisanceAt (E : NeteExperiment M) (n : ℕ) (t eps : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om) : Prop :=
  |E.alphaHat n w - M.alpha| ≤ Ralpha n eps ∧
  (∀ᵐ x ∂(M.mu.map M.X), |M.p x - E.pHat n w x| ≤ Rp n eps) ∧
  ∀ a : Bool, ∀ᵐ z ∂(covariateDirectionLaw M t),
    |reg (z.1, a, z.2) - E.gHat n w z.1 a z.2| ≤ Rg (trainCount E n t w) eps

/-- For [experiment](hyp:E) [E], [sample size](hyp:n), and [the three error-rate functions](hyp:Rp,Rg,Ralpha), [the joint nuisance guarantee](goal) says that every positive threshold has a measurable tail regression and, for each valid error tolerance, a high-probability training-measurable event on which all nuisance bounds hold. -/
def JointNuisanceGuarantee (E : NeteExperiment M) (n : ℕ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  ∀ t, 0 < t → ∃ reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ,
    IsTailRegressionVersion M t reg ∧
    ∀ eps, 0 < eps → eps < 1 → ∃ G : Set E.Om,
      MeasurableSet[trainSigma E n] G ∧ (E.P G).toReal ≥ 1 - eps ∧
      ∀ w ∈ G, NuisanceAt E n t eps Rp Rg Ralpha reg w
-- @node: ass:pin-fix-6857bb4d
/-- For [experiment](hyp:E) [E], [sample size](hyp:n), and [the three error-rate functions](hyp:Rp,Rg,Ralpha), [the joint nuisance event reading](goal) is exactly the joint nuisance guarantee. -/
def JointNuisanceEventReading (E : NeteExperiment M) (n : ℕ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop := JointNuisanceGuarantee E n Rp Rg Ralpha

-- @node: ass:pin-44
/-- For [experiment](hyp:E) [E], [sample size](hyp:n), and [the three error-rate functions](hyp:Rp,Rg,Ralpha), [the pinned nuisance errors condition](goal) requires each rate to be nonincreasing in sample size at every valid tolerance and requires the joint nuisance guarantee. -/
def NuisanceErrorsPinned (E : NeteExperiment M) (n : ℕ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  (∀ eps, 0 < eps → eps < 1 →
    Antitone (fun k => Rp k eps) ∧ -- @realizes R_p(nonincreasing in sample size)
    Antitone (fun k => Rg k eps) ∧ -- @realizes R_g(nonincreasing including zero)
    Antitone (fun k => Ralpha k eps)) ∧ -- @realizes R_\alpha(nonincreasing in sample size)
  JointNuisanceGuarantee E n Rp Rg Ralpha

-- @node: ass:rate-nuisance-errors
/-- For [experiment](hyp:E) [E], [sample size](hyp:n), and [the three error-rate functions](hyp:Rp,Rg,Ralpha), [the nuisance error bounds condition](goal) requires each rate to be nonnegative at every natural argument and includes the pinned nuisance-error conditions. -/
def NuisanceErrorBounds (E : NeteExperiment M) (n : ℕ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  (∀ eps, 0 < eps → eps < 1 →
    (∀ k, 0 ≤ Rp k eps) ∧ -- @realizes R_p(nonnegative at every natural argument including zero)
    (∀ k, 0 ≤ Rg k eps) ∧ -- @realizes R_g(nonnegative including count zero)
    (∀ k, 0 ≤ Ralpha k eps)) ∧ -- @realizes R_\alpha(nonnegative at every natural argument including zero)
  NuisanceErrorsPinned E n Rp Rg Ralpha

/-- For [experiment](hyp:E) [E], [sample size](hyp:n), [the three error-rate functions](hyp:Rp,Rg,Ralpha), and [a nuisance-error-bounds assumption](hyp:h), [each rate is nonnegative and nonincreasing at every valid tolerance, and the joint nuisance guarantee holds](goal). -/
lemma nuisanceErrorBounds_components (E : NeteExperiment M) (n : ℕ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (h : NuisanceErrorBounds E n Rp Rg Ralpha) :
    (∀ eps, 0 < eps → eps < 1 →
      ((∀ k, 0 ≤ Rp k eps) ∧ Antitone (fun k => Rp k eps)) ∧
      ((∀ k, 0 ≤ Rg k eps) ∧ Antitone (fun k => Rg k eps)) ∧
      ((∀ k, 0 ≤ Ralpha k eps) ∧ Antitone (fun k => Ralpha k eps))) ∧
    JointNuisanceGuarantee E n Rp Rg Ralpha := by
  refine ⟨?_, h.2.2⟩
  intro eps heps heps1
  exact ⟨⟨(h.1 eps heps heps1).1, (h.2.1 eps heps heps1).1⟩,
    ⟨(h.1 eps heps heps1).2.1, (h.2.1 eps heps heps1).2.1⟩,
    ⟨(h.1 eps heps heps1).2.2, (h.2.1 eps heps heps1).2.2⟩⟩

-- @node: ass:pin-fix-c3605ca3
/-- For [sample size](hyp:n) and [a regression error-rate function](hyp:Rg), [the regression-rate domain](goal) requires the rate to be nonnegative at every count no larger than half the sample size and every valid error tolerance. -/
def RegressionRateDomain (n : ℕ) (Rg : ℕ → ℝ → ℝ) : Prop :=
  ∀ k, k ≤ n / 2 → ∀ eps, 0 < eps → eps < 1 → 0 ≤ Rg k eps

/-- For [experiment](hyp:E) [E], [sample size](hyp:n), [threshold and error tolerance](hyp:t,eps), [the three error-rate functions](hyp:Rp,Rg,Ralpha), and [a worldwise moment condition](hyp:moments), [the nuisance-with-moments condition](goal) provides a measurable tail regression and a high-probability training event where pseudo-outcomes are integrable, the nuisance bounds hold, and the moment condition holds. -/
def NuisanceWithMomentsAt (E : NeteExperiment M) (n : ℕ) (t eps : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (moments : E.Om → Prop) : Prop :=
  ∃ reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ,
    IsTailRegressionVersion M t reg ∧ ∃ G : Set E.Om,
      MeasurableSet[trainSigma E n] G ∧ (E.P G).toReal ≥ 1 - eps ∧
      FittedPseudoOutcomeIntegrable E n t G ∧
      ∀ w ∈ G, NuisanceAt E n t eps Rp Rg Ralpha reg w ∧ moments w

/-- For [experiment](hyp:E) [E], [sample size](hyp:n), and [the three error-rate functions](hyp:Rp,Rg,Ralpha), [nuisance integrability](goal) says that every positive threshold has a measurable tail regression and, at every valid tolerance, a high-probability training event where its nuisance bounds and fitted-pseudo-outcome integrability hold. -/
def NuisanceIntegrability (E : NeteExperiment M) (n : ℕ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  ∀ t, 0 < t → ∃ reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ,
    IsTailRegressionVersion M t reg ∧
    ∀ eps, 0 < eps → eps < 1 → ∃ G : Set E.Om,
      MeasurableSet[trainSigma E n] G ∧ (E.P G).toReal ≥ 1 - eps ∧
      (∀ w ∈ G, NuisanceAt E n t eps Rp Rg Ralpha reg w) ∧
      FittedPseudoOutcomeIntegrable E n t G

/-- For [experiment](hyp:E) [E], [sample size](hyp:n), [threshold](hyp:t), and [world](hyp:w), [the doubly robust score variance](goal) is the extended variance of the fitted doubly robust score under the observed tail law. -/
def scoreVarDR (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) : ℝ≥0∞ :=
  evariance (drScore E n w) (obsTailLaw M t)
-- @node: ass:pin-fix-b3a62d30
/-- For [experiment](hyp:E) [E], [sample size](hyp:n), [threshold](hyp:t), and [world](hyp:w), [the score-variance condition](goal) states that the defined doubly robust score variance equals the extended variance of that score under the observed tail law. -/
def ScoreVarianceIsConditionalVariance (E : NeteExperiment M) (n : ℕ) (t : ℝ) (w : E.Om) : Prop :=
  scoreVarDR E n t w = evariance (drScore E n w) (obsTailLaw M t)

/-- For [tail regularity parameter](hyp:beta), [sample size](hyp:n), and [positive scaling factor](hyp:a), [the Hill rate shape](goal) uses one of three logarithmic power rates according as the regularity parameter is below, equal to, or above one. -/
def hillRateShape (beta : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  if beta < 1 then (Real.log (a * Real.log n) / n) ^ (1 / 3 : ℝ)
  else if beta = 1 then (Real.log n * Real.log (a * Real.log n) / n) ^ (1 / 3 : ℝ)
  else (Real.log (a * Real.log n) / n) ^ (1 / (2 + beta))
-- @node: ass:pin-fix-c4d18fdb
/-- For [experiment](hyp:E) [E], [the Hill rate guarantee](goal) says that at every confidence level in the confidence domain, sufficiently large independently sampled data have an adaptive Hill estimate within a constant multiple of the Hill rate shape of the true tail index with probability at least one minus that level. -/
def HillRateGuarantee (E : NeteExperiment M) : Prop :=
  ∀ delta, ConfidenceDomain delta → ∃ n0 : ℕ, ∃ C : ℝ,
    ∀ n, n0 ≤ n → IIDSampling E n → (E.P {w | |gamma M - hillAdaptive E n delta w| ≤
      C * hillRateShape M.beta n (8 / delta)}).toReal ≥ 1 - delta

-- @node: ass:pin-fix-27ee3ba1
/-- For [a sequence of propositions](hyp:Q), [holding for large even indices](goal) means that there is a cutoff beyond which the proposition holds at every even natural number. -/
def HoldsForLargeEven (Q : ℕ → Prop) : Prop := ∃ n0, ∀ n, n0 ≤ n → Even n → Q n
-- @node: ass:pin-fix-fc4621e4
/-- For [a sequence of propositions](hyp:Q), [holding for large even IPW indices](goal) means holding for all sufficiently large even indices. -/
def HoldsForLargeEvenIpw (Q : ℕ → Prop) : Prop := HoldsForLargeEven Q

-- @node: ass:pin-fix-d303828c
/-- For [positive lower and upper constants](hyp:cminus,cplus), [an exponent function](hyp:kappa), and [an estimated tail-index process](hyp:gammaHat), [the selected-threshold order condition](goal) requires every even-sample threshold to lie between those constants times the sample-size power determined by its estimated tail index.

@realizes t_n(two-sided random order with deterministic constants) -/
def SelectedThresholdOrder {W : Type} (cminus cplus : ℝ) (kappa : ℝ → ℝ)
    (gammaHat tn : ℕ → W → ℝ) : Prop :=
  0 < cminus ∧ cminus ≤ cplus ∧ ∀ (n : ℕ), EvenSampleSize n → ∀ w,
    cminus * (n : ℝ) ^ kappa (gammaHat n w) ≤ tn n w ∧
    tn n w ≤ cplus * (n : ℝ) ^ kappa (gammaHat n w)
-- @node: ass:pin-fix-fdafcd87
/-- For [positive lower and upper constants](hyp:cminus,cplus), [an exponent function](hyp:kappa), and [an estimated tail-index process](hyp:gammaHat), [the IPW selected-threshold order condition](goal) is the selected-threshold order condition for those inputs. -/
def SelectedThresholdOrderIpw {W : Type} (cminus cplus : ℝ) (kappa : ℝ → ℝ)
    (gammaHat tn : ℕ → W → ℝ) : Prop := SelectedThresholdOrder cminus cplus kappa gammaHat tn

-- @node: ass:pin-fix-ebdb71b8
/-- For [estimation error](hyp:err), [variance bound](hyp:v), [uniform bound](hyp:b), [confidence level](hyp:delta), [effective count](hyp:count), and [remainder term](hyp:remainder), [the IPW truncated-sampling bound](goal) bounds the error by a variance term, a boundedness term, and the remainder. -/
def IpwTruncatedSamplingBound (err v b delta count remainder : ℝ) : Prop :=
  err ≤ Real.sqrt (4 * v / (delta * count)) + (1 + 4 / delta) * b + remainder

end
end Papers.TbsExtremeEffects
