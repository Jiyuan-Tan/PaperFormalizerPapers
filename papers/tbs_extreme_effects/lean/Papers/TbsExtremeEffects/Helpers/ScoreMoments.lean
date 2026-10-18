module
public import Papers.TbsExtremeEffects.Helpers.Angular

/-! Frozen-fit score moments and the two first-factor error displays. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
set_option linter.style.longLine false
open scoped Classical ENNReal
noncomputable section
variable {q d : ℕ} {M : ExtremeModel q d}

/-- [The score](goal) for [a model](hyp:M), [an experiment](hyp:E), [an estimator type](hyp:kind), [a sample size](hyp:n), and [frozen data](hyp:w) is its DR or IPW score as selected by that type. -/
def score (E : NeteExperiment M) (kind : EstimatorKind) (n : ℕ) (w : E.Om) :=
  match kind with | .dr => drScore E n w | .ipw => ipwScore E n w
/-- [The eta estimate](goal) from [a model](hyp:M), [an experiment](hyp:E), and [an estimator type](hyp:kind) is the corresponding DR or IPW estimate. -/
def etaEstimate (E : NeteExperiment M) (kind : EstimatorKind) :=
  match kind with | .dr => etaDR E | .ipw => etaIPW E

/-- [The truncated second moment](goal) for [a model](hyp:M), [an experiment](hyp:E), [an estimator type](hyp:kind), [sample size](hyp:n), [tail threshold](hyp:t), [data-dependent cutoff](hyp:B), and [frozen data](hyp:w) is the tail-law expectation of the squared score below that cutoff. -/
def truncatedSecondMoment (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (B : E.Om → ℝ) (w : E.Om) :=
  ∫ z, if |score E kind n w z| ≤ B w then (score E kind n w z)^2 else 0 ∂(obsTailLaw M t)
/-- [The score tail moment](goal) for [a model](hyp:M), [an experiment](hyp:E), [an estimator type](hyp:kind), [sample size](hyp:n), [tail threshold](hyp:t), [cutoff](hyp:B), and [frozen data](hyp:w) is the tail-law expectation of the score magnitude above the cutoff. -/
def scoreTailMoment (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (B : E.Om → ℝ) (w : E.Om) :=
  ∫ z, if B w < |score E kind n w z| then |score E kind n w z| else 0 ∂(obsTailLaw M t)
/-- [The score second moment](goal) for [a model](hyp:M), [an experiment](hyp:E), [an estimator type](hyp:kind), [sample size](hyp:n), [tail threshold](hyp:t), and [frozen data](hyp:w) is its squared-score expectation under the tail law. -/
def scoreSecondMoment (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) := ∫ z, (score E kind n w z)^2 ∂(obsTailLaw M t)
/-- [The score variance](goal) for [a model](hyp:M), [an experiment](hyp:E), [an estimator type](hyp:kind), [sample size](hyp:n), [tail threshold](hyp:t), and [frozen data](hyp:w) is the extended-real variance of the frozen score under the tail law. -/
def scoreVariance (E : NeteExperiment M) (kind : EstimatorKind)
    (n : ℕ) (t : ℝ) (w : E.Om) : ℝ≥0∞ := evariance (score E kind n w) (obsTailLaw M t)

/-- [The global bound condition](goal) says that [the model](hyp:M)'s outcome regression is bounded in magnitude by [the nonnegative constant](hyp:Cgb) throughout the specified radius and positive-direction domain. -/
def GBound (M : ExtremeModel q d) (Cgb : ℝ) : Prop :=
  0 ≤ Cgb ∧ ∀ x, l1Norm x ≤ M.R → ∀ a : Bool, ∀ u ∈ positiveSphere l1Norm,
    |M.g x a u| ≤ Cgb

/-- [The eta remainder](goal) for [a model](hyp:M), [an experiment](hyp:E), [an estimator type](hyp:kind), [the constants](hyp:c,Cgb,K), [the nuisance-rate functions](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [tail threshold and accuracy](hyp:t,eps), and [frozen data](hyp:w) combines nuisance, tail-approximation, and regular-variation errors. -/
def etaRemainder (E : NeteExperiment M) (kind : EstimatorKind)
    (c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t eps : ℝ) (w : E.Om) :=
  let a := Ralpha n eps
  let Gt := Cgb + eBar M t
  (match kind with
    | .dr => (2 / c) * Rp (n / 2) eps * Rg (trainCount E n t w) eps
    | .ipw => (2 * Gt / c) * Rp (n / 2) eps) +
    2 * eBar M t + 2 * M.L * angularW1 M t +
    (2 * Gt / c) * (t ^ a - 1 + K * a * t ^ a)

/-- [The truncated eta error bound](goal) for [a model](hyp:M), [an experiment](hyp:E), [an estimator type](hyp:kind), [the constants](hyp:c,Cgb,K), [the nuisance-rate functions](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [tail threshold and failure probability](hyp:t,delta), [cutoff](hyp:B), and [frozen data](hyp:w) adds sampling, tail, and remainder terms. -/
def etaTruncatedError (E : NeteExperiment M) (kind : EstimatorKind)
    (c Cgb K : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t delta : ℝ) (B : E.Om → ℝ) (w : E.Om) :=
  Real.sqrt (4 * truncatedSecondMoment E kind n t B w / (delta * evalCount E n t w)) +
    (1 + 4 / delta) * scoreTailMoment E kind n t B w +
    etaRemainder E kind c Cgb K Rp Rg Ralpha n t (delta / 4) w

/-- [The eta rate conclusion](goal) says that [a model](hyp:M) and [an experiment](hyp:E) using [an estimator type](hyp:kind), [the constants](hyp:c,Cgb,K,t0,a0), and [the nuisance-rate functions](hyp:Rp,Rg,Ralpha) attain the displayed truncated-error guarantee whenever all listed sampling, nuisance, threshold, and cutoff conditions hold. -/
def EtaRateConclusion (E : NeteExperiment M) (kind : EstimatorKind)
    (c Cgb K t0 a0 : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  ∀ n, EvenSampleSize n → IIDSampling E n → ExponentTraining E n →
    NuisanceErrorBounds E n Rp Rg Ralpha → NuisanceIntegrability E n Rp Rg Ralpha →
    ∀ t, t0 ≤ t → ∀ delta, 0 < delta → delta < 1 →
    Ralpha n (delta / 4) ≤ a0 →
    (n : ℝ) * tailProb M t ≥ 16 * Real.log (4 / delta) →
    ∀ B : E.Om → ℝ, Measurable[trainSigma E n] B → (∀ w, 0 < B w) →
    (E.P {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      (match kind with
       | .dr => |etaEstimate E .dr n t w - etaTarget M| ≤
           etaTruncatedError E .dr c Cgb K Rp Rg Ralpha n t delta B w
       | .ipw => IpwTruncatedSamplingBound |etaEstimate E .ipw n t w - etaTarget M|
           (truncatedSecondMoment E .ipw n t B w) (scoreTailMoment E .ipw n t B w)
           delta (evalCount E n t w)
           (etaRemainder E .ipw c Cgb K Rp Rg Ralpha n t (delta / 4) w))}).toReal ≥ 1 - delta

/-- [The eta variance conclusion](goal) says that [a model](hyp:M) and [an experiment](hyp:E) using [an estimator type](hyp:kind), [the constants](hyp:c,Cgb,K,t0,a0), and [the nuisance-rate functions](hyp:Rp,Rg,Ralpha) attain the displayed finite-variance error guarantee whenever all listed sampling, nuisance, threshold, and moment conditions hold. -/
def EtaVarianceConclusion (E : NeteExperiment M) (kind : EstimatorKind)
    (c Cgb K t0 a0 : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) : Prop :=
  ∀ n, EvenSampleSize n → IIDSampling E n → ExponentTraining E n →
    NuisanceErrorBounds E n Rp Rg Ralpha →
    ∀ t, t0 ≤ t → ∀ delta, 0 < delta → delta < 1 →
    NuisanceWithMomentsAt E n t (delta / 4) Rp Rg Ralpha
      (fun w => scoreVariance E kind n t w ≠ ∞) →
    Ralpha n (delta / 4) ≤ a0 →
    (n : ℝ) * tailProb M t ≥ 16 * Real.log (4 / delta) →
    (E.P {w | (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
      scoreVariance E kind n t w ≠ ∞ ∧
      (match kind with
       | .dr => (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder)
       | .ipw => (fun err V delta count remainder : ℝ =>
        err ≤ Real.sqrt (4 * V / (delta * count)) + remainder))
        |etaEstimate E kind n t w - etaTarget M|
        (scoreVariance E kind n t w).toReal delta (evalCount E n t w)
        (etaRemainder E kind c Cgb K Rp Rg Ralpha n t (delta / 4) w)}).toReal ≥ 1 - delta

end
end Papers.TbsExtremeEffects
