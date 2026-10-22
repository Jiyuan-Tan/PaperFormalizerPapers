module
public import Papers.TbsExtremeEffects.Helpers.ProductBounds

/-! Deterministic threshold bands and the two adaptive-threshold regimes. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
noncomputable section
variable {q d : ℕ} {M : ExtremeModel q d}

/-- [The low-regime exponent](goal) multiplies [the tail parameter](hyp:v) by one minus twice [the regime index](hyp:s). -/
def lowRegimeExponent (s v : ℝ) := (1 - 2 * s) * v
/-- [The high-regime exponent](goal) rescales [the tail parameter](hyp:v) by one plus twice its value, capped at one. -/
def highRegimeExponent (v : ℝ) := v / (1 + 2 * min 1 v)
/-- [The corollary rate exponent](goal) is the reciprocal of two plus [the tail index](hyp:beta), floored at one. -/
def corRateExponent (beta : ℝ) := 1 / (2 + max beta 1)
/-- [The threshold band](goal) is the interval from half [the lower constant](hyp:cminus) to twice [the upper constant](hyp:cplus), each scaled using [the exponent rule](hyp:kappa), [the model's tail index](hyp:M), and [the sample size](hyp:n). -/
def thresholdBand (M : ExtremeModel q d) (cminus cplus : ℝ) (kappa : ℝ → ℝ) (n : ℕ) :=
  Set.Icc ((cminus / 2) * (n : ℝ) ^ kappa (gamma M))
    (2 * cplus * (n : ℝ) ^ kappa (gamma M))

/-- [The rate condition](goal) holds for [a rate function](hyp:rate) with [exponent](hyp:a) when positive constants bound it above and below, uniformly over sufficiently large sample sizes and confidence levels, by the logarithmic confidence factor times the sample size to that exponent. -/
-- @node: ass:pin-owner-1
def RateTheta (rate : ℕ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n, n0 ≤ n → ∀ eps, 0 < eps → eps < 1 →
      c * Real.log (1 / eps) * (n : ℝ) ^ (-a) ≤ rate n eps ∧
      rate n eps ≤ C * Real.log (1 / eps) * (n : ℝ) ^ (-a)

/-- [The IPW rate condition](goal) holds for [a rate function](hyp:rate) with [exponent](hyp:a) exactly when it satisfies the same two-sided uniform rate condition. -/
-- @node: ass:pin-owner-2
def RateThetaIpw (rate : ℕ → ℝ → ℝ) (a : ℝ) : Prop := RateTheta rate a

/-- [A probability measure](hyp:P), [error tolerance](hyp:delta), [sampling condition](hyp:sampling), [error quantity](hyp:err), and [rate](hyp:rate) satisfy [the eventual big-O guarantee](goal) when one positive constant makes the error no larger than that multiple of the rate with probability at least one minus the tolerance for all sufficiently large even samples. -/
def EventualBigOBound {W : Type} [MeasurableSpace W] (P : Measure W) (delta : ℝ)
    (sampling : ℕ → Prop) (err rate : ℕ → W → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ HoldsForLargeEven
    (fun n => sampling n → (P {w | err n w ≤ C * rate n w}).toReal ≥ 1 - delta)

/-- [A probability measure](hyp:P), [error tolerance](hyp:delta), [sampling condition](hyp:sampling), [error quantity](hyp:err), and [rate](hyp:rate) satisfy [the IPW eventual big-O guarantee](goal) when the same eventual high-probability bound holds with the IPW large-even-sample convention. -/
def EventualBigOBoundIpw {W : Type} [MeasurableSpace W] (P : Measure W) (delta : ℝ)
    (sampling : ℕ → Prop) (err rate : ℕ → W → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ HoldsForLargeEvenIpw
    (fun n => sampling n → (P {w | err n w ≤ C * rate n w}).toReal ≥ 1 - delta)

/-- [The band guarantee](goal) says that [the extreme-value model](hyp:M), [an experiment](hyp:E), and [an estimator choice](hyp:kind) admit valid tail regressions and a high-probability training event throughout the band determined by [the lower constant](hyp:cminus), [upper constant](hyp:cplus), [moment budget](hyp:V), [confidence level](hyp:delta), [exponent rule](hyp:kappa), [propensity rate](hyp:Rp), [outcome rate](hyp:Rg), [tail-index rate](hyp:Ralpha), and [sample size](hyp:n). -/
def BandGuarantee (E : NeteExperiment M) (kind : EstimatorKind)
    (cminus cplus V delta : ℝ) (kappa : ℝ → ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) : Prop :=
  ∃ reg : ℝ → ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ,
    (∀ t ∈ thresholdBand M cminus cplus kappa n, IsTailRegressionVersion M t (reg t)) ∧
    ∃ G : Set E.Om, MeasurableSet[trainSigma E n] G ∧
    (E.P G).toReal ≥ 1 - delta / 6 ∧
    (∀ t ∈ thresholdBand M cminus cplus kappa n, FittedPseudoOutcomeIntegrable E n t G) ∧
    ∀ w ∈ G, ∀ t ∈ thresholdBand M cminus cplus kappa n,
      |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 6) ∧
      (∀ᵐ x ∂(M.mu.map M.X), |M.p x - E.pHat n w x| ≤ Rp (n / 2) (delta / 6)) ∧
      (∀ a : Bool, ∀ᵐ z ∂(covariateDirectionLaw M t),
        |reg t (z.1, a, z.2) - E.gHat n w z.1 a z.2| ≤
          Rg (trainCount E n t w) (delta / 6)) ∧
      MemLp (score E kind n w) 2 (obsTailLaw M t) ∧ scoreSecondMoment E kind n t w ≤ V

/-- [The corollary error](goal) is the absolute difference between the estimator for [the extreme-value model](hyp:M), [experiment](hyp:E), [estimator choice](hyp:kind), [selected threshold](hyp:tn), [confidence level](hyp:delta), [sample size](hyp:n), and [data realization](hyp:w), and the target effect. -/
def corError (E : NeteExperiment M) (kind : EstimatorKind) (tn : ℕ → E.Om → ℝ)
    (delta : ℝ) (n : ℕ) (w : E.Om) :=
  |neteEstimator E kind n (tn n w) (delta / 6) w - thetaNETE M|
/-- [The corollary rate](goal) combines the variance term for [the extreme-value model](hyp:M), [experiment](hyp:E), [estimator choice](hyp:kind), [selected threshold](hyp:tn), [moment bound](hyp:V), [Hill constant](hyp:Cg), [confidence level](hyp:delta), [alpha rate](hyp:cAlpha), [main rate exponent](hyp:r), [sample size](hyp:n), and [data realization](hyp:w), with the estimator-specific nuisance and threshold errors. -/
def corRate (E : NeteExperiment M) (kind : EstimatorKind) (tn : ℕ → E.Om → ℝ)
    (V Cg delta cAlpha r : ℝ) (n : ℕ) (w : E.Om) :=
  Real.sqrt (V / delta) * (n : ℝ) ^ (-r) +
    (match kind with
     | .dr => Real.log (6 / delta) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ) - r)
     | .ipw => Real.log (6 / delta) * (n : ℝ) ^ (-(1 / 2 : ℝ))) +
    eBar M (tn n w) + 2 * M.L * angularW1 M (tn n w) +
    (n : ℝ) ^ (-cAlpha) * Real.log n * Real.log (6 / delta) +
    |M.alpha| * hillErrorBound M Cg delta n

end
end Papers.TbsExtremeEffects
