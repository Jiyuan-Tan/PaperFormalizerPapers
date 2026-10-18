module
public import Papers.TbsExtremeEffects.Helpers.ScoreMoments

/-! The product-decomposition bounds appearing in the fixed-threshold theorem. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
noncomputable section
variable {q d : ℕ} {M : ExtremeModel q d}

/-- [A predicate on real constants](hyp:P) has a [generic rate constant](goal) when some strictly positive constant satisfies it. -/
def GenericRateConstant (P : ℝ → Prop) : Prop := ∃ C : ℝ, 0 < C ∧ P C

/-- The [extreme-value model](hyp:M), [Hill-rate coefficient](hyp:Cg), [confidence tolerance](hyp:delta), and [sample size](hyp:n) determine the [Hill estimation error bound](goal) as the coefficient times the Hill-rate shape at tolerance `48 / delta`.

@realizes b_n(deterministic EVI error bound at tolerance delta/6) -/
def hillErrorBound (M : ExtremeModel q d) (Cg delta : ℝ) (n : ℕ) :=
  Cg * hillRateShape M.beta n (48 / delta)
/-- The [extreme-value model](hyp:M) determines [the radial denominator target](goal), one minus its tail exponent times its Hill parameter. -/
def radialH (M : ExtremeModel q d) := 1 - M.alpha * gamma M
/-- The [model](hyp:M), [Hill-rate coefficient](hyp:Cg), [confidence tolerance](hyp:delta), [exponent-error rate](hyp:Ralpha), and [sample size](hyp:n) determine [the radial product-error budget](goal) by combining exponent and Hill errors. -/
def radialQ (M : ExtremeModel q d) (Cg delta : ℝ) (Ralpha : ℕ → ℝ → ℝ) (n : ℕ) :=
  Ralpha n (delta / 12) * (gamma M + hillErrorBound M Cg delta n) +
    |M.alpha| * hillErrorBound M Cg delta n
/-- The [experiment](hyp:E), [sample size](hyp:n), [confidence tolerance](hyp:delta), and [outcome](hyp:w) determine [the estimated radial denominator](goal) as the absolute gap between one and the estimated exponent–Hill product. -/
def estimatedDenominator (E : NeteExperiment M) (n : ℕ) (delta : ℝ) (w : E.Om) :=
  |1 - E.alphaHat n w * hillAdaptive E n (delta / 6) w|
/-- The [experiment](hyp:E), [Hill-rate coefficient](hyp:Cg), [confidence tolerance](hyp:delta), [exponent-error rate](hyp:Ralpha), [sample size](hyp:n), and [outcome](hyp:w) determine [the radial reciprocal error bound](goal), using the product-error budget when the estimated denominator is positive and the reciprocal target otherwise. -/
def radialError (E : NeteExperiment M) (Cg delta : ℝ) (Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (w : E.Om) :=
  let den := estimatedDenominator E n delta w
  if 0 < den then radialQ M Cg delta Ralpha n / (radialH M * den) else 1 / radialH M

/-- The [experiment](hyp:E), [estimator type](hyp:kind), [sample size](hyp:n), [threshold](hyp:t), [confidence tolerance](hyp:delta), [truncation bound](hyp:B), and [outcome](hyp:w) determine [the sampling error term](goal) from a truncated variance radius and score-tail contribution. -/
def rateSamplingError (E : NeteExperiment M) (kind : EstimatorKind) (n : ℕ)
    (t delta : ℝ) (B : E.Om → ℝ) (w : E.Om) :=
  Real.sqrt (12 * truncatedSecondMoment E kind n t B w /
    (delta * (max (evalCount E n t w) 1 : ℕ))) +
  (1 + 12 / delta) * scoreTailMoment E kind n t B w

/-- The [experiment](hyp:E), [estimator type](hyp:kind), [overlap constants](hyp:c,Cgb), [exponent margin](hyp:a0), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold](hyp:t), [confidence tolerance](hyp:delta), [truncation bound](hyp:B), and [outcome](hyp:w) determine [the first-factor error bound](goal) as sampling error plus nuisance remainder. -/
def rateFirstFactorError (E : NeteExperiment M) (kind : EstimatorKind)
    (c Cgb a0 : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t delta : ℝ) (B : E.Om → ℝ) (w : E.Om) :=
  rateSamplingError E kind n t delta B w +
    etaRemainder E kind c Cgb (4 / (M.beta - a0)) Rp Rg Ralpha n t (delta / 12) w

/-- The [experiment](hyp:E), [estimator type](hyp:kind), [variance bound](hyp:V), [Hill-rate coefficient](hyp:Cg), [confidence tolerance](hyp:delta), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold](hyp:t), and [outcome](hyp:w) determine [the simplified rate](goal) combining variance, nuisance, tail-approximation, angular, exponent, and Hill terms. -/
def simplifiedRate (E : NeteExperiment M) (kind : EstimatorKind)
    (V Cg delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) (w : E.Om) :=
  Real.sqrt (V / (delta * n * tailProb M t)) +
  (match kind with
    | .dr => Rp (n / 2) (delta / 12) * Rg (trainCount E n t w) (delta / 12)
    | .ipw => Rp (n / 2) (delta / 12)) +
  eBar M t + 2 * M.L * angularW1 M t + Ralpha n (delta / 12) * Real.log t +
    hillErrorBound M Cg delta n

/-- The [experiment](hyp:E), [sample size](hyp:n), [threshold](hyp:t), [tolerance](hyp:eps), [nuisance rates](hyp:Rp,Rg,Ralpha), and [variance cap](hyp:V) satisfy [the second-moment nuisance condition](goal) when the nuisance event supplies square-integrable scores with second moments at most that cap for both estimators. -/
def secondMomentsOnNuisance (E : NeteExperiment M) (n : ℕ) (t eps : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (V : ℝ) : Prop :=
  NuisanceWithMomentsAt E n t eps Rp Rg Ralpha (fun w =>
    ∀ kind : EstimatorKind, MemLp (score E kind n w) 2 (obsTailLaw M t) ∧
      scoreSecondMoment E kind n t w ≤ V)

/-- The [experiment](hyp:E), [confidence tolerance](hyp:delta), [starting sample size](hyp:n0), and [Hill coefficient](hyp:Cg) satisfy [the Hill-constant guarantee](goal) when every larger IID sample has the stated Hill-error event with probability at least `1 - delta`. -/
def HillConstantAt (E : NeteExperiment M) (delta : ℝ) (n0 : ℕ) (Cg : ℝ) : Prop :=
  ∀ n, n0 ≤ n → IIDSampling E n → (E.P {w | |gamma M - hillAdaptive E n delta w| ≤
    Cg * hillRateShape M.beta n (8 / delta)}).toReal ≥ 1 - delta

/-- The [experiment](hyp:E), [overlap and tail constants](hyp:c,Cgb,a0,C,Cg,V,delta), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold](hyp:t), [DR and IPW truncation bounds](hyp:Bdr,Bipw), and [outcome](hyp:w) satisfy [product success](goal) when the evaluation count and both product-error bounds hold, together with their simplified-rate consequences under the listed moment and separation conditions. The count requirement is [clause 1](step:1), the DR and IPW product bounds are [clauses 2](step:2) and [3](step:3), and the conditional simplified-rate consequences are [clause 4](step:4). -/
def ProductSuccess (E : NeteExperiment M)
    (c Cgb a0 C Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t : ℝ) (Bdr Bipw : E.Om → ℝ) (w : E.Om) : Prop :=
  (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
  (|thetaHatDR E n t (delta / 6) w - thetaNETE M| ≤
    |muHat E n (delta / 6) w| *
      rateFirstFactorError E .dr c Cgb a0 Rp Rg Ralpha n t delta Bdr w +
      |etaTarget M| * radialError E Cg delta Ralpha n w) ∧
  (|thetaHatIPW E n t (delta / 6) w - thetaNETE M| ≤
    |muHat E n (delta / 6) w| *
      rateFirstFactorError E .ipw c Cgb a0 Rp Rg Ralpha n t delta Bipw w +
      |etaTarget M| * radialError E Cg delta Ralpha n w) ∧
  (secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V → Real.exp 1 ≤ t →
    Ralpha n (delta / 12) * Real.log t ≤ 1 →
    radialQ M Cg delta Ralpha n ≤ radialH M / 2 →
      (|thetaHatDR E n t (delta / 6) w - thetaNETE M| ≤
        C * simplifiedRate E .dr V Cg delta Rp Rg Ralpha n t w) ∧
      (|thetaHatIPW E n t (delta / 6) w - thetaNETE M| ≤
        C * simplifiedRate E .ipw V Cg delta Rp Rg Ralpha n t w))

end
end Papers.TbsExtremeEffects
