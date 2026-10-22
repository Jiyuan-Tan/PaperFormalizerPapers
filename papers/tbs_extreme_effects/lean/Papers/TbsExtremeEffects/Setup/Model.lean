module
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Population objects and the pinned almost-sure assumptions for extreme effects.
Conditional independence is expressed by indicator conditional expectations, requiring
no standard-Borel restriction on the population sample space. -/

@[expose] public section

namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
set_option linter.style.openClassical false
set_option linter.style.longLine false
open scoped BigOperators ENNReal Topology Classical
noncomputable section

-- @env: S1
variable {q d : ℕ} -- @realizes d(noise dimension Fin d)

-- @node: def:l1-norm-convention
/-- [A finite real vector](hyp:v) is assigned [its coordinate sum norm](goal), the sum of the absolute values of its coordinates.
@realizes \|\cdot\|(sum of absolute coordinates)
@realizes \|\cdot\|_1(sum of absolute coordinates) -/
def l1Norm {k : ℕ} (v : Fin k → ℝ) : ℝ := ∑ i, |v i|

/-- [The nonnegative orthant](goal) is the set of vectors whose every coordinate is nonnegative. -/
def nonnegativeOrthant {k : ℕ} : Set (Fin k → ℝ) := {v | ∀ i, 0 ≤ v i}
/-- For [a real-valued function on vectors](hyp:N), [the positive unit sphere](goal) consists of nonnegative vectors on which that function equals one. -/
def positiveSphere {k : ℕ} (N : (Fin k → ℝ) → ℝ) : Set (Fin k → ℝ) :=
  {v | v ∈ nonnegativeOrthant ∧ N v = 1}
/-- [The function $N$](hyp:N) is [a norm function](goal) when [it is nonnegative](step:1), [it vanishes only at zero](step:2), [it is absolutely homogeneous](step:3), and [it satisfies the triangle inequality](step:4). -/
def IsNormFn {k : ℕ} (N : (Fin k → ℝ) → ℝ) : Prop :=
  (∀ v, 0 ≤ N v) ∧ (∀ v, N v = 0 ↔ v = 0) ∧
  (∀ a v, N (fun i => a * v i) = |a| * N v) ∧
  (∀ v w, N (v + w) ≤ N v + N w)

/-- [The tail-index parameter](hyp:beta) determines [the radial tail measure](goal), with density $\beta r^{-\beta-1}$ on positive radii and no mass at infinity.
@realizes \nu_{\beta}(density beta r^(-beta-1) on positive radii; no mass at infinity) -/
def radialTailMeasure (beta : ℝ) : Measure ℝ≥0∞ :=
  (volume.withDensity (fun r : ℝ =>
    ENNReal.ofReal (if 0 < r then beta * r ^ (-beta - 1) else 0))).map ENNReal.ofReal

/-- For [a real-valued radial function on vectors](hyp:N) and [a set of vectors](hyp:B), [the relative sphere frontier](goal) is the ambient-vector image of that set's boundary within the positive unit sphere. -/
def relativeSphereFrontier {k : ℕ} (N : (Fin k → ℝ) → ℝ)
    (B : Set (Fin k → ℝ)) : Set (Fin k → ℝ) :=
  Subtype.val '' frontier {v : {u // u ∈ positiveSphere N} | v.val ∈ B}

/-- [The measure $\nu$](hyp:nu), [radial function $N$](hyp:N), [tail index $\beta$](hyp:beta), [spectral measure $S$](hyp:S), [normalizing sequence $b$](hyp:b), and [mass constant $c$](hyp:c) satisfy [polar rectangle convergence](goal) when every positive radial threshold and suitably regular spherical set have the stated tail limit. -/
def PolarRectangleConvergence (nu : Measure (Fin d → ℝ))
    (N : (Fin d → ℝ) → ℝ) (beta : ℝ) (S : Measure (Fin d → ℝ))
    (b : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ B : Set (Fin d → ℝ), MeasurableSet B →
    B ⊆ positiveSphere N → S (relativeSphereFrontier N B) = 0 →
    Tendsto (fun n : ℕ => (n : ℝ) *
      (nu {u | b n * r < N u ∧ (fun i => u i / N u) ∈ B}).toReal)
      atTop (𝓝 (c * r ^ (-beta) * (S B).toReal))

/-- Certificate for one chosen norm and its witnesses. -/
structure RegularVariation (nu : Measure (Fin d → ℝ)) (beta : ℝ)
    (N : (Fin d → ℝ) → ℝ) (S : Measure (Fin d → ℝ)) (b : ℕ → ℝ) (c : ℝ) : Prop where
  beta_pos : 0 < beta -- @realizes \beta(positive regular variation index)
  spectral_probability : IsProbabilityMeasure S -- @realizes S(probability measure)
  spectral_support : S (positiveSphere N)ᶜ = 0 -- @realizes S(positive N-unit sphere)
  normalizer_pos : ∀ n, 1 ≤ n → 0 < b n -- @realizes b_n(positive normalizing sequence)
  normalizer_tendsto : Tendsto b atTop atTop -- @realizes b_n(tends to infinity)
  mass_pos : 0 < c -- @realizes c(positive radial mass multiplier)
  setwise : PolarRectangleConvergence nu N beta S b c

/-- [The probability measure $\nu$](hyp:nu) and [tail index $\beta$](hyp:beta) satisfy [tail-measure convergence](goal) when [the law has total mass one](step:1), [it is supported on the nonnegative orthant](step:2), [the index is positive](step:3), and [every norm has polar regular-variation witnesses](step:4). -/
-- @node: ass:pin-38
def TailMeasureConvergence (nu : Measure (Fin d → ℝ)) (beta : ℝ) : Prop :=
  IsProbabilityMeasure nu ∧ nu nonnegativeOrthantᶜ = 0 ∧
  0 < beta ∧ -- @realizes \beta(positive index of polar convergence)
  ∀ N, IsNormFn N → ∃ S b c, RegularVariation nu beta N S b c

-- @node: def:regular-variation
/-- Regular variation of a nonnegative probability law, for every norm. -/
structure IsRegularlyVarying (nu : Measure (Fin d → ℝ)) (beta : ℝ) : Prop where
  probability : IsProbabilityMeasure nu
  nonnegative : nu nonnegativeOrthantᶜ = 0
  beta_pos : 0 < beta -- @realizes \beta(positive index of the all-norm definition)
  all_norms : ∀ N, IsNormFn N → ∃ S b c, RegularVariation nu beta N S b c

/-- Data of a population world. Mathematical assumptions are threaded predicates below. -/
structure ExtremeModel (q d : ℕ) where
  Om : Type
  measurableSpace : MeasurableSpace Om
  mu : @Measure Om measurableSpace
  probability : @IsProbabilityMeasure Om measurableSpace mu
  covariateDomain : Set (Fin q → ℝ) -- @realizes X(covariate domain 𝒳 in ℝ^q)
  X : Om → Fin q → ℝ -- @realizes X(covariate carrier; range in covariateDomain)
  X_mem_domain : ∀ w, X w ∈ covariateDomain -- @realizes X(values in the covariate domain 𝒳)
  D : Om → Bool -- @realizes D(binary treatment)
  Y0 : Om → ℝ -- @realizes Y(d)(potential outcome under treatment zero)
  Y1 : Om → ℝ -- @realizes Y(d)(potential outcome under treatment one)
  Y : Om → ℝ -- @realizes Y(real observed outcome)
  U : Om → Fin d → ℝ -- @realizes U(noise carrier Fin d → ℝ)
  measurable_X : @Measurable Om _ measurableSpace inferInstance X
  measurable_D : @Measurable Om _ measurableSpace inferInstance D
  measurable_Y0 : @Measurable Om _ measurableSpace inferInstance Y0
  measurable_Y1 : @Measurable Om _ measurableSpace inferInstance Y1
  measurable_Y : @Measurable Om _ measurableSpace inferInstance Y
  measurable_U : @Measurable Om _ measurableSpace inferInstance U
  U_nonnegative : ∀ w i, 0 ≤ U w i -- @realizes U(nonnegative coordinates)
  alpha : ℝ -- @realizes \alpha(real homogeneity exponent)
  beta : ℝ -- @realizes \beta(carrier; positivity in RegularVariation)
  R : ℝ -- @realizes R(deterministic covariate radius)
  L : ℝ -- @realizes L(deterministic Lipschitz constant)
  f : (Fin q → ℝ) → Bool → (Fin d → ℝ) → ℝ -- @realizes f(fixed real conditional mean version)
  g : (Fin q → ℝ) → Bool → (Fin d → ℝ) → ℝ -- @realizes g(asymptotic normalized conditional mean)
  e : ℝ → ℝ -- @realizes e(deterministic error envelope)
  p : (Fin q → ℝ) → ℝ -- @realizes p(population propensity)
  measurable_p : Measurable p -- @realizes p(measurable version)
  p_range : ∀ x, 0 ≤ p x ∧ p x ≤ 1 -- @realizes p(range [0,1])
  propensity_identity : -- @realizes p(conditional treatment probability given X)
    (fun w => p (X w)) =ᵐ[mu]
      (mu[(fun w => if D w then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance])
  S : Measure (Fin d → ℝ) -- @realizes S(spectral measure carrier)
  bRV : ℕ → ℝ -- @realizes b_n(regular-variation normalizing sequence)
  cRV : ℝ -- @realizes c(regular-variation mass constant)

attribute [instance] ExtremeModel.measurableSpace ExtremeModel.probability

/-- [The covariate dimension](hyp:q) and [noise dimension](hyp:d) determine [the observation record type](goal), containing covariates, treatment, outcome, and noise. -/
abbrev Obs (q d : ℕ) := (Fin q → ℝ) × Bool × ℝ × (Fin d → ℝ)
/-- [A population model](hyp:M) and [one population unit](hyp:w) determine [that unit's observed record](goal): covariates, treatment, observed outcome, and noise. -/
def observation (M : ExtremeModel q d) (w : M.Om) : Obs q d :=
  (M.X w, M.D w, M.Y w, M.U w)
/-- [A population model](hyp:M) and [one population unit](hyp:w) determine [the unit's noise radius](goal), measured by the coordinate sum norm. -/
def radius (M : ExtremeModel q d) (w : M.Om) := l1Norm (M.U w)
/-- [A population model](hyp:M) and [one population unit](hyp:w) determine [the unit's noise direction](goal), obtained by scaling noise by its radius. -/
def direction (M : ExtremeModel q d) (w : M.Om) := fun i => M.U w i / radius M w
/-- [A population model](hyp:M) and [threshold $t$](hyp:t) determine [the tail law](goal), the population law conditioned on the noise radius strictly exceeding that threshold.
@realizes t(positive deterministic threshold in consuming signatures) -/
def tailLaw (M : ExtremeModel q d) (t : ℝ) := cond M.mu {w | t < radius M w}
/-- [A population model](hyp:M) and [threshold $t$](hyp:t) determine [the tail probability](goal), the probability that its noise radius exceeds the threshold. -/
def tailProb (M : ExtremeModel q d) (t : ℝ) := (M.mu {w | t < radius M w}).toReal
/-- [A population model](hyp:M) determines [its reciprocal tail index](goal), one divided by the model's tail index.
@realizes \gamma(reciprocal of beta) -/
def gamma (M : ExtremeModel q d) := 1 / M.beta
/-- [A population model](hyp:M) determines [its spectral target](goal), the spectral average of the treatment contrast in the asymptotic conditional mean, averaged over the covariate distribution.
@realizes \eta(spectral integral with population covariate marginal) -/
def etaTarget (M : ExtremeModel q d) :=
  ∫ s, (∫ x, (M.g x true s - M.g x false s) ∂(M.mu.map M.X)) ∂M.S
/-- [A population model](hyp:M) and [threshold $t$](hyp:t) determine [the tail envelope](goal), the largest error-envelope value over radii at least $t$. -/
def eBar (M : ExtremeModel q d) (t : ℝ) := sSup (M.e '' Set.Ici t)
/-- [A population model](hyp:M) and [treatment status $a$](hyp:a) determine [the corresponding potential outcome](goal). -/
def potentialOutcome (M : ExtremeModel q d) (a : Bool) := if a then M.Y1 else M.Y0

/-- [A population model](hyp:M) determines [the covariate information structure](goal), the information generated by its covariates. -/
abbrev sigmaX (M : ExtremeModel q d) := MeasurableSpace.comap M.X inferInstance
/-- [A population model](hyp:M) determines [the covariate-and-noise information structure](goal), the information jointly generated by covariates and noise. -/
abbrev sigmaXU (M : ExtremeModel q d) :=
  MeasurableSpace.comap (fun w => (M.X w, M.U w)) inferInstance
/-- [A population model](hyp:M) determines [the covariate-treatment-noise information structure](goal), the information jointly generated by those three variables. -/
abbrev sigmaXDU (M : ExtremeModel q d) :=
  MeasurableSpace.comap (fun w => (M.X w, M.D w, M.U w)) inferInstance

/-- [A population model](hyp:M), [a sign choice](hyp:negative), and [truncation level $k$](hyp:k) determine [the bounded conditional observed-outcome part](goal), the conditional expectation of the selected nonnegative sign part capped at that level. -/
def conditionalObservedPart (M : ExtremeModel q d) (negative : Bool) (k : ℕ) : M.Om → ℝ :=
  M.mu[(fun w => min (max (if negative then -M.Y w else M.Y w) 0) (k : ℝ)) |
    sigmaXDU M]

/-- [A population model](hyp:M) has [defined conditional observed means](goal) when, almost surely, [the positive observed-outcome truncations converge to a finite real limit](step:1) and [the negative observed-outcome truncations do too](step:2). -/
def ConditionalObservedMeanDefined (M : ExtremeModel q d) : Prop :=
  ∀ᵐ w ∂M.mu,
    (∃ lp : ℝ, Tendsto (fun k => conditionalObservedPart M false k w) atTop (𝓝 lp)) ∧
    (∃ ln : ℝ, Tendsto (fun k => conditionalObservedPart M true k w) atTop (𝓝 ln))

-- @node: def:conditional-mean
/-- [A population model](hyp:M) and [a population unit](hyp:w) determine [the conditional observed mean](goal), the limit of its positive conditional truncations minus the limit of its negative ones. -/
def condMeanY (M : ExtremeModel q d) (w : M.Om) : ℝ :=
  limUnder atTop (fun k => conditionalObservedPart M false k w) -
    limUnder atTop (fun k => conditionalObservedPart M true k w)

-- @node: ass:pin-39
/-- [A population model](hyp:M) has [a conditional-mean version](goal) when [its specified conditional-mean function is measurable](step:1), [its positive and negative conditional parts have finite limits almost surely](step:2), and [that function equals the resulting conditional observed mean almost surely](step:3). -/
def ConditionalMeanVersion (M : ExtremeModel q d) : Prop :=
  Measurable (fun z : (Fin q → ℝ) × Bool × (Fin d → ℝ) => M.f z.1 z.2.1 z.2.2) ∧
  ConditionalObservedMeanDefined M ∧ -- @realizes f(finite conditional positive and negative means)
  (fun w => M.f (M.X w) (M.D w) (M.U w)) =ᵐ[M.mu] condMeanY M -- @realizes f(one measurable version of E[Y|X,D,U])

-- @node: ass:pin-7
/-- [A population model](hyp:M) satisfies [the observed-outcome equality](goal) when its observed outcome equals the potential outcome selected by treatment almost surely. -/
def ObservedOutcomeAeEq (M : ExtremeModel q d) : Prop :=
  M.Y =ᵐ[M.mu] fun w => if M.D w then M.Y1 w else M.Y0 w
-- @node: ass:consistency
/-- [A population model](hyp:M) satisfies [consistency](goal) when its observed outcome equals the potential outcome selected by treatment almost surely. -/
def Consistency (M : ExtremeModel q d) : Prop := ObservedOutcomeAeEq M

-- @node: ass:exogeneity
/-- [A population model](hyp:M) satisfies [exogeneity](goal) when, conditional on covariates, treatment and the pair of potential outcomes have factorizing indicator expectations for every measurable pair of events. -/
def Exogeneity (M : ExtremeModel q d) : Prop :=
  ∀ A : Set (ℝ × ℝ), MeasurableSet A → ∀ B : Set Bool, MeasurableSet B →
    M.mu[(fun w => if (M.Y1 w, M.Y0 w) ∈ A ∧ M.D w ∈ B then (1 : ℝ) else 0) | sigmaX M]
      =ᵐ[M.mu] fun w =>
        M.mu[(fun v => if (M.Y1 v, M.Y0 v) ∈ A then (1 : ℝ) else 0) | sigmaX M] w *
        M.mu[(fun v => if M.D v ∈ B then (1 : ℝ) else 0) | sigmaX M] w

-- @node: ass:pin-33
/-- [A population model](hyp:M) satisfies [noise independence from the covariate-treatment pair](goal) when its noise is independent of covariates and treatment jointly. -/
def NoiseIndepOfPair (M : ExtremeModel q d) : Prop :=
  IndepFun M.U (fun w => (M.X w, M.D w)) M.mu
-- @node: ass:iid-independence
/-- [A population model](hyp:M) has [independent noise](goal) when its noise is independent of covariates and treatment jointly. -/
def NoiseIndependent (M : ExtremeModel q d) : Prop := NoiseIndepOfPair M
-- @node: ass:pin-34
/-- [A population model](hyp:M) has [covariates almost surely in the radius-$R$ ball](goal) when [its radius is positive](step:1) and [its covariate coordinate sum norm is at most that radius almost surely](step:2). -/
def CovariateAeInBall (M : ExtremeModel q d) : Prop :=
  0 < M.R ∧ -- @realizes R(positive fixed bound)
  ∀ᵐ w ∂M.mu, l1Norm (M.X w) ≤ M.R -- @realizes X(almost surely in the l1 ball B_R)
-- @node: ass:f-homo-bounded-x
/-- [A population model](hyp:M) has [bounded covariates](goal) when its covariates lie almost surely in its positive radius-$R$ ball. -/
def CovariateBounded (M : ExtremeModel q d) : Prop := CovariateAeInBall M

-- @node: ass:pin-fix-8cd5c960
/-- [A population model](hyp:M) satisfies [uniform asymptotic homogeneity](goal) when its normalized conditional mean is uniformly within its error envelope of the asymptotic mean over bounded covariates, treatments, and positive unit-sphere directions. -/
def HomogeneityUniform (M : ExtremeModel q d) : Prop :=
  ∀ t, 0 < t → ∀ a : Bool, ∀ x, l1Norm x ≤ M.R →
    ∀ u ∈ positiveSphere l1Norm,
      |M.f x a (fun i => t * u i) / t ^ M.alpha - M.g x a u| ≤ M.e t -- @realizes g(uniform asymptotic mean on B_R × Bool × positive sphere) @realizes f(homogeneity of the same version) @realizes \alpha(normalizing exponent)
-- @node: ass:pin-fix-8ef6fd29
/-- [A population model](hyp:M) satisfies [asymptotic homogeneity on the positive sphere](goal) when its normalized conditional mean converges uniformly to the asymptotic mean there. -/
def HomogeneityOnPositiveSphere (M : ExtremeModel q d) : Prop := HomogeneityUniform M

/-- [A population model](hyp:M) has [a Lipschitz asymptotic mean](goal) when [its Lipschitz constant is nonnegative](step:1) and [its asymptotic mean changes no faster than that constant times the coordinate-sum distance in covariates and directions](step:2). -/
def LipschitzG (M : ExtremeModel q d) : Prop :=
  0 ≤ M.L ∧ -- @realizes L(nonnegative Lipschitz constant)
  ∀ x x', l1Norm x ≤ M.R → l1Norm x' ≤ M.R → ∀ a : Bool,
    ∀ u ∈ positiveSphere l1Norm, ∀ u' ∈ positiveSphere l1Norm,
      |M.g x a u - M.g x' a u'| ≤
        M.L * (l1Norm (x - x') + l1Norm (u - u')) -- @realizes g(L-Lipschitz on B_R × positive l1 sphere for each treatment)
-- @node: ass:pin-43
/-- [A population model](hyp:M) satisfies [the pinned homogeneity conditions](goal) when [its error envelope is nonnegative at positive radii](step:1), [it vanishes at infinity](step:2), [uniform homogeneity holds](step:3), and [the Lipschitz condition holds](step:4). -/
def HomogeneityPinned (M : ExtremeModel q d) : Prop :=
  (∀ t, 0 < t → 0 ≤ M.e t) ∧ -- @realizes e(nonnegative for positive radii)
  Tendsto M.e atTop (𝓝 0) ∧ -- @realizes e(tends to zero at infinity)
  HomogeneityUniform M ∧ LipschitzG M
-- @node: ass:f-homo-asymptotic
/-- [A population model](hyp:M) has [asymptotic homogeneity](goal) when its error envelope vanishes at infinity and its uniform-homogeneity and Lipschitz conditions hold. -/
def AsymptoticHomogeneity (M : ExtremeModel q d) : Prop := HomogeneityPinned M

-- @node: ass:iid-regular-variation
/-- [A population model](hyp:M) has [regularly varying noise](goal) when [its tail index is positive](step:1), [its noise distribution is regularly varying with that index](step:2), and [its stored spectral data form the coordinate-sum-norm certificate](step:3). -/
def NoiseRegularlyVarying (M : ExtremeModel q d) : Prop :=
  0 < M.beta ∧ IsRegularlyVarying (M.mu.map M.U) M.beta ∧
  RegularVariation (M.mu.map M.U) M.beta l1Norm M.S M.bRV M.cRV -- @realizes c(own cRV is the positive mass multiplier in the l1 certificate)
-- @node: ass:prop-id-regular-variation
/-- [A population model](hyp:M) satisfies [the propensity-identification regular-variation condition](goal) when its noise is regularly varying with the model's stored spectral certificate. -/
def PropIdRegularVariation (M : ExtremeModel q d) : Prop := NoiseRegularlyVarying M
-- @node: ass:rate-alpha-less-beta
/-- [A population model](hyp:M) satisfies [the exponent ordering](goal) when its homogeneity exponent is smaller than its tail index. -/
def AlphaLtBeta (M : ExtremeModel q d) : Prop := M.alpha < M.beta

-- @node: ass:pin-fix-f18f3355
/-- [A population model](hyp:M) satisfies [the spectral-integral representation of the target](goal) when its target equals the spectral average of the covariate-averaged difference between the treated and untreated asymptotic means. -/
def EtaTargetIsSpectralIntegral (M : ExtremeModel q d) : Prop :=
  etaTarget M = ∫ s, (∫ x, (M.g x true s - M.g x false s) ∂(M.mu.map M.X)) ∂M.S

/-- For [a population model](hyp:M) and [a tail threshold](hyp:t), [the normalized tail effect at that threshold](goal) is the tail-conditional average potential-outcome contrast divided by the threshold raised to the homogeneity exponent. -/
def neteAt (M : ExtremeModel q d) (t : ℝ) : ℝ :=
  ∫ w, (M.Y1 w - M.Y0 w) / t ^ M.alpha ∂(tailLaw M t)
-- @node: def:nete
/-- For [a population model](hyp:M), [the normalized extreme treatment effect](goal) is the limiting value of its normalized tail effect as the threshold grows.

@realizes \theta^{\tmop{NETE}}(limit of normalized potential-outcome contrast) -/
def thetaNETE (M : ExtremeModel q d) : ℝ := limUnder atTop (neteAt M)

/-- For [a population model](hyp:M) and [a tail threshold](hyp:t), [the angular factor](goal) is the tail-conditional average difference between treated and untreated asymptotic means evaluated at each observation's covariates and noise direction. -/
def angularFactor (M : ExtremeModel q d) (t : ℝ) :=
  ∫ w, (M.g (M.X w) true (direction M w) - M.g (M.X w) false (direction M w))
    ∂(tailLaw M t)
/-- For [a population model](hyp:M) and [a tail threshold](hyp:t), [the radial factor](goal) is the tail-conditional average of the noise radius, raised to the homogeneity exponent and normalized by the threshold raised to that exponent. -/
def radialFactor (M : ExtremeModel q d) (t : ℝ) :=
  ∫ w, radius M w ^ M.alpha / t ^ M.alpha ∂(tailLaw M t)

/-- Given [a population model](hyp:M), [a treatment level](hyp:a), [a choice of whether to retain the negative part](hyp:negative), [a conditioning information set](hyp:G), and [a truncation level](hyp:k), [the truncated conditional potential-outcome part](goal) is the conditional expectation of the corresponding nonnegative potential-outcome part capped at that level. -/
def conditionalPotentialPart (M : ExtremeModel q d) (a negative : Bool)
    (G : MeasurableSpace M.Om) (k : ℕ) : M.Om → ℝ :=
  M.mu[(fun w => min (max (if negative then -potentialOutcome M a w
    else potentialOutcome M a w) 0) (k : ℝ)) | G]

/-- Given [a population model](hyp:M), [a treatment level](hyp:a), and [a conditioning information set](hyp:G), [the conditional potential mean is defined](goal) when almost every observation has [a finite limit for its increasingly truncated positive part](step:1) and [a finite limit for its increasingly truncated negative part](step:2). -/
def ConditionalPotentialMeanDefined (M : ExtremeModel q d) (a : Bool)
    (G : MeasurableSpace M.Om) : Prop :=
  ∀ᵐ w ∂M.mu,
    (∃ lp : ℝ, Tendsto (fun k => conditionalPotentialPart M a false G k w) atTop (𝓝 lp)) ∧
    (∃ ln : ℝ, Tendsto (fun k => conditionalPotentialPart M a true G k w) atTop (𝓝 ln))

/-- Given [a population model](hyp:M), [a treatment level](hyp:a), [a conditioning information set](hyp:G), and [an observation](hyp:w), [the conditional potential mean](goal) is the limiting truncated positive conditional mean minus the limiting truncated negative conditional mean. -/
def conditionalPotentialMean (M : ExtremeModel q d) (a : Bool)
    (G : MeasurableSpace M.Om) (w : M.Om) : ℝ :=
  limUnder atTop (fun k => conditionalPotentialPart M a false G k w) -
    limUnder atTop (fun k => conditionalPotentialPart M a true G k w)

/-- For [a population model](hyp:M), [the identification side conditions](goal) require [propensity scores strictly between zero and one almost surely](step:1), [well-defined and information-invariant conditional potential means for both treatment levels](step:2), and [eventual tail-law integrability of each potential outcome](step:3). -/
def IdentificationSideConditions (M : ExtremeModel q d) : Prop :=
  (∀ᵐ w ∂M.mu, 0 < M.p (M.X w) ∧ M.p (M.X w) < 1) ∧
  (∀ a : Bool,
    ConditionalPotentialMeanDefined M a (sigmaXDU M) ∧
    ConditionalPotentialMeanDefined M a (sigmaXU M) ∧
    conditionalPotentialMean M a (sigmaXDU M) =ᵐ[M.mu]
      conditionalPotentialMean M a (sigmaXU M)) ∧
  ∀ᶠ t in atTop, ∀ a : Bool, Integrable (potentialOutcome M a) (tailLaw M t)

end
end Papers.TbsExtremeEffects
