module
public import Papers.TbsNeuralCausalPi.Setup.Notation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Order.LiminfLimsup
public import Causalean.Stat.Concentration.VC.Basic
/-! # Measure comparison assumptions -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory

-- @node: ass:pin-fix-72c9e86d
/-- For [measures mu and muhat](hyp:mu,muhat), the [probability-measure requirement](goal)
asserts that [mu is a probability measure](step:1) and [muhat is a probability measure](step:2). -/
def MeasuresAreProbability {X : Type*} [MeasurableSpace X]
    (mu muhat : Measure X) : Prop :=
  IsProbabilityMeasure mu ∧ IsProbabilityMeasure muhat
open Filter
open scoped Topology NNReal ENNReal
noncomputable section
-- @env: S4
variable {M : Type*} [MetricSpace M]
-- @node: ass:prop-convg-opt-setting
/-- On [a metric parameter space M](hyp:M), for [stage parameter sets](hyp:Theta), [a limiting set](hyp:ThetaInf), [approximation
tolerances](hyp:eps), [constraint error tolerances](hyp:delta), [slack tolerances](hyp:tau),
[an objective](hyp:f), and [stage constraints](hyp:gn), the [optimization convergence
setting](goal) requires [nested stage sets contained in the limit](step:1), [the limit to
be the closure of their union](step:2), [positive approximation and constraint error
tolerances at every stage](step:3), [approximation tolerances tending to zero](step:4),
[constraint error tolerances tending to zero](step:5), [slack tolerances tending to zero](step:6),
[continuity of the objective on the limit set](step:7), and [continuity of every stage constraint there](step:8). -/
def ConvgOptSetting (Theta : ℕ → Set M) (ThetaInf : Set M)
    (eps delta tau : ℕ → ℝ) (f : M → ℝ) (gn : ℕ → M → ℝ) : Prop :=
  (∀ n, Theta n ⊆ Theta (n+1) ∧ Theta (n+1) ⊆ ThetaInf) ∧
  ThetaInf = closure (⋃ n, Theta n) ∧
  (∀ n, 0 < eps n ∧ 0 < delta n) ∧
  Tendsto eps atTop (𝓝 0) ∧ Tendsto delta atTop (𝓝 0) ∧ Tendsto tau atTop (𝓝 0) ∧
  ContinuousOn f ThetaInf ∧ ∀ n, ContinuousOn (gn n) ThetaInf
-- @node: ass:prop-convg-opt-compact
/-- On [a metric parameter space M](hyp:M), for [the limiting parameter set](hyp:ThetaInf), the [limit compactness requirement](goal)
asserts that this set is compact. -/
def ThetaInfCompact (ThetaInf : Set M) : Prop := IsCompact ThetaInf
-- @node: ass:prop-convg-opt-approximate-lipschitz
/-- On [a metric parameter space M](hyp:M), for [a limiting parameter set](hyp:ThetaInf), [stage constraints](hyp:gn),
[a nonnegative Lipschitz constant](hyp:Lg), and [stage slack tolerances](hyp:tau),
the [approximate Lipschitz requirement](goal) bounds the absolute difference of each constraint
at any two points of the limit set by the constant times their distance plus that stage's slack. -/
def ApproxLipschitzConstraints (ThetaInf : Set M) (gn : ℕ → M → ℝ)
    (Lg : ℝ≥0) (tau : ℕ → ℝ) : Prop :=
  ∀ n, ∀ a ∈ ThetaInf, ∀ b ∈ ThetaInf,
    |gn n a - gn n b| ≤ Lg * dist a b + tau n
-- @node: ass:prop-convg-opt-uniform-error
/-- On [a metric parameter space M](hyp:M), for [a limiting parameter set](hyp:ThetaInf), [stage constraints](hyp:gn),
[a limiting constraint](hyp:g), and [error tolerances](hyp:delta), the [uniform constraint
error requirement](goal) asserts [strict positivity of every tolerance](step:1) and
[a uniform absolute error bounded by that tolerance, together with nonnegative stage
constraints, throughout the limit set](step:2). -/
def UniformConstraintError (ThetaInf : Set M) (gn : ℕ → M → ℝ) -- @realizes \delta_n(uniform error bound between each constraint and the one limiting constraint)
    (g : M → ℝ) (delta : ℕ → ℝ) : Prop :=
  (∀ n, 0 < delta n) ∧ -- @realizes \delta_n(strictly positive at every index, including for an empty parameter set)
    ∀ n, ∀ a ∈ ThetaInf, |gn n a - g a| ≤ delta n ∧ 0 ≤ gn n a
/-- On [a metric parameter space M](hyp:M), for [stage parameter sets](hyp:Theta), [a limiting set](hyp:ThetaInf), [a candidate
subset](hyp:tildeTheta), and [approximation tolerances](hyp:eps), the [compact subset
approximation requirement](goal) asserts [compactness of the candidate](step:1),
[its inclusion in the limit set](step:2), and [approximation of each candidate point by a
point in every stage set within that stage's tolerance](step:3). -/
def CompactSubsetApproximableAt (Theta : ℕ → Set M) (ThetaInf tildeTheta : Set M)
    (eps : ℕ → ℝ) : Prop :=
  IsCompact tildeTheta ∧ tildeTheta ⊆ ThetaInf ∧
    ∀ n, ∀ a ∈ tildeTheta, ∃ b ∈ Theta n, dist b a ≤ eps n
-- @node: ass:prop-convg-opt-approximation
/-- On [a metric parameter space M](hyp:M), for [stage parameter sets](hyp:Theta), [a limiting set](hyp:ThetaInf), and [approximation
tolerances](hyp:eps), the [compact approximation requirement](goal) asserts that some
compact subset of the limit set has every point approximable from every stage set
within the corresponding tolerance. -/
def CompactSubsetApproximable (Theta : ℕ → Set M) (ThetaInf : Set M)
    (eps : ℕ → ℝ) : Prop :=
  ∃ tildeTheta : Set M, CompactSubsetApproximableAt Theta ThetaInf tildeTheta eps
-- @node: ass:prop-convg-opt-nonempty
/-- On [a metric parameter space M](hyp:M), for [a limiting parameter set](hyp:ThetaInf), [a candidate subset](hyp:tildeTheta), and
[a limiting constraint](hyp:g), the [feasibility requirement](goal) asserts [a zero of the
constraint in the limit set](step:1) and [a zero in the candidate subset](step:2). -/
def LimitFeasibleNonempty (ThetaInf tildeTheta : Set M) (g : M → ℝ) : Prop :=
  {a ∈ ThetaInf | g a = 0}.Nonempty ∧ {a ∈ tildeTheta | g a = 0}.Nonempty
-- @node: ass:bk-6
/-- On [a metric parameter space M](hyp:M), for [stage parameter sets](hyp:Theta), [stage constraints](hyp:gn), [a nonnegative
Lipschitz constant](hyp:Lg), [approximation tolerances](hyp:eps), [constraint error
tolerances](hyp:delta), and [an objective](hyp:f), the [finite attainment requirement](goal)
asserts that at every stage the objective has a minimizer among stage parameters whose
constraint is at most the Lipschitz constant times the approximation tolerance plus the
constraint error tolerance. -/
def FiniteProblemsAttained (Theta : ℕ → Set M) (gn : ℕ → M → ℝ)
    (Lg : ℝ≥0) (eps delta : ℕ → ℝ) (f : M → ℝ) : Prop :=
  ∀ n, ∃ a ∈ {a ∈ Theta n | gn n a ≤ Lg * eps n + delta n},
    IsMinOn f {a ∈ Theta n | gn n a ≤ Lg * eps n + delta n} a

-- @node: ass:lemma-combin-err-weights
/-- For [component weights p](hyp:p), the [mixture weight requirement](goal) asserts that
the weights are nonnegative and sum to one. -/
def MixtureWeights {n : ℕ} (p : Fin n → ℝ) : Prop := p ∈ probabilitySimplex n
-- @node: ass:bk-1
/-- For [two families of component measures](hyp:mu,muhat), the [finite first moment
requirement](goal) asserts that the vector norm is integrable under every component
measure in both families. -/
def ComponentsFiniteFirstMoment {n d : ℕ} (mu muhat : Fin n → Measure (L1Vec d)) : Prop :=
  ∀ k, Integrable (fun x => ‖x‖) (mu k) ∧ Integrable (fun x => ‖x‖) (muhat k)
-- @node: ass:pin-75
/-- For [two families of component measures](hyp:mu,muhat), the [component probability
requirement](goal) asserts that every measure in both families is a probability measure. -/
def MixtureComponentsProbability {n d : ℕ} (mu muhat : Fin n → Measure (L1Vec d)) : Prop :=
  ∀ k, IsProbabilityMeasure (mu k) ∧ IsProbabilityMeasure (muhat k)
-- @node: ass:lemma-gumbel-err-parameters
/-- For [weights p](hyp:p) and [temperature tau](hyp:tau), the [softmax parameter
requirement](goal) asserts [positive temperature](step:1), [temperature below one](step:2),
and [strictly positive weights for every component](step:3). -/
def SoftmaxParameters {n : ℕ} (p : Fin n → ℝ) (tau : ℝ) : Prop :=
  0 < tau ∧ tau < 1 ∧ ∀ k, 0 < p k
-- @node: ass:lemma-lip-condition-bounded
/-- For [regression functions f and fhat](hyp:f,fhat) and [a bound K](hyp:K), the
[regression boundedness requirement](goal) asserts that both functions have absolute
value at most K on the interval from negative K to K. -/
def RegressionBounded (f fhat : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (-K) K, |f t| ≤ K ∧ |fhat t| ≤ K

/-- For [regression functions f and fhat](hyp:f,fhat) and [a bound K](hyp:K), the
[global regression boundedness requirement](goal) asserts that both functions have
absolute value at most K at every real argument. -/
def RegressionGloballyBounded (f fhat : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ t, |f t| ≤ K ∧ |fhat t| ≤ K
-- @node: ass:bk-owner-3
/-- For [joint treatment-outcome measures mu and nu](hyp:mu,nu) and [a box radius K](hyp:K),
the [box support requirement](goal) asserts that [mu gives mass one to the box](step:1)
and [nu gives mass one to the box](step:2). -/
def RegressionLawsSupportedInBox (mu nu : Measure (L1Vec 2)) (K : ℝ) : Prop :=
  mu (boundedCube 2 K) = 1 ∧ nu (boundedCube 2 K) = 1
-- @node: ass:lemma-lip-condition-regression
/-- For [joint treatment-outcome measures mu and nu](hyp:mu,nu), [regression functions
f and fhat](hyp:f,fhat), [a nonnegative Lipschitz constant L](hyp:L), and [a box radius K](hyp:K),
the [Lipschitz regression version requirement](goal) asserts [that f is L-Lipschitz on
the interval from negative K to K](step:1), [that fhat is L-Lipschitz there](step:2),
[that f of treatment equals the conditional mean of outcome given treatment almost
everywhere under nu](step:3), and [that fhat gives that conditional mean almost everywhere under mu](step:4). -/
def LipschitzRegressionVersions (mu nu : Measure (L1Vec 2)) -- @realizes \hat{T}(chosen regression functions for the two laws of the scalar treatment-outcome pair) -- @realizes \hat{Y}(chosen regression functions for the two laws of the scalar treatment-outcome pair)
    (f fhat : ℝ → ℝ) (L : ℝ≥0) (K : ℝ) : Prop :=
  LipschitzOnWith L f (Set.Icc (-K) K) ∧
  LipschitzOnWith L fhat (Set.Icc (-K) K) ∧
  (fun x => f (x.ofLp 0)) =ᵐ[nu]
    nu[fun x => x.ofLp 1 | MeasurableSpace.comap (fun x : L1Vec 2 => x.ofLp 0) inferInstance] ∧
  (fun x => fhat (x.ofLp 0)) =ᵐ[mu]
    mu[fun x => x.ofLp 1 | MeasurableSpace.comap (fun x : L1Vec 2 => x.ofLp 0) inferInstance]

/-- For [joint treatment-outcome measures mu and nu](hyp:mu,nu), [regression functions
f and fhat](hyp:f,fhat), and [a nonnegative Lipschitz constant L](hyp:L), the [global
regression version requirement](goal) asserts [global L-Lipschitz continuity of f](step:1),
[global L-Lipschitz continuity of fhat](step:2), [measurability of f](step:3),
[measurability of fhat](step:4), [that f of treatment equals the conditional mean of
outcome given treatment almost everywhere under nu](step:5), and [that fhat gives
that conditional mean almost everywhere under mu](step:6). -/
def LipschitzRegressionVersionsGlobal (mu nu : Measure (L1Vec 2)) -- @realizes \hat{T}(chosen regression functions for the two laws of the scalar treatment-outcome pair) -- @realizes \hat{Y}(chosen regression functions for the two laws of the scalar treatment-outcome pair)
    (f fhat : ℝ → ℝ) (L : ℝ≥0) : Prop :=
  LipschitzWith L f ∧ LipschitzWith L fhat ∧ Measurable f ∧ Measurable fhat ∧
  (fun x => f (x.ofLp 0)) =ᵐ[nu]
    nu[fun x => x.ofLp 1 | MeasurableSpace.comap (fun x : L1Vec 2 => x.ofLp 0) inferInstance] ∧
  (fun x => fhat (x.ofLp 0)) =ᵐ[mu]
    mu[fun x => x.ofLp 1 | MeasurableSpace.comap (fun x : L1Vec 2 => x.ofLp 0) inferInstance]
-- @node: ass:lemma-sup-wasserstein-pseudodimension
/-- For [a class of vector-valued functions](hyp:F) and [a real dimension bound](hyp:dF),
the [coordinate pseudodimension requirement](goal) asserts [that the bound is nonnegative](step:1)
and [that every coordinate function class has pseudodimension at most some natural
number strictly smaller than that bound](step:2). -/
def CoordinatePseudoDimBound {X : Type*} {d : ℕ} (F : Set (X → L1Vec d)) -- @realizes d_{\mathcal{F}}(strict coordinatewise pseudo-dimension bound)
    (dF : ℝ) : Prop :=
  0 ≤ dF ∧ -- @realizes d_{\mathcal{F}}(finite nonnegative real bound, also in zero output dimension)
    ∀ j : Fin d, ∃ k : ℕ, (k : ℝ) < dF ∧
    Causalean.Stat.Concentration.HasPseudoDimAtMost (fun f : F => fun x => (f.val x).ofLp j) k
-- @node: ass:lemma-sup-wasserstein-bounded
/-- For [a class of vector-valued functions](hyp:F) and [an output bound K](hyp:K), the
[uniform boundedness requirement](goal) asserts [that K is positive](step:1) and [that
every function in the class has coordinate supremum norm at most K at every input](step:2). -/
def ClassUniformlyBounded {X : Type*} {d : ℕ} (F : Set (X → L1Vec d)) (K : ℝ) : Prop := -- @realizes K(positive deterministic coordinate sup-norm output bound)
  0 < K ∧ ∀ f ∈ F, ∀ x, ‖(f x).ofLp‖ ≤ K
end
end Papers.TbsNeuralCausalPi
