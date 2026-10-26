module
public import Causalean.Mathlib.Probability.Certified.FiniteKernel
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.Data.PNat.Notation
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! # Finite-chain cotype, weighted cubes, and the disclosed extension gate

Positive integers are represented by natural numbers with explicit positivity guards.
Sequence coordinates and finite states are relabelled starting at zero.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory Filter

namespace Papers.OaiMetricMarkovCotype

universe u v

-- @env: S1
variable {X : Type u} [MetricSpace X] -- @realizes X(metric carrier) @realizes d(metric distance)

-- @node: def:real-ell-one
/-- [The real sequence space ℓ₁](goal) consists of absolutely summable real sequences,
with norm equal to the sum of their absolute values.
@realizes \ell_1(real lp exponent one)
@realizes \ell_1(\R)(real lp exponent one)
@realizes \|\cdot\|_1(inherited lp norm at exponent one)
@realizes \R(real scalar field) -/
abbrev RealEllOne := lp (fun _ : ℕ => ℝ) 1

/-- [The complex sequence space ℓ₁](goal) consists of absolutely summable complex
sequences, with norm equal to the sum of their moduli.
@realizes \ell_1(\mathbb C)(complex lp exponent one)
@realizes \|\cdot\|_1(inherited complex lp norm, the sum of coordinate moduli) -/
abbrev ComplexEllOne := lp (fun _ : ℕ => ℂ) 1

-- @node: def:index-sets
/-- For [a positive number of states n](hyp:n), [the state set](goal) consists of
the integers from zero through n minus one.
@realizes [n](Fin n relabelling of the finite state set)
@realizes \N(positive natural carrier for the state count)
@realizes n(positive state count) -/
abbrev StateSet (n : ℕ+) := Fin (n : ℕ)

/-- [The admissible sequence exponents](goal) are real numbers that are
[strictly greater than one](step:1) and [at most two](step:2). -/
abbrev SequenceExponent := {p : ℝ //
  1 < p ∧ -- @realizes p(sequence-space exponent strictly greater than one)
  p ≤ 2} -- @realizes p(sequence-space exponent at most two)

/-- For [a real vector π on a finite state set](hyp:π), [being a probability
vector](goal) means that its entries are nonnegative and sum to one.
@realizes \pi(nonnegative entries and sum one; zero masses allowed) -/
abbrev IsProbabilityVector {n : ℕ} (π : Fin n → ℝ) : Prop :=
  Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsProbabilityVector π

-- @node: ass:stochastic-nonnegative
/-- For [a real transition matrix A](hyp:A), [entrywise nonnegativity](goal)
means that every transition entry is nonnegative. -/
def StochasticNonnegative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, 0 ≤ A i j -- @realizes a_{ij}(nonnegative transition entries)

-- @node: ass:stochastic-row-sums
/-- For [a real transition matrix A](hyp:A), [the unit row-sum condition](goal)
requires the entries in each row to sum to one. -/
def StochasticRowSums {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, ∑ j, A i j = 1 -- @realizes A(row sums one, together with entry nonnegativity)

-- @node: ass:detailed-balance
/-- For [state weights π](hyp:π) and [a transition matrix A](hyp:A),
[detailed balance](goal) means that the weight of a transition from any state
to another equals the weight of the reverse transition. -/
def DetailedBalance {n : ℕ} (π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, π i * A i j = π j * A j i

-- @node: def:stochastic-matrix
/-- [A real transition matrix A](hyp:A) [is stochastic](goal) when
[all its entries are nonnegative](step:1) and [each row sums to one](step:2). -/
structure IsStochastic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop where
  nonneg : StochasticNonnegative A -- @realizes A(nonnegative) @realizes a_{ij}(≥0)
  row_sums : StochasticRowSums A -- @realizes A(row sums one) @realizes a_{ij}(≤1)

-- @node: def:reversibility
/-- [A transition matrix A](hyp:A) [is reversible](goal) with respect to
[state weights π](hyp:π) when [the weighted transition flow between every
pair of states is the same in both directions](step:1). -/
structure IsReversible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) : Prop where
  detailed_balance : DetailedBalance π A

-- @node: isStochastic_iff_isStochasticMatrix
/-- [A real transition matrix A](hyp:A) [is stochastic in this formulation
if and only if it is stochastic in the finite-kernel formulation](goal). -/
lemma isStochastic_iff_isStochasticMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsStochastic A ↔
      Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsStochasticMatrix A :=
  by
    constructor
    · intro h
      exact ⟨h.nonneg, h.row_sums⟩
    · rintro ⟨h_nonneg, h_rows⟩
      exact ⟨h_nonneg, h_rows⟩

-- @node: ass:cotype-condition
/-- For [a metric space X](hyp:X) and [a real constant C](hyp:C),
[the metric Markov cotype two condition](goal) requires the following for every
positive finite state count, positive integer time, probability vector, stochastic
matrix reversible with respect to that vector, and collection of points in X:
there are modified points whose probability-weighted squared displacement plus
time times their one-step weighted squared-distance energy is at most C squared
times the original points' weighted squared-distance energy averaged over
transition times from one through the chosen time. -/
def MetricMarkovCotypeCondition (X : Type u) [MetricSpace X] (C : ℝ) : Prop :=
  ∀ (n t : ℕ), 0 < n → 0 < t → -- @realizes n(positive number of states) @realizes t(positive time)
    ∀ (π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ),
      IsProbabilityVector π → IsStochastic A → IsReversible A π →
      ∀ x : Fin n → X, -- @realizes x_i(input points in the metric space)
      ∃ y : Fin n → X, -- @realizes y_i(modified points in the same space)
        (∑ i, π i * dist (x i) (y i) ^ 2) +
          (t : ℝ) * ∑ i, ∑ j, π i * A i j * dist (y i) (y j) ^ 2 ≤
        C ^ 2 * ∑ i, ∑ j, π i *
          (((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, A ^ s) i j) *
            dist (x i) (x j) ^ 2

-- @node: def:cotype
/-- [A metric space X](hyp:X) [has metric Markov cotype two with constant](goal)
[C](hyp:C) when [its finite reversible-chain tests satisfy the metric Markov
cotype two inequality with that constant](step:1). -/
structure HasMetricMarkovCotypeTwo (X : Type u) [MetricSpace X] (C : ℝ) : Prop where
  cotype_condition : MetricMarkovCotypeCondition X C

-- @node: def:cotype-constant
/-- For [a metric space X](hyp:X), [its metric Markov cotype two constant](goal)
is the infimum of all positive real constants satisfying the cotype condition,
with value infinity if no such constant exists.
@realizes N_2(X)(extended infimum of all positive admissible constants) -/
def metricMarkovCotypeConstant (X : Type u) [MetricSpace X] : ℝ≥0∞ :=
  ⨅ (C : ℝ) (_ : 0 < C) (_ : HasMetricMarkovCotypeTwo X C), ENNReal.ofReal C

-- @env: S2
variable {𝓑 : Type v} [Fintype 𝓑] -- @realizes \mathcal B(finite coordinate carrier)

-- @node: ass:flat-finite-cuts
/-- For [a finite coordinate index set 𝓑](hyp:𝓑), [the finite-cut index
condition](goal) requires that the set contain at least one coordinate. -/
def FiniteCutIndex (𝓑 : Type v) [Fintype 𝓑] : Prop :=
  Nonempty 𝓑 -- @realizes \mathcal B(nonempty coordinate index set)

-- @node: ass:flat-positive-weights
/-- On [the finite coordinate set 𝓑](hyp:𝓑), [weights w](hyp:w)
[are strictly positive](goal) when every coordinate weight is greater than zero.
@realizes \|\cdot\|_{1,w}(positive-weight domain of the weighted norm)
@realizes R(positive-weight domain of the quartic remainder) -/
def PositiveWeights (w : 𝓑 → ℝ) : Prop :=
  ∀ B, 0 < w B -- @realizes w_B(strictly positive coordinate weights) @realizes B(coordinate index)

-- @node: def:weighted-norms
/-- On [the finite coordinate set 𝓑](hyp:𝓑), for [weights w](hyp:w) and
[a real vector u](hyp:u), [the weighted ℓ₁ expression](goal) is the sum of
each coordinate's weight times its absolute value.
@realizes \|\cdot\|_{1,w}(weighted sum of absolute values)
@realizes u(real coordinate vector) -/
def weightedL1Norm (w u : 𝓑 → ℝ) : ℝ := ∑ B, w B * |u B|

/-- On [the finite coordinate set 𝓑](hyp:𝓑), for [weights w](hyp:w) and
[a real vector u](hyp:u), [the weighted squared Hilbert expression](goal)
is the sum of each coordinate's weight times its squared value.
@realizes \|\cdot\|_H(squared weighted Hilbert norm) -/
def weightedHNormSq (w u : 𝓑 → ℝ) : ℝ := ∑ B, w B * u B ^ 2

-- @node: def:weighted-space
/-- On [the finite coordinate set 𝓑](hyp:𝓑), for [weights w](hyp:w) and
[a real vector u](hyp:u), [the weighted Hilbert norm expression](goal) is
the real square root of the weighted sum of squared coordinates.
@realizes H(real coordinate space equipped with the explicit weighted norm)
@realizes \|\cdot\|_H(square root of the weighted sum of squares) -/
def weightedHNorm (w u : 𝓑 → ℝ) : ℝ := Real.sqrt (weightedHNormSq w u)

-- @node: def:cube-inner-product
/-- On [the finite coordinate set 𝓑](hyp:𝓑), for [weights w](hyp:w) and
[real vectors u](hyp:u) and [u′](hyp:u'), [the weighted inner product
expression](goal) is the sum of the coordinatewise products times their weights.
@realizes \langle\cdot,\cdot\rangle_H(weighted real inner product as its finite sum) -/
def weightedInner (w u u' : 𝓑 → ℝ) : ℝ := ∑ B, w B * u B * u' B

/-- For [a coordinate index set 𝓑](hyp:𝓑), [the unit cube](goal) is the set
of real vectors whose coordinates all lie between zero and one, inclusive.
@realizes Q(product of closed unit intervals) -/
def unitCube (𝓑 : Type v) : Set (𝓑 → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 1)

-- @node: wInner_real_eq_sum
/-- For [weights w](hyp:w) and [real vectors u](hyp:u) and [u′](hyp:u'),
[their weighted inner product equals the sum over coordinates of the weight
times the two coordinate values](goal). -/
lemma wInner_real_eq_sum (w u u' : 𝓑 → ℝ) :
    weightedInner w u u' = ∑ B, w B * u B * u' B := by
  rfl

-- @node: ass:flat-arguments
/-- On [the coordinate set 𝓑](hyp:𝓑), [vectors u](hyp:u) and [u′](hyp:u')
[are cube arguments](goal) when [every coordinate of u lies between zero and
one, inclusive](step:1), and [the same holds for u′](step:2). -/
def CubeArguments (u u' : 𝓑 → ℝ) : Prop :=
  u ∈ unitCube 𝓑 ∧ -- @realizes u(coordinates in [0,1])
  u' ∈ unitCube 𝓑 -- @realizes u'(coordinates in [0,1])

-- @node: ass:flat-center
/-- On [the coordinate set 𝓑](hyp:𝓑), [a real vector e](hyp:e)
[is binary](goal) when each coordinate equals either zero or one. -/
def BinaryVector (e : 𝓑 → ℝ) : Prop :=
  ∀ B, e B = 0 ∨ e B = 1 -- @realizes e(binary coordinate vector)

/-- At [a real argument r](hyp:r), [the cubic smoothing polynomial](goal)
equals three times r squared minus two times r cubed.
@realizes \phi(polynomial formula on the domain CubicSmoothDomain) -/
def cubicSmooth (r : ℝ) : ℝ := 3 * r ^ 2 - 2 * r ^ 3

/-- [A real argument r](hyp:r) [is in the cubic smoothing domain](goal)
when it lies between zero and one, inclusive. -/
def CubicSmoothDomain (r : ℝ) : Prop :=
  r ∈ Set.Icc (0 : ℝ) 1 -- @realizes \phi(argument in the closed unit interval)

-- @node: cubicSmooth_mem_unitInterval
/-- If [r lies between zero and one, inclusive](hyp:hr), then
[its cubic smoothing also lies between zero and one, inclusive](goal). -/
lemma cubicSmooth_mem_unitInterval {r : ℝ} (hr : CubicSmoothDomain r) :
    cubicSmooth r ∈ Set.Icc (0 : ℝ) 1 := by -- @realizes \phi(values in the closed unit interval)
  obtain ⟨hr0, hr1⟩ := hr
  constructor
  · calc
      0 ≤ r ^ 2 * (3 - 2 * r) :=
        mul_nonneg (sq_nonneg r) (by linarith)
      _ = cubicSmooth r := by unfold cubicSmooth; ring
  · have hcomplement : 0 ≤ (1 - r) ^ 2 * (1 + 2 * r) :=
      mul_nonneg (sq_nonneg (1 - r)) (by linarith)
    have hidentity : (1 - r) ^ 2 * (1 + 2 * r) = 1 - cubicSmooth r := by
      unfold cubicSmooth
      ring
    rw [hidentity] at hcomplement
    linarith

-- @node: def:cubic
/-- On [the coordinate set 𝓑](hyp:𝓑), [the cubic map](goal) sends
[a real vector u](hyp:u) to the vector obtained by applying the cubic smoothing
polynomial to each coordinate.
@realizes \Phi(coordinatewise cubic smoothing) -/
def cubicMap (u : 𝓑 → ℝ) : 𝓑 → ℝ := fun B => cubicSmooth (u B)

-- @node: def:flat-potential
/-- On [the finite coordinate set 𝓑](hyp:𝓑), for [weights w](hyp:w),
[a center e](hyp:e), and [a vector u](hyp:u), [the quartic potential](goal)
is the square of the weighted sum of squared coordinate displacements from e.
@realizes F_e(fourth power of the weighted displacement norm)
@realizes a(displacement u minus e) -/
def quarticPotential (w e u : 𝓑 → ℝ) : ℝ := (weightedHNormSq w (u - e)) ^ 2

/-- On [the coordinate set 𝓑](hyp:𝓑), [the displacement](goal) of
[a vector u](hyp:u) from [a center e](hyp:e) is their coordinatewise difference,
u minus e.
@realizes a(displacement u minus the binary center e) -/
def flatDisplacement (u e : 𝓑 → ℝ) : 𝓑 → ℝ := u - e

/-- On [the coordinate set 𝓑](hyp:𝓑), [the increment](goal) from
[a vector u](hyp:u) to [a vector u′](hyp:u') is u′ minus u coordinatewise.
@realizes \delta(increment u prime minus u) -/
def flatIncrement (u u' : 𝓑 → ℝ) : 𝓑 → ℝ := u' - u

/-- On [the finite coordinate set 𝓑](hyp:𝓑), for [weights w](hyp:w),
[a center e](hyp:e), [an initial vector u](hyp:u), and [a final vector u′](hyp:u'),
[the quartic remainder](goal) is the change in quartic potential minus four
times the initial weighted squared displacement times the weighted inner product
of that displacement with the increment.
@realizes R(quartic remainder after subtracting the linear term) -/
def flatRemainder (w e u u' : 𝓑 → ℝ) : ℝ :=
  quarticPotential w e u' - quarticPotential w e u -
    4 * weightedHNormSq w (u - e) * weightedInner w (u - e) (u' - u)

/-- [A natural-number time t](hyp:t) [belongs to the geometric parameter
domain](goal) when it is strictly positive.
@realizes \N(positive natural time domain)
@realizes t(positive time for the geometric parameters)
@realizes p(positive time restricts the killing probability to (0,1/2])
@realizes q(positive time restricts the survival probability to (0,1)) -/
def GeometricParameterDomain (t : ℕ) : Prop :=
  0 < t

-- @node: def:geometric-parameters
/-- For [a natural-number time t](hyp:t) [that is strictly positive](hyp:_h_time),
[the geometric killing probability](goal) is one divided by t plus one.
@realizes p(killing probability 1 divided by t plus one, for positive time) -/
def geomKillProb (t : ℕ) (_h_time : GeometricParameterDomain t) : ℝ :=
  1 / ((t : ℝ) + 1)

/-- For [a natural-number time t](hyp:t) [that is strictly positive](hyp:h_time),
[the geometric survival probability](goal) is one minus the killing probability,
or equivalently t divided by t plus one.
@realizes q(survival probability one minus the killing probability, for positive time) -/
def geomSurvProb (t : ℕ) (h_time : GeometricParameterDomain t) : ℝ :=
  1 - geomKillProb t h_time

-- @env: S3
variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- On [the outcome space Ω](hyp:Ω) with [its measurable structure](hyp:mΩ), under [a probability measure
μ](hyp:μ), [the probability](goal) of [an event s](hyp:s) is its real-valued
measure, recorded together with its bounds of zero and one.
@realizes \Prob(event probability in the closed unit interval) -/
def eventProbability (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨μ.real s, measureReal_nonneg, measureReal_le_one⟩

/-- On [the outcome space Ω](hyp:Ω) with [its measurable structure](hyp:mΩ), under [a probability measure
μ](hyp:μ), [the expectation](goal) of [an integrable real or Banach-valued
random variable f](hyp:f) is its Bochner integral.
@realizes \E(Bochner expectation on arbitrary real or Banach-valued L1 arguments) -/
def expectation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω →₁[μ] V) : V :=
  L1.integral f

/-- On [the outcome space Ω](hyp:Ω) with [its measurable structure](hyp:mΩ), under [a probability measure
μ](hyp:μ), [the nonnegative expectation](goal) of [an extended nonnegative
function f](hyp:f) is its nonnegative integral, which may be infinite.
@realizes \E(extended nonnegative expectation on nonnegative scalar arguments) -/
def nonnegativeExpectation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ ω, f ω ∂μ

-- @node: ass:martingale-process
/-- On [the outcome space Ω](hyp:Ω) with [its measurable structure](hyp:mΩ)
and [finite coordinate set 𝓑](hyp:𝓑), for [a measure μ](hyp:μ),
[a filtration 𝓕](hyp:𝓕), [a vector-valued process M](hyp:M), and
[a terminal random vector](hyp:Minf), [the cube martingale condition](goal)
requires that [M be a martingale for this filtration and measure](step:1),
[every value of M lie in the unit cube](step:2), [M converge to the terminal
vector almost surely](step:3), and [the terminal vector lie in the cube almost
surely](step:4). -/
def CubeMartingale (μ : Measure Ω) (𝓕 : Filtration ℕ mΩ)
    (M : ℕ → Ω → 𝓑 → ℝ) (Minf : Ω → 𝓑 → ℝ) : Prop :=
  Martingale M 𝓕 μ ∧ -- @realizes M_m(H-valued martingale for the given filtration)
  (∀ m ω, M m ω ∈ unitCube 𝓑) ∧ -- @realizes M_m(cube-valued process)
  (∀ᵐ ω ∂μ, Tendsto (fun m => M m ω) atTop (𝓝 (Minf ω))) ∧ -- @realizes M_\infty(almost sure limit)
  (∀ᵐ ω ∂μ, Minf ω ∈ unitCube 𝓑) -- @realizes M_\infty(terminal values in the cube almost surely)

-- @node: ass:martingale-center
/-- On [the outcome space Ω](hyp:Ω) with [its measurable structure](hyp:mΩ)
and [coordinate set 𝓑](hyp:𝓑), for [a filtration 𝓕](hyp:𝓕) and
[a random vector e](hyp:e), [the initial binary center condition](goal)
requires that [e be strongly measurable with respect to the initial information
in the filtration](step:1) and [every coordinate of e equal zero or one at every
outcome](step:2). -/
def InitialBinaryCenter (𝓕 : Filtration ℕ mΩ) (e : Ω → 𝓑 → ℝ) : Prop :=
  StronglyMeasurable[𝓕 0] e ∧ -- @realizes \calF_m(initial sigma algebra for the random center)
  ∀ ω, BinaryVector (e ω) -- @realizes e(random binary center)

-- @node: def:lipschitz-constant
/-- For [a map f between spaces with distances](hyp:f), [its extended Lipschitz
constant](goal) is the infimum of all nonnegative, possibly infinite bounds L
such that the distance between any two images is at most L times the distance
between their original points; the infimum of an empty set is infinity.
@realizes \Lip(extended infimum; the infimum of the empty set is infinity) -/
def lipConst {α : Type u} {β : Type v} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : α → β) : ℝ≥0∞ :=
  sInf {L : ℝ≥0∞ | ∀ x y, edist (f x) (f y) ≤ L * edist x y}

-- @node: ass:pin-2
/-- For [a map f between spaces with distances](hyp:f), [the Lipschitz constant
reading condition](goal) says that its extended Lipschitz constant equals the
infimum of all nonnegative, possibly infinite distance expansion bounds. -/
def LipConstReading {α : Type u} {β : Type v} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : α → β) : Prop :=
  lipConst f = sInf {L : ℝ≥0∞ | ∀ x y, edist (f x) (f y) ≤ L * edist x y}

-- @node: lipConst_le_iff
/-- For [a map f between spaces with distances](hyp:f) and [a finite nonnegative
bound K](hyp:K), [the extended Lipschitz constant of f is at most K if and only
if every pair of images has distance at most K times the distance between the
original points](goal). -/
lemma lipConst_le_iff {α : Type u} {β : Type v} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : α → β) (K : NNReal) : lipConst f ≤ K ↔ LipschitzWith K f := by
  let constants : Set ℝ≥0∞ := {L | ∀ x y, edist (f x) (f y) ≤ L * edist x y}
  constructor
  · intro h
    have h_nonempty : constants.Nonempty := by
      by_contra h_empty
      have h_top : lipConst f = ⊤ := by
        change sInf constants = ⊤
        rw [Set.not_nonempty_iff_eq_empty.mp h_empty, sInf_empty]
      exact ENNReal.coe_ne_top (top_le_iff.mp (h_top ▸ h))
    let : Nonempty constants := h_nonempty.to_subtype
    intro x y
    have h_inf : edist (f x) (f y) ≤ lipConst f * edist x y := by
      change edist (f x) (f y) ≤ sInf constants * edist x y
      rw [sInf_eq_iInf', ENNReal.iInf_mul (fun h_top => (edist_ne_top x y h_top).elim)]
      exact le_iInf fun L => L.property x y
    exact h_inf.trans (mul_le_mul' h le_rfl)
  · intro h
    exact sInf_le h

-- @node: ass:markov-type-condition
/-- For [a metric space Z](hyp:Z) and [a real constant M](hyp:M), [the Markov
type two inequality](goal) requires that, for every finite reversible Markov
chain with a probability distribution satisfying detailed balance and every
assignment of its states to points of Z, the expected squared distance traveled
in any positive number t of steps is at most M squared times t times the expected
squared distance traveled in one step, starting with that distribution. -/
def MarkovTypeTwoCondition (Z : Type u) [MetricSpace Z] (M : ℝ) : Prop :=
  -- @realizes Z(metric source of the Markov type tests) @realizes d_Z(its metric distance)
  ∀ (n t : ℕ), 0 < n → 0 < t →
    ∀ (π : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ),
      IsProbabilityVector π → IsStochastic A → IsReversible A π →
      ∀ u : Fin n → Z, -- @realizes u_i(Markov type test points in Z)
        (∑ i, ∑ j, π i * (A ^ t) i j * dist (u i) (u j) ^ 2) ≤
          M ^ 2 * (t : ℝ) * ∑ i, ∑ j, π i * A i j * dist (u i) (u j) ^ 2

-- @node: def:markov-type
/-- [A metric space Z](hyp:Z) [has Markov type two with constant](goal)
[M](hyp:M) when [M is strictly positive](step:1) and [every finite reversible
Markov chain mapped into Z has expected squared displacement after t positive
steps at most M squared times t times its one-step expected squared displacement,
starting from any probability distribution satisfying detailed balance](step:2). -/
structure HasMarkovTypeTwo (Z : Type u) [MetricSpace Z] (M : ℝ) : Prop where
  constant_pos : 0 < M -- @realizes M(strictly positive Markov type constant)
  markov_type_condition : MarkovTypeTwoCondition Z M

-- @node: lem:mendel-naor-extension
/-- [The Mendel–Naor extension assertion](goal) says that there exists a universal
real constant K₀ such that [K₀ is nonnegative](step:1) and [whenever real ℓ₁ is
linearly isometric to the continuous dual of the space of real sequences tending
to zero, every Lipschitz map from a subset of a real Banach space with Markov
type two constant M into real ℓ₁ with metric Markov cotype two constant C extends
to the whole space, agrees with the original map on the subset, and has Lipschitz
constant at most K₀ times M times C times the original Lipschitz constant, for
all strictly positive M and C](step:2).

The disclosed cited logical gate: Manor Mendel and Assaf Naor (2013),
*Spectral calculus and Lipschitz extension for barycentric metric spaces*,
Corollary 1.13, handle `cite:mendel-naor-2013`, arXiv:1301.3963.
Source checked at https://web.math.princeton.edu/~naor/homepage%20files/cat0-extension.pdf
(Corollary 1.13, dual Banach targets), specialized to p = 2 and target real ℓ₁,
conditional on an explicit linear isometric identification of ℓ₁ with c₀*.
Here `StrongDual` is the continuous dual with its operator norm. The identification
is a separate paper-side obligation, not part of the cited input.
The gate is assumed by the extension corollary; it is not proved here.
-/
def MendelNaorExtension : Sort 0 :=
  ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ (_h_dual : Nonempty (RealEllOne ≃ₗᵢ[ℝ]
      StrongDual ℝ (ZeroAtInftyContinuousMap ℕ ℝ))), -- @realizes c_0(null sequences, sup norm)
    ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
      (M C : ℝ),
      0 < M → -- @realizes M(positive uniform Markov type constant)
      HasMarkovTypeTwo Z M →
      0 < C → -- @realizes C(positive uniform metric Markov cotype constant)
      HasMetricMarkovCotypeTwo RealEllOne C →
      ∀ (S : Set Z) (f : S → RealEllOne),
        (∃ L : NNReal, LipschitzWith L f) →
        ∃ F : Z → RealEllOne, (∀ x : S, F x = f x) ∧
          lipConst F ≤ ENNReal.ofReal (K₀ * M * C) * lipConst f

end Papers.OaiMetricMarkovCotype
