module
public import Causalean.Stat.FiniteDesign.DesignCore
public import Causalean.Experimentation.DesignBased.Designs.BernoulliMoments
public import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Finite biased cubes and invariant hypergraph properties

Vertices are `Fin n`, the zero-indexed relabeling of the paper's `[n]`.
The Bernoulli design is clamped outside `[0,1]` solely to give the probability
curve a total real domain. On `[0,1]` it includes the endpoint product laws.
The Fourier and captured-mass identities are scaffolded in `Helpers/Fourier`
and `TMain`; their quantitative conclusions are proved obligations, not fields.
-/

@[expose] public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

-- @env: S1
variable {J : Type*} [Fintype J] [DecidableEq J] -- @realizes J(finite coordinate type)

-- @realizes h(Boolean function)
-- @realizes x(configuration on J)
/-- For [a Boolean function](hyp:h) on [a finite coordinate set](hyp:J) and
[a configuration](hyp:x), its [real indicator](goal) is one when the function is
true and zero otherwise. -/
def boolValue (h : (J → Bool) → Bool) (x : J → Bool) : ℝ :=
  if h x then 1 else 0

/-- On [a finite coordinate set](hyp:J), the [independent Bernoulli law](goal)
assigns every coordinate success probability equal to [the bias](hyp:p) clamped
to the interval from zero to one, including both endpoints. -/
noncomputable def biasedLaw (J : Type*) [Fintype J] [DecidableEq J] (p : ℝ) :
    FiniteDesign (J → Bool) :=
  bernoulliDesign (fun _ => max 0 (min p 1))
    (fun _ => le_max_left _ _) (fun _ => max_le zero_le_one (min_le_right _ _))

-- @realizes \E_p(product-design expectation)
/-- The [cube expectation](goal) of [a real-valued function](hyp:g) on
[a finite coordinate set](hyp:J) is its expectation under independent Bernoulli
coordinates with [bias](hyp:p) clamped to the interval from zero to one. -/
noncomputable abbrev cubeExpectation (p : ℝ) (g : (J → Bool) → ℝ) : ℝ :=
  (biasedLaw J p).E g

-- @realizes \Var_p(product-design variance)
/-- The [cube variance](goal) of [a real-valued function](hyp:g) on
[a finite coordinate set](hyp:J) is its variance under independent Bernoulli
coordinates with [bias](hyp:p) clamped to the interval from zero to one. -/
noncomputable abbrev cubeVariance (p : ℝ) (g : (J → Bool) → ℝ) : ℝ :=
  (biasedLaw J p).Var g

/-- The [closed bias domain condition](goal) requires [the Bernoulli bias](hyp:p)
to lie between zero and one, inclusive. -/
def BiasDomain (p : ℝ) : Prop :=
  p ∈ Set.Icc 0 1 -- @realizes p(closed-interval Bernoulli bias, including endpoints)

-- @node: ass:bias
/-- The [interior bias condition](goal) requires [the Bernoulli bias](hyp:p) to be
[strictly positive](step:1) and [strictly less than one](step:2). -/
def BiasInterior (p : ℝ) : Prop :=
  0 < p ∧ p < 1 -- @realizes p(interior Bernoulli bias)

-- @node: ass:low-m
/-- The [low-degree parameter condition](goal) requires [the real degree
parameter](hyp:m) to be at least two. -/
def LowDegreeParam (m : ℝ) : Prop := 2 ≤ m -- @realizes m(real parameter at least two)

-- @node: ass:main-r
/-- The [main uniformity condition](goal) requires [the number of vertices per
edge](hyp:r) to be at least three. -/
def MainUniformity (r : ℕ) : Prop := 3 ≤ r -- @realizes r(integer uniformity at least three)

-- @node: ass:main-n
/-- The [main vertex-count condition](goal) requires [the number of vertices](hyp:n)
to be at least [the number of vertices per edge](hyp:r). -/
def MainVertexCount (n r : ℕ) : Prop := r ≤ n -- @realizes n(number of vertices at least r)

-- @node: ass:main-p
/-- The [main bias condition](goal) requires [the Bernoulli bias](hyp:p) to be
[strictly positive](step:1) and [strictly less than one](step:2). -/
def MainBias (p : ℝ) : Prop := 0 < p ∧ p < 1 -- @realizes p(interior bias in main theorem)

-- @env: S2
variable {n r : ℕ}

-- @node: def:vertex-edge-sets
-- @realizes [n](vertices Fin n)
-- @realizes E_{n,r}(r-element vertex subsets)
-- @realizes E(abbreviation of the same edge set)
/-- An [edge](goal) is a subset of [the vertex set of size n](hyp:n) containing
exactly [r vertices](hyp:r). -/
abbrev Edge (n r : ℕ) := {e : Finset (Fin n) // e.card = r}

/-- The [permuted edge](goal) is obtained by applying [a vertex permutation](hyp:τ)
to every vertex of [an edge](hyp:e) of [size r](hyp:r) in
[a vertex set of size n](hyp:n). -/
def edgePerm (τ : Equiv.Perm (Fin n)) (e : Edge n r) : Edge n r := -- @realizes e(edge coordinate)
  ⟨e.val.map τ.toEmbedding, (Finset.card_map _).trans e.property⟩

-- @node: def:hypergraph-property
/-- The [hypergraph property condition](goal) says that [a Boolean function of
the edge configuration](hyp:f), with [n vertices](hyp:n) and [r vertices per
edge](hyp:r), is unchanged by every permutation of the vertices. -/
structure IsHypergraphProperty (f : (Edge n r → Bool) → Bool) : Prop where
  invariant : ∀ (τ : Equiv.Perm (Fin n)) (x : Edge n r → Bool),
    f (fun e => x (edgePerm τ e)) = f x -- @realizes f(invariance under every vertex permutation)

-- @node: def:coordinate-replacement
-- @realizes b(Boolean replacement value)
/-- The [coordinate replacement](goal) of [a configuration](hyp:x) on
[a finite coordinate set](hyp:J) replaces [one coordinate](hyp:e) by
[a Boolean value](hyp:b), leaving every other coordinate unchanged. -/
abbrev replaceCoord (x : J → Bool) (e : J) (b : Bool) : J → Bool :=
  Function.update x e b -- @realizes x_{e\leftarrow b}(coordinate replacement)

-- @node: def:finite-coordinate-influences
-- @realizes i(coordinate in J)
/-- The [influence of a coordinate](goal) is the probability that forcing
[that coordinate](hyp:i) to true rather than false changes [a Boolean
function](hyp:h) on [a finite coordinate set](hyp:J), under independent
Bernoulli coordinates with [bias](hyp:p) clamped to the interval from zero to one. -/
noncomputable def coordInfluence (p : ℝ) (h : (J → Bool) → Bool) (i : J) : ℝ :=
  -- @realizes I_i(h)(pivotal probability)
  (biasedLaw J p).Pr (fun x => h (replaceCoord x i true) ≠ h (replaceCoord x i false))

/-- The [total coordinate influence](goal) of [a Boolean function](hyp:h) on
[a finite coordinate set](hyp:J) is the sum of its coordinate pivotal
probabilities under [Bernoulli bias](hyp:p). -/
noncomputable def totalCoordInfluence (p : ℝ) (h : (J → Bool) → Bool) : ℝ :=
  ∑ i, coordInfluence p h i -- @realizes I(h)(sum of pivotal influences)

-- @node: ass:low-individual-influences
/-- The [small individual influences condition](goal) requires every coordinate
in [the finite coordinate set](hyp:J) to have influence at most the total
influence of [the Boolean function](hyp:h) divided by [the real parameter](hyp:m),
with influences evaluated at [Bernoulli bias](hyp:p). -/
def SmallIndividualInfluences (p : ℝ) (h : (J → Bool) → Bool) (m : ℝ) : Prop :=
  ∀ i : J, coordInfluence p h i ≤ totalCoordInfluence p h / m

-- @node: def:influences
/-- The [influence of an edge](goal) is the probability that forcing [that
edge](hyp:e) present rather than absent changes [the Boolean hypergraph
function](hyp:f), for [n vertices](hyp:n), [r vertices per edge](hyp:r), and
independent edge inclusion with [bias](hyp:p). -/
noncomputable abbrev edgeInfluence (p : ℝ) (f : (Edge n r → Bool) → Bool)
    (e : Edge n r) : ℝ := coordInfluence p f e -- @realizes I_{e,p}(f)(edge pivotal probability)

/-- The [total edge influence](goal) of [a Boolean hypergraph function](hyp:f)
is the sum of its edge pivotal probabilities at [Bernoulli bias](hyp:p), over
all edges with [r vertices](hyp:r) among [n vertices](hyp:n). -/
noncomputable abbrev totalEdgeInfluence (p : ℝ) (f : (Edge n r → Bool) → Bool) : ℝ :=
  ∑ e, edgeInfluence p f e -- @realizes I_p(f)(sum over all r-edges)

-- @node: def:logarithm-convention
/-- The [natural logarithm](goal) uses the real logarithm convention, extended
to zero by a value of zero and to negative arguments by the logarithm of their
absolute value. -/
noncomputable abbrev natLog : ℝ → ℝ := Real.log

-- @node: def:increasing-nontrivial
/-- The [increasing and nontrivial condition](goal) on [a Boolean function](hyp:f)
on [a finite coordinate set](hyp:J) requires it to be [nondecreasing when
coordinates change from false to true](step:1) and [nonconstant](step:2). -/
structure IsIncreasingNontrivial (f : (J → Bool) → Bool) : Prop where
  mono : Monotone f -- @realizes f(coordinatewise increasing Boolean function)
  nonconst : ∃ x y, f x ≠ f y -- @realizes f(nonconstant)

/-- The [probability curve](goal) of [a Boolean function](hyp:f) on
[a finite coordinate set](hyp:J) gives the probability that it is true under
independent Bernoulli coordinates with [bias](hyp:p) clamped to the interval
from zero to one. -/
noncomputable def probCurve (f : (J → Bool) → Bool) (p : ℝ) : ℝ :=
  (biasedLaw J p).E (boolValue f) -- @realizes q(expectation of f at bias p)

-- @node: def:threshold-quantiles
-- @realizes a(probability level, scoped to 0<a<1 in quantile helpers)
/-- The [threshold quantile](goal) for [a Boolean function](hyp:f) on
[a finite coordinate set](hyp:J) at [a probability level](hyp:a) is the infimum
of biases between zero and one at which its probability of being true is at
least that level. -/
noncomputable def thresholdQuantile (f : (J → Bool) → Bool) (a : ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ a ≤ probCurve f p} -- @realizes p_a(paper range)

-- @node: def:threshold-width
/-- The [threshold width](goal) for [a Boolean function](hyp:f) on
[a finite coordinate set](hyp:J) and [a tail level ε](hyp:ε) is its quantile
at probability one minus ε minus its quantile at probability ε. -/
noncomputable def thresholdWidth (f : (J → Bool) → Bool) (ε : ℝ) : ℝ :=
  thresholdQuantile f (1 - ε) - thresholdQuantile f ε

-- @node: ass:threshold-epsilon
-- @realizes \varepsilon(tail level between zero and one half)
/-- The [threshold tail-level condition](goal) requires [the tail level](hyp:ε)
to be [strictly positive](step:1) and [strictly less than one half](step:2). -/
def ThresholdEpsilon (ε : ℝ) : Prop := 0 < ε ∧ ε < 1 / 2

-- @node: def:bias-scale
-- @realizes \sigma(square root of Bernoulli variance)
/-- The [bias scale](goal) at [Bernoulli bias p](hyp:p) is the square root
of p times one minus p. -/
noncomputable def biasScale (p : ℝ) : ℝ := Real.sqrt (p * (1 - p))

/-- The [normalized coordinate character](goal) at [bias p](hyp:p) subtracts p
from the zero-or-one value of [coordinate i](hyp:i) in [a configuration](hyp:x)
on [a finite coordinate set](hyp:J), and divides by the bias scale. -/
noncomputable def coordChar (p : ℝ) (i : J) (x : J → Bool) : ℝ :=
  ((if x i then 1 else 0) - p) / biasScale p -- @realizes \chi_i(normalized centered coordinate)

-- @node: def:fourier-basis
-- @realizes A(subset of J indexing the basis)
/-- The [Fourier character](goal) indexed by [a coordinate subset](hyp:A) of
[a finite coordinate set](hyp:J), evaluated at [a configuration](hyp:x) and
[bias](hyp:p), is the product of its normalized coordinate characters over
that subset; the empty product is one. -/
noncomputable def fourierChar (p : ℝ) (A : Finset J) (x : J → Bool) : ℝ :=
  ∏ i ∈ A, coordChar p i x -- @realizes \chi_A(product of normalized coordinates, empty product one)

-- @realizes g(real function on the current cube)
/-- The [real Fourier coefficient](goal) of [a real-valued function](hyp:g) on
[a finite coordinate set](hyp:J), for [a coordinate subset](hyp:A) and
[Bernoulli bias](hyp:p), is the expectation of the function times the Fourier
character of that subset. -/
noncomputable def fourierCoeffR (p : ℝ) (g : (J → Bool) → ℝ) (A : Finset J) : ℝ :=
  (biasedLaw J p).E (fun x => g x * fourierChar p A x)

-- @node: def:fourier-coefficients
/-- The [Boolean Fourier coefficient](goal) of [a Boolean function](hyp:h) on
[a finite coordinate set](hyp:J), indexed by [a coordinate subset](hyp:A) at
[Bernoulli bias](hyp:p), is the expectation of its zero-or-one indicator times
the Fourier character of that subset. -/
noncomputable def fourierCoeff (p : ℝ) (h : (J → Bool) → Bool) (A : Finset J) : ℝ :=
  fourierCoeffR p (boolValue h) A -- @realizes \widehat h(inner product with chi_A)

-- @node: def:difference
/-- The [coordinate difference](goal) of [a Boolean function](hyp:h) on
[a finite coordinate set](hyp:J), at [a configuration](hyp:x) and
[a coordinate](hyp:i), is its zero-or-one value with that coordinate forced
true minus its value with that coordinate forced false.

This difference is independent of the original value of the replaced coordinate. -/
def coordDiff (h : (J → Bool) → Bool) (i : J) (x : J → Bool) : ℝ :=
  -- @realizes \Delta_i h(paper range)
  boolValue h (replaceCoord x i true) - boolValue h (replaceCoord x i false)

/-- The [weighted spectral mass](goal) of [a Boolean function](hyp:h) on
[a finite coordinate set](hyp:J) at [Bernoulli bias](hyp:p) is the sum over all
coordinate subsets of the squared Fourier coefficient multiplied by the
number of coordinates in that subset. -/
noncomputable def weightedSpectralMass (p : ℝ) (h : (J → Bool) → Bool) : ℝ :=
  ∑ S : Finset J, (S.card : ℝ) * fourierCoeff p h S ^ 2 -- @realizes S(Fourier support subset of J)

-- @node: def:parseval
/-- The [Fourier identities condition](goal) for [a Boolean function](hyp:h) on
[a finite coordinate set](hyp:J) at [bias p](hyp:p) says that, whenever p is
strictly between zero and one, [the weighted spectral mass equals p times
one minus p times the total coordinate influence](step:1), and [the variance
of the function's zero-or-one indicator equals the sum of squared Fourier
coefficients over nonempty coordinate subsets](step:2). -/
def FourierIdentities (p : ℝ) (h : (J → Bool) → Bool) : Prop :=
  BiasInterior p →
    weightedSpectralMass p h = biasScale p ^ 2 * totalCoordInfluence p h ∧
    (biasedLaw J p).Var (boolValue h) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset J => S ≠ ∅), fourierCoeff p h S ^ 2

-- @node: def:low-cutoff
-- @realizes k(real cutoff sigma log m / 64)
/-- The [low-degree cutoff](goal) at [Bernoulli bias](hyp:p) and [real degree
parameter m](hyp:m) is the bias scale times the natural logarithm of m,
divided by 64. -/
noncomputable def lowCutoff (p m : ℝ) : ℝ := biasScale p * Real.log m / 64

-- @node: def:restriction-setup
/-- The [hypergraph Fourier coefficient](goal) of [a Boolean hypergraph
function](hyp:f), for [an edge subset](hyp:S) at [Bernoulli bias](hyp:p), is
the expectation of its zero-or-one indicator times that subset's Fourier
character, with [n vertices](hyp:n) and [r vertices per edge](hyp:r). -/
noncomputable abbrev hyperFourierCoeff (p : ℝ) (f : (Edge n r → Bool) → Bool)
    (S : Finset (Edge n r)) : ℝ := fourierCoeff p f S -- @realizes \widehat f(paper range)

-- @node: def:free-edges
/-- The [free edges](goal) for [a vertex block](hyp:B) are all edges with
[r vertices](hyp:r) among [n vertices](hyp:n) that meet the block. -/
def freeEdges (B : Finset (Fin n)) : Finset (Edge n r) := -- @realizes B(vertex block)
  Finset.univ.filter (fun e => (e.val ∩ B).Nonempty) -- @realizes F_B(edges meeting B)

-- @node: def:block-cutoff
/-- The [block cutoff](goal) for [Bernoulli bias](hyp:p) and [integer block
size m](hyp:m) is the bias scale times the natural logarithm of m, divided by 64. -/
noncomputable abbrev blockCutoff (p : ℝ) (m : ℕ) : ℝ := lowCutoff p m

-- @node: ass:block-domain
-- @realizes m(integer block size between r+1 and n)
/-- The [block domain condition](goal) on [edge size r](hyp:r), [block size m](hyp:m),
and [vertex count n](hyp:n) requires [m to be at least r plus one](step:1) and
[m to be at most n](step:2). -/
def BlockDomain (r m n : ℕ) : Prop := r + 1 ≤ m ∧ m ≤ n

-- @node: ass:capture-integer-domain
-- @realizes m(integer capture block size between one and n)
/-- The [capture domain condition](goal) on [vertex count n](hyp:n), [edge
size r](hyp:r), and [block size m](hyp:m) requires [r to be at least three](step:1),
[r to be at most n](step:2), [m to be at least one](step:3), and
[m to be at most n](step:4). -/
def CaptureDomain (n r m : ℕ) : Prop := 3 ≤ r ∧ r ≤ n ∧ 1 ≤ m ∧ m ≤ n

-- @node: ass:capture-k
/-- The [positive capture cutoff condition](goal) requires [the real capture
cutoff](hyp:k) to be strictly positive. -/
def CapturePositiveCutoff (k : ℝ) : Prop := 0 < k -- @realizes k(positive capture cutoff)

-- @realizes \alpha(r/(r-1), real subtraction)
/-- The [capture exponent](goal) for [edge size r](hyp:r) is r divided by
r minus one, with the subtraction and division taken over the real numbers. -/
noncomputable def captureExponent (r : ℕ) : ℝ := (r : ℝ) / ((r : ℝ) - 1)

-- @node: def:capture-cutoffs
/-- The [support cutoff](goal) for [edge size r](hyp:r) and [capture cutoff k](hyp:k)
is k divided by r, raised to the power r divided by r minus one. -/
noncomputable def supportCutoff (r : ℕ) (k : ℝ) : ℝ :=
  (k / r) ^ captureExponent r -- @realizes L(real support cutoff (k/r)^alpha)

-- @node: ass:capture-condition
/-- The [capture condition](goal) for [edge size r](hyp:r), [vertex count n](hyp:n),
[block size m](hyp:m), and [capture cutoff k](hyp:k) requires r times the
support cutoff times the ratio of m minus one to n minus one to be at most
one half, with subtraction and division taken over the real numbers. -/
def CaptureCondition (r n m : ℕ) (k : ℝ) : Prop :=
  (r : ℝ) * supportCutoff r k * (((m : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2

-- @node: ass:capture-support
/-- The [capture support condition](goal) on [a set of edges](hyp:S) with
[r vertices per edge](hyp:r) among [n vertices](hyp:n), for [a real size bound L](hyp:L),
requires [at least one edge](step:1) and [at most L edges](step:2). -/
def CaptureSupport (S : Finset (Edge n r)) (L : ℝ) : Prop :=
  1 ≤ S.card ∧ (S.card : ℝ) ≤ L -- @realizes S(nonempty edge support with cardinality at most L)

/-- The [captured Fourier mass](goal) of [a Boolean hypergraph function](hyp:f)
at [Bernoulli bias p](hyp:p), for [r vertices per edge](hyp:r) among
[n vertices](hyp:n) and [a real support-size bound L](hyp:L), is the sum of
squared Fourier coefficients over nonempty edge subsets containing at most L edges. -/
noncomputable def capturedMass (p : ℝ) (f : (Edge n r → Bool) → Bool) (L : ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Edge n r) => 1 ≤ S.card ∧ (S.card : ℝ) ≤ L),
    hyperFourierCoeff p f S ^ 2

-- @node: def:captured-mass
/-- The [captured-mass estimate](goal) for [edge size r](hyp:r), [block size m](hyp:m),
[vertex count n](hyp:n), [Bernoulli bias p](hyp:p), and [a Boolean hypergraph
function](hyp:f) asserts that the captured Fourier mass at the support cutoff
associated with the block cutoff is at most twice r times m to the power
minus one quarter times the total edge influence, whenever p is strictly
between zero and one, r plus one is at most m and m is at most n, the function
is invariant under vertex permutations, r is at least three and at most n,
m is at least one and at most n, the block cutoff is positive, and the capture
condition holds at that cutoff.

The block cutoff is the bias scale times the natural logarithm of m divided
by 64. `TMain` establishes this proposition using `capturedMass_le`. -/
def CapturedMassEstimate (r m n : ℕ) (p : ℝ) (f : (Edge n r → Bool) → Bool) : Prop :=
  BiasInterior p → BlockDomain r m n → IsHypergraphProperty f → CaptureDomain n r m →
    CapturePositiveCutoff (blockCutoff p m) → CaptureCondition r n m (blockCutoff p m) →
      capturedMass p f (supportCutoff r (blockCutoff p m)) ≤
        2 * r * (m : ℝ) ^ (-(1 : ℝ) / 4) * totalEdgeInfluence p f

-- @env: S3
variable (n m : ℕ) (hmn : m ≤ n)

/-- The [uniform block sampling law](goal) selects a subset of [n vertices](hyp:n)
containing exactly [m vertices](hyp:m), with all such subsets equally likely,
given [that m is at most n](hyp:hmn). -/
noncomputable def blockLaw (n m : ℕ) (hmn : m ≤ n) :
    FiniteDesign {B : Finset (Fin n) // B.card = m} :=
  completeRandomization m ((Fintype.card_fin n).symm ▸ hmn)

-- @env: S4
variable (S : Finset (Edge n r)) (k : ℝ)

/-- The [block capture probability](goal) for [a support set of edges](hyp:S)
with [r vertices per edge](hyp:r) among [n vertices](hyp:n) is the probability
that a uniformly sampled block of [m vertices](hyp:m) meets at least one and
at most [k support edges](hyp:k), given [that m is at most n](hyp:hmn). -/
noncomputable def blockCaptureProb (n r m : ℕ) (hmn : m ≤ n) (k : ℝ)
    (S : Finset (Edge n r)) : ℝ :=
  (blockLaw n m hmn).Pr (fun B =>
    1 ≤ (S ∩ freeEdges B.val).card ∧ ((S ∩ freeEdges B.val).card : ℝ) ≤ k)

end Papers.OaiUniformInfluenceHypergraph
