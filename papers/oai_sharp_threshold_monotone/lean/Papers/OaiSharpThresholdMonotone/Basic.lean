module
public import Causalean.Stat.FiniteDesign.DesignCore
public import Causalean.Stat.FiniteDesign.Product
public import Causalean.Experimentation.DesignBased.Designs.BernoulliMoments
public import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
public import Causalean.Mathlib.Probability.Poisson.Poincare.Tensorization
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Biased Boolean cubes and graph properties

Vertices `Fin n` relabel the paper's vertices `1,…,n`. Graph edges are two-element
vertex subsets. Expectations use the canonical finite independent Bernoulli design.
Clamping extends the probability curve to all real biases, agreeing with the paper
on `[0,1]`. Fourier identities and quantitative estimates are local lemma obligations.
-/

@[expose] public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

-- @env: S1
variable {J : Type*} [Fintype J] [DecidableEq J] -- @realizes J(finite coordinate type)

/-- For [a Boolean statistic](hyp:h) on [a finite coordinate set](hyp:J) and
[a configuration](hyp:x), its [real-valued indicator](goal) is one when the
statistic is true and zero otherwise. -/
def boolValue (h : (J → Bool) → Bool) -- @realizes h(Boolean product function)
    (x : J → Bool) : ℝ := -- @realizes x(product configuration)
  if h x then 1 else 0

/-- On [a finite coordinate set](hyp:J), the [independent Bernoulli product law](goal)
uses [a common bias](hyp:p), clamped to the closed unit interval. -/
noncomputable def biasedLaw (J : Type*) [Fintype J] [DecidableEq J] (p : ℝ) :
    FiniteDesign (J → Bool) :=
  bernoulliDesign (fun _ => max 0 (min p 1))
    (fun _ => le_max_left _ _) (fun _ => max_le zero_le_one (min_le_right _ _))

-- @node: ass:finite-coordinate-set
/-- The [finiteness condition](goal) for [a coordinate set](hyp:J) says that it has
only finitely many elements. -/
def FiniteCoordinateSet (J : Type*) : Prop := Finite J -- @realizes J(finite index set)

/-- The [probability domain condition](goal) on [a real bias](hyp:p) requires it to
be [at least zero](step:1) and [at most one](step:2). -/
def ProbabilityBias (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 -- @realizes p(closed unit interval probability domain)

-- @node: ass:interior-bias
/-- The [interior bias condition](goal) on [a real bias](hyp:p) requires it to be
[strictly positive](step:1) and [strictly less than one](step:2). -/
def BiasInterior (p : ℝ) : Prop :=
  0 < p ∧ p < 1 -- @realizes p(interior Bernoulli probability)

-- @node: ass:natural-logarithms
/-- The [natural logarithm convention](goal) requires [a real logarithm function](hyp:logarithm)
to equal the natural logarithm at every real argument.

Every public logarithmic expression below and in the results uses `Real.log`
directly, so this convention requires no additional theorem hypothesis. -/
def NaturalLogarithms (logarithm : ℝ → ℝ) : Prop := logarithm = Real.log

-- @node: def:coordinate-replacement
/-- For [a finite coordinate set](hyp:J), [a selected coordinate](hyp:i),
[a configuration](hyp:x), and [a replacement bit](hyp:b), the
[updated configuration](goal) replaces that coordinate by the bit and keeps all others. -/
noncomputable abbrev coordinateReplace (i : J) -- @realizes i(coordinate in J)
    (x : J → Bool) (b : Bool) : J → Bool := -- @realizes b(Boolean replacement value)
  Causalean.Mathlib.Probability.PoissonAddOnePoincare.coordinateReplace i x b
  -- @realizes x_{e\leftarrow b}(update one coordinate)

-- @node: def:bias-scale
/-- For [a real bias](hyp:p), the [bias scale](goal) is the square root of the bias
times one minus the bias, the Bernoulli standard deviation on the probability domain. -/
noncomputable def biasScale (p : ℝ) : ℝ :=
  Real.sqrt (p * (1 - p)) -- @realizes \sigma(square root of Bernoulli variance)

-- @node: def:product-norm
/-- On [a finite coordinate set](hyp:J), for [a bias](hyp:p), [a real exponent](hyp:q),
and [a real-valued statistic](hyp:g), the [product norm expression](goal) is the
expectation of the absolute value raised to that exponent, followed by the reciprocal power. -/
noncomputable def cubeNorm (p q : ℝ) -- @realizes q(real norm exponent, used for q at least one)
    (g : (J → Bool) → ℝ) : ℝ := -- @realizes g(real function on the cube)
  ((biasedLaw J p).E (fun x => |g x| ^ q)) ^ (1 / q)
  -- @realizes \|g\|_q(product norm formula)

/-- On [a finite coordinate set](hyp:J), the [normalized coordinate character](goal)
at [a bias](hyp:p), [a coordinate](hyp:i), and [a configuration](hyp:x) is the
coordinate's zero-or-one value minus the bias, divided by the bias scale. -/
noncomputable def coordChar (p : ℝ) (i : J) (x : J → Bool) : ℝ :=
  ((if x i then 1 else 0) - p) / biasScale p -- @realizes \chi_i(normalized centered bit)

-- @node: def:fourier-characters
/-- On [a finite coordinate set](hyp:J), the [Fourier character](goal) for
[a bias](hyp:p), [a coordinate subset](hyp:S), and [a configuration](hyp:x) is the
product of the normalized coordinate characters over that subset, with empty product one. -/
noncomputable def fourierChar (p : ℝ) (S : Finset J) -- @realizes S(Fourier subset of J)
    (x : J → Bool) : ℝ :=
  ∏ i ∈ S, coordChar p i x -- @realizes \chi_S(product character, empty product one)

-- @node: def:fourier-coefficients
/-- On [a finite coordinate set](hyp:J), the [Fourier coefficient](goal) of
[a real-valued statistic](hyp:g) at [a coordinate subset](hyp:S) and [a bias](hyp:p)
is the product-law expectation of the statistic times that subset's character. -/
noncomputable def fourierCoeffR (p : ℝ) (g : (J → Bool) → ℝ) (S : Finset J) : ℝ :=
  (biasedLaw J p).E (fun x => g x * fourierChar p S x)
  -- @realizes \widehat g(S)(inner product with the character)

/-- On [a finite coordinate set](hyp:J), the [Boolean Fourier coefficient](goal)
of [a Boolean statistic](hyp:h), for [a bias](hyp:p) and [a coordinate subset](hyp:S),
is the Fourier coefficient of its zero-or-one real-valued indicator. -/
noncomputable def fourierCoeff (p : ℝ) (h : (J → Bool) → Bool) (S : Finset J) : ℝ :=
  fourierCoeffR p (boolValue h) S -- @realizes \widehat h(S)(Boolean Fourier coefficient)

/-- On [a finite coordinate set](hyp:J), the [Fourier expansion](goal) of
[a real-valued statistic](hyp:g) at [a bias](hyp:p) sums each Fourier coefficient
times its character over all coordinate subsets. -/
noncomputable def fourierExpansion (p : ℝ) (g : (J → Bool) → ℝ) : (J → Bool) → ℝ :=
  fun x => ∑ S : Finset J, fourierCoeffR p g S * fourierChar p S x

-- @node: def:eq-parseval
/-- For [a real-valued statistic](hyp:g) on [a finite coordinate set](hyp:J) and
[a bias](hyp:p), the [Fourier identity condition](goal) requires that, when the bias
is strictly between zero and one, [the expansion reconstructs the statistic](step:1),
[its second moment equals the sum of squared coefficients](step:2), and
[its variance equals the sum of squared coefficients over nonempty subsets](step:3).

The corresponding supporting lemmas are in `Helpers.Fourier`. -/
def fourierIdentities (p : ℝ) (g : (J → Bool) → ℝ) : Prop :=
  BiasInterior p →
    g = fourierExpansion p g ∧
    (biasedLaw J p).E (fun x => g x ^ 2) =
      ∑ S : Finset J, fourierCoeffR p g S ^ 2 ∧
    (biasedLaw J p).Var g =
      ∑ S ∈ Finset.univ.filter (fun S : Finset J => S ≠ ∅), fourierCoeffR p g S ^ 2

-- @node: def:coordinate-difference
/-- For [a real-valued statistic](hyp:g) on [a finite coordinate set](hyp:J),
[a coordinate](hyp:i), and [a configuration](hyp:x), the [coordinate difference](goal)
is the value with that coordinate set to true minus the value with it set to false.

`coordDiffRemaining` below gives the paper's function on the other coordinates. -/
noncomputable def coordDiffR (g : (J → Bool) → ℝ) (i : J) (x : J → Bool) : ℝ :=
  g (coordinateReplace i x true) - g (coordinateReplace i x false)
  -- @realizes \Delta_i g(section difference)

/-- For [a Boolean statistic](hyp:h) on [a finite coordinate set](hyp:J) and
[a coordinate](hyp:i), the [Boolean coordinate difference](goal) is the function
subtracting its zero-or-one indicator with that bit false from its indicator with that bit true. -/
noncomputable abbrev coordDiff (h : (J → Bool) → Bool) (i : J) : (J → Bool) → ℝ :=
  coordDiffR (boolValue h) i -- @realizes \Delta_i h(Boolean section difference)

/-- On [a finite coordinate set](hyp:J), for [a selected coordinate](hyp:i),
[a configuration of all other coordinates](hyp:y), and [a bit](hyp:b), the
[extended configuration](goal) assigns that bit to the selected coordinate and
uses the given configuration elsewhere. -/
def insertCoordinate (i : J) (y : {j : J // j ≠ i} → Bool) (b : Bool) : J → Bool :=
  fun j => if hj : j = i then b else y ⟨j, hj⟩

/-- For [a real-valued statistic](hyp:g) on [a finite coordinate set](hyp:J),
[a coordinate](hyp:i), and [a configuration of the remaining coordinates](hyp:x),
the [remaining-coordinate difference](goal) is the statistic with the missing bit
inserted as true minus the statistic with it inserted as false. -/
noncomputable def coordDiffRemaining (g : (J → Bool) → ℝ) (i : J)
    (x : {j : J // j ≠ i} → Bool) : ℝ := -- @realizes x(remaining-coordinate argument)
  g (insertCoordinate i x true) - g (insertCoordinate i x false)
  -- @realizes \Delta_i g(function on remaining coordinates)

/-- For [a Boolean statistic](hyp:h) on [a finite coordinate set](hyp:J),
[a bias](hyp:p), and [a coordinate](hyp:i), the [coordinate influence](goal) is the
product-law probability that changing that bit changes the statistic. -/
noncomputable def coordInfluence (p : ℝ) (h : (J → Bool) → Bool) (i : J) : ℝ :=
  (biasedLaw J p).Pr (fun x => coordDiffR (boolValue h) i x ≠ 0)
  -- @realizes I_i(h)(pivotal probability)

-- @node: def:product-influences
/-- For [a Boolean statistic](hyp:h) on [a finite coordinate set](hyp:J) and
[a bias](hyp:p), the [total influence](goal) is the sum of all coordinate influences. -/
noncomputable def totalCoordInfluence (p : ℝ) (h : (J → Bool) → Bool) : ℝ :=
  ∑ i, coordInfluence p h i -- @realizes I(h)(sum of coordinate influences)

/-- For [a Boolean statistic](hyp:h) on [a finite coordinate set](hyp:J),
[a bias](hyp:p), and [a coordinate](hyp:i), the [coordinate spectral mass](goal)
is the sum of squared Fourier coefficients over subsets containing that coordinate. -/
noncomputable def coordSpectralMass (p : ℝ) (h : (J → Bool) → Bool) (i : J) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset J => i ∈ S), fourierCoeff p h S ^ 2

/-- For [a Boolean statistic](hyp:h) on [a finite coordinate set](hyp:J) and
[a bias](hyp:p), the [degree-weighted spectral mass](goal) sums each squared
Fourier coefficient multiplied by the size of its coordinate subset. -/
noncomputable def weightedSpectralMass (p : ℝ) (h : (J → Bool) → Bool) : ℝ :=
  ∑ S : Finset J, (S.card : ℝ) * fourierCoeff p h S ^ 2

-- @node: def:eq-dirichlet
/-- For [a Boolean statistic](hyp:h) on [a finite coordinate set](hyp:J) and
[a bias](hyp:p), the [Fourier influence identity condition](goal) requires that,
at interior biases, [each coordinate's spectral mass equals its influence times
the Bernoulli variance](step:1) and [the degree-weighted spectral mass equals
total influence times the Bernoulli variance](step:2). -/
def fourierInfluenceIdentities (p : ℝ) (h : (J → Bool) → Bool) : Prop :=
  BiasInterior p →
    (∀ i : J, coordSpectralMass p h i = biasScale p ^ 2 * coordInfluence p h i) ∧
    weightedSpectralMass p h = biasScale p ^ 2 * totalCoordInfluence p h

-- @node: ass:low-degree-m
/-- The [low-degree comparison condition](goal) requires [a real comparison
parameter](hyp:m) to be at least two. -/
def LowDegreeParam (m : ℝ) : Prop := 2 ≤ m -- @realizes m(real influence comparison parameter)

-- @node: ass:low-degree-small-influences
/-- For [a Boolean statistic](hyp:h) on [a finite coordinate set](hyp:J),
[a bias](hyp:p), and [a comparison parameter](hyp:m), the [small individual
influences condition](goal) requires each coordinate influence to be at most
the total influence divided by the comparison parameter. -/
def SmallIndividualInfluences (p : ℝ) (h : (J → Bool) → Bool) (m : ℝ) : Prop :=
  ∀ i : J, coordInfluence p h i ≤ totalCoordInfluence p h / m

/-- For [a bias](hyp:p) and [a real comparison parameter](hyp:m), the
[low-degree cutoff](goal) is the bias scale times the natural logarithm of the
comparison parameter, divided by 64. -/
noncomputable def lowCutoff (p m : ℝ) : ℝ :=
  biasScale p * Real.log m / 64 -- @realizes k(literal real degree cutoff)

-- @node: ass:low-degree-cutoff
/-- For [a bias](hyp:p) and [a real comparison parameter](hyp:m), the
[cutoff condition](goal) requires [a proposed cutoff](hyp:k) to equal the bias
scale times the natural logarithm of the comparison parameter, divided by 64. -/
def LowDegreeCutoff (p m k : ℝ) : Prop :=
  k = biasScale p * Real.log m / 64 -- @realizes k(pinned cutoff)

-- @node: def:low-degree-noise-parameter
/-- For [a bias](hyp:p), the [low-degree noise parameter](goal) is one quarter
of the bias scale. -/
noncomputable def noiseParameter (p : ℝ) : ℝ :=
  biasScale p / 4 -- @realizes \rho(sigma over four)

-- @node: def:low-degree-noise-operator
/-- On [a finite coordinate set](hyp:J), the [noise operator](goal) for
[a bias](hyp:p), [a noise multiplier](hyp:ρ), and [a real-valued statistic](hyp:g)
reconstructs the Fourier expansion after multiplying each coefficient by the
noise multiplier raised to the size of its coordinate subset. -/
noncomputable def noiseOperator (p ρ : ℝ) (g : (J → Bool) → ℝ) : (J → Bool) → ℝ :=
  fun x => ∑ S : Finset J, ρ ^ S.card * fourierCoeffR p g S * fourierChar p S x
  -- @realizes T_\rho(Fourier multiplier)

/-- The [projection degree condition](goal) requires [a real degree cutoff](hyp:d)
to be nonnegative. -/
def ProjectionDegree (d : ℝ) : Prop :=
  0 ≤ d -- @realizes d(nonnegative real projection cutoff)

-- @node: def:low-degree-projection
/-- On [a finite coordinate set](hyp:J), the [low-degree projection](goal) of
[a real-valued statistic](hyp:g), for [a bias](hyp:p) and [a real degree cutoff](hyp:d),
retains only Fourier terms whose coordinate subsets have size at most the cutoff. -/
noncomputable def lowProjection (p d : ℝ)
    (g : (J → Bool) → ℝ) : (J → Bool) → ℝ :=
  fun x => ∑ S ∈ Finset.univ.filter (fun S : Finset J => (S.card : ℝ) ≤ d),
    fourierCoeffR p g S * fourierChar p S x -- @realizes P_{\le d}(Fourier projection)

-- @env: S2
variable {n : ℕ} -- @realizes n(natural vertex count, at least two in both main results)

-- @node: def:graph-coordinates
/-- For [a vertex count](hyp:n), the [graph edge type](goal) consists of two-element
subsets of the vertices numbered from zero up to one less than that count. -/
abbrev GraphEdge (n : ℕ) := {e : Finset (Fin n) // e.card = 2}
-- @realizes [n](Fin n, zero-indexed relabeling)
-- @realizes E_n(two-element vertex subsets)

-- @node: def:graph-encoding
/-- For [a vertex count](hyp:n), a [graph configuration](goal) assigns a Boolean
presence indicator to every unordered pair of distinct vertices. -/
abbrev GraphConfig (n : ℕ) := GraphEdge n → Bool

/-- For [a vertex count](hyp:n), [a vertex permutation](hyp:τ), and [an edge](hyp:e),
the [permuted edge](goal) is the pair obtained by applying the permutation to
both endpoints. -/
def edgePerm (τ : Equiv.Perm (Fin n)) (e : GraphEdge n) : GraphEdge n :=
  ⟨e.val.map τ.toEmbedding, (Finset.card_map _).trans e.property⟩

-- @node: ass:graph-property-invariance
/-- For [a vertex count](hyp:n) and [a family of graphs](hyp:P), the
[permutation invariance condition](goal) says that relabeling vertices by any
permutation preserves membership in the family in both directions. -/
def GraphPropertyInvariant (P : Set (GraphConfig n)) : Prop :=
  ∀ (τ : Equiv.Perm (Fin n)) (x : GraphConfig n),
    (fun e => x (edgePerm τ e)) ∈ P ↔ x ∈ P -- @realizes \mathcal P(permutation invariance)

-- @node: ass:increasing-family
/-- For [a vertex count](hyp:n) and [a family of graphs](hyp:P), the
[increasing family condition](goal) says that adding edges to a member of the
family always yields another member. -/
def IncreasingFamily (P : Set (GraphConfig n)) : Prop :=
  ∀ x y : GraphConfig n, x ≤ y → x ∈ P → y ∈ P -- @realizes \mathcal P(upward closure)

-- @node: ass:nontrivial-family
/-- For [a vertex count](hyp:n) and [a family of graphs](hyp:P), the
[nontriviality condition](goal) requires that [the family contains some graph](step:1)
and [the family does not contain every graph](step:2). -/
def NontrivialFamily (P : Set (GraphConfig n)) : Prop :=
  P.Nonempty ∧ P ≠ Set.univ -- @realizes \mathcal P(nonempty proper family)

-- @node: def:graph-property
-- @realizes \mathcal P(graph family)
/-- For [a vertex count](hyp:n) and [a family of graphs](hyp:P), the
[graph property condition](goal) records that membership is invariant under
every permutation of the vertices. -/
structure IsGraphProperty (P : Set (GraphConfig n)) : Prop where
  invariance : GraphPropertyInvariant P -- @realizes \mathcal P(permutation invariance)

-- @node: def:increasing-graph-property
/-- For [a vertex count](hyp:n) and [a family of graphs](hyp:P), the
[increasing graph property condition](goal) requires [invariance under vertex
permutations](step:1) and [closure under adding edges](step:2). -/
structure IsIncreasingGraphProperty (P : Set (GraphConfig n)) : Prop where
  invariance : GraphPropertyInvariant P -- @realizes \mathcal P(permutation invariance)
  increasing : IncreasingFamily P -- @realizes \mathcal P(increasing family)

-- @node: def:nontrivial-graph-property
/-- For [a vertex count](hyp:n) and [a family of graphs](hyp:P), the
[nontrivial graph property condition](goal) requires [invariance under vertex
permutations](step:1) and [the family to be nonempty and different from the family
of all graphs](step:2). -/
structure IsNontrivialGraphProperty (P : Set (GraphConfig n)) : Prop where
  invariance : GraphPropertyInvariant P -- @realizes \mathcal P(permutation invariance)
  nontrivial : NontrivialFamily P -- @realizes \mathcal P(nonempty and proper)

-- @node: ass:graph-symmetry
/-- For [a vertex count](hyp:n) and [a Boolean graph statistic](hyp:f), the
[graph symmetry condition](goal) says that relabeling the vertices by any
permutation leaves the statistic unchanged on every graph. -/
def GraphSymmetric (f : GraphConfig n → Bool) : Prop := -- @realizes f(Boolean graph function)
  ∀ (τ : Equiv.Perm (Fin n)) (x : GraphConfig n), f (fun e => x (edgePerm τ e)) = f x
  -- @realizes f(vertex-permutation invariance)

-- @node: ass:restriction-boolean-function
/-- For [a vertex count](hyp:n) and [a Boolean graph statistic](hyp:f), the
[Boolean value condition](goal) says that the statistic's real-valued indicator
is either zero or one on every graph. -/
def BooleanGraphFunction (f : GraphConfig n → Bool) : Prop :=
  ∀ x, boolValue f x = 0 ∨ boolValue f x = 1 -- @realizes f(Boolean real cast)

/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), [a Boolean graph
statistic](hyp:f), and [a selected edge](hyp:e), the [edge influence](goal) is
the probability under independent Bernoulli edges that forcing the selected edge
present rather than absent changes the statistic. -/
noncomputable def edgeInfluence (p : ℝ) (f : GraphConfig n → Bool)
    (e : GraphEdge n) : ℝ := -- @realizes e(graph edge coordinate)
  (biasedLaw (GraphEdge n) p).Pr
    (fun x => f (coordinateReplace e x true) ≠ f (coordinateReplace e x false))
  -- @realizes I_{e,p}(f)(edge pivotal probability)
  -- @realizes I_e(f)(same fixed-bias pivotal probability)

-- @node: def:graph-influences
/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), and [a Boolean graph
statistic](hyp:f), the [total graph influence](goal) is the sum of the pivotal
probabilities over all edges. -/
noncomputable def graphTotalInfluence (p : ℝ) (f : GraphConfig n → Bool) : ℝ :=
  ∑ e, edgeInfluence p f e -- @realizes I_p(f)(sum of edge influences)
  -- @realizes I(f)(fixed-bias total influence)

-- @node: def:graph-bias-convention
/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), and [a Boolean graph
statistic](hyp:f), the [graph variance](goal) is the variance of the statistic's
zero-or-one indicator under independent Bernoulli edges. -/
noncomputable def graphVariance (p : ℝ) (f : GraphConfig n → Bool) : ℝ :=
  (biasedLaw (GraphEdge n) p).Var (boolValue f) -- @realizes \Var_p(f)(Bernoulli product variance)
  -- @realizes \Var(f)(same variance with bias suppressed)

/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), [a Boolean graph
statistic](hyp:f), and [a subset of edges](hyp:S), the [graph Fourier
coefficient](goal) is the expectation of the statistic's zero-or-one indicator
times the product of the normalized centered edge indicators in that subset. -/
noncomputable abbrev graphFourierCoeff (p : ℝ) (f : GraphConfig n → Bool)
    (S : Finset (GraphEdge n)) : ℝ :=
  fourierCoeff p f S -- @realizes \widehat f(S)(fixed-bias graph coefficient)

-- @node: ass:variance-n
/-- The [variance vertex-count condition](goal) requires [the number of
vertices](hyp:n) to be at least two. -/
def VarianceVertexCount (n : ℕ) : Prop := 2 ≤ n -- @realizes n(variance domain)

-- @node: ass:variance-symmetry
/-- For [a vertex count](hyp:n) and [a Boolean graph statistic](hyp:f), the
[variance symmetry condition](goal) requires the statistic to be unchanged by
every permutation of the vertices. -/
def VarianceSymmetric (f : GraphConfig n → Bool) : Prop := GraphSymmetric f

-- @node: ass:variance-bias
/-- The [variance bias condition](goal) requires [an edge bias](hyp:p) to be
[strictly positive](step:1) and [strictly less than one](step:2). -/
def VarianceBias (p : ℝ) : Prop := 0 < p ∧ p < 1 -- @realizes p(interior variance bias)

-- @node: ass:restriction-free-edges
/-- For [a vertex count](hyp:n) and [a finite set of free edges](hyp:F), the
[free-edge set condition](goal) requires every free edge to belong to the full
set of graph edges. -/
def FreeEdgeSet (F : Finset (GraphEdge n)) : Prop := -- @realizes F(free edge subset)
  F ⊆ Finset.univ -- @realizes F(subset of the graph coordinates)

-- @node: def:restriction-exterior
/-- For [a vertex count](hyp:n) and [a set of free edges](hyp:F), the
[exterior edge set](goal) consists of all graph edges outside the free set. -/
def exteriorEdges (F : Finset (GraphEdge n)) : Finset (GraphEdge n) :=
  Finset.univ \ F -- @realizes H(complementary edge coordinates)

/-- For [a vertex count](hyp:n), [a set of free edges](hyp:F), [an assignment
of presence indicators to the free edges](hyp:x), and [an assignment to all other
edges](hyp:y), the [merged graph configuration](goal) uses the free assignment
on the free edges and the exterior assignment elsewhere. -/
def mergeAssignment (F : Finset (GraphEdge n)) (x : {e // e ∈ F} → Bool)
    (y : {e // e ∉ F} → Bool) : GraphConfig n := -- @realizes y(exterior assignment)
  fun e => if h : e ∈ F then x ⟨e, h⟩ else y ⟨e, h⟩

-- @node: def:restricted-function
/-- For [a vertex count](hyp:n), [a Boolean graph statistic](hyp:f), [a set of
free edges](hyp:F), and [a fixed assignment on the other edges](hyp:y), the
[restricted statistic](goal) evaluates the original statistic after combining
each free-edge configuration with the fixed exterior assignment. -/
def restrictFn (f : GraphConfig n → Bool) (F : Finset (GraphEdge n))
    (y : {e // e ∉ F} → Bool) : ({e // e ∈ F} → Bool) → Bool :=
  fun x => f (mergeAssignment F x y) -- @realizes f_y(restricted Boolean function)
  -- @realizes x(free-coordinate configuration)

/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), [a Boolean graph
statistic](hyp:f), [a free-edge set](hyp:F), [a fixed exterior assignment](hyp:y),
and [a selected free edge](hyp:e), the [restricted edge influence](goal) is the
probability under independent Bernoulli free edges that changing the selected
edge changes the statistic while the exterior remains fixed. -/
noncomputable abbrev restrictedCoordInfluence (p : ℝ) (f : GraphConfig n → Bool)
    (F : Finset (GraphEdge n)) (y : {e // e ∉ F} → Bool) (e : {e // e ∈ F}) : ℝ :=
  coordInfluence p (restrictFn f F y) e -- @realizes I_e(f_y)(restricted pivotal influence)

/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), [a Boolean graph
statistic](hyp:f), [a free-edge set](hyp:F), and [a fixed exterior assignment](hyp:y),
the [restricted total influence](goal) sums the pivotal probabilities of all free
edges under their independent Bernoulli law with the exterior fixed. -/
noncomputable abbrev restrictedTotalInfluence (p : ℝ) (f : GraphConfig n → Bool)
    (F : Finset (GraphEdge n)) (y : {e // e ∉ F} → Bool) : ℝ :=
  totalCoordInfluence p (restrictFn f F y) -- @realizes I(f_y)(restricted total influence)

/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), [a Boolean graph
statistic](hyp:f), [a free-edge set](hyp:F), [a fixed exterior assignment](hyp:y),
and [a subset of the free edges](hyp:A), the [restricted Fourier coefficient](goal)
is the expectation, over independent Bernoulli free edges, of the restricted
statistic's indicator times the product of the subset's normalized centered bits. -/
noncomputable abbrev restrictedFourierCoeff (p : ℝ) (f : GraphConfig n → Bool)
    (F : Finset (GraphEdge n)) (y : {e // e ∉ F} → Bool) (A : Finset {e // e ∈ F}) : ℝ :=
  fourierCoeff p (restrictFn f F y) A -- @realizes \widehat{f_y}(A)(free-coordinate coefficient)

-- @node: ass:restriction-law
/-- For [a vertex count](hyp:n), [a free-edge set](hyp:F), [an edge bias](hyp:p),
and [a probability design on exterior assignments](hyp:ν), the [exterior Bernoulli
law condition](goal) requires each assignment's probability to be the product,
over exterior edges, of the bias for present edges and one minus the bias for
absent edges. -/
def ExteriorBernoulliLaw (F : Finset (GraphEdge n)) (p : ℝ)
    (ν : FiniteDesign ({e // e ∉ F} → Bool)) : Prop :=
  ∀ y, ν.p y = ∏ e, if y e then p else 1 - p -- @realizes y(exterior Bernoulli product law)

-- @node: ass:restriction-cutoff
/-- The [positive cutoff condition](goal) requires [a real cutoff](hyp:k) to be
strictly greater than zero. -/
def PositiveCutoff (k : ℝ) : Prop := 0 < k -- @realizes k(positive real restriction cutoff)

-- @env: S3
variable {m : ℕ}

-- @node: ass:block-m
/-- For [an integer block size](hyp:m) and [a vertex count](hyp:n), the
[block-size condition](goal) requires [the block size to be at least three](step:1)
and [the block size to be at most the vertex count](step:2). -/
def BlockSize (m n : ℕ) : Prop := 3 ≤ m ∧ m ≤ n -- @realizes m(integer block size)

-- @node: ass:block-law
/-- For [a vertex count](hyp:n), [a block size](hyp:m), and [a probability design
on vertex subsets of that size](hyp:π), the [uniform block law condition](goal)
requires each such subset to have probability equal to the reciprocal of the
number of such subsets. -/
def UniformBlockLaw (n m : ℕ)
    (π : FiniteDesign {B : Finset (Fin n) // B.card = m}) : Prop :=
  ∀ B, π.p B = 1 / (Fintype.card {B : Finset (Fin n) // B.card = m} : ℝ)
  -- @realizes B(uniform m-element vertex block)

/-- For [a vertex count](hyp:n) and [a block size](hyp:m), with [the block size
at most the vertex count](hyp:hmn), the [block sampling law](goal) selects uniformly
among all vertex subsets of that size. -/
noncomputable def blockLaw (n m : ℕ) (hmn : m ≤ n) :
    FiniteDesign {B : Finset (Fin n) // B.card = m} :=
  completeRandomization m ((Fintype.card_fin n).symm ▸ hmn)

/-- For [a vertex count](hyp:n) and [a vertex block](hyp:B), the [free-edge
set of the block](goal) consists of all graph edges with at least one endpoint
in the block. -/
def freeEdges (B : Finset (Fin n)) : Finset (GraphEdge n) := -- @realizes B(vertex block)
  Finset.univ.filter (fun e => (e.val ∩ B).Nonempty) -- @realizes F_B(edges meeting the block)

-- @node: def:block-parameters
/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), [a block size](hyp:m),
and [a vertex block of that size](hyp:B), the [block parameters](goal) pair
the edges meeting the block with the bias scale times the natural logarithm
of the block size divided by 64. -/
noncomputable def blockParameters (p : ℝ) (m : ℕ)
    (B : {B : Finset (Fin n) // B.card = m}) : Finset (GraphEdge n) × ℝ :=
  (freeEdges B.val, -- @realizes F_B(edges meeting the m-element block)
    lowCutoff p m) -- @realizes k(block cutoff sigma times log m divided by 64)

/-- For [a vertex count](hyp:n) and [a vertex block](hyp:B), the [block exterior
edge set](goal) consists of graph edges with both endpoints outside the block. -/
def blockExteriorEdges (B : Finset (Fin n)) : Finset (GraphEdge n) :=
  exteriorEdges (freeEdges B) -- @realizes H_B(edges with both endpoints outside the block)

/-- For [a vertex count](hyp:n), the [square-root block size](goal) is the
integer part of the square root of that count. -/
def sqrtBlockSize (n : ℕ) : ℕ := Nat.sqrt n -- @realizes m(floor of the square root)

-- @node: def:block-capture-parameters
/-- For [an edge bias](hyp:p) and [a vertex count](hyp:n), the [capture
parameters](goal) pair the integer part of the square root of the vertex count
with the bias scale times the natural logarithm of that block size divided by 64. -/
noncomputable def captureParameters (p : ℝ) (n : ℕ) : ℕ × ℝ :=
  (sqrtBlockSize n, -- @realizes m(floor of the square root in the capture regime)
    lowCutoff p (sqrtBlockSize n)) -- @realizes k(capture cutoff sigma times log m divided by 64)

-- @node: ass:block-capture-size
/-- The [capture logarithmic size condition](goal) requires the natural
logarithm of [the vertex count](hyp:n) to be at least sixteen. -/
def CaptureLogSize (n : ℕ) : Prop :=
  16 ≤ Real.log (n : ℝ) -- @realizes t(logarithmic vertex count at least sixteen)

-- @env: S4
variable (P : Set (GraphConfig n)) -- @realizes \mathcal P(family of graph configurations)

/-- For [a vertex count](hyp:n) and [a family of graphs](hyp:P), the [property
indicator](goal) is true on graphs belonging to the family and false on all
other graphs. -/
noncomputable def propertyIndicator (P : Set (GraphConfig n)) : GraphConfig n → Bool :=
  fun x => @decide (x ∈ P) (Classical.propDecidable _)

-- @node: def:property-probability
/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), and [a family of
graphs](hyp:P), the [property probability](goal) is the probability that a graph
with independent Bernoulli edges belongs to the family. -/
noncomputable def propertyProb (p : ℝ) (P : Set (GraphConfig n)) : ℝ := by
  classical
  exact (biasedLaw (GraphEdge n) p).Pr (fun x => x ∈ P)
  -- @realizes \mu_p(\mathcal P)(probability under independent Bernoulli edges)

/-- For [a vertex count](hyp:n), [an edge bias](hyp:p), and [a family of
graphs](hyp:P), the [property expectation](goal) is the expected zero-or-one
membership indicator under independent Bernoulli edges. -/
noncomputable def propertyExpectation (p : ℝ) (P : Set (GraphConfig n)) : ℝ :=
  (biasedLaw (GraphEdge n) p).E (boolValue (propertyIndicator P))
  -- @realizes \mu(p)(indicator expectation at the varying bias)

/-- For [a vertex count](hyp:n), [a family of graphs](hyp:P), [a selected
edge](hyp:e), and [an assignment on all remaining edges](hyp:x), the [edge
difference](goal) is the family's zero-or-one membership indicator with the
selected edge present minus its indicator with that edge absent. -/
noncomputable abbrev edgeDiff (P : Set (GraphConfig n)) (e : GraphEdge n)
    (x : {e' : GraphEdge n // e' ≠ e} → Bool) : ℝ :=
  coordDiffRemaining (boolValue (propertyIndicator P)) e x
  -- @realizes \Delta_e f(indicator difference on remaining edge coordinates)

-- @node: def:property-quantile
/-- For [a vertex count](hyp:n), [a probability level](hyp:a), and [a family
of graphs](hyp:P), the [property quantile](goal) is the infimum of edge biases
in the closed unit interval for which the family's probability under independent
Bernoulli edges is at least that level. -/
noncomputable def propertyQuantile (a : ℝ) (P : Set (GraphConfig n)) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ a ≤ propertyProb p P}
  -- @realizes p_a(\mathcal P)(infimum of biases meeting the level)
  -- @realizes a(quantile level, constrained to the open unit interval in quantile lemmas)

-- @node: ass:threshold-n
/-- The [threshold vertex-count condition](goal) requires [the number of
vertices](hyp:n) to be at least two. -/
def ThresholdVertexCount (n : ℕ) : Prop := 2 ≤ n -- @realizes n(threshold domain)

-- @node: ass:threshold-property
/-- For [a vertex count](hyp:n) and [a family of graphs](hyp:P), the [threshold
property condition](goal) requires [invariance under vertex permutations](step:1),
[closure under adding edges](step:2), and [that the family be nonempty and
different from the family of all graphs](step:3). -/
def ThresholdProperty (P : Set (GraphConfig n)) : Prop :=
  GraphPropertyInvariant P ∧ -- @realizes \mathcal P(vertex symmetry)
  IncreasingFamily P ∧ -- @realizes \mathcal P(increasing under edge addition)
  NontrivialFamily P -- @realizes \mathcal P(nonempty and proper)

-- @node: ass:threshold-epsilon
/-- The [threshold tolerance condition](goal) requires [a real tolerance](hyp:ε)
to be [strictly positive](step:1) and [strictly less than one half](step:2). -/
def ThresholdEpsilon (ε : ℝ) : Prop :=
  0 < ε ∧ ε < 1 / 2 -- @realizes \varepsilon(full printed open range)

end Papers.OaiSharpThresholdMonotone
