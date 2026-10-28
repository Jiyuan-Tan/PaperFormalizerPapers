module
public import Causalean.Stat.FiniteDesign.DesignCore
public import Toolkit.Foundations.Probability.BiasedCube
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Powerset

/-! # Finite graph containment, integral covers, and Bernoulli tests

The finite-design law gives independent edges without measurable-space assumptions.
Thresholds use infima and suprema; their attainment on the paper's finite graph
 domains is recorded in `Helpers.Thresholds`, rather than assumed by consumers.
The sole borrowed logical input is `DiscreteConvexityCover`.
-/

@[expose] public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

-- @env: S1
variable {V W : Type} [Fintype V] [DecidableEq V]
  -- @realizes V(finite vertex carrier V)

-- @env: S2
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  -- @realizes X(finite ground-set carrier)
  -- @realizes Y(finite requirement ground-set carrier)

/-- For [a host order n](hyp:n), the [host vertex labels](goal) are the integers from zero to n − 1.
@realizes [n](n host labels)
@realizes n(natural vertex bound and host order) -/
abbrev HostVertex (n : ℕ) := Fin n

/-- The [complete host graph](goal) on [n vertices](hyp:n) joins every pair of distinct labels.
@realizes K_n(complete simple graph on the host labels) -/
def completeHost (n : ℕ) : SimpleGraph (HostVertex n) := ⊤

/-- For [a host order n](hyp:n), the [possible host edges](goal) are unordered pairs of distinct host vertices.
@realizes E(edge carrier consists of unordered non-diagonal pairs) -/
abbrev KEdge (n : ℕ) := {e : Sym2 (HostVertex n) // ¬ e.IsDiag}

/-- On [the finite ground set X](hyp:X), the [subset represented by an indicator assignment](goal)
consists of the elements to which [the Boolean assignment z](hyp:z) assigns true.
@realizes S(finite subset encoded by a Boolean assignment) -/
def toFinset' (z : X → Bool) : Finset X := Finset.univ.filter (fun x => z x = true)

-- @node: def:product-measure
/-- The [product measure](goal) on [a finite ground set X](hyp:X) includes each element
independently with [probability r](hyp:r), clamped to the unit interval.
@realizes \mu_r(independent Bernoulli subset law; clamp inactive for r in [0,1]) -/
noncomputable def productMeasure (X : Type) [Fintype X] [DecidableEq X] (r : ℝ) :=
  Toolkit.Foundations.Probability.bernoulliCube X r

/-- The [mass of a subset family](goal) is the probability that an independent random subset of
[the finite ground set X](hyp:X), with [inclusion parameter r](hyp:r) clamped to the unit interval,
belongs to [the family D](hyp:D).
@realizes \Prob(finite-design probability of the specified event)
@realizes \calD(arbitrary family of finite subsets) -/
noncomputable def muMass (X : Type) [Fintype X] [DecidableEq X]
    (r : ℝ) (D : Set (Finset X)) : ℝ := by
  classical
  exact (productMeasure X r).Pr (fun z => toFinset' z ∈ D)

-- @node: ass:finite-simple
/-- The [finite-vertex condition](goal) says that [the vertex set V](hyp:V) is finite. -/
def FiniteSimpleGraphs (V : Type) : Prop := Finite V

-- @node: def:copy-convention
/-- For [a target graph J](hyp:J) on [vertices V](hyp:V) and [a host graph G](hyp:G)
on [vertices W](hyp:W), [copy containment](goal) means that the host contains an injective,
edge-preserving copy of the target; extra host edges are allowed. -/
def ContainsCopy (J : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  J.IsContained G -- @realizes J(simple graph on its vertex carrier V)

-- @node: def:random-host
/-- The [random host law](goal) on [n labelled vertices](hyp:n) selects every possible edge
independently with [probability p](hyp:p), where [p lies between zero and one](hyp:_hp).
@realizes G(n,p)(independent Bernoulli-p edges on the complete labelled host)
@realizes p(real density constrained by the unit-interval argument) -/
noncomputable def randomHost (n : ℕ) (p : ℝ)
    (_hp : p ∈ Set.Icc 0 1) : FiniteDesign (KEdge n → Bool) :=
  Toolkit.Foundations.Probability.bernoulliCube (KEdge n) p

/-- The [host graph](goal) on [n labelled vertices](hyp:n) has exactly the edges marked true
by [the Boolean edge assignment z](hyp:z).
@realizes G(labelled simple graph with the indicated edge set) -/
def hostGraph {n : ℕ} (z : KEdge n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬ e.IsDiag, z ⟨e, h⟩ = true}

/-- The [graph associated with an edge set](goal) on [n labelled vertices](hyp:n) has exactly
the edges in [the finite set G](hyp:G). -/
def graphOfEdges {n : ℕ} (G : Finset (KEdge n)) : SimpleGraph (Fin n) :=
  hostGraph (fun e => decide (e ∈ G))

/-- The [containment probability](goal) is the probability that an independent random graph on
[n labelled vertices](hyp:n), with [edge parameter p](hyp:p) clamped to the unit interval,
contains a copy of [the target graph J](hyp:J) on [vertices V](hyp:V).

Continuous real-parameter extension of the containment probability. On `[0,1]`
this is definitionally the probability under `randomHost n p hp`. -/
noncomputable def containmentProb (J : SimpleGraph V) (n : ℕ) (p : ℝ) : ℝ := by
  classical
  exact (productMeasure (KEdge n) p).Pr (fun z => ContainsCopy J (hostGraph z))

-- @node: def:containment-threshold
/-- The [raw containment threshold](goal) for [a target graph J](hyp:J) on [vertices V](hyp:V)
in [a host of order n](hyp:n) is the infimum of edge probabilities between zero and one
for which the probability of containing a copy is at least one half.

The printed minimum; attainment on graphs with at most n vertices is a local lemma. -/
noncomputable def containmentThresholdRaw (J : SimpleGraph V) (n : ℕ) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ -- @realizes p(unit-interval edge density)
    (1 / 2 : ℝ) ≤ containmentProb J n p}

-- @node: def:containment-edgeless
/-- The [containment threshold](goal) for [a target graph J](hyp:J) on [vertices V](hyp:V)
in [a host of order n](hyp:n) is [zero if the target has no edges](step:1),
and [its raw containment threshold otherwise](step:2).
@realizes p_c(containment threshold, set to zero for edgeless graphs) -/
noncomputable def containmentThreshold (J : SimpleGraph V) (n : ℕ) : ℝ := by
  classical
  exact if J.edgeSet = ∅ then 0 else containmentThresholdRaw J n

-- @node: def:containment-family
/-- The [containment family](goal) for [a graph H](hyp:H) on [vertices V](hyp:V)
in [a host of order n](hyp:n) consists of the host edge sets whose graphs contain a copy of H,
allowing extra edges among the copied vertices.
@realizes \calF_H(edge subsets whose graphs contain a non-induced copy of H) -/
def containmentFamily (H : SimpleGraph V) (n : ℕ) : Set (Finset (KEdge n)) :=
  {G | ContainsCopy H (graphOfEdges G)}

-- @node: def:cover
/-- On [the finite ground set X](hyp:X), [the covering relation](goal) between
[a finite family C](hyp:C) and [a subset family F](hyp:F) means that every member of F
contains at least one member of C.
@realizes \mathcal C(finite family covering every member of the specified family)
@realizes A(member of the family being covered, quantified in the covering relation) -/
def Covers (C : Finset (Finset X)) (F : Set (Finset X)) : Prop :=
  ∀ A ∈ F, ∃ S ∈ C, S ⊆ A

/-- For [a finite family C of subsets](hyp:C) of [the ground set X](hyp:X) and
[a real parameter p](hyp:p), the [cover polynomial](goal) sums p raised to the cardinality
of each member of C. -/
def coverPolynomial (C : Finset (Finset X)) (p : ℝ) : ℝ := ∑ S ∈ C, p ^ S.card

-- @node: def:cover-cost
/-- For [a finite family C of subsets](hyp:C) of [the ground set X](hyp:X),
the [cover cost](goal) sums [the density p](hyp:p) raised to each member's cardinality,
with [p certified to lie between zero and one](hyp:_hp).
@realizes c_p(sum of nonnegative powers at a unit-interval density)
@realizes p(cover-cost density constrained to the closed unit interval) -/
def coverCost (C : Finset (Finset X)) (p : ℝ) (_hp : p ∈ Set.Icc 0 1) : ℝ :=
  coverPolynomial C p

/-- For [a finite family C of subsets](hyp:C) and [a density p](hyp:p),
if [p lies between zero and one](hyp:hp), then [the cover cost is nonnegative](goal).
@realizes c_p(nonnegative on its certified unit-interval domain) -/
lemma coverCost_nonneg (C : Finset (Finset X)) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    0 ≤ coverCost C p hp := by
  exact Finset.sum_nonneg (fun S _ => pow_nonneg hp.1 S.card)

-- @node: def:general-cover-cost
/-- On [the finite ground set X](hyp:X), [the existence of a cover of bounded cost](goal)
for [a subset family F](hyp:F), at [density r](hyp:r) and [cost bound c](hyp:c),
means there is a finite family that [covers F](step:1) and for which
[r lies between zero and one and the cover cost at r is at most c](step:2). -/
def HasCoverOfCostLe (F : Set (Finset X)) (r c : ℝ) : Prop :=
  ∃ C : Finset (Finset X), Covers C F ∧
    ∃ hr : r ∈ Set.Icc 0 1, coverCost C r hr ≤ c

-- @node: def:q-definition
/-- The [raw integral expectation threshold](goal) for [a graph H](hyp:H) on [vertices V](hyp:V)
in [a host of order n](hyp:n) is the supremum of densities between zero and one
at which its containment family has a finite cover of cost at most one half.

The printed maximum; finite-domain attainment is proved locally, not assumed. -/
noncomputable def expectationThresholdRaw (H : SimpleGraph V) (n : ℕ) : ℝ :=
  sSup {p : ℝ | p ∈ Set.Icc 0 1 ∧ HasCoverOfCostLe (containmentFamily H n) p (1 / 2)}

-- @node: def:q-edgeless
/-- The [integral expectation threshold](goal) for [a graph H](hyp:H) on [vertices V](hyp:V)
in [a host of order n](hyp:n) is [zero if H has no edges](step:1) and
[its raw integral expectation threshold otherwise](step:2).
@realizes q(integral expectation threshold, zero on edgeless targets) -/
noncomputable def expectationThreshold (H : SimpleGraph V) (n : ℕ) : ℝ := by
  classical
  exact if H.edgeSet = ∅ then 0 else expectationThresholdRaw H n

-- @node: def:discrete-k0
/-- The [absolute integer K₀](goal) is two raised to the seventy-fifth power.
@realizes K_0(absolute integer 2^75) -/
def K0 : ℕ := 2 ^ 75

-- @node: ass:pin-1
/-- On [the finite ground set X](hyp:X), for [a subset S](hyp:S), [a member count K](hyp:K),
and [a family D](hyp:D), [coverage by K family members](goal) means that there is a tuple
of K subsets such that [every entry belongs to D](step:1) and [their union contains S](step:2),
with repeated entries allowed. -/
def CoveredByMembers (K : ℕ) (D : Set (Finset X)) (S : Finset X) : Prop :=
  ∃ t : Fin K → Finset X, (∀ i, t i ∈ D) ∧ S ⊆ Finset.univ.biUnion t

/-- On [the finite ground set X](hyp:X), the [exceptional family](goal) for
[a subset family D](hyp:D) and [a member count K](hyp:K) consists of the subsets
that cannot be covered by a union of K members of D, with repetition allowed.
@realizes \mathcal E_{K_0}(\calD)(exceptional sets for possibly repeated unions) -/
def exceptionalFamily (K : ℕ) (D : Set (Finset X)) : Set (Finset X) :=
  {S | ¬ CoveredByMembers K D S}

-- @node: ass:discrete-ground
/-- The [discrete ground-set condition](goal) requires [the finite ground set X](hyp:X)
to have at least one element. -/
def DiscreteGround (X : Type) [Fintype X] : Prop :=
  Nonempty X -- @realizes X(nonempty in the discrete-convexity input)

-- @node: ass:discrete-density
/-- The [discrete density condition](goal) requires [the real parameter r](hyp:r)
to be [strictly positive](step:1) and [strictly less than one](step:2).
@realizes r(open-unit-interval product parameter) -/
def DiscreteDensity (r : ℝ) : Prop := 0 < r ∧ r < 1

-- @node: ass:discrete-mass
/-- The [discrete mass condition](goal) for [a family D of subsets](hyp:D) of
[the finite ground set X](hyp:X), at [inclusion parameter r](hyp:r), requires its
independent-subset probability to be at least one minus the reciprocal of K₀. -/
def DiscreteMass (X : Type) [Fintype X] [DecidableEq X]
    (r : ℝ) (D : Set (Finset X)) : Prop :=
  1 - 1 / (K0 : ℝ) ≤ muMass X r D -- @realizes \calD(required high mass)

-- @node: thm:discrete
/-- The [discrete convexity cover assertion](goal) says that, on every nonempty finite ground set,
at any density strictly between zero and one, any subset family of probability at least
one minus the reciprocal of K₀ has the following property: the subsets not covered by
unions of K₀ family members admit a finite cover of cost at most one half at that density.

OpenAI (2026), *Talagrand's discrete-convexity conjecture*, Theorem 1.1,
handle `cite:openai26dc` / `OpenAI26DC`. Source: retained introduction, equation (1.1)
and Theorem 1.1, from
https://github.com/openai/math/blob/main/preprints/Talagrands-discrete-convexity-conjecture-September-23-2026/build/source/sections/00_intro.tex .
The labelled finite-set statement transports along a bijection to any nonempty finite X.
No monotonicity is required, and tuple members may repeat. This is the sole logical gate. -/
def DiscreteConvexityCover : Sort 0 :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (r : ℝ) (D : Set (Finset X)),
    DiscreteGround X → DiscreteDensity r → DiscreteMass X r D →
    HasCoverOfCostLe (exceptionalFamily K0 D) r (1 / 2)

-- @node: def:nonisolated
/-- The [nonisolated vertices](goal) of [a graph J](hyp:J) on [the finite vertex set V](hyp:V)
are the vertices with positive degree.
@realizes V_+(vertices of positive degree)
@realizes \deg_J(degree of a locally bound vertex v)
@realizes v(vertex of the finite graph) -/
def nonisolated (J : SimpleGraph V) [DecidableRel J.Adj] : Finset V :=
  Finset.univ.filter (fun v => 0 < J.degree v)

-- @node: def:degeneracy
/-- The [degeneracy](goal) of [a graph H](hyp:H) on [the finite vertex set V](hyp:V)
is the largest minimum degree among its induced subgraphs on nonempty vertex subsets,
with value zero when there are no such subsets.
@realizes \degen(maximum minimum degree over nonempty induced vertex subsets;
adding available edges can only increase minimum degree) -/
noncomputable def degeneracy (H : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S : Finset V => S.Nonempty)).sup
    (fun S => (H.induce (S : Set V)).minDegree)

-- @node: def:q-lower-d
/-- For [a graph H](hyp:H) on [the finite vertex set V](hyp:V), the [degeneracy parameter
used in the expectation-threshold lower bound](goal) is the degeneracy of H.
@realizes d(degeneracy of the graph in the lower bound) -/
noncomputable def qLowerDegeneracy (H : SimpleGraph V) : ℕ := degeneracy H

-- @node: def:satisfaction
/-- On [the ground set Y](hyp:Y), [satisfaction](goal) of [a finite requirement family Q](hyp:Q)
by [a subset S](hyp:S) means that S contains at least one member of Q.
@realizes \calQ(requirement family of finite subsets)
@realizes T(requirement member contained in S) -/
def Satisfies (Q : Finset (Finset Y)) (S : Finset Y) : Prop := ∃ T ∈ Q, T ⊆ S

-- @node: def:smoothed-test
/-- On [the finite ground set Y](hyp:Y), the [smoothed test value](goal) for
[a requirement family Q](hyp:Q) and [an initial subset S](hyp:S) is the probability
that S contains a requirement after adjoining an independent random subset with
[inclusion parameter r](hyp:r) clamped to the unit interval.
@realizes f_{\calQ}(probability of satisfaction after an independent Bernoulli-r extension)
@realizes Z(independent Bernoulli-r subset of Y) -/
noncomputable def smoothedTest (Y : Type) [Fintype Y] [DecidableEq Y]
    (r : ℝ) (Q : Finset (Finset Y)) (S : Finset Y) : ℝ := by
  classical
  exact (productMeasure Y r).Pr (fun z => Satisfies Q (S ∪ toFinset' z))

-- @node: def:natural-logarithms
/-- The [natural logarithm function](goal) is the real natural logarithm, with value zero
at zero and the logarithm of the absolute value at negative arguments.
@realizes \log(natural logarithm reused from Mathlib) -/
noncomputable def naturalLog : ℝ → ℝ := Real.log

-- @node: def:stars-a
/-- The [absolute star constant A](goal) is 400 times the exponential of four.
@realizes A(positive absolute star constant 400 exp(4)) -/
noncomputable def starConstA : ℝ := 400 * Real.exp 4

-- @node: ass:star-forest-components
/-- For [a graph J](hyp:J) on [vertices V](hyp:V), [the star-component property](goal)
means that every connected component with at least two vertices has a center,
and two vertices in that component are adjacent exactly when they are distinct
and one of them is the center. -/
def NontrivialComponentsAreStars (J : SimpleGraph V) : Prop :=
  ∀ C : J.ConnectedComponent, C.supp.Nontrivial →
    ∃ c ∈ C.supp, ∀ u ∈ C.supp, ∀ w ∈ C.supp,
      J.Adj u w ↔ u ≠ w ∧ (u = c ∨ w = c)

-- @node: def:star-forest
/-- A [star forest](goal) is [a graph J](hyp:J) on [vertices V](hyp:V) whose
[connected components with at least two vertices are stars](step:1). -/
structure IsStarForest (J : SimpleGraph V) : Prop where
  components : NontrivialComponentsAreStars J -- @realizes J(star-forest component property)

-- @node: ass:main-order
/-- The [main host-order condition](goal) requires [the host order n](hyp:n) to be at least two. -/
def MainOrder (n : ℕ) : Prop := 2 ≤ n -- @realizes n(main order at least two)

-- @node: ass:main-graph
/-- The [main graph-size condition](goal) requires [the finite vertex set V](hyp:V)
to have at most [n vertices](hyp:n). -/
def MainGraphSize (V : Type) [Fintype V] (n : ℕ) : Prop :=
  Fintype.card V ≤ n -- @realizes H(vertex count at most n)

-- @node: ass:typical-cover-order
/-- The [typical-cover host-order condition](goal) requires [the number n of host vertices](hyp:n)
to be at least two. -/
def TypicalCoverOrder (n : ℕ) : Prop := 2 ≤ n

-- @node: ass:typical-cover-graph
/-- For [a graph H](hyp:H) on [the finite vertex set V](hyp:V) and [a host order n](hyp:n),
the [typical-cover graph condition](goal) requires that [H have at least one edge](step:1)
and that [V contain at most n vertices](step:2). -/
def TypicalCoverGraph (H : SimpleGraph V) (n : ℕ) : Prop :=
  H.edgeSet.Nonempty ∧ -- @realizes H(has an edge in typical_cover)
  Fintype.card V ≤ n -- @realizes H(at most n vertices in typical_cover)

-- @node: ass:typical-cover-density
/-- For [a graph H](hyp:H) on [the finite vertex set V](hyp:V), [a host order n](hyp:n),
and [a density r](hyp:r), the [typical-cover density condition](goal) requires that
[r exceed the integral expectation threshold of H in an n-vertex host](step:1)
and that [r be less than one](step:2). -/
def TypicalCoverDensity (H : SimpleGraph V) (n : ℕ) (r : ℝ) : Prop :=
  expectationThreshold H n < r ∧ -- @realizes r(above q(H;n) in typical_cover)
  r < 1 -- @realizes r(below one in typical_cover)

-- @node: ass:typical-cover-mass
/-- For [a host order n](hyp:n), [an inclusion parameter r](hyp:r), and
[a family D of host edge sets](hyp:D), the [typical-cover mass condition](goal)
requires D to have probability at least one minus the reciprocal of K₀ under independent
edge selection with parameter r clamped to the unit interval. -/
def TypicalCoverMass (n : ℕ) (r : ℝ) (D : Set (Finset (KEdge n))) : Prop :=
  1 - 1 / (K0 : ℝ) ≤ muMass (KEdge n) r D

-- @node: ass:q-lower-edge
/-- For [a graph H](hyp:H) on [the vertex set V](hyp:V), the
[edge condition for the expectation-threshold lower bound](goal) requires H to have an edge. -/
def QLowerEdge (H : SimpleGraph V) : Prop := H.edgeSet.Nonempty

-- @node: ass:q-lower-order
/-- The [host-order condition for the expectation-threshold lower bound](goal) requires
[the finite vertex set V](hyp:V) to have at most [n vertices](hyp:n). -/
def QLowerOrder (V : Type) [Fintype V] (n : ℕ) : Prop := Fintype.card V ≤ n

-- @node: ass:split-count
/-- The [split-count condition](goal) requires [the integer number m of pieces](hyp:m)
to be strictly positive.
@realizes m(positive integral piece count) -/
def SplitCount (m : ℕ) : Prop := 0 < m

-- @node: ass:split-degeneracy
/-- For [a graph H](hyp:H) on [the finite vertex set V](hyp:V) and
[an integer bound d](hyp:d), the [split-degeneracy condition](goal) requires
the degeneracy of H to be at most d. -/
def SplitDegeneracy (H : SimpleGraph V) (d : ℕ) : Prop := degeneracy H ≤ d

-- @node: ass:compression-ground
/-- The [compression ground-set condition](goal) requires [the ground set Y](hyp:Y) to be finite. -/
def CompressionGround (Y : Type) : Prop := Finite Y

-- @node: ass:compression-density
/-- The [compression density condition](goal) requires [the real density r](hyp:r)
to be [strictly positive](step:1) and [strictly less than one](step:2). -/
def CompressionDensity (r : ℝ) : Prop := 0 < r ∧ r < 1

-- @node: ass:compression-size
/-- The [compression size condition](goal) requires [the integer requirement-size bound s](hyp:s)
to be at least one.
@realizes s(positive integer requirement-size bound in compression) -/
def CompressionSize (s : ℕ) : Prop := 1 ≤ s

-- @node: ass:compression-family
/-- For [a finite family R of requirements](hyp:R) on [the ground set Y](hyp:Y) and
[an integer size bound s](hyp:s), the [compression family condition](goal) requires
[R to be nonempty](step:1) and [every requirement in R to have between one and s elements,
inclusive](step:2).
@realizes \calR(nonempty family with requirement sizes between 1 and s) -/
def CompressionFamily (R : Finset (Finset Y)) (s : ℕ) : Prop :=
  R.Nonempty ∧ ∀ T ∈ R, 1 ≤ T.card ∧ T.card ≤ s

-- @node: ass:parameters
/-- For [a host order n](hyp:n), [a real density r](hyp:r), and [an integer size bound s](hyp:s),
the [transfer parameter condition](goal) requires that [r be positive](step:1),
[r be less than one](step:2), [s be at most ten times the natural logarithm of n](step:3),
and [r raised to s be at least n raised to minus one hundredth](step:4). -/
def TransferParameters (n : ℕ) (r : ℝ) (s : ℕ) : Prop :=
  0 < r ∧ r < 1 ∧ -- @realizes r(open-unit-interval source density)
  (s : ℝ) ≤ 10 * naturalLog n ∧ -- @realizes s(natural size bound at most 10 log n)
  (n : ℝ) ^ (-(1 : ℝ) / 100) ≤ r ^ s -- @realizes s(power constraint in the parameter regime)

-- @node: ass:transfer-order
/-- For [a minimum host order N₁](hyp:N₁) and [an actual host order n](hyp:n),
the [transfer order condition](goal) requires n to be at least N₁. -/
def TransferOrder (N₁ n : ℕ) : Prop := N₁ ≤ n

-- @node: ass:transfer-configuration
/-- For [a host order n](hyp:n), [an integer degree bound s](hyp:s),
[a family D of host edge sets](hyp:D), [a set Y of host vertices](hyp:Y), and
[a graph J on the host vertices](hyp:J), the [transfer configuration condition](goal)
requires that [Y have at most n to the two-thirds power vertices](step:1),
[every edge of J join Y to its complement](step:2),
[some edge set in D contain every edge of J](step:3),
[at most n divided by eight vertices outside Y have positive degree in J](step:4),
and [every vertex outside Y have degree at most s in J](step:5). -/
def TransferConfiguration (n s : ℕ) (D : Set (Finset (KEdge n)))
    (Y : Finset (Fin n)) (J : SimpleGraph (Fin n)) [DecidableRel J.Adj] : Prop :=
  (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) ∧ -- @realizes Y(card≤n^(2/3))
  (∀ u v, J.Adj u v → (u ∈ Y ∧ v ∉ Y) ∨ (v ∈ Y ∧ u ∉ Y)) ∧
  (∃ G ∈ D, J ≤ graphOfEdges G) ∧ -- @realizes G(source witness in D containing J)
  (((Finset.univ \ Y).filter (fun w => 0 < J.degree w)).card : ℝ) ≤ (n : ℝ) / 8 ∧
  ∀ w ∉ Y, J.degree w ≤ s

-- @node: ass:degree-embedding-order
/-- For [a minimum host order N₂](hyp:N₂) and [an actual host order n](hyp:n),
the [degree-embedding order condition](goal) requires n to be at least N₂. -/
def DegreeEmbeddingOrder (N₂ n : ℕ) : Prop := N₂ ≤ n

-- @node: ass:degree-embedding-bounds
/-- For [a graph J](hyp:J) on [the finite vertex set V](hyp:V), [a host order n](hyp:n),
and [an integer degeneracy bound s](hyp:s), the [degree-embedding bounds](goal) require
[at most n divided by four vertices of J to have positive degree](step:1),
[the degeneracy of J to be at most s](step:2), and
[the maximum degree of J to be at most n to the two-thirds power](step:3). -/
def DegreeEmbeddingBounds (J : SimpleGraph V) [DecidableRel J.Adj] (n s : ℕ) : Prop :=
  ((nonisolated J).card : ℝ) ≤ (n : ℝ) / 4 ∧ -- @realizes V_+(support bound n/4)
  degeneracy J ≤ s ∧ -- @realizes J(degeneracy at most s)
  (J.maxDegree : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) -- @realizes \Delta(max degree≤n^(2/3))

-- @node: ass:degree-embedding-size
/-- The [degree-embedding size condition](goal) requires [the finite vertex set V](hyp:V)
to have at most [n vertices](hyp:n). -/
def DegreeEmbeddingSize (V : Type) [Fintype V] (n : ℕ) : Prop := Fintype.card V ≤ n

-- @node: ass:stars-order
/-- For [a minimum host order N₃](hyp:N₃) and [an actual host order n](hyp:n),
the [star-forest order condition](goal) requires n to be at least N₃. -/
def StarsOrder (N₃ n : ℕ) : Prop := N₃ ≤ n

-- @node: ass:stars-size
/-- The [star-forest size condition](goal) requires [the finite vertex set V](hyp:V)
to have at most [n vertices](hyp:n). -/
def StarsSize (V : Type) [Fintype V] (n : ℕ) : Prop := Fintype.card V ≤ n

-- @node: ass:stars-support
/-- For [a graph J](hyp:J) on [the finite vertex set V](hyp:V) and [a host order n](hyp:n),
the [star-forest support condition](goal) requires at most n divided by one hundred
vertices of J to have positive degree. -/
def StarsSupport (J : SimpleGraph V) [DecidableRel J.Adj] (n : ℕ) : Prop :=
  ((nonisolated J).card : ℝ) ≤ (n : ℝ) / 100 -- @realizes V_+(star support bound n/100)

-- @node: ass:stars-small-q
/-- For [a graph J](hyp:J) on [the finite vertex set V](hyp:V) and [a host order n](hyp:n),
the [small expectation-threshold condition for star forests](goal) requires the integral
expectation threshold of J in an n-vertex host to be less than the reciprocal of twice
the absolute star constant A. -/
def StarsSmallQ (J : SimpleGraph V) (n : ℕ) : Prop :=
  expectationThreshold J n < 1 / (2 * starConstA)

/-- For [a graph H](hyp:H) on [the finite vertex set V](hyp:V), [a host order n](hyp:n),
and [an injective assignment f of these vertices to host labels](hyp:f),
the [edges of the labelled copy](goal) are the host edges obtained by applying f
to the endpoints of each edge of H. -/
noncomputable def copyEdges (H : SimpleGraph V) {n : ℕ} (f : V ↪ Fin n) :
    Finset (KEdge n) := by
  classical
  exact Finset.univ.filter (fun e => e.val ∈ (H.map f).edgeSet)

end Papers.OaiGraphDecompositionsIntegral
