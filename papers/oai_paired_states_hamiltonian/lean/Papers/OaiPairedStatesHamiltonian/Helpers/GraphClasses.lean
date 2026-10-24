module

public import Papers.OaiPairedStatesHamiltonian.Helpers.Forests
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-! Finite graph domains, vertex connectivity, Pfaffian orientations and P4-Hamiltonicity. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


-- @env: S3
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  -- @realizes G(finite simple undirected graph)

/-- A [finite simple graph](hyp:G) is [planar](goal) if there exists a sphere map
[with no loops or parallel edges](step:1) [whose underlying simple graph is isomorphic to it](step:2).

Disconnected maps and isolated vertices are allowed. -/
noncomputable def IsPlanar : Prop := ∃ M : SphereMap, M.IsSimple ∧ Nonempty (M.toSimpleGraph ≃g G)

/-- For a [finite simple graph](hyp:G) and a [natural-number connectivity level](hyp:k),
[vertex connectivity at that level](goal) requires [strictly more vertices than the level](step:1)
and [connectedness after deleting any set of fewer vertices than the level](step:2). -/
noncomputable def IsVertexConnected (k : ℕ) : Prop :=
  k < Fintype.card V ∧ -- @realizes G(at least four vertices for k = 3)
  ∀ S : Finset V, S.card < k → (G.induce {v | v ∉ S}).Connected
    -- @realizes G(connectivity after deletion of every at most two vertices for k = 3)

-- @node: ass:main-domain
/-- A [finite simple graph](hyp:G) belongs to the [main graph domain](goal) when it is
[regular of degree three](step:1), [colorable with two colors](step:2), [planar](step:3),
and [three-vertex-connected](step:4). -/
noncomputable def MainDomain [DecidableRel G.Adj] : Prop :=
  G.IsRegularOfDegree 3 ∧ -- @realizes G(cubic)
  G.Colorable 2 ∧ -- @realizes G(bipartite)
  IsPlanar G ∧ -- @realizes G(planar, including disconnected planar graphs in this predicate)
  IsVertexConnected G 3 -- @realizes G(three-vertex-connected)
-- @node: ass:edge-avoidance-domain
/-- For a [finite simple graph](hyp:G) and a [prescribed unordered vertex pair](hyp:e),
the [edge-avoidance domain condition](goal) requires [that the graph be cubic, bipartite,
planar, and three-vertex-connected](step:1) and [that the prescribed pair be an edge](step:2). -/
noncomputable def EdgeAvoidanceDomain [DecidableRel G.Adj] (e : Sym2 V) : Prop :=
  MainDomain G ∧ e ∈ G.edgeSet -- @realizes e(prescribed edge of G)
-- @node: ass:pin-2
/-- For a [finite simple graph](hyp:G) and a [prescribed unordered vertex pair](hyp:e),
the [pinned edge-avoidance condition](goal) requires [a cubic, bipartite, planar,
three-vertex-connected graph](step:1) and [membership of the prescribed pair in its edge set](step:2). -/
noncomputable def EdgeAvoidancePinned [DecidableRel G.Adj] (e : Sym2 V) : Prop := MainDomain G ∧ e ∈ G.edgeSet

-- @env: S4
variable (o : V → V → Prop)

-- @node: ass:pfaffian-orientation
/-- For a [finite simple graph](hyp:G), the [Pfaffian orientation condition](goal) requires
an orientation such that [each edge is oriented in exactly one direction](step:1) and
[every even simple cycle whose vertex deletion leaves a graph with a perfect matching has an
odd number of darts agreeing with the orientation](step:2). -/
noncomputable def PfaffianOrientationCondition : Prop :=
  ∃ o : V → V → Prop,
    (∀ u v, G.Adj u v → (o u v ↔ ¬ o v u)) ∧
    ∀ v (C : G.Walk v v), C.IsCycle → Even C.length →
      (∃ M : (G.induce {w | w ∉ C.support}).Subgraph, M.IsPerfectMatching) →
        Odd (C.darts.filter (fun d => o d.fst d.snd)).length
        -- @realizes C(even cycle; the matching is on the vertices outside its support)
-- @node: def:pfaffian
/-- A [finite simple graph](hyp:G) is [Pfaffian](goal) when it admits an edge orientation
for which every even simple cycle whose vertex deletion permits a perfect matching has an odd
number of darts agreeing with the orientation. -/
structure IsPfaffian : Prop where
  orientation : PfaffianOrientationCondition G -- @realizes G(admits a Pfaffian edge orientation)
-- @node: ass:pfaffian-paths-graph
/-- A [finite simple graph](hyp:G) satisfies the [Pfaffian paths graph condition](goal)
when it is [regular of degree three](step:1), [three-vertex-connected](step:2), and
[Pfaffian](step:3). -/
noncomputable def PfaffianPathsGraph [DecidableRel G.Adj] : Prop :=
  G.IsRegularOfDegree 3 ∧ -- @realizes G(cubic in the Pfaffian corollary)
  IsVertexConnected G 3 ∧ -- @realizes G(three-vertex-connected in the Pfaffian corollary)
  Nonempty (IsPfaffian G) -- @realizes G(Pfaffian; planarity is unrestricted)
-- @node: ass:pfaffian-paths-bipartite
/-- For a [finite simple graph](hyp:G), the [bipartite condition for Pfaffian paths](goal)
means that the vertices admit a proper coloring with two colors. -/
noncomputable def PfaffianPathsBipartite : Prop := G.Colorable 2 -- @realizes G(bipartite in the Pfaffian corollary)

/-- A [finite simple graph](hyp:G) is [P4-Hamiltonian](goal) if every simple path of length
three has all three of its edges contained in some Hamiltonian cycle. -/
noncomputable def IsP4Hamiltonian : Prop :=
  ∀ u v (p : G.Walk u v), p.IsPath → p.length = 3 →
    ∃ a, ∃ C : G.Walk a a, C.IsHamiltonianCycle ∧ ∀ e ∈ p.edges, e ∈ C.edges
    -- @realizes P_4(path on four vertices, all three edges contained in the cycle)


end OaiPairedStatesHamiltonian
