module

public import Papers.OaiPairedStatesHamiltonian.Helpers.TreeBranches
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite sphere maps with explicit vertices, darts, and edge identities. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


/-- For [a permutation of a set](hyp:p), the [type of its orbits](goal) identifies two
elements exactly when they lie in the same cycle. -/
abbrev orbitType {D : Type} (p : Equiv.Perm D) := Quotient (Equiv.Perm.SameCycle.setoid p)

/-- For [a permutation](hyp:p) and [an element of its underlying set](hyp:d), the
[orbit containing that element](goal) is its equivalence class under membership in the same cycle. -/
noncomputable def orbitOf {D : Type} (p : Equiv.Perm D) (d : D) : orbitType p := Quotient.mk _ d

/-- Rotation data retain vertices even when their dart fibre is empty. -/
structure RotationSystem where
  Vertex : Type -- @realizes V(explicit finite vertices, including isolated vertices)
  Dart : Type -- @realizes E(two distinct darts per edge)
  [vertexFintype : Fintype Vertex]
  [dartFintype : Fintype Dart]
  [vertexDecidableEq : DecidableEq Vertex]
  [dartDecidableEq : DecidableEq Dart]
  vert : Dart → Vertex -- @realizes v(vertex at the tail of an edge-side dart)
  edgeInv : Equiv.Perm Dart
  edgeInv_involutive : Function.Involutive edgeInv
  edgeInv_fixedPointFree : ∀ d, edgeInv d ≠ d
  rot : Equiv.Perm Dart
  rot_vertex : ∀ d, vert (rot d) = vert d
  rot_fibre : ∀ v, rot.IsCycleOn {d | vert d = v}

attribute [instance] RotationSystem.vertexFintype RotationSystem.dartFintype
  RotationSystem.vertexDecidableEq RotationSystem.dartDecidableEq

namespace RotationSystem
variable (R : RotationSystem)
/-- For [a rotation system](hyp:R), the [edge type](goal) consists of orbits of the
operation that reverses a dart, so the two directions of an edge represent one edge. -/
abbrev Edge := orbitType R.edgeInv
/-- For [a rotation system](hyp:R), the [face permutation](goal) first reverses a dart
along its edge and then applies the rotation at the resulting vertex. -/
noncomputable def facePerm : Equiv.Perm R.Dart := R.rot * R.edgeInv
/-- For [a rotation system](hyp:R), the [type of facial orbits](goal) consists of the
cycles of the face permutation. -/
abbrev FaceOrbit := orbitType R.facePerm
/-- For [a rotation system](hyp:R), the [type of punctures](goal) consists of vertices
that are not the tail of any dart, namely the isolated vertices. -/
abbrev Puncture := {v : R.Vertex // ∀ d, R.vert d ≠ v}
/-- For [a rotation system](hyp:R), the [type of local boundaries](goal) includes
both facial orbits and punctures at isolated vertices. -/
abbrev LocalBoundary := R.FaceOrbit ⊕ R.Puncture
/-- In [a rotation system](hyp:R), the [edge represented by](goal)
[a dart](hyp:d) is its orbit under reversal along an edge. -/
noncomputable def edgeOf (d : R.Dart) : R.Edge := orbitOf R.edgeInv d
/-- In [a rotation system](hyp:R), the [head vertex of](goal) [a dart](hyp:d) is the
tail vertex of the reversed dart. -/
noncomputable def head (d : R.Dart) : R.Vertex := R.vert (R.edgeInv d)

-- @node: RotationSystem.adjacency_symm
/-- In a rotation system, for [vertices u and v](hyp:u,v),
[if u and v are distinct and a dart goes from u to v, then they are distinct in the
reverse order and a dart goes from v to u](goal). -/
lemma adjacency_symm (u v : R.Vertex) :
    (u ≠ v ∧ ∃ d, R.vert d = u ∧ R.head d = v) →
      (v ≠ u ∧ ∃ d, R.vert d = v ∧ R.head d = u) := by
  rintro ⟨hne, d, hd, he⟩
  refine ⟨hne.symm, R.edgeInv d, he, ?_⟩
  simpa [head, R.edgeInv_involutive d] using hd

/-- For [a rotation system](hyp:R), the [underlying simple graph](goal) has the same
vertices, with two vertices adjacent exactly when they are distinct and a dart joins them. -/
noncomputable def toSimpleGraph : SimpleGraph R.Vertex where
  Adj u v := u ≠ v ∧ ∃ d, R.vert d = u ∧ R.head d = v
  symm := ⟨fun u v h => R.adjacency_symm u v h⟩
  loopless := ⟨fun v h => h.1 rfl⟩

/-- For [a rotation system](hyp:R), the [type of connected components](goal) groups
vertices according to connectivity in the underlying simple graph. -/
abbrev Component := R.toSimpleGraph.ConnectedComponent
/-- For [a rotation system](hyp:R), [its connected components admit a finite enumeration](goal). -/
noncomputable instance : Fintype R.Component := Fintype.ofFinite _
/-- For [a rotation system](hyp:R), [equality of connected components is decidable](goal). -/
noncomputable instance : DecidableEq R.Component := Classical.decEq _
/-- For [a rotation system](hyp:R), [its edges admit a finite enumeration](goal). -/
noncomputable instance : Fintype R.Edge := Fintype.ofFinite _
/-- For [a rotation system](hyp:R), [equality of edges is decidable](goal). -/
noncomputable instance : DecidableEq R.Edge := Classical.decEq _
/-- For [a rotation system](hyp:R), [its facial orbits admit a finite enumeration](goal). -/
noncomputable instance : Fintype R.FaceOrbit := Fintype.ofFinite _
/-- For [a rotation system](hyp:R), [equality of facial orbits is decidable](goal). -/
noncomputable instance : DecidableEq R.FaceOrbit := Classical.decEq _

-- @node: RotationSystem.dart_component_eq_head
/-- In a rotation system, [a dart](hyp:d) has
[its tail and head in the same connected component](goal), including when the edge is a loop. -/
lemma dart_component_eq_head (d : R.Dart) :
    R.toSimpleGraph.connectedComponentMk (R.vert d) =
      R.toSimpleGraph.connectedComponentMk (R.head d) := by
  by_cases h : R.vert d = R.head d
  · exact congrArg R.toSimpleGraph.connectedComponentMk h
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := R.toSimpleGraph) ⟨h, d, rfl, rfl⟩

-- @node: RotationSystem.boundary_component_wellDefined
/-- In a rotation system, if [two darts](hyp:d,e)
[belong to the same cycle of the face permutation](hyp:h), then
[their tail vertices lie in the same connected component](goal). -/
lemma boundary_component_wellDefined (d e : R.Dart) (h : R.facePerm.SameCycle d e) :
    R.toSimpleGraph.connectedComponentMk (R.vert d) =
      R.toSimpleGraph.connectedComponentMk (R.vert e) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (by
      simpa only [facePerm, Equiv.Perm.mul_apply, R.rot_vertex, head] using
        R.dart_component_eq_head ((R.facePerm ^ n) d))

-- @node: RotationSystem.edge_component_wellDefined
/-- In a rotation system, if [two darts](hyp:d,e)
[belong to the same orbit under edge reversal](hyp:h), then
[their tail vertices lie in the same connected component](goal). -/
lemma edge_component_wellDefined (d e : R.Dart) (h : R.edgeInv.SameCycle d e) :
    R.toSimpleGraph.connectedComponentMk (R.vert d) =
      R.toSimpleGraph.connectedComponentMk (R.vert e) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (R.dart_component_eq_head ((R.edgeInv ^ n) d))

/-- In [a rotation system](hyp:R), the [component containing](goal)
[a facial orbit](hyp:b) is the connected component of the tail of any dart in that orbit. -/
noncomputable def orbitComponent (b : R.FaceOrbit) : R.Component :=
  Quotient.lift (fun d => R.toSimpleGraph.connectedComponentMk (R.vert d))
    (R.boundary_component_wellDefined) b
/-- In [a rotation system](hyp:R), the [component containing](goal) [an edge](hyp:e)
is the connected component of the tail of either of its darts. -/
noncomputable def edgeComponent (e : R.Edge) : R.Component :=
  Quotient.lift (fun d => R.toSimpleGraph.connectedComponentMk (R.vert d))
    (R.edge_component_wellDefined) e
/-- In [a rotation system](hyp:R), the [component of](goal) [a local boundary](hyp:b)
is [the component of its facial orbit when it is an orbit boundary](step:1), and
[the component of its isolated vertex when it is a puncture](step:2). -/
noncomputable def compOf (b : R.LocalBoundary) : R.Component :=
  match b with
  | Sum.inl o => R.orbitComponent o
  | Sum.inr v => R.toSimpleGraph.connectedComponentMk v.val
/-- In [a rotation system](hyp:R), the [length of](goal) [a local boundary](hyp:b)
is [the number of darts in its facial orbit for an orbit boundary](step:1), and
[zero for a puncture](step:2). -/
noncomputable def boundaryLength (b : R.LocalBoundary) : ℕ :=
  match b with
  | Sum.inl o => (Finset.univ.filter (fun d => orbitOf R.facePerm d = o)).card
  | Sum.inr _ => 0

/-- For [a rotation system](hyp:R), the [componentwise Euler condition](goal) says
that in every connected component the number of vertices plus the number of local
boundaries equals the number of edges plus two.

A puncture supplies the one boundary of an isolated component. -/
noncomputable def componentEuler : Prop := ∀ K : R.Component,
  Fintype.card {v : R.Vertex // R.toSimpleGraph.connectedComponentMk v = K} +
    Fintype.card {b : R.LocalBoundary // R.compOf b = K} =
      Fintype.card {e : R.Edge // R.edgeComponent e = K} + 2

/-- For [a rotation system](hyp:R), [a type of regions](hyp:F), and
[an assignment of local boundaries to regions](hyp:place), the
[placement adjacency relation](goal) connects [a component to a region when some
boundary of that component is assigned to that region](step:1), connects
[a region to a component when a boundary of that component is assigned to that region](step:2), and
[never connects two components or two regions](step:3). -/
noncomputable def placementAdj (F : Type) (place : R.LocalBoundary → F) :
    (R.Component ⊕ F) → (R.Component ⊕ F) → Prop
  | Sum.inl K, Sum.inr f => ∃ b, R.compOf b = K ∧ place b = f
  | Sum.inr f, Sum.inl K => ∃ b, R.compOf b = K ∧ place b = f
  | _, _ => False
-- @node: RotationSystem.placementAdj_symm
/-- For a rotation system, [a type of regions](hyp:F), and
[an assignment of local boundaries to regions](hyp:place),
[placement adjacency is symmetric: whenever one node is adjacent to another,
the second is adjacent to the first](goal). -/
lemma placementAdj_symm (F : Type) (place : R.LocalBoundary → F) :
    ∀ ⦃a b⦄, R.placementAdj F place a b → R.placementAdj F place b a := by
  intro a b hab
  cases a <;> cases b <;> exact hab
-- @node: RotationSystem.placementAdj_irrefl
/-- For a rotation system, [a type of regions](hyp:F), and
[an assignment of local boundaries to regions](hyp:place),
[no component or region node is adjacent to itself in the placement relation](goal). -/
lemma placementAdj_irrefl (F : Type) (place : R.LocalBoundary → F) :
    ∀ n, ¬ R.placementAdj F place n n := by
  intro n
  cases n <;> exact id
/-- For [a rotation system](hyp:R), [a type of regions](hyp:F), and
[an assignment of local boundaries to regions](hyp:place), the [placement graph](goal)
has components and regions as its two kinds of vertices; a component and a region
are adjacent exactly when a boundary of that component is assigned to that region. -/
noncomputable def placementGraph (F : Type) (place : R.LocalBoundary → F) :
    SimpleGraph (R.Component ⊕ F) where
  Adj := R.placementAdj F place
  symm := ⟨R.placementAdj_symm F place⟩
  loopless := ⟨R.placementAdj_irrefl F place⟩
end RotationSystem

/-- A sphere embedding consists of genus-zero components and their actual placement.
Connectivity and the boundary-edge count say that the component/face incidence
multigraph is a tree, including the empty map with its single face. -/
structure SphereMap extends RotationSystem where
  genusZero : toRotationSystem.componentEuler
  Face : Type -- @realizes F(actual global complementary regions)
  [faceFintype : Fintype Face]
  [faceDecidableEq : DecidableEq Face]
  boundaryFace : toRotationSystem.LocalBoundary → Face -- @realizes F(local boundaries and punctures assigned to regions)
  placement_connected : (toRotationSystem.placementGraph Face boundaryFace).Connected
  placement_card : Nat.card (toRotationSystem.Component ⊕ Face) =
    Nat.card toRotationSystem.LocalBoundary + 1

attribute [instance] SphereMap.faceFintype SphereMap.faceDecidableEq

-- @node: def:intermediate-plane-graphs
/-- The [type of intermediate plane graphs](goal) is the type of sphere maps,
including loops, parallel edges, and their edge-side incidences.

Triangulations separately require `SphereMap.IsSimple` through `IsSphereTriangulation`. -/
def IntermediatePlaneGraph : Type 1 := SphereMap

namespace SphereMap
-- @env: S1
variable (M : SphereMap) -- @realizes M(sphere embedding; connectedness imposed by IsConnectedMap)

/-- For [a sphere map](hyp:M), the [edge type](goal) consists of pairs of opposite
darts, retaining the identities of loops and parallel edges. -/
abbrev Edge := M.toRotationSystem.Edge -- @realizes E(edge orbits retain loops and parallel identity)
/-- For [a sphere map](hyp:M), the [type of connected components](goal) groups
vertices by connectivity in its underlying simple graph. -/
abbrev Component := M.toRotationSystem.Component
/-- For [a sphere map](hyp:M), the [type of facial orbits](goal) consists of cycles
of the permutation that reverses a dart and then rotates at its new tail vertex. -/
abbrev FaceOrbit := M.toRotationSystem.FaceOrbit
/-- For [a sphere map](hyp:M), the [type of local boundaries](goal) consists of
facial orbits together with punctures at isolated vertices. -/
abbrev LocalBoundary := M.toRotationSystem.LocalBoundary
/-- For [a sphere map](hyp:M), the [face permutation](goal) first reverses a dart
along its edge and then rotates at the resulting vertex. -/
noncomputable abbrev facePerm := M.toRotationSystem.facePerm
/-- For [a sphere map](hyp:M), the [dart-to-edge assignment](goal) sends each dart
to its orbit under edge reversal. -/
noncomputable abbrev edgeOf := M.toRotationSystem.edgeOf
/-- In [a sphere map](hyp:M), the [face incident to](goal) [a dart](hyp:d) is the
global region assigned to the facial orbit containing that dart. -/
noncomputable def faceOf (d : M.Dart) : M.Face :=
  M.boundaryFace (Sum.inl (orbitOf M.facePerm d))
/-- For [a sphere map](hyp:M), the [head-vertex assignment](goal) sends each dart
to the tail vertex of its reversed dart. -/
noncomputable abbrev head := M.toRotationSystem.head
  -- @realizes w(adjacent vertex at the head of a dart)
/-- For [a sphere map](hyp:M), the [underlying simple graph](goal) retains its
vertices and joins distinct vertices exactly when a dart runs between them. -/
noncomputable abbrev toSimpleGraph := M.toRotationSystem.toSimpleGraph
/-- For [a sphere map](hyp:M), the [boundary-to-component assignment](goal) sends
each facial orbit to its component and each puncture to the component of its isolated vertex. -/
noncomputable abbrev compOf := M.toRotationSystem.compOf
/-- For [a sphere map](hyp:M), the [placement graph](goal) has components and faces
as vertices, with a component adjacent to a face exactly when one of its local boundaries
is assigned to that face. -/
noncomputable abbrev placementGraph := M.toRotationSystem.placementGraph M.Face M.boundaryFace

/-- In [a sphere map](hyp:M), the [darts incident to](goal) [a face](hyp:f) are
all darts whose assigned face is that face. -/
noncomputable def faceDarts (f : M.Face) : Finset M.Dart :=
  Finset.univ.filter (fun d => M.faceOf d = f)
/-- In [a sphere map](hyp:M), the [vertices incident to](goal) [a face](hyp:f)
are the tails of its incident darts together with the isolated vertices whose punctures
are assigned to that face. -/
noncomputable def faceVertices (f : M.Face) : Finset M.Vertex :=
  (M.faceDarts f).image M.vert ∪
    Finset.univ.filter (fun v => ∃ hv : ∀ d, M.vert d ≠ v,
      M.boundaryFace (Sum.inr ⟨v, hv⟩) = f)

-- @node: def:face-length
/-- In [a sphere map](hyp:M), the [length of](goal) [a face](hyp:f) is the sum
of the lengths of all local boundaries assigned to it, with punctures contributing zero. -/
noncomputable def faceLength (f : M.Face) : ℕ :=
  ∑ b : M.LocalBoundary, if M.boundaryFace b = f then M.toRotationSystem.boundaryLength b else 0

-- @node: def:embedding
/-- For [a sphere map](hyp:M), the [type of choices of an outer face](goal) is
the type of its faces. -/
noncomputable def outerFaceChoice := M.Face
/-- A [plane map](goal) is a sphere map together with a choice of one of its faces
as the outer face. -/
abbrev PlaneMap := Σ M : SphereMap, M.outerFaceChoice

-- @node: SphereMap.adjacency_symm
/-- In a sphere map, for [two vertices](hyp:u,v),
[if they are distinct and a dart runs from the first to the second, then they are
distinct in the reverse order and a dart runs from the second to the first](goal). -/
lemma adjacency_symm (u v : M.Vertex) :
    (u ≠ v ∧ ∃ d, M.vert d = u ∧ M.head d = v) →
      (v ≠ u ∧ ∃ d, M.vert d = v ∧ M.head d = u) := by
  exact M.toRotationSystem.adjacency_symm u v

-- @node: ass:duality-embedding
/-- For [a sphere map](hyp:M), [connectedness of the map](goal) means that its
underlying simple graph is connected, including the requirement that it has a vertex. -/
noncomputable def IsConnectedMap : Prop := M.toSimpleGraph.Connected
  -- @realizes M(connected sphere graph in the duality lemma)

-- @node: ass:bk-1
/-- For [a sphere map](hyp:M), [finiteness of the map](goal) requires
[finitely many vertices](step:1) and [finitely many darts](step:2). -/
noncomputable def FiniteMap : Prop := Finite M.Vertex ∧ Finite M.Dart
-- @node: ass:bk-2
/-- For [a sphere map](hyp:M), the [finite-vertex condition](goal) says that
its set of vertices is finite. -/
noncomputable def FiniteVertices : Prop := Finite M.Vertex

/-- For [a sphere map](hyp:M), [simplicity](goal) requires
[every dart to have distinct tail and head vertices](step:1) and
[any two darts with the same unordered pair of endpoints to represent the same edge](step:2). -/
noncomputable def IsSimple : Prop :=
  (∀ d, M.vert d ≠ M.head d) ∧
  ∀ d e, s(M.vert d, M.head d) = s(M.vert e, M.head e) → M.edgeOf d = M.edgeOf e

/-- In [a sphere map](hyp:M), [an edge](hyp:e) is [incident to](goal)
[a face](hyp:f) when some dart representing that edge is assigned to that face. -/
noncomputable def edgeOnFace (e : M.Edge) (f : M.Face) : Prop :=
  ∃ d, M.edgeOf d = e ∧ M.faceOf d = f

/-- In [a sphere map](hyp:M), the [endpoint set of](goal) [an edge](hyp:e)
consists of the tail vertices of its representing darts. -/
noncomputable def edgeEndpoints (e : M.Edge) : Finset M.Vertex :=
  (Finset.univ.filter (fun d => M.edgeOf d = e)).image M.vert

-- @node: SphereMap.nextIndex_lt
/-- In a sphere map, for [a list of darts](hyp:ds) and
[a position within that list](hyp:i), [the next position, with wraparound at the
end, is strictly less than the list's length](goal). -/
lemma nextIndex_lt (ds : List M.Dart) (i : Fin ds.length) :
    (i.val + 1) % ds.length < ds.length := by
  exact Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)

/-- In [a sphere map](hyp:M), [a list of darts](hyp:ds) is a
[closed directed trail](goal) when [it is nonempty](step:1),
[it uses no undirected edge twice](step:2), and [the head of each dart is the tail
of the next dart, including wraparound from the last to the first](step:3). -/
noncomputable def IsClosedTrail (ds : List M.Dart) : Prop :=
  ds ≠ [] ∧ (ds.map M.edgeOf).Nodup ∧
  ∀ i : Fin ds.length,
    M.head (ds.get i) = M.vert (ds.get ⟨(i.val + 1) % ds.length,
      M.nextIndex_lt ds i⟩)

/-- In [a sphere map](hyp:M), [a list of darts](hyp:ds) is an
[oriented simple cycle](goal) when [it is a closed directed trail](step:1) and
[its tail vertices are all distinct](step:2).

Loops and cycles formed by two parallel edges are allowed. -/
noncomputable def IsSimpleCycle (ds : List M.Dart) : Prop :=
  M.IsClosedTrail ds ∧ (ds.map M.vert).Nodup

/-- For [a sphere map](hyp:M), the [type of oriented simple cycles](goal)
consists of lists of darts satisfying the simple-cycle condition. -/
noncomputable def Cycle := {ds : List M.Dart // M.IsSimpleCycle ds}

/-- In [a sphere map](hyp:M), with [a list of darts whose edges must be avoided](hyp:ds),
[two local boundaries](hyp:b,c) are [joined avoiding those edges](goal) when a
possibly empty sequence of crossings of other edges connects them, each crossing
passing between the facial orbits of opposite darts. -/
noncomputable def localBoundariesJoinedAvoiding (ds : List M.Dart)
    (b c : M.LocalBoundary) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ d, M.edgeOf d ∉ ds.map M.edgeOf ∧
    Sum.inl (orbitOf M.facePerm d) = a ∧
    Sum.inl (orbitOf M.facePerm (M.edgeInv d)) = b) b c

/-- In [a sphere map](hyp:M), [a face](hyp:f) lies [behind](goal)
[a local boundary](hyp:b) relative to [a component](hyp:K) when
[the boundary belongs to that component](step:1) and [the face can be reached from
the boundary's assigned face in the placement graph without visiting that component node](step:2). -/
noncomputable def FaceBehind (K : M.Component) (b : M.LocalBoundary) (f : M.Face) : Prop :=
  M.compOf b = K ∧
  Relation.ReflTransGen (fun x y : M.Component ⊕ M.Face =>
    x ≠ Sum.inl K ∧ y ≠ Sum.inl K ∧ M.placementGraph.Adj x y)
      (Sum.inr (M.boundaryFace b)) (Sum.inr f)

/-- In [a sphere map](hyp:M), the [left local region of](goal)
[an oriented simple cycle](hyp:C) consists of local boundaries reachable from
the facial orbit of some dart of the cycle by crossing only edges outside the cycle. -/
noncomputable def leftLocalRegion (C : M.Cycle) : Set M.LocalBoundary :=
  {b | ∃ d ∈ C.val,
    M.localBoundariesJoinedAvoiding C.val (Sum.inl (orbitOf M.facePerm d)) b}
/-- In [a sphere map](hyp:M), the [right local region of](goal)
[an oriented simple cycle](hyp:C) consists of local boundaries that belong to
the component of a tail vertex of the cycle and do not belong to its left local region. -/
noncomputable def rightLocalRegion (C : M.Cycle) : Set M.LocalBoundary :=
  {b | (∃ d ∈ C.val, M.compOf b = M.toSimpleGraph.connectedComponentMk (M.vert d)) ∧
    b ∉ M.leftLocalRegion C}
/-- In [a sphere map](hyp:M), the [left region of](goal)
[an oriented simple cycle](hyp:C) consists of faces lying behind a boundary in
its left local region, relative to that boundary's component. -/
noncomputable def leftRegion (C : M.Cycle) : Set M.Face :=
  {f | ∃ b ∈ M.leftLocalRegion C, M.FaceBehind (M.compOf b) b f}
/-- In [a sphere map](hyp:M), the [right region of](goal)
[an oriented simple cycle](hyp:C) consists of faces lying behind a boundary in
its right local region, relative to that boundary's component. -/
noncomputable def rightRegion (C : M.Cycle) : Set M.Face :=
  {f | ∃ b ∈ M.rightLocalRegion C, M.FaceBehind (M.compOf b) b f}

/-- In [a sphere map](hyp:M), with [a chosen outer face](hyp:outer),
[an oriented simple cycle](hyp:C) is [counterclockwise](goal) when the outer face
belongs to its right region. -/
noncomputable def IsCounterclockwise (outer : M.Face) (C : M.Cycle) : Prop :=
  outer ∈ M.rightRegion C
/-- In [a sphere map](hyp:M), with [a chosen outer face](hyp:outer),
[an oriented simple cycle](hyp:C) is [clockwise](goal) when the outer face
belongs to its left region. -/
noncomputable def IsClockwise (outer : M.Face) (C : M.Cycle) : Prop :=
  outer ∈ M.leftRegion C

/-- In [a sphere map](hyp:M), for [a set of faces specifying a side](hyp:R) and
[an oriented simple cycle](hyp:C), [a vertex](hyp:v) lies [strictly on that side](goal)
when [it is not a tail vertex of the cycle](step:1) and [it is incident to at least
one face in the specified set](step:2). -/
noncomputable def strictlyOnSide (R : Set M.Face) (C : M.Cycle) (v : M.Vertex) : Prop :=
  v ∉ C.val.map M.vert ∧ v ∈ (Finset.univ.filter (fun v => ∃ f ∈ R, v ∈ M.faceVertices f))

-- @node: SphereMap.global_euler
/-- For a sphere map, [the number of vertices plus the number of faces
equals the number of edges plus one plus the number of connected components](goal). -/
lemma global_euler : Fintype.card M.Vertex + Fintype.card M.Face =
    Fintype.card M.Edge + 1 + Fintype.card M.Component := by
  have fiber_card {α β : Type} [Fintype α] [Fintype β] (g : α → β) :
      (∑ b, Fintype.card {a // g a = b}) = Fintype.card α := by
    simp_rw [Fintype.card_subtype]
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset α) (Finset.univ : Finset β) g
  have heuler := congrArg (fun f : M.Component → ℕ => ∑ K, f K)
    (funext M.genusZero)
  simp only [Finset.sum_add_distrib, fiber_card, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at heuler
  have hplace := M.placement_card
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_sum] at hplace
  change Fintype.card M.Vertex + Fintype.card M.LocalBoundary =
    Fintype.card M.Edge + Fintype.card M.Component * 2 at heuler
  simp only [← Nat.card_eq_fintype_card, LocalBoundary, RotationSystem.LocalBoundary,
    RotationSystem.FaceOrbit, Component, RotationSystem.Component,
    Edge, RotationSystem.Edge] at heuler hplace ⊢
  omega
-- @node: SphereMap.face_has_boundary
/-- In a sphere map with at least one vertex, [a face](hyp:f)
[has at least one local boundary assigned to it](goal). -/
lemma face_has_boundary [Nonempty M.Vertex] (f : M.Face) : ∃ b, M.boundaryFace b = f := by
  let K : M.Component := M.toSimpleGraph.connectedComponentMk (Classical.arbitrary M.Vertex)
  obtain ⟨p⟩ := M.placement_connected.preconnected (Sum.inr f) (Sum.inl K)
  have ha := p.adj_snd (p.not_nil_of_ne (by simp))
  change M.toRotationSystem.placementAdj M.Face M.boundaryFace (Sum.inr f) p.snd at ha
  cases hs : p.snd with
  | inl L =>
    rw [hs] at ha
    obtain ⟨b, hb, hf⟩ := ha
    exact ⟨b, hf⟩
  | inr g =>
    rw [hs] at ha
    exact False.elim ha
-- @node: SphereMap.boundary_unique_in_component
/-- In a sphere map, if [two local boundaries](hyp:b,c)
[belong to the same component](hyp:hK) and [are assigned to the same face](hyp:hf),
then [they are the same boundary](goal). -/
lemma boundary_unique_in_component (b c : M.LocalBoundary)
    (hK : M.compOf b = M.compOf c) (hf : M.boundaryFace b = M.boundaryFace c) : b = c := by
  let edge : M.LocalBoundary → M.placementGraph.edgeSet := fun a =>
    ⟨s(Sum.inl (M.compOf a), Sum.inr (M.boundaryFace a)), ⟨a, rfl, rfl⟩⟩
  have hsurj : Function.Surjective edge := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y =>
      cases x with
      | inl K =>
        cases y with
        | inl L => exact False.elim he
        | inr f =>
          obtain ⟨a, hK, hf⟩ := he
          refine ⟨a, Subtype.ext ?_⟩
          change s(Sum.inl (M.compOf a), Sum.inr (M.boundaryFace a)) = s(Sum.inl K, Sum.inr f)
          exact congrArg₂ (fun K f => s(Sum.inl K, Sum.inr f)) hK hf
      | inr f =>
        cases y with
        | inl K =>
          obtain ⟨a, hK, hf⟩ := he
          refine ⟨a, Subtype.ext ?_⟩
          change s(Sum.inl (M.compOf a), Sum.inr (M.boundaryFace a)) = s(Sum.inr f, Sum.inl K)
          exact (congrArg₂ (fun K f => s(Sum.inl K, Sum.inr f)) hK hf).trans
            (Sym2.eq_swap)
        | inr g => exact False.elim he
  have hle : Nat.card M.LocalBoundary ≤ Nat.card M.placementGraph.edgeSet := by
    have hc := M.placement_connected.card_vert_le_card_edgeSet_add_one
    have hp := M.placement_card
    simp only [placementGraph, LocalBoundary, RotationSystem.LocalBoundary] at hc hp ⊢
    omega
  have hinj : Function.Injective edge := (hsurj.bijective_of_nat_card_le hle).1
  apply hinj
  apply Subtype.ext
  change s(Sum.inl (M.compOf b), Sum.inr (M.boundaryFace b)) =
    s(Sum.inl (M.compOf c), Sum.inr (M.boundaryFace c))
  rw [hK, hf]
-- @node: SphereMap.placement_isTree
/-- For a sphere map, [the placement graph connecting components to
their incident faces is a tree](goal). -/
lemma placement_isTree : M.placementGraph.IsTree := by
  let edge : M.LocalBoundary → M.placementGraph.edgeSet := fun b =>
    ⟨s(Sum.inl (M.compOf b), Sum.inr (M.boundaryFace b)), ⟨b, rfl, rfl⟩⟩
  have hinj : Function.Injective edge := by
    intro b c h
    have he := congrArg Subtype.val h
    have heq : M.compOf b = M.compOf c ∧ M.boundaryFace b = M.boundaryFace c := by
      simpa only [edge, Sym2.eq_iff, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, and_self, or_false, and_false] using he
    exact M.boundary_unique_in_component b c heq.1 heq.2
  have hsurj : Function.Surjective edge := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y =>
      cases x with
      | inl K =>
        cases y with
        | inl L => exact False.elim he
        | inr f =>
          obtain ⟨b, hb, hf⟩ := he
          exact ⟨b, Subtype.ext (congrArg₂ (fun K f => s(Sum.inl K, Sum.inr f)) hb hf)⟩
      | inr f =>
        cases y with
        | inr g => exact False.elim he
        | inl K =>
          obtain ⟨b, hb, hf⟩ := he
          exact ⟨b, Subtype.ext ((congrArg₂
            (fun K f => s(Sum.inl K, Sum.inr f)) hb hf).trans Sym2.eq_swap)⟩
  have hc := Nat.card_congr (Equiv.ofBijective edge ⟨hinj, hsurj⟩)
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  exact ⟨M.placement_connected, by rw [← hc]; exact M.placement_card.symm⟩

-- @node: SphereMap.faceBehind_existsUnique
/-- In a sphere map, for [a component](hyp:K) and [a face](hyp:f),
[there is exactly one local boundary of that component behind which the face lies](goal). -/
lemma faceBehind_existsUnique (K : M.Component) (f : M.Face) :
    ∃! b : M.LocalBoundary, M.FaceBehind K b f := by
  obtain ⟨x, ⟨hx, hpath⟩, huniq⟩ :=
    tree_branch_existsUnique M.placement_isTree (Sum.inl K) (Sum.inr f) (by simp)
  cases x with
  | inl L => exact False.elim hx
  | inr g =>
    obtain ⟨b, hb, hg⟩ := hx
    refine ⟨b, ⟨hb, ?_⟩, ?_⟩
    · simpa only [hg] using hpath
    · intro c hc
      have he : Sum.inr (M.boundaryFace c) = (Sum.inr g : M.Component ⊕ M.Face) :=
        huniq _ ⟨⟨c, hc.1, rfl⟩, hc.2⟩
      exact M.boundary_unique_in_component c b (hc.1.trans hb.symm)
        ((Sum.inr.inj he).trans hg.symm)
-- @node: SphereMap.cycle_component_eq
/-- In a sphere map, for [an oriented simple cycle](hyp:C) and
[two darts](hyp:d,e), if [the first dart belongs to the cycle](hyp:hd) and
[the second dart belongs to the cycle](hyp:he), then [their tail vertices lie
in the same connected component](goal). -/
lemma cycle_component_eq (C : M.Cycle) (d e : M.Dart)
    (hd : d ∈ C.val) (he : e ∈ C.val) :
    M.toSimpleGraph.connectedComponentMk (M.vert d) =
      M.toSimpleGraph.connectedComponentMk (M.vert e) := by
  have hpos : 0 < C.val.length := List.length_pos_iff.mpr C.property.1.1
  have hindex (n : ℕ) (hn : n < C.val.length) :
      M.toSimpleGraph.connectedComponentMk (M.vert (C.val.get ⟨n, hn⟩)) =
        M.toSimpleGraph.connectedComponentMk (M.vert (C.val.get ⟨0, hpos⟩)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hprev := ih (by omega)
      have hs := C.property.1.2.2 ⟨n, by omega⟩
      have ht := (M.toRotationSystem.dart_component_eq_head (C.val.get ⟨n, by omega⟩)).trans
        (congrArg M.toSimpleGraph.connectedComponentMk hs)
      simp only [Nat.mod_eq_of_lt hn] at ht
      exact ht.symm.trans hprev
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp he
  exact (hindex i.val i.isLt).trans (hindex j.val j.isLt).symm

-- @node: SphereMap.localBoundariesJoinedAvoiding_compOf
/-- In a sphere map, for [a list of darts whose edges are excluded](hyp:ds)
and [two local boundaries](hyp:b,c), if [the boundaries can be joined by crossings
that avoid those edges](hyp:h), then [they belong to the same component](goal). -/
lemma localBoundariesJoinedAvoiding_compOf (ds : List M.Dart) (b c : M.LocalBoundary)
    (h : M.localBoundariesJoinedAvoiding ds b c) : M.compOf b = M.compOf c := by
  induction h with
  | refl => rfl
  | tail h hstep ih =>
    obtain ⟨d, hd, rfl, rfl⟩ := hstep
    exact ih.trans (M.toRotationSystem.dart_component_eq_head d)

-- @node: SphereMap.leftLocalRegion_compOf
/-- In a sphere map, for [an oriented simple cycle](hyp:C),
[a dart](hyp:d), and [a local boundary](hyp:b), if [the dart belongs to the cycle](hyp:hd)
and [the boundary belongs to its left local region](hyp:hb), then [the boundary's
component is the component of the dart's tail vertex](goal). -/
lemma leftLocalRegion_compOf (C : M.Cycle) (d : M.Dart) (hd : d ∈ C.val)
    (b : M.LocalBoundary) (hb : b ∈ M.leftLocalRegion C) :
    M.compOf b = M.toSimpleGraph.connectedComponentMk (M.vert d) := by
  obtain ⟨e, he, hpath⟩ := hb
  exact (M.localBoundariesJoinedAvoiding_compOf C.val _ b hpath).symm.trans
    (M.cycle_component_eq C e d he hd)

-- @node: SphereMap.cycle_sides_partition
/-- In a sphere map, [an oriented simple cycle](hyp:C) has
[disjoint left and right regions whose union is the set of all faces](goal). -/
lemma cycle_sides_partition (C : M.Cycle) :
    Disjoint (M.leftRegion C) (M.rightRegion C) ∧ M.leftRegion C ∪ M.rightRegion C = Set.univ := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  let K := M.toSimpleGraph.connectedComponentMk (M.vert d)
  have hleft (b : M.LocalBoundary) (hb : b ∈ M.leftLocalRegion C) : M.compOf b = K :=
    M.leftLocalRegion_compOf C d hd b hb
  have hright (b : M.LocalBoundary) (hb : b ∈ M.rightLocalRegion C) : M.compOf b = K := by
    obtain ⟨⟨e, he, hb⟩, _⟩ := hb
    exact hb.trans (M.cycle_component_eq C e d he hd)
  constructor
  · apply Set.disjoint_left.mpr
    intro f hf hg
    obtain ⟨b, hb, hbf⟩ := hf
    obtain ⟨c, hc, hcf⟩ := hg
    have hbK := hleft b hb
    have hcK := hright c hc
    rw [hbK] at hbf
    rw [hcK] at hcf
    have heq : b = c := (M.faceBehind_existsUnique K f).unique hbf hcf
    exact hc.2 (heq ▸ hb)
  · apply Set.eq_univ_of_forall
    intro f
    obtain ⟨b, hbf, _⟩ := M.faceBehind_existsUnique K f
    have hbK := hbf.1
    have hbf' : M.FaceBehind (M.compOf b) b f := by simpa only [hbK] using hbf
    by_cases hb : b ∈ M.leftLocalRegion C
    · exact Or.inl ⟨b, hb, hbf'⟩
    · exact Or.inr ⟨b, ⟨⟨d, hd, hbK⟩, hb⟩, hbf'⟩
-- @node: SphereMap.faceLength_eq_card_faceDarts
/-- In a sphere map, [a face](hyp:f) has [length equal to the number
of darts incident to it](goal). -/
lemma faceLength_eq_card_faceDarts (f : M.Face) : M.faceLength f = (M.faceDarts f).card := by
  have hfiber := Finset.sum_fiberwise_eq_sum_filter'
    (Finset.univ : Finset M.Dart) (Finset.univ : Finset M.FaceOrbit)
    (orbitOf M.facePerm) (fun o => if M.boundaryFace (Sum.inl o) = f then 1 else 0 : M.FaceOrbit → ℕ)
  simp only [Finset.mem_univ, Finset.filter_true] at hfiber
  unfold faceLength
  rw [Fintype.sum_sum_type]
  simp only [RotationSystem.boundaryLength, ite_self, Finset.sum_const_zero, add_zero]
  calc
    _ = ∑ o : M.FaceOrbit, ∑ d ∈ Finset.univ.filter (fun d => orbitOf M.facePerm d = o),
        if M.boundaryFace (Sum.inl o) = f then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro o ho
      by_cases h : M.boundaryFace (Sum.inl o) = f <;> simp [h]
    _ = _ := hfiber.trans (by
      simp [faceDarts, faceOf]
      congr 1)

-- @node: SphereMap.exists_faceEquivBoundary
/-- For a sphere map, if [the map is connected](hyp:hM), then
[there is a bijection from faces to local boundaries that assigns each face a
boundary placed on that face](goal).

This includes the one-vertex map, whose unique boundary is a puncture. -/
lemma exists_faceEquivBoundary (hM : M.IsConnectedMap) :
    ∃ q : M.Face ≃ M.LocalBoundary, ∀ f, M.boundaryFace (q f) = f := by
  let : Nonempty M.Vertex := hM.nonempty
  let : Subsingleton M.Component := hM.preconnected.subsingleton_connectedComponent
  have hinj : Function.Injective M.boundaryFace := by
    intro b c hf
    exact M.boundary_unique_in_component b c (Subsingleton.elim _ _) hf
  let e := Equiv.ofBijective M.boundaryFace ⟨hinj, M.face_has_boundary⟩
  exact ⟨e.symm, e.apply_symm_apply⟩
-- @node: SphereMap.exists_faceEquivOrbit
/-- For a sphere map with at least one dart, if [the map is connected](hyp:hM),
then [there is a bijection from faces to facial orbits that sends the face of
every dart to the facial orbit containing that dart](goal). -/
lemma exists_faceEquivOrbit (hM : M.IsConnectedMap) [Nonempty M.Dart] :
    ∃ q : M.Face ≃ M.FaceOrbit, ∀ d, q (M.faceOf d) = orbitOf M.facePerm d := by
  have no_puncture (v : M.Puncture) : False := by
    let d := Classical.arbitrary M.Dart
    obtain ⟨p⟩ := hM.preconnected v.val (M.vert d)
    have ha := p.adj_snd (p.not_nil_of_ne (v.property d).symm)
    obtain ⟨_, e, he, _⟩ := ha
    exact v.property e he
  let e : M.LocalBoundary ≃ M.FaceOrbit :=
    { toFun := fun b => match b with
        | Sum.inl o => o
        | Sum.inr v => False.elim (no_puncture v)
      invFun := Sum.inl
      left_inv := by intro b; cases b with
        | inl o => rfl
        | inr v => exact False.elim (no_puncture v)
      right_inv := fun _ => rfl }
  obtain ⟨q, hq⟩ := M.exists_faceEquivBoundary hM
  refine ⟨q.trans e, ?_⟩
  intro d
  have hqd : q (M.faceOf d) = Sum.inl (orbitOf M.facePerm d) := by
    apply M.boundary_unique_in_component
    · exact hM.preconnected.subsingleton_connectedComponent.elim _ _
    · exact hq (M.faceOf d)
  change e (q (M.faceOf d)) = orbitOf M.facePerm d
  rw [hqd]
  rfl
end SphereMap

end OaiPairedStatesHamiltonian
