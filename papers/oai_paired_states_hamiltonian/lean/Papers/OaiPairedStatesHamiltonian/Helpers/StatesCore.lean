module

public import Papers.OaiPairedStatesHamiltonian.Helpers.Triangulation
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Incidence states, pairs, directed choices and opposite-edge graphs. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


namespace SphereMap

-- @node: SphereMap.dart_eq_of_endpoints
/-- In [a sphere map](hyp:M) that [has no loops or multiple edges](hyp:hM),
[two directed edges](hyp:d,e) with [the same starting vertex](hyp:ht) and
[the same ending vertex](hyp:hh) [are equal](goal). -/
lemma dart_eq_of_endpoints (M : SphereMap) (hM : M.IsSimple) (d e : M.Dart)
    (ht : M.vert d = M.vert e) (hh : M.head d = M.head e) : d = e := by
  have he := hM.2 d e (by rw [ht, hh])
  rcases (M.edgeOf_eq_iff d e).mp he with he | he
  · exact he.symm
  · have htail : M.vert e = M.head d := congrArg M.vert he
    exact (hM.1 d (ht.trans htail)).elim

end SphereMap

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [a designated outer
face](hyp:t0), an [assignment](goal) chooses a nonroot vertex for every black
nonouter face, with blackness determined by the normalized coloring. -/
abbrev Assignment := (t : blackNonOuter T col t0) → (nonRoot T t0)
  -- @realizes t(subtype of black nonouter faces A)

-- @node: ass:state-bijection
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[bijectivity of an assignment](goal) means that [the assignment from black nonouter
faces to nonroot vertices](hyp:r) uses each nonroot vertex exactly once. -/
noncomputable def StateBijection (r : Assignment T col t0) : Prop := Function.Bijective r
  -- @realizes r(bijection from A to X)
  -- @realizes s(same bijectivity requirement on the second state)
-- @node: ass:state-incidence
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[incidence of an assignment](goal) means that [the assignment of nonroot vertices
to black nonouter faces](hyp:r) chooses a vertex belonging to each assigned face. -/
noncomputable def StateIncidence (r : Assignment T col t0) : Prop :=
  ∀ t, (r t).val ∈ T.faceVertices t.val
  -- @realizes r(assignments are incident with their triangles)
  -- @realizes s(the second state satisfies the same incidence requirement)
-- @node: def:state
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[the state condition](goal) on [an assignment](hyp:r) requires both
[using each nonroot vertex exactly once](step:1) and
[assigning each face one of its own vertices](step:2). -/
structure IsState (r : Assignment T col t0) : Prop where
  bijective : StateBijection T col t0 r -- @realizes r(bijective)
  incident : StateIncidence T col t0 r -- @realizes r(incident)
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[a state](goal) is a bijective assignment of black nonouter faces to nonroot
vertices in which every assigned vertex belongs to its face. -/
abbrev State := {r : Assignment T col t0 // IsState T col t0 r}
  -- @realizes r(bijective incident assignment A to X)
  -- @realizes s(second state with the same domain and range)
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[the finite enumeration of states](goal) lists all bijective incident assignments. -/
noncomputable instance : Fintype (State T col t0) := Fintype.ofFinite _
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[the equality decision for states](goal) determines whether two bijective incident
assignments are identical. -/
noncomputable instance : DecidableEq (State T col t0) := Classical.decEq _

-- @node: ass:pair-distinct
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[pointwise distinctness](goal) of [two states](hyp:r,s) means that they assign
different vertices to every black nonouter face. -/
noncomputable def PairDistinct (r s : State T col t0) : Prop := ∀ t, r.val t ≠ s.val t
-- @node: def:pair
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[the pair condition](goal) on [two states](hyp:r,s) requires
[different assigned vertices at every black nonouter face](step:1). -/
structure IsPair (r s : State T col t0) : Prop where
  distinct : PairDistinct T col t0 r s
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[a pair](goal) is an ordered pair of states assigning different vertices at every
black nonouter face. -/
abbrev Pair := {p : State T col t0 × State T col t0 // IsPair T col t0 p.1 p.2}
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[the finite enumeration of pairs](goal) lists all ordered pairs of pointwise
distinct states. -/
noncomputable instance : Fintype (Pair T col t0) := Fintype.ofFinite _
-- @node: ass:pair-existence
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[pair existence](goal) means that there are two states assigning different vertices
at every black nonouter face. -/
noncomputable def PairExists : Prop := ∃ r s : State T col t0, IsPair T col t0 r s

-- @node: def:delta
/-- In [a sphere map](hyp:T) with [a face coloring](hyp:col), [the sign](goal) of
[a directed edge](hyp:d) is positive one when its left face has color true and
negative one otherwise. -/
noncomputable def delta (d : T.Dart) : ℤ := if col (T.faceOf d) then 1 else -1
  -- @realizes \delta(sign of the black face on the left of a dart)

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
and [a state](hyp:r), [an edge choice](goal) selects, in every black nonouter face,
a vertex different from the vertex assigned by the state. -/
abbrev EdgeChoice (r : State T col t0) :=
  (t : blackNonOuter T col t0) → {w : T.Vertex // w ∈ T.faceVertices t.val ∧ w ≠ (r.val t).val}

-- @node: def:disk-edge-choice
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation certificate](hyp:hT), [a state](hyp:r), and
[a choice of a different incident vertex in each black nonouter face](hyp:choice),
[the chosen directed edges](goal) run from each state's assigned vertex to that
face's chosen vertex. -/
noncomputable def ChosenEdges (hT : IsSphereTriangulation T) (r : State T col t0)
    (choice : EdgeChoice T col t0 r) : Finset T.Dart :=
  Finset.univ.image (fun t : blackNonOuter T col t0 => faceDart T hT t.val (r.val t).val (choice t).val
    (r.property.incident t) (choice t).property.1 (Ne.symm (choice t).property.2))

-- @node: def:qs
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
and [a state](hyp:s), [the opposite-edge graph](goal) retains all vertices and
joins the endpoints of each edge incident to a black nonouter face whose endpoints
both differ from that face's assigned vertex. -/
noncomputable def Qs (s : State T col t0) : SimpleGraph T.Vertex :=
  SimpleGraph.fromEdgeSet {e | ∃ t : blackNonOuter T col t0, ∃ d : T.Dart,
    T.faceOf d = t.val ∧ T.vert d ≠ (s.val t).val ∧ T.head d ≠ (s.val t).val ∧
    e = s(T.vert d, T.head d)} -- @realizes Q_s(opposite edges, with all vertices retained)

-- @node: ass:cancel-cyclic
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
and [a state](hyp:s), [the cyclicity condition](goal) says that the opposite-edge
graph is not acyclic. -/
noncomputable def QsCyclic (s : State T col t0) : Prop := ¬ (Qs T col t0 s).IsAcyclic
-- @node: ass:root-forest
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
and [a state](hyp:s), [the forest condition](goal) says that the opposite-edge
graph is acyclic. -/
noncomputable def QsForest (s : State T col t0) : Prop := (Qs T col t0 s).IsAcyclic
-- @node: ass:pin-1
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
and [a state](hyp:s), [the simple-cycle condition](goal) says that the opposite-edge
graph contains a closed walk that is a cycle. -/
noncomputable def QsHasSimpleCycle (s : State T col t0) : Prop :=
  ∃ v, ∃ C : (Qs T col t0 s).Walk v v, C.IsCycle

-- @node: def:incidence-weights
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), and [an outer face](hyp:t0),
[incidence weights](goal) assign a real number to every black nonouter face and
every vertex belonging to that face. -/
noncomputable def IncidenceWeights : Type := (t : blackNonOuter T col t0) → (T.faceVertices t.val) → ℝ
  -- @realizes a(real incidence function on black nonouter triangles)
-- @node: def:omega
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[real incidence weights](hyp:a), and [a state](hyp:s), [the state's total weight](goal)
is the sum, over black nonouter faces, of the weight at each assigned vertex. -/
noncomputable def omega (a : IncidenceWeights T col t0) (s : State T col t0) : ℝ :=
  ∑ t, a t ⟨(s.val t).val, s.property.incident t⟩ -- @realizes \omega(sum of assigned incidence weights)

-- @node: pair_vertex_ne
/-- If [two states](hyp:r,s) [form a pointwise distinct pair](hyp:h), then
[at any black nonouter face](hyp:t) [their assigned vertices are different](goal). -/
lemma pair_vertex_ne (r s : State T col t0) (h : IsPair T col t0 r s)
    (t : blackNonOuter T col t0) : (r.val t).val ≠ (s.val t).val := by
  intro heq
  exact h.distinct t (Subtype.ext heq)

-- @node: def:paired-edges
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation certificate](hyp:hT), and [two states](hyp:r,s)
[assigning different vertices at every black nonouter face](hyp:h),
[the paired directed edges](goal) contain the edge from the first state's assigned
vertex to the second state's assigned vertex in each such face. -/
noncomputable def pairedEdges (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) : Finset T.Dart :=
  Finset.univ.image (fun t : blackNonOuter T col t0 => faceDart T hT t.val (r.val t).val (s.val t).val
    (r.property.incident t) (s.property.incident t) (pair_vertex_ne T col t0 r s h t))
  -- @realizes D(darts from r(t) to s(t), with undirected grouping below)

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation certificate](hyp:hT), and [an ordered pair of pointwise
distinct states](hyp:p), [the undirected paired edges](goal) are obtained by
forgetting the directions of the edges between the two assigned vertices. -/
noncomputable def undirectedPairedEdges (hT : IsSphereTriangulation T) (p : Pair T col t0) : Finset T.Edge :=
  (pairedEdges T col t0 hT p.val.1 p.val.2 p.property).image T.edgeOf
  -- @realizes D(undirected paired edge set used to group pairs)

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation certificate](hyp:hT), and [a pair of states](hyp:p),
[the grouping key](goal) is the pair's set of undirected paired edges. -/
noncomputable def groupKey (hT : IsSphereTriangulation T) (p : Pair T col t0) : Finset T.Edge :=
  undirectedPairedEdges T col t0 hT p

-- @node: ass:pin-3
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
and [a sphere triangulation certificate](hyp:hT), [the paired-edge reading condition](goal)
says that two pairs have equal grouping keys exactly when they have equal sets of
undirected paired edges. -/
noncomputable def PairedEdgesReading (hT : IsSphereTriangulation T) : Prop :=
  ∀ p q : Pair T col t0, groupKey T col t0 hT p = groupKey T col t0 hT q ↔
    undirectedPairedEdges T col t0 hT p = undirectedPairedEdges T col t0 hT q

/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
and [two states](hyp:r,s), [the pair permutation](goal) sends each vertex assigned
by the first state to the vertex assigned to the same face by the second state. -/
noncomputable def pairPermutation (r s : State T col t0) : Equiv.Perm (nonRoot T t0) :=
  (Equiv.ofBijective r.val r.property.bijective).symm.trans
    (Equiv.ofBijective s.val s.property.bijective)

-- @node: pairPermutation_apply_state
/-- For [two states](hyp:r,s) and [a black nonouter face](hyp:t), [the pair
permutation sends the first state's assigned vertex to the second state's assigned
vertex at that face](goal). -/
lemma pairPermutation_apply_state (r s : State T col t0) (t : blackNonOuter T col t0) :
    pairPermutation T col t0 r s (r.val t) = s.val t := by
  change (Equiv.ofBijective s.val s.property.bijective)
    ((Equiv.ofBijective r.val r.property.bijective).symm
      ((Equiv.ofBijective r.val r.property.bijective) t)) = _
  rw [Equiv.symm_apply_apply]
  rfl

-- @node: pairPermutation_fixedPointFree
/-- If [two states](hyp:r,s) [assign different vertices at every black nonouter
face](hyp:h), then [every nonroot vertex](hyp:v) [is moved by their pair
permutation](goal). -/
lemma pairPermutation_fixedPointFree (r s : State T col t0) (h : IsPair T col t0 r s)
    (v : nonRoot T t0) : pairPermutation T col t0 r s v ≠ v := by
  obtain ⟨t, rfl⟩ := r.property.bijective.2 v
  rw [pairPermutation_apply_state]
  exact (h.distinct t).symm

-- @node: pairedDart
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation certificate](hyp:hT), and [two states](hyp:r,s)
[assigning different vertices at every black nonouter face](hyp:h),
[the paired directed edge](goal) of [a black nonouter face](hyp:t) runs from the
first state's assigned vertex to the second state's assigned vertex along that face. -/
noncomputable def pairedDart (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) (t : blackNonOuter T col t0) : T.Dart :=
  faceDart T hT t.val (r.val t).val (s.val t).val
    (r.property.incident t) (s.property.incident t) (pair_vertex_ne T col t0 r s h t)

-- @node: pairedDart_spec
/-- If [the map is a sphere triangulation](hyp:hT) and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then for
[any such face](hyp:t), [its paired directed edge starts at the first state's
assigned vertex, ends at the second state's assigned vertex, and has that face
on one of its two sides](goal). -/
lemma pairedDart_spec (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) (t : blackNonOuter T col t0) :
    FaceDart T t.val (r.val t).val (s.val t).val (pairedDart T col t0 hT r s h t) :=
  Classical.choose_spec (exists_faceDart T hT t.val (r.val t).val (s.val t).val
    (r.property.incident t) (s.property.incident t) (pair_vertex_ne T col t0 r s h t))

-- @node: pairedDart_injective
/-- If [the map is a sphere triangulation](hyp:hT) and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then
[different black nonouter faces supply different paired directed edges](goal). -/
lemma pairedDart_injective (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) : Function.Injective (pairedDart T col t0 hT r s h) := by
  intro t u he
  apply r.property.bijective.1
  apply Subtype.ext
  exact (pairedDart_spec T col t0 hT r s h t).1.symm.trans
    ((congrArg T.vert he).trans (pairedDart_spec T col t0 hT r s h u).1)

-- @node: pairedEdges_mem_iff
/-- If [the map is a sphere triangulation](hyp:hT) and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then
[a directed edge](hyp:d) [belongs to the paired edge set exactly when it is the
paired directed edge of some black nonouter face](goal). -/
lemma pairedEdges_mem_iff (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) (d : T.Dart) :
    d ∈ pairedEdges T col t0 hT r s h ↔ ∃ t, pairedDart T col t0 hT r s h t = d := by
  simp only [pairedEdges, pairedDart, Finset.mem_image, Finset.mem_univ, true_and]

-- @node: pairedEdges_unique_outgoing
/-- If [the map is a sphere triangulation](hyp:hT) and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then
[each nonroot vertex](hyp:v) [is the starting vertex of exactly one paired
directed edge](goal). -/
lemma pairedEdges_unique_outgoing (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) (v : nonRoot T t0) :
    ∃! d, d ∈ pairedEdges T col t0 hT r s h ∧ T.vert d = v.val := by
  obtain ⟨t, ht⟩ := r.property.bijective.2 v
  refine ⟨pairedDart T col t0 hT r s h t, ⟨?_, ?_⟩, ?_⟩
  · exact (pairedEdges_mem_iff T col t0 hT r s h _).mpr ⟨t, rfl⟩
  · exact (pairedDart_spec T col t0 hT r s h t).1.trans (congrArg Subtype.val ht)
  · rintro d ⟨hd, hv⟩
    obtain ⟨u, rfl⟩ := (pairedEdges_mem_iff T col t0 hT r s h d).mp hd
    have hu : r.val u = r.val t := Subtype.ext
      (((pairedDart_spec T col t0 hT r s h u).1.symm.trans hv).trans
        (congrArg Subtype.val ht).symm)
    exact congrArg (pairedDart T col t0 hT r s h) (r.property.bijective.1 hu)

-- @node: pairedEdges_unique_incoming
/-- If [the map is a sphere triangulation](hyp:hT) and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then
[each nonroot vertex](hyp:v) [is the ending vertex of exactly one paired
directed edge](goal). -/
lemma pairedEdges_unique_incoming (hT : IsSphereTriangulation T) (r s : State T col t0)
    (h : IsPair T col t0 r s) (v : nonRoot T t0) :
    ∃! d, d ∈ pairedEdges T col t0 hT r s h ∧ T.head d = v.val := by
  obtain ⟨t, ht⟩ := s.property.bijective.2 v
  refine ⟨pairedDart T col t0 hT r s h t, ⟨?_, ?_⟩, ?_⟩
  · exact (pairedEdges_mem_iff T col t0 hT r s h _).mpr ⟨t, rfl⟩
  · exact (pairedDart_spec T col t0 hT r s h t).2.1.trans (congrArg Subtype.val ht)
  · rintro d ⟨hd, hv⟩
    obtain ⟨u, rfl⟩ := (pairedEdges_mem_iff T col t0 hT r s h d).mp hd
    have hu : s.val u = s.val t := Subtype.ext
      (((pairedDart_spec T col t0 hT r s h u).2.1.symm.trans hv).trans
        (congrArg Subtype.val ht).symm)
    exact congrArg (pairedDart T col t0 hT r s h) (s.property.bijective.1 hu)

-- @node: pairedDart_edge_injective
/-- If [the map is a sphere triangulation](hyp:hT), [the two faces across every
edge have different colors](hyp:hcol), and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then
[different black nonouter faces supply different undirected paired edges](goal). -/
lemma pairedDart_edge_injective (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (r s : State T col t0)
    (h : IsPair T col t0 r s) :
    Function.Injective (fun t => T.edgeOf (pairedDart T col t0 hT r s h t)) := by
  intro t u he
  apply Subtype.ext
  have ht := (pairedDart_spec T col t0 hT r s h t).2.2
  have hu := (pairedDart_spec T col t0 hT r s h u).2.2
  have hbt := (Finset.mem_filter.mp t.property).2.1
  have hbu := (Finset.mem_filter.mp u.property).2.1
  have hc := normalizedColoring_partition T col hcol t0
  rcases (T.edgeOf_eq_iff _ _).mp he with he | he
  · rw [he] at hu
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact ht.symm.trans hu
    · exact (hc _ ((ht ▸ hbt).trans (hu ▸ hbu).symm)).elim
    · exact (hc _ ((hu ▸ hbu).trans (ht ▸ hbt).symm)).elim
    · exact ht.symm.trans hu
  · rw [he, T.edgeInv_involutive] at hu
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact (hc _ ((ht ▸ hbt).trans (hu ▸ hbu).symm)).elim
    · exact ht.symm.trans hu
    · exact ht.symm.trans hu
    · exact (hc _ ((hu ▸ hbu).trans (ht ▸ hbt).symm)).elim

-- @node: pairedDart_ne_inverse
/-- If [the map is a sphere triangulation](hyp:hT), [the two faces across every
edge have different colors](hyp:hcol), and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then for
[any two black nonouter faces](hyp:t,u), [the paired directed edge of the second
face is never the reverse of the paired directed edge of the first](goal). -/
lemma pairedDart_ne_inverse (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (r s : State T col t0)
    (h : IsPair T col t0 r s) (t u : blackNonOuter T col t0) :
    pairedDart T col t0 hT r s h u ≠ T.edgeInv (pairedDart T col t0 hT r s h t) := by
  intro he
  have hedge := (T.edgeOf_eq_iff (pairedDart T col t0 hT r s h t)
    (pairedDart T col t0 hT r s h u)).mpr (Or.inr he)
  have htu := pairedDart_edge_injective T col t0 hT hcol r s h hedge
  subst u
  exact T.edgeInv_fixedPointFree _ he.symm

-- @node: pairPermutation_no_two_cycle
/-- If [the map is a sphere triangulation](hyp:hT), [the two faces across every
edge have different colors](hyp:hcol), and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then
[any nonroot vertex](hyp:v) [does not return to itself after two applications
of the pair permutation](goal). -/
lemma pairPermutation_no_two_cycle (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (r s : State T col t0)
    (h : IsPair T col t0 r s) (v : nonRoot T t0) :
    pairPermutation T col t0 r s (pairPermutation T col t0 r s v) ≠ v := by
  obtain ⟨t, rfl⟩ := r.property.bijective.2 v
  obtain ⟨u, hu⟩ := r.property.bijective.2 (s.val t)
  rw [pairPermutation_apply_state, ← hu, pairPermutation_apply_state]
  intro hs
  let d := pairedDart T col t0 hT r s h t
  let e := pairedDart T col t0 hT r s h u
  have hd := pairedDart_spec T col t0 hT r s h t
  have he := pairedDart_spec T col t0 hT r s h u
  have hedge : T.edgeOf d = T.edgeOf e := hT.props.2.1.2 d e (by
    rw [hd.1, hd.2.1, he.1, he.2.1, hu, hs]
    exact Sym2.eq_swap)
  have htu := pairedDart_edge_injective T col t0 hT hcol r s h hedge
  subst u
  exact h.distinct t hu

-- @node: pairPermutation_orbit_length_ge_three
/-- If [the map is a sphere triangulation](hyp:hT), [the two faces across every
edge have different colors](hyp:hcol), and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then
[the orbit of any nonroot vertex](hyp:v) [has length at least three under the
pair permutation](goal). -/
lemma pairPermutation_orbit_length_ge_three (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (r s : State T col t0)
    (h : IsPair T col t0 r s) (v : nonRoot T t0) :
    3 ≤ ((pairPermutation T col t0 r s).toList v).length := by
  let p := pairPermutation T col t0 r s
  have hv : v ∈ p.support := Equiv.Perm.mem_support.mpr
    (pairPermutation_fixedPointFree T col t0 r s h v)
  have hlen := Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hv
  by_contra hn
  change ¬ 3 ≤ (p.toList v).length at hn
  have heq : (p.toList v).length = 2 := by omega
  have hnext := p.next_toList_eq_apply v (p v)
    (Equiv.Perm.mem_toList_iff.mpr ⟨Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.SameCycle.refl p v), hv⟩)
  have hi : (p.toList v)[1]'(by omega) = p v := by
    simpa using p.getElem_toList v 1 (by omega)
  have hzero : (p.toList v)[0]'(by omega) = v := p.toList_getElem_zero v hv
  have hstep := List.next_getElem (p.toList v) (p.nodup_toList v) 1 (by omega)
  simp only [hi] at hstep
  have hwrap : (1 + 1) % (p.toList v).length = 0 := by rw [heq]
  simp only [hwrap, hzero, hnext] at hstep
  exact pairPermutation_no_two_cycle T col t0 hT hcol r s h v hstep

-- @node: pairedVertexDart
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation certificate](hyp:hT), and [two states](hyp:r,s)
[assigning different vertices at every black nonouter face](hyp:h),
[the paired directed edge indexed by a vertex](goal) is the paired edge supplied
by the face that the first state assigns to [that nonroot vertex](hyp:v). -/
noncomputable def pairedVertexDart (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (v : nonRoot T t0) : T.Dart :=
  pairedDart T col t0 hT r s h ((Equiv.ofBijective r.val r.property.bijective).symm v)

-- @node: pairedVertexDart_spec
/-- If [the map is a sphere triangulation](hyp:hT) and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then for
[any nonroot vertex](hyp:v), [the paired directed edge indexed by that vertex
starts there and ends at its image under the pair permutation](goal). -/
lemma pairedVertexDart_spec (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (v : nonRoot T t0) :
    T.vert (pairedVertexDart T col t0 hT r s h v) = v.val ∧
      T.head (pairedVertexDart T col t0 hT r s h v) =
        (pairPermutation T col t0 r s v).val := by
  have hs := pairedDart_spec T col t0 hT r s h
    ((Equiv.ofBijective r.val r.property.bijective).symm v)
  refine ⟨hs.1.trans ?_, hs.2.1⟩
  exact congrArg Subtype.val ((Equiv.ofBijective r.val r.property.bijective).apply_symm_apply v)

-- @node: pairedVertexDart_edge_injective
/-- If [the map is a sphere triangulation](hyp:hT), [the faces across each edge
have different colors](hyp:hcol), and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then
[distinct nonroot vertices index distinct undirected paired edges](goal). -/
lemma pairedVertexDart_edge_injective (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (r s : State T col t0)
    (h : IsPair T col t0 r s) :
    Function.Injective (fun v => T.edgeOf (pairedVertexDart T col t0 hT r s h v)) :=
  (pairedDart_edge_injective T col t0 hT hcol r s h).comp
    (Equiv.ofBijective r.val r.property.bijective).symm.injective

-- @node: paired_orbit_isSimpleCycle
/-- If [the map is a sphere triangulation](hyp:hT), [the faces across each edge
have different colors](hyp:hcol), and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then
[the orbit starting at any nonroot vertex](hyp:v) [gives a simple directed cycle
when each vertex is replaced by its indexed paired directed edge](goal). -/
lemma paired_orbit_isSimpleCycle (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (r s : State T col t0)
    (h : IsPair T col t0 r s) (v : nonRoot T t0) :
    T.IsSimpleCycle (((pairPermutation T col t0 r s).toList v).map
      (pairedVertexDart T col t0 hT r s h)) := by
  let p := pairPermutation T col t0 r s
  let ds := pairedVertexDart T col t0 hT r s h
  have hlen := pairPermutation_orbit_length_ge_three T col t0 hT hcol r s h v
  have hspec := pairedVertexDart_spec T col t0 hT r s h
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro he
    have hl := congrArg List.length he
    simp only [List.length_map, List.length_nil] at hl
    omega
  · rw [List.map_map]
    exact (p.nodup_toList v).map (pairedVertexDart_edge_injective T col t0 hT hcol r s h)
  · intro i
    have hi : i.val < (p.toList v).length := by simpa using i.isLt
    have hnext := p.next_toList_eq_apply v ((p.toList v)[i.val]) (List.getElem_mem hi)
    have hstep := List.next_getElem (p.toList v) (p.nodup_toList v) i.val hi
    rw [hnext] at hstep
    have hmod : (i.val + 1) % (p.toList v).length < (p.toList v).length :=
      Nat.mod_lt _ (Nat.zero_lt_of_lt hi)
    simp only [List.get_eq_getElem, List.getElem_map, List.length_map]
    change T.head (ds ((p.toList v)[i.val])) =
      T.vert (ds ((p.toList v)[(i.val + 1) % (p.toList v).length]))
    rw [(hspec _).2, (hspec _).1]
    exact congrArg Subtype.val hstep
  · simp only [List.map_map]
    change ((p.toList v).map (fun x => T.vert (ds x))).Nodup
    simp only [ds, (hspec _).1]
    exact (p.nodup_toList v).map Subtype.val_injective

-- @node: pairedOrbitCycle
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation certificate](hyp:hT), [a coloring with different colors
across every edge](hyp:hcol), and [two states](hyp:r,s)
[assigning different vertices at every black nonouter face](hyp:h),
[the paired orbit cycle](goal) follows the pair permutation from
[a nonroot vertex](hyp:v), using the paired directed edge indexed by each vertex. -/
noncomputable def pairedOrbitCycle (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (r s : State T col t0)
    (h : IsPair T col t0 r s) (v : nonRoot T t0) : T.Cycle :=
  ⟨((pairPermutation T col t0 r s).toList v).map (pairedVertexDart T col t0 hT r s h),
    paired_orbit_isSimpleCycle T col t0 hT hcol r s h v⟩

-- @node: pairedOrbitCycle_vertices
/-- If [the map is a sphere triangulation](hyp:hT), [the faces across each edge
have different colors](hyp:hcol), and [two states](hyp:r,s)
[assign different vertices at every black nonouter face](hyp:h), then for
[any starting nonroot vertex](hyp:v), [the ordered starting vertices of the
paired orbit cycle are exactly the ordered vertices of its pair-permutation
orbit](goal). -/
lemma pairedOrbitCycle_vertices (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (r s : State T col t0)
    (h : IsPair T col t0 r s) (v : nonRoot T t0) :
    (pairedOrbitCycle T col t0 hT hcol r s h v).val.map T.vert =
      ((pairPermutation T col t0 r s).toList v).map Subtype.val := by
  simp only [pairedOrbitCycle, List.map_map]
  apply List.map_congr_left
  intro x hx
  exact (pairedVertexDart_spec T col t0 hT r s h x).1

/-- In [a sphere map](hyp:T), [the reversal of a directed-edge list](goal) takes
[a list of directed edges](hyp:ds) in reverse order and reverses each edge's direction. -/
noncomputable def reverseDarts (ds : List T.Dart) : List T.Dart := ds.reverse.map T.edgeInv

-- @node: pairOrbitRep
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
and [an ordered pair of states assigning different vertices at every black
nonouter face](hyp:p), [the chosen orbit representative](goal) is a nonroot
vertex belonging to [a specified orbit of the pair permutation](hyp:q). -/
noncomputable def pairOrbitRep (p : Pair T col t0)
    (q : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) : nonRoot T t0 :=
  Classical.choose (Quotient.exists_rep q)

-- @node: pairCycleAt
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation certificate](hyp:hT), [a coloring with different colors
across every edge](hyp:hcol), and [an ordered pair of states assigning different
vertices at every black nonouter face](hyp:p), [the cycle associated with an
orbit](goal) is the paired orbit cycle starting from the chosen representative
of [that orbit of the pair permutation](hyp:q). -/
noncomputable def pairCycleAt (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0)
    (q : orbitType (pairPermutation T col t0 p.val.1 p.val.2)) : T.Cycle :=
  pairedOrbitCycle T col t0 hT hcol p.val.1 p.val.2 p.property (pairOrbitRep T col t0 p q)

-- @node: pairedCycles
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [an outer face](hyp:t0),
[a sphere triangulation certificate](hyp:hT), [a coloring with different colors
across every edge](hyp:hcol), and [an ordered pair of states assigning different
vertices at every black nonouter face](hyp:p), [the finite collection of paired
cycles](goal) is obtained by [enumerating the finitely many orbits of the pair
permutation](step:1) and [collecting the cycle associated with each orbit](step:2). -/
noncomputable def pairedCycles (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) : Finset T.Cycle :=
  letI := Fintype.ofFinite (orbitType (pairPermutation T col t0 p.val.1 p.val.2))
  Finset.univ.image (pairCycleAt T col t0 hT hcol p)

-- @node: pairedCycles_spec
/-- If [the map is a sphere triangulation](hyp:hT), [the faces across each edge
have different colors](hyp:hcol), and [an ordered pair of states assigns
different vertices at every black nonouter face](hyp:p), then [its collection
of paired cycles has at least three edges in every cycle, uses only nonroot
vertices, has disjoint vertex sets for distinct cycles, contains exactly all
paired directed edges, and covers exactly all nonroot vertices](goal). -/
lemma pairedCycles_spec (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) :
    let cs := pairedCycles T col t0 hT hcol p;
      (∀ C ∈ cs, 3 ≤ C.val.length) ∧
      (∀ C ∈ cs, ∀ d ∈ C.val, T.vert d ∈ nonRoot T t0) ∧
      (∀ C ∈ cs, ∀ C' ∈ cs, C ≠ C' →
        Disjoint (C.val.map T.vert).toFinset (C'.val.map T.vert).toFinset) ∧
      cs.biUnion (fun C => C.val.toFinset) = pairedEdges T col t0 hT p.val.1 p.val.2 p.property ∧
      cs.biUnion (fun C => (C.val.map T.vert).toFinset) = nonRoot T t0 := by
  let f := pairPermutation T col t0 p.val.1 p.val.2
  let rep := pairOrbitRep T col t0 p
  have hrep (q : orbitType f) : orbitOf f (rep q) = q :=
    Classical.choose_spec (Quotient.exists_rep q)
  let cycle := pairCycleAt T col t0 hT hcol p
  let : Fintype (orbitType f) := Fintype.ofFinite _
  let cs := pairedCycles T col t0 hT hcol p
  have hsupport (v : nonRoot T t0) : v ∈ f.support :=
    Equiv.Perm.mem_support.mpr (pairPermutation_fixedPointFree T col t0 _ _ p.property v)
  have hmem (q : orbitType f) (v : nonRoot T t0) :
      v ∈ f.toList (rep q) ↔ orbitOf f v = q := by
    rw [Equiv.Perm.mem_toList_iff, and_iff_left (hsupport _)]
    constructor
    · intro h
      exact (Quotient.sound h).symm.trans (hrep q)
    · intro h
      exact Quotient.exact ((hrep q).trans h.symm)
  have hverts (q : orbitType f) : (cycle q).val.map T.vert =
      (f.toList (rep q)).map Subtype.val :=
    pairedOrbitCycle_vertices T col t0 hT hcol _ _ p.property _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hC
    simpa only [cycle, pairCycleAt, pairedOrbitCycle, List.length_map] using
      pairPermutation_orbit_length_ge_three T col t0 hT hcol _ _ p.property (rep q)
  · intro C hC d hd
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hC
    have hv : T.vert d ∈ (cycle q).val.map T.vert := List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [hverts] at hv
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hv
    exact hv ▸ v.property
  · intro C hC D hD hne
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨q', _, rfl⟩ := Finset.mem_image.mp hD
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    rw [List.mem_toFinset, hverts] at hv hv'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hv'
    have hyx : y = x := Subtype.ext he
    have hqq : q = q' := ((hmem q x).mp hx).symm.trans
      ((congrArg (orbitOf f) hyx).symm.trans ((hmem q' y).mp hy))
    exact hne (congrArg cycle hqq)
  · ext d
    constructor
    · intro hd
      obtain ⟨C, hC, hd⟩ := Finset.mem_biUnion.mp hd
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
      exact (pairedEdges_mem_iff T col t0 hT _ _ p.property _).mpr
        ⟨(Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm v, rfl⟩
    · intro hd
      obtain ⟨t, rfl⟩ := (pairedEdges_mem_iff T col t0 hT _ _ p.property d).mp hd
      let v := p.val.1.val t
      refine Finset.mem_biUnion.mpr ⟨cycle (orbitOf f v),
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      apply List.mem_toFinset.mpr
      change _ ∈ (f.toList (rep (orbitOf f v))).map _
      refine List.mem_map.mpr ⟨v, (hmem _ _).mpr rfl, ?_⟩
      change pairedDart T col t0 hT _ _ p.property
        ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective).symm
          ((Equiv.ofBijective p.val.1.val p.val.1.property.bijective) t)) = _
      rw [Equiv.symm_apply_apply]
  · ext v
    constructor
    · intro hv
      obtain ⟨C, hC, hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hC
      rw [List.mem_toFinset, hverts] at hv
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
      exact x.property
    · intro hv
      let x : nonRoot T t0 := ⟨v, hv⟩
      refine Finset.mem_biUnion.mpr ⟨cycle (orbitOf f x),
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [List.mem_toFinset, hverts]
      exact List.mem_map.mpr ⟨x, (hmem _ _).mpr rfl, rfl⟩


-- @node: pairedEdges_directed_cycleDecomposition
/-- If [the map is a sphere triangulation](hyp:hT), [the faces across each edge
have different colors](hyp:hcol), and [an ordered pair of states assigns
different vertices at every black nonouter face](hyp:p), then [there exists a
finite collection of simple directed cycles, each with at least three edges
and only nonroot vertices, such that distinct cycles have disjoint vertex sets,
their directed edges together are exactly the paired directed edges, and their
vertices together are exactly the nonroot vertices](goal). -/
lemma pairedEdges_directed_cycleDecomposition (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (p : Pair T col t0) :
    ∃ cs : Finset T.Cycle,
      (∀ C ∈ cs, 3 ≤ C.val.length) ∧
      (∀ C ∈ cs, ∀ d ∈ C.val, T.vert d ∈ nonRoot T t0) ∧
      (∀ C ∈ cs, ∀ C' ∈ cs, C ≠ C' →
        Disjoint (C.val.map T.vert).toFinset (C'.val.map T.vert).toFinset) ∧
      cs.biUnion (fun C => C.val.toFinset) = pairedEdges T col t0 hT p.val.1 p.val.2 p.property ∧
      cs.biUnion (fun C => (C.val.map T.vert).toFinset) = nonRoot T t0 := by
  exact ⟨pairedCycles T col t0 hT hcol p, pairedCycles_spec T col t0 hT hcol p⟩

end OaiPairedStatesHamiltonian
