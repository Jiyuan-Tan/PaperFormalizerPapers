module

public import Papers.OaiPairedStatesHamiltonian.Helpers.Forests

/-! Triangular faces, separating triangles, roots and derived standing counts. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


namespace SphereMap
variable (T : SphereMap)
/-- For [a sphere map](hyp:T) and [one of its faces](hyp:f), [having a three-cycle
boundary](goal) means that [the boundary has length three](step:1) and [the face has
exactly three distinct vertices](step:2). -/
noncomputable def faceBoundaryIsThreeCycle (f : T.Face) : Prop :=
  T.faceLength f = 3 ∧ (T.faceVertices f).card = 3
end SphereMap

-- @node: ass:sphere-triangulation-properties
/-- For [a sphere map](hyp:T), [the triangulation properties](goal) require that
[the map is connected](step:1), [it has no loops or parallel edges](step:2),
[it has at least four vertices](step:3), and [every face has a boundary of length
three with three distinct vertices](step:4). -/
noncomputable def SphereTriangulationProperties (T : SphereMap) : Prop :=
  T.IsConnectedMap ∧ -- @realizes T(connected sphere map)
  T.IsSimple ∧ -- @realizes T(no loops or parallel edges in a triangulation)
  4 ≤ Fintype.card T.Vertex ∧ -- @realizes T(at least four vertices)
  ∀ f, T.faceBoundaryIsThreeCycle f -- @realizes T(every face boundary is a three-cycle)
-- @node: def:sphere-triangulation
/-- For [a sphere map](hyp:T), [being a sphere triangulation](goal) records
[connectedness, absence of loops and parallel edges, at least four vertices,
and a three-cycle boundary for every face](step:1). -/
structure IsSphereTriangulation (T : SphereMap) : Prop where
  props : SphereTriangulationProperties T

-- @node: ass:partition-coloring
/-- For [a sphere map](hyp:T) and [a coloring of its faces by two Boolean colors](hyp:col),
[a partition coloring](goal) requires the two incident faces across every edge
to have different colors. -/
noncomputable def PartitionColoring (T : SphereMap) (col : T.Face → Bool) : Prop :=
  ∀ d : T.Dart, col (T.faceOf d) ≠ col (T.faceOf (T.edgeInv d))
  -- @realizes T(every edge has one incident face of each color)

-- @env: S2
variable (T : SphereMap) -- @realizes T(connected simple sphere triangulation via IsSphereTriangulation)

/-- For [a sphere map](hyp:T), [a Boolean face coloring](hyp:col), and [a distinguished
face](hyp:t0), [the normalized coloring](goal) [keeps the original colors if that face
is black](step:1) and [reverses every color otherwise](step:2), so that the distinguished
face is black. -/
noncomputable def normalizedColoring (col : T.Face → Bool) (t0 : T.Face) : T.Face → Bool :=
  if col t0 then col else fun f => !(col f)
-- @node: normalizedColoring_self
/-- [The distinguished face is black under the normalized coloring](goal). -/
lemma normalizedColoring_self (col : T.Face → Bool) (t0 : T.Face) :
    normalizedColoring T col t0 t0 = true := by
  unfold normalizedColoring
  cases h : col t0 <;> simp [h]

-- @node: normalizedColoring_partition
/-- If [the original coloring gives different colors to the incident faces across
every edge](hyp:hcol), then [the normalized coloring has the same property](goal). -/
lemma normalizedColoring_partition (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (t0 : T.Face) : PartitionColoring T (normalizedColoring T col t0) := by
  intro d
  have h := hcol d
  unfold normalizedColoring
  cases hc : col t0 <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · cases hf : col (T.faceOf d) <;> cases hg : col (T.faceOf (T.edgeInv d)) <;> simp_all
  · exact h

-- @node: def:roots
/-- For [a sphere map](hyp:T) and [a distinguished outer face](hyp:t0), [the roots](goal)
are the vertices of that face. -/
noncomputable def roots (t0 : T.Face) : Finset T.Vertex := T.faceVertices t0
  -- @realizes t_0(distinguished outer facial triangle, normalized black)
-- @node: def:black-face-count
/-- For [a sphere map](hyp:T) and [a Boolean face coloring](hyp:col), [the black face
count](goal) is the number of faces colored true. -/
noncomputable def blackFaceCount (col : T.Face → Bool) : ℕ :=
  (Finset.univ.filter (fun f => col f = true)).card -- @realizes k(number of black faces)
/-- For [a sphere map](hyp:T) and [a Boolean face coloring](hyp:col), [the white face
count](goal) is the number of faces colored false. -/
noncomputable def whiteFaceCount (col : T.Face → Bool) : ℕ :=
  (Finset.univ.filter (fun f => col f = false)).card
-- @node: def:counts
/-- For [a sphere map](hyp:T) with [a Boolean face coloring](hyp:col), [the standing
count identities](goal) say that [white and black faces are equally numerous](step:1),
[there are three times as many edges as black faces](step:2), and [there are two more
vertices than black faces](step:3). -/
noncomputable def StandingCounts (col : T.Face → Bool) : Prop :=
  whiteFaceCount T col = blackFaceCount T col ∧
  Fintype.card T.Edge = 3 * blackFaceCount T col ∧
  Fintype.card T.Vertex = blackFaceCount T col + 2

-- @node: SphereMap.edgeOf_eq_iff
/-- [Two directed edge incidences represent the same edge exactly when they are
equal or one is the reversal of the other](goal). -/
lemma SphereMap.edgeOf_eq_iff (M : SphereMap) (d e : M.Dart) :
    M.edgeOf d = M.edgeOf e ↔ e = d ∨ e = M.edgeInv d := by
  constructor
  · intro h
    have hs : M.edgeInv.SameCycle d e := Quotient.exact h
    obtain ⟨n, rfl⟩ := hs.exists_nat_pow_eq
    clear h hs
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h
      · exact Or.inr (congrArg M.edgeInv h)
      · exact Or.inl ((congrArg M.edgeInv h).trans (M.edgeInv_involutive d))
  · rintro (rfl | rfl)
    · rfl
    · exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr
        (Equiv.Perm.SameCycle.refl M.edgeInv d)).symm

-- @node: colored_dart_count
/-- If [the sphere map is a triangulation](hyp:hT), then [the number of directed
edge incidences belonging to faces of the chosen color is three times the number
of faces of that color](goal). -/
lemma colored_dart_count (hT : IsSphereTriangulation T) (col : T.Face → Bool) (b : Bool) :
    (Finset.univ.filter (fun d => col (T.faceOf d) = b)).card =
      3 * (Finset.univ.filter (fun f => col f = b)).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset T.Dart) (Finset.univ.filter (fun f => col f = b)) T.faceOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  rw [← h]
  have hf (f : T.Face) : (Finset.univ.filter (fun d => T.faceOf d = f)).card = 3 := by
    exact (T.faceLength_eq_card_faceDarts f).symm.trans (hT.props.2.2.2 f).1
  simp_rw [hf]
  simp [Nat.mul_comm]

-- @node: colored_darts_equiv_edges
/-- If [the coloring assigns different colors to the two incident faces across
every edge](hyp:hcol), then [the number of directed edge incidences whose face has
the chosen color equals the number of edges](goal). -/
lemma colored_darts_equiv_edges (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (b : Bool) :
    Fintype.card {d : T.Dart // col (T.faceOf d) = b} = Fintype.card T.Edge := by
  let g : {d : T.Dart // col (T.faceOf d) = b} → T.Edge := fun d => T.edgeOf d.val
  apply Fintype.card_congr (Equiv.ofBijective g ?_)
  constructor
  · intro d e h
    rcases (T.edgeOf_eq_iff d.val e.val).mp h with he | he
    · exact Subtype.ext he.symm
    · exfalso
      have hc := hcol d.val
      rw [d.property, ← he, e.property] at hc
      exact hc rfl
  · intro e
    obtain ⟨d, rfl⟩ := Quotient.exists_rep e
    by_cases hd : col (T.faceOf d) = b
    · exact ⟨⟨d, hd⟩, rfl⟩
    · have hi : col (T.faceOf (T.edgeInv d)) = b := by
        have hc := hcol d
        cases b <;> cases hf : col (T.faceOf d) <;>
          cases hg : col (T.faceOf (T.edgeInv d)) <;> simp_all
      exact ⟨⟨T.edgeInv d, hi⟩, ((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm⟩

-- @node: standingCounts_of_triangulation
/-- If [the sphere map is a triangulation](hyp:hT) and [the coloring assigns different
colors across every edge](hyp:hcol), then [the black and white face counts are equal,
the edge count is three times the black face count, and the vertex count is the black
face count plus two](goal). -/
lemma standingCounts_of_triangulation (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) : StandingCounts T col := by
  have hb : 3 * blackFaceCount T col = Fintype.card T.Edge := by
    unfold blackFaceCount
    rw [← colored_dart_count T hT col true]
    simpa only [Fintype.card_subtype] using colored_darts_equiv_edges T col hcol true
  have hw : 3 * whiteFaceCount T col = Fintype.card T.Edge := by
    unfold whiteFaceCount
    rw [← colored_dart_count T hT col false]
    simpa only [Fintype.card_subtype] using colored_darts_equiv_edges T col hcol false
  have hfaces : Fintype.card T.Face = blackFaceCount T col + whiteFaceCount T col := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun f : T.Face => col f = true)
    simpa [blackFaceCount, whiteFaceCount, Bool.not_eq_true] using h.symm
  let : Nonempty T.Vertex := hT.props.1.nonempty
  let : Subsingleton T.Component := hT.props.1.preconnected.subsingleton_connectedComponent
  let : Unique T.Component := uniqueOfSubsingleton
    (T.toSimpleGraph.connectedComponentMk (Classical.arbitrary T.Vertex))
  have hc : Fintype.card T.Component = 1 := Fintype.card_unique
  have heuler := T.global_euler
  rw [hc] at heuler
  unfold StandingCounts
  refine ⟨?_, hb.symm, ?_⟩ <;> omega

-- @node: def:state-sets
/-- For [a sphere map](hyp:T), [a Boolean face coloring](hyp:col), and [a distinguished
outer face](hyp:t0), [the black nonouter faces](goal) are the faces other than the outer
face that are black after normalizing its color to black. -/
noncomputable def blackNonOuter (col : T.Face → Bool) (t0 : T.Face) : Finset T.Face :=
  Finset.univ.filter (fun f => normalizedColoring T col t0 f = true ∧ f ≠ t0)
  -- @realizes A(black faces other than the outer face)
  -- @realizes t(black nonouter triangle, as subtype of this finset)
/-- For [a sphere map](hyp:T) and [a distinguished outer face](hyp:t0), [the nonroot
vertices](goal) are all vertices outside that face. -/
noncomputable def nonRoot (t0 : T.Face) : Finset T.Vertex :=
  Finset.univ \ roots T t0 -- @realizes X(nonroot vertices)

-- @node: def:state-cardinality
/-- For [a sphere map](hyp:T), [a Boolean face coloring](hyp:col), and [a distinguished
outer face](hyp:t0), [the state set cardinality identities](goal) require that
[the number of black nonouter faces is the normalized black face count minus one](step:1)
and [the number of nonroot vertices is that same count minus one](step:2). -/
noncomputable def StateSetsCard (col : T.Face → Bool) (t0 : T.Face) : Prop :=
  (blackNonOuter T col t0).card = blackFaceCount T (normalizedColoring T col t0) - 1 ∧
  (nonRoot T t0).card = blackFaceCount T (normalizedColoring T col t0) - 1
-- @node: stateSetsCard_of_triangulation
/-- If [the sphere map is a triangulation](hyp:hT) and [the face coloring assigns
different colors across each edge](hyp:hcol), then [the black nonouter faces and
the nonroot vertices each number one less than the normalized black face count](goal). -/
lemma stateSetsCard_of_triangulation (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face) :
    StateSetsCard T col t0 := by
  have hcounts := standingCounts_of_triangulation T hT (normalizedColoring T col t0)
    (normalizedColoring_partition T col hcol t0)
  have hout : t0 ∈ Finset.univ.filter (fun f => normalizedColoring T col t0 f = true) := by
    simp [normalizedColoring_self]
  have hblack : blackNonOuter T col t0 =
      (Finset.univ.filter (fun f => normalizedColoring T col t0 f = true)).erase t0 := by
    ext f
    simp [blackNonOuter, and_comm]
  have hroots : (roots T t0).card = 3 := (hT.props.2.2.2 t0).2
  unfold StateSetsCard
  constructor
  · rw [hblack, Finset.card_erase_of_mem hout]
    rfl
  · have hv := hcounts.2.2
    unfold nonRoot
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hroots, hv]
    omega

-- @node: ass:separating-triangle-properties
/-- For [a sphere map](hyp:T) and [a cycle in it](hyp:C), [the separating triangle
properties](goal) require that [the cycle has length three](step:1), [some vertex lies
strictly on its left side](step:2), and [some vertex lies strictly on its right side](step:3). -/
noncomputable def SeparatingTriangleProperties (C : T.Cycle) : Prop :=
  C.val.length = 3 ∧
  (∃ v, T.strictlyOnSide (T.leftRegion C) C v) ∧
  (∃ v, T.strictlyOnSide (T.rightRegion C) C v)
-- @node: def:separating-triangle
/-- For [a sphere map](hyp:T) and [a cycle in it](hyp:C), [being a separating triangle](goal)
records [a cycle of length three with a vertex strictly on each side](step:1). -/
structure IsSeparatingTriangle (C : T.Cycle) : Prop where
  props : SeparatingTriangleProperties T C
-- @node: ass:pairs-no-separating
/-- For [a sphere map](hyp:T), [the no-separating-triangle condition used for pairs](goal)
requires that no cycle is a triangle with a vertex strictly on each side. -/
noncomputable def PairsNoSeparatingTriangle : Prop := ∀ C : T.Cycle, ¬ IsSeparatingTriangle T C
-- @node: ass:trees-no-separating
/-- For [a sphere map](hyp:T), [the no-separating-triangle condition used for trees](goal)
requires that no cycle is a triangle with a vertex strictly on each side. -/
noncomputable def TreesNoSeparatingTriangle : Prop := ∀ C : T.Cycle, ¬ IsSeparatingTriangle T C

-- @node: triangulation_has_dart_at_vertex
/-- If [the sphere map is a triangulation](hyp:hT), then [every vertex is the initial
vertex of some directed edge incidence](goal). -/
lemma triangulation_has_dart_at_vertex (hT : IsSphereTriangulation T) (v : T.Vertex) :
    ∃ d, T.vert d = v := by
  have hex : ∃ w : T.Vertex, w ≠ v := by
    by_contra hn
    have hsub : (Finset.univ : Finset T.Vertex) ⊆ {v} := by
      intro w hw
      simp only [Finset.mem_singleton]
      by_contra hne
      exact hn ⟨w, hne⟩
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_univ, Finset.card_singleton] at hcard
    have := hT.props.2.2.1
    omega
  obtain ⟨w, hw⟩ := hex
  obtain ⟨p⟩ := hT.props.1.preconnected v w
  obtain ⟨_, d, hd, _⟩ := p.adj_snd (p.not_nil_of_ne hw.symm)
  exact ⟨d, hd⟩

-- @node: triangulation_faceVertices_eq_image
/-- If [the sphere map is a triangulation](hyp:hT), then [the vertices of the given face
are exactly the initial vertices of its directed boundary edge incidences](goal). -/
lemma triangulation_faceVertices_eq_image (hT : IsSphereTriangulation T) (t : T.Face) :
    T.faceVertices t = (T.faceDarts t).image T.vert := by
  have hnone : (Finset.univ.filter (fun v : T.Vertex => ∃ hv : ∀ d, T.vert d ≠ v,
      T.boundaryFace (Sum.inr ⟨v, hv⟩) = t)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨_, h, _⟩ := Finset.mem_filter.mp hv
    obtain ⟨d, hd⟩ := triangulation_has_dart_at_vertex T hT v
    exact h d hd
  simp only [SphereMap.faceVertices, hnone, Finset.union_empty]

/-- For [a sphere map](hyp:T), [a face](hyp:t), [two specified vertices](hyp:v,w),
and [a directed edge incidence](hyp:d), [being a face dart with these endpoints](goal)
means that [its initial vertex is the first specified vertex](step:1), [its terminal
vertex is the second](step:2), and [the given face is incident to it or its reversal](step:3). -/
noncomputable def FaceDart (t : T.Face) (v w : T.Vertex) (d : T.Dart) : Prop :=
  T.vert d = v ∧ T.head d = w ∧
    (T.faceOf d = t ∨ T.faceOf (T.edgeInv d) = t)
-- @node: exists_faceDart
/-- If [the sphere map is a triangulation](hyp:hT), [the first vertex belongs to the
given face](hyp:hv), [the second vertex also belongs to it](hyp:hw), and [these vertices
are distinct](hyp:hvw), then [a directed edge incidence goes from the first to the second
and has the face on one of its two sides](goal). -/
lemma exists_faceDart (hT : IsSphereTriangulation T) (t : T.Face)
    (v w : T.Vertex) (hv : v ∈ T.faceVertices t) (hw : w ∈ T.faceVertices t)
    (hvw : v ≠ w) : ∃ d, FaceDart T t v w d := by
  rw [triangulation_faceVertices_eq_image T hT t] at hv hw
  obtain ⟨d, hd, hdv⟩ := Finset.mem_image.mp hv
  obtain ⟨e, he, hew⟩ := Finset.mem_image.mp hw
  let : Nonempty T.Dart := ⟨d⟩
  have hcyc : T.facePerm.IsCycleOn (↑(T.faceDarts t) : Set T.Dart) := by
    simpa [SphereMap.faceDarts] using T.dual_rot_fibre hT.props.1 t
  have hcard : (T.faceDarts t).card = 3 :=
    (T.faceLength_eq_card_faceDarts t).symm.trans (hT.props.2.2.2 t).1
  have hnext (a : T.Dart) : T.vert (T.facePerm a) = T.head a := T.rot_vertex _
  obtain ⟨n, hn, hde⟩ := hcyc.exists_pow_eq hd he
  rw [hcard] at hn
  have hdt : T.faceOf d = t := (Finset.mem_filter.mp hd).2
  have het : T.faceOf e = t := (Finset.mem_filter.mp he).2
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn_cases with rfl | rfl | rfl
  · simp only [pow_zero, Equiv.Perm.one_apply] at hde
    exact False.elim (hvw (hdv.symm.trans ((congrArg T.vert hde).trans hew)))
  · refine ⟨d, hdv, ?_, Or.inl hdt⟩
    simpa only [pow_one, ← hnext] using (congrArg T.vert hde).trans hew
  · have hthree := hcyc.pow_card_apply hd
    rw [hcard] at hthree
    have hfe : T.facePerm e = d := by
      rw [← hde, ← Equiv.Perm.mul_apply, ← pow_succ']
      exact hthree
    refine ⟨T.edgeInv e, ?_, ?_, Or.inr ?_⟩
    · change T.head e = v
      rw [← hnext, hfe, hdv]
    · simpa only [SphereMap.head, RotationSystem.head, T.edgeInv_involutive e] using hew
    · simpa only [T.edgeInv_involutive e] using het

/-- For [a sphere map](hyp:T) [known to be a triangulation](hyp:hT), [a face](hyp:t), and
[two vertices](hyp:v,w), with [the first on the face](hyp:hv), [the second on the face](hyp:hw),
and [the vertices distinct](hyp:hvw), [the chosen face dart](goal) is a directed edge
incidence from the first vertex to the second with that face on one side. -/
noncomputable def faceDart (hT : IsSphereTriangulation T) (t : T.Face)
    (v w : T.Vertex) (hv : v ∈ T.faceVertices t) (hw : w ∈ T.faceVertices t)
    (hvw : v ≠ w) : T.Dart := Classical.choose (exists_faceDart T hT t v w hv hw hvw)

-- @node: exists_thirdVertex
/-- If [the sphere map is a triangulation](hyp:hT), [the first vertex belongs to the
given face](hyp:hv), [the second vertex belongs to it](hyp:hw), and [the two are distinct](hyp:hvw),
then [the face contains a vertex distinct from both](goal). -/
lemma exists_thirdVertex (hT : IsSphereTriangulation T) (t : T.Face)
    (v w : T.Vertex) (hv : v ∈ T.faceVertices t) (hw : w ∈ T.faceVertices t)
    (hvw : v ≠ w) : ∃ u, u ∈ T.faceVertices t ∧ u ≠ v ∧ u ≠ w := by
  by_contra h
  have hsub : T.faceVertices t ⊆ {v, w} := by
    intro u hu
    by_cases huv : u = v
    · simp [huv]
    · have huw : u = w := by
        by_contra huw
        exact h ⟨u, hu, huv, huw⟩
      simp [huw]
  have hcard := Finset.card_le_card hsub
  have hthree : (T.faceVertices t).card = 3 := (hT.props.2.2.2 t).2
  have htwo : ({v, w} : Finset T.Vertex).card ≤ 2 := Finset.card_le_two
  omega

/-- For [a sphere map](hyp:T) [known to be a triangulation](hyp:hT), [a face](hyp:t), and
[two vertices](hyp:v,w), with [the first on the face](hyp:hv), [the second on the face](hyp:hw),
and [the vertices distinct](hyp:hvw), [the chosen third vertex](goal) is a vertex of that
face distinct from both, together with a guarantee of these properties. -/
noncomputable def thirdVertex (hT : IsSphereTriangulation T) (t : T.Face)
    (v w : T.Vertex) (hv : v ∈ T.faceVertices t) (hw : w ∈ T.faceVertices t)
    (hvw : v ≠ w) : {u : T.Vertex // u ∈ T.faceVertices t ∧ u ≠ v ∧ u ≠ w} :=
  ⟨Classical.choose (exists_thirdVertex T hT t v w hv hw hvw),
    Classical.choose_spec (exists_thirdVertex T hT t v w hv hw hvw)⟩
  -- @realizes u(the third distinct vertex of the supplying black triangle)


end OaiPairedStatesHamiltonian
