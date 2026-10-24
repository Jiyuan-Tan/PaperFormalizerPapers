module

public import Papers.OaiPairedStatesHamiltonian.Helpers.PairPhases
public import Papers.OaiPairedStatesHamiltonian.Helpers.Spokes
public import Papers.OaiPairedStatesHamiltonian.Helpers.ReverseCycleSides

/-! Lifting paired-edge cycles through their supplying triangle centers. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

-- @node: incidenceCorner_exists
/-- If [the sphere map is a triangulation](hyp:hT) and [a vertex belongs to a black
nonouter face](hyp:hv), then [there is a spoke corner whose face is that face and
whose vertex is that vertex](goal). -/
lemma incidenceCorner_exists (hT : IsSphereTriangulation T)
    (t : blackNonOuter T col t0) (v : T.Vertex) (hv : v ∈ T.faceVertices t.val) :
    ∃ d : SpokeCorner T (blackNonOuter T col t0), T.faceOf d.val = t.val ∧ T.vert d.val = v := by
  rw [triangulation_faceVertices_eq_image T hT] at hv
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hv
  have hf := (Finset.mem_filter.mp hd).2
  exact ⟨⟨d, hf.symm ▸ t.property⟩, hf, rfl⟩

-- @node: incidenceCorner
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [a designated outer
face](hyp:t0), and [a triangulation of the map](hyp:hT), the [chosen incidence
corner](goal) is a spoke corner at [a black nonouter face](hyp:t) and [a
vertex](hyp:v) [belonging to that face](hyp:hv). -/
noncomputable def incidenceCorner (hT : IsSphereTriangulation T)
    (t : blackNonOuter T col t0) (v : T.Vertex) (hv : v ∈ T.faceVertices t.val) :
    SpokeCorner T (blackNonOuter T col t0) :=
  Classical.choose (incidenceCorner_exists T col t0 hT t v hv)

-- @node: incidenceCorner_spec
/-- If [the sphere map is a triangulation](hyp:hT) and [the vertex belongs to the
black nonouter face](hyp:hv), then [the chosen incidence corner has exactly that
face and that vertex](goal). -/
lemma incidenceCorner_spec (hT : IsSphereTriangulation T)
    (t : blackNonOuter T col t0) (v : T.Vertex) (hv : v ∈ T.faceVertices t.val) :
    T.faceOf (incidenceCorner T col t0 hT t v hv).val = t.val ∧
      T.vert (incidenceCorner T col t0 hT t v hv).val = v :=
  Classical.choose_spec (incidenceCorner_exists T col t0 hT t v hv)

-- @node: pairCycleFace_spec
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates faces of
opposite colors](hyp:hcol), and [the directed edge belongs to the undirected edges
selected by the state pair](hyp:hd), then [its underlying edge lies on its chosen
supplying face](goal). -/
lemma pairCycleFace_spec (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    T.edgeOnFace (T.edgeOf d) (pairCycleIncidence T col t0 hT hcol p d hd).1.val :=
  (Classical.choose_spec (exists_pairCycleIncidence T col t0 hT hcol p d hd)).2

-- @node: pairCycleFace_edge
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [the directed edge is selected by the state
pair](hyp:hd), then [there is a black nonouter face equal to its chosen supplying
face whose paired directed edge has the same underlying undirected edge](goal). -/
lemma pairCycleFace_edge (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    ∃ t : blackNonOuter T col t0,
      (pairCycleIncidence T col t0 hT hcol p d hd).1 = t ∧
      T.edgeOf d = T.edgeOf (pairedDart T col t0 hT p.val.1 p.val.2 p.property t) := by
  obtain ⟨e, he, hed⟩ := Finset.mem_image.mp hd
  obtain ⟨t, rfl⟩ := (pairedEdges_mem_iff T col t0 hT _ _ p.property e).mp he
  obtain ⟨a, ha, hf⟩ := pairCycleFace_spec T col t0 hT hcol p d hd
  have ht := (pairedDart_spec T col t0 hT _ _ p.property t).2.2
  have heq : (pairCycleIncidence T col t0 hT hcol p d hd).1 = t := by
    apply Subtype.ext
    exact selected_edge_face_unique T _ (bounded_faces_disjoint T col t0 hcol)
      _ _ (pairCycleIncidence T col t0 hT hcol p d hd).1.property t.property
      a _ (Or.inl hf) ht (ha.trans hed.symm)
  exact ⟨t, heq, hed.symm⟩

-- @node: pairCycleFace_injective
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [every directed edge of the cycle is selected by the
state pair](hyp:hC), then [distinct directed edges of the cycle have distinct
chosen supplying faces](goal). -/
lemma pairCycleFace_injective (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    Function.Injective (fun d : {d // d ∈ C.val} =>
      (pairCycleIncidence T col t0 hT hcol p d.val (hC d.val d.property)).1) := by
  intro d e he
  obtain ⟨t, ht, hd⟩ := pairCycleFace_edge T col t0 hT hcol p d.val (hC _ d.property)
  obtain ⟨u, hu, he'⟩ := pairCycleFace_edge T col t0 hT hcol p e.val (hC _ e.property)
  have htu : t = u := ht.symm.trans (he.trans hu)
  rw [← htu] at he'
  apply Subtype.ext
  exact List.inj_on_of_nodup_map C.property.1.2.1 d.property e.property (hd.trans he'.symm)

-- @node: pairCycleTail_mem
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [the directed edge is selected by the state
pair](hyp:hd), then [its starting vertex belongs to its chosen supplying
face](goal). -/
lemma pairCycleTail_mem (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    T.vert d ∈ T.faceVertices (pairCycleIncidence T col t0 hT hcol p d hd).1.val := by
  obtain ⟨t, ht, he⟩ := pairCycleFace_edge T col t0 hT hcol p d hd
  rw [ht]
  have hs := pairedDart_spec T col t0 hT _ _ p.property t
  rcases (T.edgeOf_eq_iff d _).mp he with he | he
  · rw [← he, hs.1]
    exact p.val.1.property.incident t
  · have hv : T.vert d = T.head (pairedDart T col t0 hT p.val.1 p.val.2 p.property t) := by
      rw [he]
      exact (congrArg T.vert (T.edgeInv_involutive d)).symm
    rw [hv, hs.2.1]
    exact p.val.2.property.incident t

-- @node: pairCycleSpokes
/-- For [a sphere map](hyp:T) with [a face coloring](hyp:col), [an outer
face](hyp:t0), [a triangulation](hyp:hT), and [opposite colors across each
edge](hyp:hcol), the [two-spoke replacement](goal) of [a directed edge](hyp:d)
[selected by](hyp:hd) [a state pair](hyp:p) first [chooses its supplying face and
terminal incidence](step:1), then [returns the spoke from its starting vertex to
that face center followed by the spoke from that center to its ending vertex](step:2). -/
noncomputable def pairCycleSpokes (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    SpokeDart T (blackNonOuter T col t0) × SpokeDart T (blackNonOuter T col t0) :=
  let i := pairCycleIncidence T col t0 hT hcol p d hd
  ((incidenceCorner T col t0 hT i.1 (T.vert d)
      (pairCycleTail_mem T col t0 hT hcol p d hd), true),
    (incidenceCorner T col t0 hT i.1 (T.head d) i.2.property, false))

-- @node: pairCycleSpokes_spec
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [the directed edge is selected by the state
pair](hyp:hd), then [the first replacement spoke runs from its starting vertex to
its chosen supplying face center, and the second runs from that center to its
ending vertex](goal). -/
lemma pairCycleSpokes_spec (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    let N := spokeGraphBounded T col t0 hT hcol
    let ab := pairCycleSpokes T col t0 hT hcol p d hd
    N.vert ab.1 = Sum.inl (T.vert d) ∧
    N.head ab.1 = Sum.inr (pairCycleIncidence T col t0 hT hcol p d hd).1 ∧
    N.vert ab.2 = Sum.inr (pairCycleIncidence T col t0 hT hcol p d hd).1 ∧
    N.head ab.2 = Sum.inl (T.head d) := by
  dsimp only
  have ha := incidenceCorner_spec T col t0 hT
    (pairCycleIncidence T col t0 hT hcol p d hd).1 (T.vert d)
    (pairCycleTail_mem T col t0 hT hcol p d hd)
  have hb := incidenceCorner_spec T col t0 hT
    (pairCycleIncidence T col t0 hT hcol p d hd).1 (T.head d)
    (pairCycleIncidence T col t0 hT hcol p d hd).2.property
  let N := spokeGraphBounded T col t0 hT hcol
  have hv (e : N.Dart) : N.vert e = spokeVert T (blackNonOuter T col t0) e := rfl
  have hi (e : N.Dart) : N.edgeInv e = (e.1, !e.2) :=
    spokeRotation_edgeInv T hT _ _ e
  dsimp only [N] at hv hi
  simp only [SphereMap.head, RotationSystem.head, hi, hv, pairCycleSpokes,
    spokeVert, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, ha.2]
  exact ⟨True.intro, congrArg Sum.inr (Subtype.ext ha.1),
    congrArg Sum.inr (Subtype.ext hb.1), congrArg Sum.inl hb.2⟩

-- @node: pairCycleLiftDarts
/-- For [a sphere map](hyp:T) with [a face coloring](hyp:col), [an outer
face](hyp:t0), [a triangulation](hyp:hT), and [opposite colors across every
edge](hyp:hcol), the [lifted list of directed spokes](goal) replaces each directed
edge of [a cycle](hyp:C), [all of whose edges are selected](hyp:hC) by [a state
pair](hyp:p), with its two-spoke path through its supplying face center, preserving
the cycle's order. -/
noncomputable def pairCycleLiftDarts (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    List (SpokeDart T (blackNonOuter T col t0)) :=
  C.val.attach.flatMap (fun d =>
    let ab := pairCycleSpokes T col t0 hT hcol p d.val (hC _ d.property)
    [ab.1, ab.2])

-- @node: pairCycleSpokes_edge_eq
/-- Assume [the sphere map is a triangulation](hyp:hT), [every edge separates
opposite face colors](hyp:hcol), and [both original directed edges are selected
by the state pair](hyp:hd,he). If [the first spoke comes from the first edge's
replacement](hyp:ha), [the second spoke comes from the second edge's
replacement](hyp:hb), and [these spokes have the same underlying edge](hyp:hab),
then [the two original directed edges have the same chosen supplying face](goal). -/
lemma pairCycleSpokes_edge_eq (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d e : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p)
    (he : T.edgeOf e ∈ undirectedPairedEdges T col t0 hT p)
    (a b : (spokeGraphBounded T col t0 hT hcol).Dart)
    (ha : a ∈ [(pairCycleSpokes T col t0 hT hcol p d hd).1,
      (pairCycleSpokes T col t0 hT hcol p d hd).2])
    (hb : b ∈ [(pairCycleSpokes T col t0 hT hcol p e he).1,
      (pairCycleSpokes T col t0 hT hcol p e he).2])
    (hab : (spokeGraphBounded T col t0 hT hcol).edgeOf a =
      (spokeGraphBounded T col t0 hT hcol).edgeOf b) :
    (pairCycleIncidence T col t0 hT hcol p d hd).1 =
      (pairCycleIncidence T col t0 hT hcol p e he).1 := by
  have hs := pairCycleSpokes_spec T col t0 hT hcol p d hd
  have ht := pairCycleSpokes_spec T col t0 hT hcol p e he
  dsimp only [SphereMap.head, RotationSystem.head] at hs ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases ((spokeGraphBounded T col t0 hT hcol).edgeOf_eq_iff _ _).mp hab with h | h
  · exact Sum.inr.inj (ht.2.1.symm.trans ((congrArg
      (spokeGraphBounded T col t0 hT hcol).head h).trans hs.2.1)) |>.symm
  · have h' := congrArg (spokeGraphBounded T col t0 hT hcol).vert h
    rw [ht.1, hs.2.1] at h'
    contradiction
  · have h' := congrArg (spokeGraphBounded T col t0 hT hcol).vert h
    rw [ht.2.2.1, hs.1] at h'
    contradiction
  · exact (Sum.inr.inj (ht.2.2.1.symm.trans
      ((congrArg (spokeGraphBounded T col t0 hT hcol).vert h).trans hs.2.1))).symm
  · have h' := congrArg (spokeGraphBounded T col t0 hT hcol).vert h
    rw [ht.1, hs.2.2.1] at h'
    contradiction
  · have h' := congrArg (spokeGraphBounded T col t0 hT hcol).head h
    dsimp only [SphereMap.head, RotationSystem.head] at h'
    rw [(spokeGraphBounded T col t0 hT hcol).edgeInv_involutive] at h'
    exact (Sum.inr.inj (ht.2.1.symm.trans (h'.trans hs.2.2.1))).symm
  · exact (Sum.inr.inj (ht.2.2.1.symm.trans
      ((congrArg (spokeGraphBounded T col t0 hT hcol).vert h).trans hs.2.2.1))).symm
  · have h' := congrArg (spokeGraphBounded T col t0 hT hcol).vert h
    rw [ht.2.2.1, hs.2.2.2] at h'
    contradiction

-- @node: pairCycleSpokes_edge_ne
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [the directed edge is selected by the state
pair](hyp:hd), then [the two spokes replacing it have different underlying
undirected edges](goal). -/
lemma pairCycleSpokes_edge_ne (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    let N := spokeGraphBounded T col t0 hT hcol
    let ab := pairCycleSpokes T col t0 hT hcol p d hd
    N.edgeOf ab.1 ≠ N.edgeOf ab.2 := by
  dsimp only
  intro he
  have hs := pairCycleSpokes_spec T col t0 hT hcol p d hd
  rcases ((spokeGraphBounded T col t0 hT hcol).edgeOf_eq_iff _ _).mp he with h | h
  · have hv := congrArg (spokeGraphBounded T col t0 hT hcol).vert h
    rw [hs.2.2.1, hs.1] at hv
    contradiction
  · have hv := congrArg (spokeGraphBounded T col t0 hT hcol).head h
    have hh : (spokeGraphBounded T col t0 hT hcol).head
        ((spokeGraphBounded T col t0 hT hcol).edgeInv
          (pairCycleSpokes T col t0 hT hcol p d hd).1) =
        (spokeGraphBounded T col t0 hT hcol).vert
          (pairCycleSpokes T col t0 hT hcol p d hd).1 :=
      congrArg (spokeGraphBounded T col t0 hT hcol).vert
        ((spokeGraphBounded T col t0 hT hcol).edgeInv_involutive _)
    rw [hh, hs.2.2.2, hs.1] at hv
    exact hT.props.2.1.1 d (Sum.inl.inj hv).symm

-- @node: pairCycleLift_edges_nodup
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [every directed edge of the cycle is selected by the
state pair](hyp:hC), then [the lifted cycle's list of underlying spoke edges has
no repetitions](goal). -/
lemma pairCycleLift_edges_nodup (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    ((pairCycleLiftDarts T col t0 hT hcol p C hC).map
      (spokeGraphBounded T col t0 hT hcol).edgeOf).Nodup := by
  unfold pairCycleLiftDarts
  rw [List.map_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro d hd
    simpa using pairCycleSpokes_edge_ne T col t0 hT hcol p d.val (hC _ d.property)
  · apply (List.nodup_attach.mpr (C.property.2.of_map T.vert)).pairwise_of_forall_ne
    intro d hd e he hne
    apply List.disjoint_left.mpr
    intro z hz hw
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hw
    exact hne (pairCycleFace_injective T col t0 hT hcol p C hC
      (pairCycleSpokes_edge_eq T col t0 hT hcol p d.val e.val
        (hC _ d.property) (hC _ e.property) a b ha hb hab.symm))

-- @node: pairCycleLift_vertices_nodup
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [every directed edge of the cycle is selected by the
state pair](hyp:hC), then [the starting vertices of the lifted directed spokes
have no repetitions](goal). -/
lemma pairCycleLift_vertices_nodup (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    ((pairCycleLiftDarts T col t0 hT hcol p C hC).map
      (spokeGraphBounded T col t0 hT hcol).vert).Nodup := by
  have hv (d : {d // d ∈ C.val}) :
      ([(pairCycleSpokes T col t0 hT hcol p d.val (hC _ d.property)).1,
        (pairCycleSpokes T col t0 hT hcol p d.val (hC _ d.property)).2].map
        (spokeGraphBounded T col t0 hT hcol).vert) =
      [Sum.inl (T.vert d.val), Sum.inr
        (pairCycleIncidence T col t0 hT hcol p d.val (hC _ d.property)).1] := by
    simp only [List.map_cons, List.map_nil,
      (pairCycleSpokes_spec T col t0 hT hcol p d.val (hC _ d.property)).1,
      (pairCycleSpokes_spec T col t0 hT hcol p d.val (hC _ d.property)).2.2.1]
  unfold pairCycleLiftDarts
  rw [List.map_flatMap]
  simp only [hv]
  apply List.nodup_flatMap.mpr
  constructor
  · intro d hd
    simp
  · apply (List.nodup_attach.mpr (C.property.2.of_map T.vert)).pairwise_of_forall_ne
    intro d hd e he hne
    simp only [List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
    intro z hz hw
    rcases hz with rfl | rfl <;> rcases hw with hw | hw
    · exact hne (Subtype.ext (List.inj_on_of_nodup_map C.property.2 d.property e.property
        (Sum.inl.inj hw)))
    · contradiction
    · contradiction
    · exact hne (pairCycleFace_injective T col t0 hT hcol p C hC (Sum.inr.inj hw))

-- @node: zip_subdivision_open
/-- For two maps, an initial element, a list of subsequent elements, and a final
endpoint, [pairing successive entries after replacing each element by its two
images gives exactly the ordered list formed from each original transition by
pairing the first image with the second image at its start, then the second
image at its start with the first image at its end](goal). -/
lemma zip_subdivision_open {α β : Type*} (a b : α → β) (xs : List α) (x y : α) :
    ((x :: xs).flatMap (fun z => [a z, b z])).zip
        (b x :: xs.flatMap (fun z => [a z, b z]) ++ [a y]) =
      ((x :: xs).zip (xs ++ [y])).flatMap (fun p =>
        [(a p.1, b p.1), (b p.1, a p.2)]) := by
  induction xs generalizing x with
  | nil => simp
  | cons z xs ih =>
    simpa only [List.flatMap_cons, List.cons_append, List.nil_append,
      List.zip_cons_cons] using congrArg (fun l => (a x, b x) :: (b x, a z) :: l) (ih z)

-- @node: zip_subdivision_cycle
/-- For two maps and a list regarded cyclically, [the consecutive pairs in the
list obtained by replacing each element by its two images are exactly, for each
original cyclic transition, the pair of images at its start followed by the pair
from the second image at its start to the first image at its end](goal). -/
lemma zip_subdivision_cycle {α β : Type*} (a b : α → β) (xs : List α) :
    (xs.flatMap (fun z => [a z, b z])).zip
        ((xs.flatMap (fun z => [a z, b z])).rotate 1) =
      (xs.zip (xs.rotate 1)).flatMap (fun p =>
        [(a p.1, b p.1), (b p.1, a p.2)]) := by
  cases xs with
  | nil => simp
  | cons x xs => simpa using zip_subdivision_open a b xs x x

-- @node: pairCycleLift_isSimple
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [every directed edge of the cycle is selected by the
state pair](hyp:hC), then [replacing its edges by their two-spoke paths gives a
simple cycle in the spoke graph of black nonouter faces](goal). -/
lemma pairCycleLift_isSimple (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    (spokeGraphBounded T col t0 hT hcol).IsSimpleCycle
      (pairCycleLiftDarts T col t0 hT hcol p C hC) := by
  let N := spokeGraphBounded T col t0 hT hcol
  let a (d : {d // d ∈ C.val}) := (pairCycleSpokes T col t0 hT hcol p d.val (hC _ d.property)).1
  let b (d : {d // d ∈ C.val}) := (pairCycleSpokes T col t0 hT hcol p d.val (hC _ d.property)).2
  have hz : ∀ x y, (x, y) ∈ (pairCycleLiftDarts T col t0 hT hcol p C hC).zip
      ((pairCycleLiftDarts T col t0 hT hcol p C hC).rotate 1) → N.head x = N.vert y := by
    intro x y hxy
    change (x, y) ∈ (C.val.attach.flatMap (fun d => [a d, b d])).zip
      ((C.val.attach.flatMap (fun d => [a d, b d])).rotate 1) at hxy
    rw [zip_subdivision_cycle] at hxy
    obtain ⟨⟨d, e⟩, hde, hxy⟩ := List.mem_flatMap.mp hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (pairCycleSpokes_spec T col t0 hT hcol p d.val (hC _ d.property)).2.1.trans
        (pairCycleSpokes_spec T col t0 hT hcol p d.val (hC _ d.property)).2.2.1.symm
    · have he : T.head d.val = T.vert e.val := by
        apply cyclic_zip_map_step C.val T.head T.vert
        · apply List.ext_getElem
          · simp
          · intro i hi hj
            simpa only [List.getElem_map, List.getElem_rotate, List.get_eq_getElem] using
              C.property.1.2.2 ⟨i, by simpa using hi⟩
        · have hm : (d.val, e.val) ∈ (C.val.attach.zip (C.val.attach.rotate 1)).map
              (fun z => (z.1.val, z.2.val)) := List.mem_map.mpr ⟨(d, e), hde, rfl⟩
          have heq : (C.val.attach.zip (C.val.attach.rotate 1)).map
              (fun z => (z.1.val, z.2.val)) = C.val.zip (C.val.rotate 1) := by
            change (C.val.attach.zip (C.val.attach.rotate 1)).map
              (Prod.map Subtype.val Subtype.val) = _
            rw [← List.zip_map, List.attach_map_subtype_val, List.map_rotate,
              List.attach_map_subtype_val]
          exact heq ▸ hm
      exact (pairCycleSpokes_spec T col t0 hT hcol p d.val (hC _ d.property)).2.2.2.trans
        ((congrArg Sum.inl he).trans
          (pairCycleSpokes_spec T col t0 hT hcol p e.val (hC _ e.property)).1.symm)
  refine ⟨⟨?_, pairCycleLift_edges_nodup T col t0 hT hcol p C hC, ?_⟩,
    pairCycleLift_vertices_nodup T col t0 hT hcol p C hC⟩
  · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
    have hm : a ⟨d, hd⟩ ∈ pairCycleLiftDarts T col t0 hT hcol p C hC :=
      List.mem_flatMap.mpr ⟨⟨d, hd⟩, List.mem_attach _ _, by simp [a]⟩
    exact fun h => by simp [h] at hm
  · intro i
    apply hz
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simp [i.isLt], ?_⟩
    simp only [List.getElem_zip, List.getElem_rotate, List.get_eq_getElem]
    rfl

-- @node: pairCycleLift
/-- For [a sphere map](hyp:T) with [a face coloring](hyp:col), [an outer
face](hyp:t0), [a triangulation](hyp:hT), and [opposite colors across every
edge](hyp:hcol), the [lifted simple cycle](goal) of [a cycle](hyp:C) [using only
edges selected](hyp:hC) by [a state pair](hyp:p) is the cycle in the spoke graph
obtained by replacing each edge with its two-spoke path through the supplying
face center. -/
noncomputable def pairCycleLift (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    (spokeGraphBounded T col t0 hT hcol).Cycle :=
  ⟨pairCycleLiftDarts T col t0 hT hcol p C hC,
    pairCycleLift_isSimple T col t0 hT hcol p C hC⟩

-- @node: pairCycleFace_sides
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [the directed edge is selected by the state
pair](hyp:hd), then [its chosen supplying face is the face on one of its two
sides](goal). -/
lemma pairCycleFace_sides (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    T.faceOf d = (pairCycleIncidence T col t0 hT hcol p d hd).1.val ∨
      T.faceOf (T.edgeInv d) = (pairCycleIncidence T col t0 hT hcol p d hd).1.val := by
  obtain ⟨e, he, hf⟩ := pairCycleFace_spec T col t0 hT hcol p d hd
  rcases (T.edgeOf_eq_iff d e).mp he.symm with rfl | rfl
  · exact Or.inl hf
  · exact Or.inr hf

-- @node: pairCycleSpokes_shortcut
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [the directed edge is selected by the state
pair](hyp:hd), then [that directed edge shortcuts its two-spoke replacement: it
runs from the first spoke's original vertex to the second spoke's original
vertex along a side of their supplying face](goal). -/
lemma pairCycleSpokes_shortcut (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    let ab := pairCycleSpokes T col t0 hT hcol p d hd
    FaceDart T (T.faceOf ab.1.1.val) (T.vert ab.1.1.val) (T.vert ab.2.1.val) d := by
  dsimp only [pairCycleSpokes]
  have ha := incidenceCorner_spec T col t0 hT _ _ (pairCycleTail_mem T col t0 hT hcol p d hd)
  have hb := incidenceCorner_spec T col t0 hT _ _
    (pairCycleIncidence T col t0 hT hcol p d hd).2.property
  exact ⟨ha.2.symm, hb.2.symm, ha.1.symm ▸ pairCycleFace_sides T col t0 hT hcol p d hd⟩

-- @node: pairCycleLift_projection
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [every directed edge of the cycle is selected by the
state pair](hyp:hC), then [projecting its lifted spoke cycle recovers the original
cycle exactly](goal). -/
lemma pairCycleLift_projection (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    spokeCycleProjection T col t0 hT hcol (pairCycleLift T col t0 hT hcol p C hC) = C := by
  apply Subtype.ext
  let a (d : {d // d ∈ C.val}) := (pairCycleSpokes T col t0 hT hcol p d.val (hC _ d.property)).1
  let b (d : {d // d ∈ C.val}) := (pairCycleSpokes T col t0 hT hcol p d.val (hC _ d.property)).2
  change projectSpokeDarts T _ (C.val.attach.flatMap (fun d => [a d, b d])) = C.val
  unfold projectSpokeDarts
  rw [zip_subdivision_cycle, List.filterMap_flatMap]
  have hshort (d : {d // d ∈ C.val}) :
      ∃ e, FaceDart T (T.faceOf (a d).1.val) (T.vert (a d).1.val) (T.vert (b d).1.val) e :=
    ⟨d.val, pairCycleSpokes_shortcut T col t0 hT hcol p d.val (hC _ d.property)⟩
  have hchoose (d : {d // d ∈ C.val}) : (Classical.choose (hshort d) : T.Dart) = d.val := by
    have hs := Classical.choose_spec (hshort d)
    have ht := pairCycleSpokes_shortcut T col t0 hT hcol p d.val (hC _ d.property)
    exact T.dart_eq_of_endpoints hT.props.2.1 _ _ (hs.1.trans ht.1.symm)
      (hs.2.1.trans ht.2.1.symm)
  dsimp only [a, b, pairCycleSpokes] at hshort hchoose
  calc
    _ = (C.val.attach.zip (C.val.attach.rotate 1)).flatMap (fun z => [z.1.val]) := by
      apply List.flatMap_congr
      intro z hz
      simp only [List.filterMap_cons, List.filterMap_nil, a, b, pairCycleSpokes,
        Bool.false_eq_true, ↓reduceIte]
      rw [dif_pos (hshort z.1), hchoose]
    _ = C.val := by
      rw [← List.map_eq_flatMap]
      change (C.val.attach.zip (C.val.attach.rotate 1)).map (Subtype.val ∘ Prod.fst) = _
      rw [← List.map_map]
      rw [List.map_fst_zip (by simp), List.attach_map_subtype_val]

-- @node: signedSpokeDart_incidenceCorner
/-- If [the sphere map is a triangulation](hyp:hT) and [the vertex belongs to the
black nonouter face](hyp:hv), then [the signed weight of the spoke at their chosen
incidence corner is the negative incidence weight when its direction flag is
true, and the positive incidence weight when the flag is false](goal). -/
lemma signedSpokeDart_incidenceCorner (hT : IsSphereTriangulation T)
    (a : IncidenceWeights T col t0) (t : blackNonOuter T col t0)
    (v : T.Vertex) (hv : v ∈ T.faceVertices t.val) (b : Bool) :
    signedSpokeDart T col t0 a (incidenceCorner T col t0 hT t v hv, b) =
      if b then -a t ⟨v, hv⟩ else a t ⟨v, hv⟩ := by
  have hs := incidenceCorner_spec T col t0 hT t v hv
  have he : a ⟨T.faceOf (incidenceCorner T col t0 hT t v hv).val,
        (incidenceCorner T col t0 hT t v hv).property⟩
      ⟨T.vert (incidenceCorner T col t0 hT t v hv).val, corner_incident T _ _⟩ = a t ⟨v, hv⟩ := by
    congr 1
    · exact Subtype.ext hs.1
    · exact (Subtype.heq_iff_coe_eq (fun x => by dsimp only; rw [hs.1])).mpr hs.2
  unfold signedSpokeDart
  rw [he]

-- @node: pairCycleFace_reverse
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), [the directed edge is selected by the state pair](hyp:hd),
and [its reversal is also selected](hyp:hi), then [reversing it leaves its chosen
supplying face unchanged](goal). -/
lemma pairCycleFace_reverse (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (p : Pair T col t0) (d : T.Dart)
    (hd : T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p)
    (hi : T.edgeOf (T.edgeInv d) ∈ undirectedPairedEdges T col t0 hT p) :
    (pairCycleIncidence T col t0 hT hcol p (T.edgeInv d) hi).1 =
      (pairCycleIncidence T col t0 hT hcol p d hd).1 := by
  apply Subtype.ext
  exact selected_edge_face_unique T _ (bounded_faces_disjoint T col t0 hcol)
    _ _ (pairCycleIncidence T col t0 hT hcol p (T.edgeInv d) hi).1.property
    (pairCycleIncidence T col t0 hT hcol p d hd).1.property _ _
    (pairCycleFace_sides T col t0 hT hcol p (T.edgeInv d) hi)
    (pairCycleFace_sides T col t0 hT hcol p d hd)
    (((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm)

-- @node: orientedPairCycleWeight_eq_sum
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [every directed edge of the cycle is selected by the
state pair](hyp:hC), then [the cycle's oriented weight equals the sum, over its
directed edges, of the incidence weight at each edge's chosen supplying face and
ending vertex](goal). -/
lemma orientedPairCycleWeight_eq_sum (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (a : IncidenceWeights T col t0) (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    orientedPairCycleWeight T col t0 hT hcol a p C hC =
      ∑ d : {d // d ∈ C.val},
        a (pairCycleIncidence T col t0 hT hcol p d.val (hC _ d.property)).1
          (pairCycleIncidence T col t0 hT hcol p d.val (hC _ d.property)).2 := by
  unfold orientedPairCycleWeight cycleWeight
  rw [List.map_map, ← List.sum_toFinset _ (List.nodup_attach.mpr (C.property.2.of_map T.vert))]
  have he : C.val.attach.toFinset = Finset.univ := by ext; simp
  rw [he]
  rfl

-- @node: orientedPairCycleWeight_reverse_eq_sum
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [every directed edge of the cycle is selected by the
state pair](hyp:hC), then [the reversed cycle's oriented weight equals the sum,
over the original cycle's directed edges, of the incidence weight at each edge's
chosen supplying face and starting vertex](goal). -/
lemma orientedPairCycleWeight_reverse_eq_sum (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (a : IncidenceWeights T col t0)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    orientedPairCycleWeight T col t0 hT hcol a p (reverseCycle T C)
        (reverseCycle_paired T col t0 hT p C hC) =
      ∑ d : {d // d ∈ C.val},
        a (pairCycleIncidence T col t0 hT hcol p d.val (hC _ d.property)).1
          ⟨T.vert d.val, pairCycleTail_mem T col t0 hT hcol p d.val (hC _ d.property)⟩ := by
  rw [orientedPairCycleWeight_eq_sum]
  let e : {d // d ∈ (reverseCycle T C).val} ≃ {d // d ∈ C.val} :=
    { toFun := fun d => ⟨T.edgeInv d.val, (T.mem_reverseCycle_iff C d.val).mp d.property⟩
      invFun := fun d => ⟨T.edgeInv d.val, (T.mem_reverseCycle_iff C _).mpr
        (by rw [T.edgeInv_involutive]; exact d.property)⟩
      left_inv := fun d => Subtype.ext (T.edgeInv_involutive d.val)
      right_inv := fun d => Subtype.ext (T.edgeInv_involutive d.val) }
  apply Fintype.sum_equiv e
  intro d
  have hf := pairCycleFace_reverse T col t0 hT hcol p d.val
    (reverseCycle_paired T col t0 hT p C hC _ d.property) (hC _ (e d).property)
  have hh : T.head d.val = T.vert (e d).val := rfl
  congr 1
  · exact hf.symm
  · apply (Subtype.heq_iff_coe_eq (fun v => by
        rw [← congrArg Subtype.val hf]; rfl)).mpr
    exact hh

-- @node: signedSpokeWeight_pairCycleLift
/-- If [the sphere map is a triangulation](hyp:hT), [every edge separates opposite
face colors](hyp:hcol), and [every directed edge of the cycle is selected by the
state pair](hyp:hC), then [the signed weight of its lifted spoke cycle equals its
oriented weight minus the oriented weight of its reversal](goal). -/
lemma signedSpokeWeight_pairCycleLift (hT : IsSphereTriangulation T)
    (hcol : PartitionColoring T col) (a : IncidenceWeights T col t0)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    signedSpokeWeight T col t0 hT hcol a (pairCycleLift T col t0 hT hcol p C hC) =
      orientedPairCycleWeight T col t0 hT hcol a p C hC -
        orientedPairCycleWeight T col t0 hT hcol a p (reverseCycle T C)
          (reverseCycle_paired T col t0 hT p C hC) := by
  unfold signedSpokeWeight pairCycleLift pairCycleLiftDarts
  rw [List.map_flatMap, List.flatMap, List.sum_flatten, List.map_map]
  simp only [pairCycleSpokes, List.map_cons, List.map_nil,
    signedSpokeDart_incidenceCorner, Bool.false_eq_true, ↓reduceIte]
  rw [← List.sum_toFinset _ (List.nodup_attach.mpr (C.property.2.of_map T.vert))]
  have he : C.val.attach.toFinset = Finset.univ := by ext; simp
  rw [he, orientedPairCycleWeight_eq_sum T col t0 hT hcol a p C hC,
    orientedPairCycleWeight_reverse_eq_sum T col t0 hT hcol a p C hC,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  dsimp only [Function.comp_apply, pairCycleIncidence]
  simp only [List.sum_cons, List.sum_nil, add_zero]
  ring

-- @node: pairedCycle_weight_comparison
/-- Assume [the sphere map is a triangulation](hyp:hT), [every edge separates
opposite face colors](hyp:hcol), and [every counterclockwise cycle in the spoke
graph has strictly positive signed weight](hyp:hpos). If [every directed edge of
the original cycle is selected by the state pair](hyp:hC), then [its clockwise
weight is strictly less than its counterclockwise weight](goal). -/
lemma pairedCycle_weight_comparison (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col)
    (a : IncidenceWeights T col t0)
    (hpos : ∀ C : (spokeGraphBounded T col t0 hT hcol).Cycle,
      (spokeGraphBounded T col t0 hT hcol).IsCounterclockwise (spokeOuter T col t0 hT hcol) C →
        0 < signedSpokeWeight T col t0 hT hcol a C)
    (p : Pair T col t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p) :
    clockwiseCycleWeight T col t0 hT hcol a p C hC <
      counterclockwiseCycleWeight T col t0 hT hcol a p C hC := by
  have gap (D : T.Cycle)
      (hD : ∀ d ∈ D.val, T.edgeOf d ∈ undirectedPairedEdges T col t0 hT p)
      (hcc : T.IsCounterclockwise t0 D) :
      0 < orientedPairCycleWeight T col t0 hT hcol a p D hD -
        orientedPairCycleWeight T col t0 hT hcol a p (reverseCycle T D)
          (reverseCycle_paired T col t0 hT p D hD) := by
    have ho : (spokeGraphBounded T col t0 hT hcol).IsCounterclockwise
        (spokeOuter T col t0 hT hcol) (pairCycleLift T col t0 hT hcol p D hD) := by
      apply (spokeCycle_orientation T col t0 hT hcol _).mpr
      rwa [pairCycleLift_projection]
    have hw := hpos _ ho
    rwa [signedSpokeWeight_pairCycleLift] at hw
  by_cases hcc : T.IsCounterclockwise t0 C
  · have hcw : ¬ T.IsClockwise t0 C := fun h =>
      Set.disjoint_left.mp (T.cycle_sides_partition C).1 h hcc
    simpa only [clockwiseCycleWeight, counterclockwiseCycleWeight, if_pos hcc, if_neg hcw]
      using sub_pos.mp (gap C hC hcc)
  · have hcw : T.IsClockwise t0 C := by
      have hh : t0 ∈ T.leftRegion C ∪ T.rightRegion C :=
        (T.cycle_sides_partition C).2.symm ▸ Set.mem_univ t0
      exact hh.resolve_right hcc
    have hr : T.IsCounterclockwise t0 (reverseCycle T C) := by
      change t0 ∈ T.rightRegion (reverseCycle T C)
      rw [T.reverseCycle_rightRegion hT C]
      exact hcw
    have hw := gap (reverseCycle T C) (reverseCycle_paired T col t0 hT p C hC) hr
    have hi : reverseCycle T (reverseCycle T C) = C := by
      apply Subtype.ext
      simp only [reverseCycle, reverseDarts, List.map_reverse, List.reverse_reverse, List.map_map]
      rw [show T.edgeInv ∘ T.edgeInv = id from funext T.edgeInv_involutive, List.map_id]
    simp only [hi] at hw
    simpa only [clockwiseCycleWeight, counterclockwiseCycleWeight, if_neg hcc, if_pos hcw]
      using sub_pos.mp hw

end OaiPairedStatesHamiltonian
