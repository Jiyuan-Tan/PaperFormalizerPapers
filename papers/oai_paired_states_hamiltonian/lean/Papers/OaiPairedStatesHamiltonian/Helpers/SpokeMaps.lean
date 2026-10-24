module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SpokePlacement

/-! Inherited spoke embeddings, their cycle projections, and signed incidence weights. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


variable (T : SphereMap)

/-- For [a sphere map](hyp:T) that [is a sphere triangulation](hyp:hT), and
[selected faces](hyp:faces) such that [no edge has selected faces on both sides](hyp:hfaces),
the [spoke map](goal) replaces the selected triangles by spokes and inherits its
placement by gluing sectors across the removed original edges. -/
noncomputable def buildSpokes (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) : SphereMap where
  toRotationSystem := spokeRotation T hT faces hfaces
  genusZero := spoke_genus T hT faces hfaces
  Face := SpokeFace T faces
  boundaryFace := spokeBoundaryFace T hT faces hfaces
  placement_connected := spoke_placement_connected T hT faces hfaces
  placement_card := spoke_placement_card T hT faces hfaces

variable (col : T.Face → Bool) (t0 : T.Face)
/-- For [a sphere map](hyp:T), [a Boolean face coloring](hyp:col), and
[a distinguished outer face](hyp:t0), the [set of black faces](goal) consists of
all faces colored black after normalizing the coloring to make the outer face black. -/
noncomputable def blackFaces : Finset T.Face := Finset.univ.filter (fun f => normalizedColoring T col t0 f = true)
-- @node: bounded_faces_disjoint
/-- If [the face coloring separates the two faces incident to every edge](hyp:hcol),
then [no edge has bounded black faces on both sides](goal). -/
lemma bounded_faces_disjoint (hcol : PartitionColoring T col) (d : T.Dart) :
    ¬ (T.faceOf d ∈ blackNonOuter T col t0 ∧ T.faceOf (T.edgeInv d) ∈ blackNonOuter T col t0) := by
  rintro ⟨hd, he⟩
  have hd' := (Finset.mem_filter.mp hd).2.1
  have he' := (Finset.mem_filter.mp he).2.1
  exact normalizedColoring_partition T col hcol t0 d (hd'.trans he'.symm)
-- @node: black_faces_disjoint
/-- If [the face coloring separates the two faces incident to every edge](hyp:hcol),
then [no edge has black faces on both sides in the normalized coloring](goal). -/
lemma black_faces_disjoint (hcol : PartitionColoring T col) (d : T.Dart) :
    ¬ (T.faceOf d ∈ blackFaces T col t0 ∧ T.faceOf (T.edgeInv d) ∈ blackFaces T col t0) := by
  rintro ⟨hd, he⟩
  have hd' := (Finset.mem_filter.mp hd).2
  have he' := (Finset.mem_filter.mp he).2
  exact normalizedColoring_partition T col hcol t0 d (hd'.trans he'.symm)

-- @node: def:h0
/-- For [a sphere map](hyp:T) that [is a sphere triangulation](hyp:hT),
[a face coloring](hyp:col) that [separates faces across every edge](hyp:hcol), and
[a distinguished outer face](hyp:t0), the [bounded spoke map](goal) replaces each
black triangle other than the outer face by spokes, retaining isolated vertices. -/
noncomputable def spokeGraphBounded (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col) : SphereMap :=
  buildSpokes T hT (blackNonOuter T col t0) (bounded_faces_disjoint T col t0 hcol)
  -- @realizes H_0(spokes at all bounded black centers, isolated vertices retained)
-- @node: def:h
/-- For [a sphere map](hyp:T) that [is a sphere triangulation](hyp:hT),
[a face coloring](hyp:col) that [separates faces across every edge](hyp:hcol), and
[a distinguished outer face](hyp:t0), the [full spoke map](goal) replaces every
black triangle in the normalized coloring, including the outer face, by spokes. -/
noncomputable def spokeGraphAll (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col) : SphereMap :=
  buildSpokes T hT (blackFaces T col t0) (black_faces_disjoint T col t0 hcol)
  -- @realizes H(spokes at every black center, including t0)

-- @node: outer_not_bounded
/-- [The distinguished outer face is excluded from the set of bounded black faces](goal). -/
lemma outer_not_bounded : t0 ∉ blackNonOuter T col t0 := by
  intro h
  exact (Finset.mem_filter.mp h).2.2 rfl
/-- For [a sphere map](hyp:T) that [is a sphere triangulation](hyp:hT),
[a face coloring](hyp:col) that [separates faces across every edge](hyp:hcol), and
[a distinguished outer face](hyp:t0), the [outer face of the bounded spoke map](goal)
is the face class containing the original outer face. -/
noncomputable def spokeOuter (hT : IsSphereTriangulation T) (hcol : PartitionColoring T col) :
    (spokeGraphBounded T col t0 hT hcol).Face :=
  spokeFaceClass T (blackNonOuter T col t0) (Sum.inl ⟨t0, outer_not_bounded T col t0⟩)

end OaiPairedStatesHamiltonian
