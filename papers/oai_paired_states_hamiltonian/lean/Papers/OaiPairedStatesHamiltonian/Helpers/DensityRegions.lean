module

public import Papers.OaiPairedStatesHamiltonian.Helpers.DensityComponentEuler
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleDisk

/-! Deleted-edge regions are exactly the inherited induced faces. Boundary sides
are counted as darts, so both occurrences of a bridge remain in the count. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

variable (T : SphereMap)

-- @node: SphereMap.retainedEdges
/-- For [a sphere map](hyp:T) and [a selected finite set of vertices](hyp:U), the
[retained edges](goal) are the edges whose endpoints all belong to that set. -/
noncomputable def retainedEdges (U : Finset T.Vertex) : Set T.Edge :=
  {e | T.edgeEndpoints e ⊆ U}

-- @node: SphereMap.faceRegion
/-- For [a sphere map](hyp:T), [a set of retained edges](hyp:S), and [a starting
face](hyp:f), the [face region](goal) consists of all faces reachable from the
starting face by crossing only edges outside the retained set, including the
starting face itself. -/
noncomputable def faceRegion (S : Set T.Edge) (f : T.Face) : Set T.Face :=
  {g | Relation.ReflTransGen (fun a b => ∃ d, T.edgeOf d ∉ S ∧
    T.faceOf d = a ∧ T.faceOf (T.edgeInv d) = b) f g}

-- @node: SphereMap.regionSides
/-- For [a sphere map](hyp:T), [a set of retained edges](hyp:S), and [a set of
faces](hyp:R), the [region sides](goal) are the directed edge occurrences whose
edges are retained and whose incident faces belong to the given set. -/
noncomputable def regionSides (S : Set T.Edge) (R : Set T.Face) : Finset T.Dart :=
  Finset.univ.filter (fun d => T.edgeOf d ∈ S ∧ T.faceOf d ∈ R)

-- @node: SphereMap.retainedEdges_edgeOf
/-- [The edge of a directed edge occurrence is retained exactly when both its
tail and its head belong to the selected vertex set](goal). -/
lemma retainedEdges_edgeOf (U : Finset T.Vertex) (d : T.Dart) :
    T.edgeOf d ∈ T.retainedEdges U ↔ T.vert d ∈ U ∧ T.head d ∈ U := by
  constructor
  · intro h
    have hv : T.vert d ∈ T.edgeEndpoints (T.edgeOf d) :=
      Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    have hi : T.head d ∈ T.edgeEndpoints (T.edgeOf d) := by
      apply Finset.mem_image.mpr
      exact ⟨T.edgeInv d, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm⟩, rfl⟩
    exact ⟨h hv, h hi⟩
  · rintro ⟨hv, hw⟩ v hmem
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
    rcases (T.edgeOf_eq_iff d e).mp (Finset.mem_filter.mp he).2.symm with rfl | rfl
    · exact hv
    · exact hw

-- @node: SphereMap.inducedFaceRelation_symmetric
/-- [The relation joining faces across an edge that is removed when restricting
to a vertex set is symmetric](goal). -/
lemma inducedFaceRelation_symmetric (U : Set T.Vertex) :
    Std.Symm (T.inducedFaceRelation U) := by
  constructor
  rintro f g ⟨d, hd, rfl, rfl⟩
  refine ⟨T.edgeInv d, ?_, rfl, ?_⟩
  · intro hi
    apply hd
    have hv := hi.2
    change T.vert (T.edgeInv (T.edgeInv d)) ∈ U at hv
    rw [T.edgeInv_involutive] at hv
    exact ⟨hv, hi.1⟩
  · rw [T.edgeInv_involutive]

-- @node: SphereMap.inducedFaceClass_eq_iff_faceRegion
/-- [Two original faces represent the same induced face exactly when the second
is reachable from the first by crossing only edges not retained by the selected
vertex set](goal). -/
lemma inducedFaceClass_eq_iff_faceRegion (U : Finset T.Vertex) (f g : T.Face) :
    T.inducedFaceClass (↑U : Set T.Vertex) f =
      T.inducedFaceClass (↑U : Set T.Vertex) g ↔
        g ∈ T.faceRegion (T.retainedEdges U) f := by
  let rel := T.inducedFaceRelation (↑U : Set T.Vertex)
  let : Std.Symm rel := T.inducedFaceRelation_symmetric _
  have hrel : rel = (fun a b => ∃ d, T.edgeOf d ∉ T.retainedEdges U ∧
      T.faceOf d = a ∧ T.faceOf (T.edgeInv d) = b) := by
    funext a b
    apply propext
    simp only [rel, inducedFaceRelation, T.retainedEdges_edgeOf, Finset.mem_coe]
  have he : (T.inducedFaceClass (↑U : Set T.Vertex) f =
      T.inducedFaceClass (↑U : Set T.Vertex) g) ↔ Relation.EqvGen rel f g :=
    ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := Relation.EqvGen.setoid rel) h⟩
  rw [he]
  rw [Relation.EqvGen.eqvGen_eq_reflTransGen, hrel]
  rfl

-- @node: SphereMap.regionSides_eq_induced_face_darts
/-- [The sides of the deleted-edge region containing an original face are
exactly the directed edge occurrences with both endpoints selected and with
incident face representing the same induced face as that original face](goal). -/
lemma regionSides_eq_induced_face_darts (U : Finset T.Vertex) (f : T.Face) :
    T.regionSides (T.retainedEdges U) (T.faceRegion (T.retainedEdges U) f) =
      Finset.univ.filter (fun d => T.vert d ∈ U ∧ T.head d ∈ U ∧
        T.inducedFaceClass (↑U : Set T.Vertex) (T.faceOf d) =
          T.inducedFaceClass (↑U : Set T.Vertex) f) := by
  ext d
  simp only [regionSides, Finset.mem_filter, Finset.mem_univ, true_and,
    T.retainedEdges_edgeOf, ← T.inducedFaceClass_eq_iff_faceRegion]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2.symm⟩,
    fun h => ⟨⟨h.1, h.2.1⟩, h.2.2.symm⟩⟩

-- @node: SphereMap.regionSides_card_eq_kept_darts
/-- [The number of sides of the deleted-edge region containing an original face
equals the number of retained directed edge occurrences whose incident faces
represent the same induced face as that original face](goal). -/
lemma regionSides_card_eq_kept_darts (U : Finset T.Vertex) (f : T.Face) :
    (T.regionSides (T.retainedEdges U) (T.faceRegion (T.retainedEdges U) f)).card =
      Fintype.card {d : T.KeptDart (↑U : Set T.Vertex) //
        T.inducedFaceClass (↑U : Set T.Vertex) (T.faceOf d.val) =
          T.inducedFaceClass (↑U : Set T.Vertex) f} := by
  rw [T.regionSides_eq_induced_face_darts, Fintype.card_subtype]
  symm
  apply Finset.card_bij (fun d _ => d.val)
  · intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.property.1, d.property.2,
      (Finset.mem_filter.mp hd).2⟩
  · intro d hd e he h
    exact Subtype.ext h
  · intro d hd
    obtain ⟨_, hv, hw, hf⟩ := Finset.mem_filter.mp hd
    exact ⟨⟨d, hv, hw⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, rfl⟩

-- @node: SphereMap.regionSides_card_eq_induced_faceLength
/-- [The number of sides of the deleted-edge region containing an original face
equals the length of the induced face represented by that face](goal). -/
lemma regionSides_card_eq_induced_faceLength (U : Finset T.Vertex) (f : T.Face) :
    (T.regionSides (T.retainedEdges U) (T.faceRegion (T.retainedEdges U) f)).card =
      (T.induce (↑U : Set T.Vertex)).faceLength
        (T.inducedFaceClass (↑U : Set T.Vertex) f) := by
  rw [T.regionSides_eq_induced_face_darts,
    (T.induce (↑U : Set T.Vertex)).faceLength_eq_card_faceDarts]
  symm
  apply Finset.card_bij (fun d _ => d.val)
  · intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.property.1, d.property.2,
      (T.inducedBoundaryFace_dart _ d).symm.trans (Finset.mem_filter.mp hd).2⟩
  · intro d hd e he h
    exact Subtype.ext h
  · intro d hd
    obtain ⟨_, hv, hw, hf⟩ := Finset.mem_filter.mp hd
    refine ⟨⟨d, hv, hw⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact (T.inducedBoundaryFace_dart _ _).trans hf

-- @node: SphereMap.faceRegion_eq_singleton_of_retained
/-- If [all vertices of an original face belong to the selected vertex
set](hyp:hf), then [its deleted-edge region consists of that face alone](goal). -/
lemma faceRegion_eq_singleton_of_retained (U : Finset T.Vertex) (f : T.Face)
    (hf : T.faceVertices f ⊆ U) :
    T.faceRegion (T.retainedEdges U) f = {f} := by
  ext g
  rw [← T.inducedFaceClass_eq_iff_faceRegion]
  constructor
  · intro he
    apply Eq.symm
    apply T.inducedFaceClass_eq_of_retained _ f g ?_ he
    intro d hd
    have tail (e : T.Dart) : T.vert e ∈ T.faceVertices (T.faceOf e) :=
      Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩)
    refine ⟨hf (hd ▸ tail d), hf ?_⟩
    have h := tail (T.facePerm d)
    rw [T.dual_rot_vertex] at h
    have hv : T.vert (T.facePerm d) = T.head d := T.rot_vertex (T.edgeInv d)
    simpa only [hv, hd] using h
  · intro he
    exact congrArg (T.inducedFaceClass (↑U : Set T.Vertex)) he.symm

-- @node: SphereMap.regionSides_card_of_retained_face
/-- If [the map is a sphere triangulation](hyp:hT) and [all vertices of an
original face are selected](hyp:hf), then [the deleted-edge region containing
that face has exactly three sides](goal). -/
lemma regionSides_card_of_retained_face (hT : IsSphereTriangulation T)
    (U : Finset T.Vertex) (f : T.Face) (hf : T.faceVertices f ⊆ U) :
    (T.regionSides (T.retainedEdges U) (T.faceRegion (T.retainedEdges U) f)).card = 3 := by
  rw [T.faceRegion_eq_singleton_of_retained U f hf]
  have he : T.regionSides (T.retainedEdges U) {f} = T.faceDarts f := by
    ext d
    simp only [regionSides, faceDarts, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_singleton_iff]
    constructor
    · exact And.right
    · intro hd
      refine ⟨(T.retainedEdges_edgeOf U d).mpr ⟨?_, ?_⟩, hd⟩
      · apply hf
        rw [← hd]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩)
      · apply hf
        have hv : T.vert (T.facePerm d) = T.head d := T.rot_vertex (T.edgeInv d)
        rw [← hd, ← T.dual_rot_vertex d, ← hv]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨T.facePerm d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩)
  rw [he, ← T.faceLength_eq_card_faceDarts]
  exact (hT.props.2.2.2 f).1

-- @node: SphereMap.sum_induced_face_color_card
/-- [Summing, over all induced faces, the number of original faces of a chosen
color represented by each induced face gives the total number of original
faces of that color](goal). -/
lemma sum_induced_face_color_card (U : Finset T.Vertex) (col : T.Face → Bool) (b : Bool) :
    (∑ q : T.InducedFace (↑U : Set T.Vertex),
      (Finset.univ.filter (fun f => col f = b ∧
        T.inducedFaceClass (↑U : Set T.Vertex) f = q)).card) =
      (Finset.univ.filter (fun f => col f = b)).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter (fun f => col f = b))
    (Finset.univ : Finset (T.InducedFace (↑U : Set T.Vertex)))
    (T.inducedFaceClass (↑U : Set T.Vertex))
  simpa only [Finset.filter_filter, Finset.mem_univ, Finset.filter_true, and_true] using h

-- @node: SphereMap.sum_induced_face_color_defect
/-- If [the map is a sphere triangulation](hyp:hT) and [adjacent faces have
opposite colors](hyp:hcol), then [the sum over induced faces of the number of
original black faces minus the number of original white faces represented by
each induced face is zero](goal). -/
lemma sum_induced_face_color_defect (hT : IsSphereTriangulation T)
    (U : Finset T.Vertex) (col : T.Face → Bool) (hcol : PartitionColoring T col) :
    (∑ q : T.InducedFace (↑U : Set T.Vertex),
      (((Finset.univ.filter (fun f => col f = true ∧
          T.inducedFaceClass (↑U : Set T.Vertex) f = q)).card : ℤ) -
        (Finset.univ.filter (fun f => col f = false ∧
          T.inducedFaceClass (↑U : Set T.Vertex) f = q)).card)) = 0 := by
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum,
    T.sum_induced_face_color_card U col true, T.sum_induced_face_color_card U col false]
  have h := (standingCounts_of_triangulation T hT col hcol).1
  change whiteFaceCount T col = blackFaceCount T col at h
  exact sub_eq_zero.mpr (congrArg (fun n : ℕ => (n : ℤ)) h.symm)

end SphereMap
end OaiPairedStatesHamiltonian
