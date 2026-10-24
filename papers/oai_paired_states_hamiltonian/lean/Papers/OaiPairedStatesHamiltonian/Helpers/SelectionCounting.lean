module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SelectionCycles

/-! Cancellation and signed incidence counting for selected edges in a disk. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

-- @node: cycle_selected_internal_signs_cancel
/-- If [the map is connected](hyp:hT) and [faces on opposite sides of every
edge have opposite colors](hyp:hcol), then [the signed sum of selected sides
in the cycle's left region, excluding edges of the cycle, is zero](goal),
where a true-colored face contributes one and a false-colored face minus one. -/
lemma cycle_selected_internal_signs_cancel (T : SphereMap) (hT : T.IsConnectedMap)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (C : T.Cycle)
    (S : Set T.Edge) :
    (∑ d ∈ Finset.univ.filter (fun d => T.edgeOf d ∈ S ∧
      T.edgeOf d ∉ C.val.map T.edgeOf ∧ T.faceOf d ∈ T.leftRegion C),
        (if col (T.faceOf d) then 1 else -1 : ℤ)) = 0 := by
  apply Finset.sum_involution (fun d _ => T.edgeInv d)
  · intro d hd
    have hc := hcol d
    cases h : col (T.faceOf d) <;>
      cases hi : col (T.faceOf (T.edgeInv d)) <;> simp_all
  · intro d hd hn
    exact T.edgeInv_fixedPointFree d
  · intro d hd
    obtain ⟨_, hs, he, hf⟩ := Finset.mem_filter.mp hd
    have hi : T.edgeOf (T.edgeInv d) = T.edgeOf d :=
      (T.edgeOf_eq_iff (T.edgeInv d) d).mpr (Or.inr (T.edgeInv_involutive d).symm)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.symm ▸ hs,
      hi.symm ▸ he, (T.leftRegion_across_noncycle hT C d he).mp hf⟩
  · intro d hd
    exact T.edgeInv_involutive d

-- @node: cycle_selected_side_sum
/-- If [the map is connected](hyp:hT), [adjacent faces have opposite
colors](hyp:hcol), [the designated outer face is outside the cycle's left
region](hyp:hout), and [every cycle edge is selected](hyp:hC), then [the signed
sum of selected sides in the left region equals the cycle's signed boundary
sum](goal), with true and false colors contributing one and minus one. -/
lemma cycle_selected_side_sum (T : SphereMap) (hT : T.IsConnectedMap)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (C : T.Cycle)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C) (S : Set T.Edge)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ S) :
    (∑ d ∈ Finset.univ.filter (fun d => T.edgeOf d ∈ S ∧
      T.faceOf d ∈ T.leftRegion C), (if col (T.faceOf d) then 1 else -1 : ℤ)) =
        (C.val.map (delta T col)).sum := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun d => T.edgeOf d ∈ S ∧ T.faceOf d ∈ T.leftRegion C))
    (fun d => T.edgeOf d ∈ C.val.map T.edgeOf)
    (fun d => (if col (T.faceOf d) then 1 else -1 : ℤ))
  have hb : (Finset.univ.filter (fun d => T.edgeOf d ∈ S ∧
      T.faceOf d ∈ T.leftRegion C)).filter
        (fun d => T.edgeOf d ∈ C.val.map T.edgeOf) = C.val.toFinset := by
    rw [← cycle_region_boundary_darts T hT C outer hout]
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hs, hf⟩, he⟩
      exact ⟨hf, he⟩
    · rintro ⟨hf, he⟩
      obtain ⟨e, heC, heq⟩ := List.mem_map.mp he
      exact ⟨⟨heq ▸ hC e heC, hf⟩, List.mem_map.mpr ⟨e, heC, heq⟩⟩
  have hi : (Finset.univ.filter (fun d => T.edgeOf d ∈ S ∧
      T.faceOf d ∈ T.leftRegion C)).filter
        (fun d => T.edgeOf d ∉ C.val.map T.edgeOf) =
      Finset.univ.filter (fun d => T.edgeOf d ∈ S ∧
        T.edgeOf d ∉ C.val.map T.edgeOf ∧ T.faceOf d ∈ T.leftRegion C) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hb, hi, cycle_selected_internal_signs_cancel T hT col hcol C S,
    add_zero] at hsplit
  rw [← hsplit]
  have hn : C.val.Nodup := C.property.2.of_map T.vert
  exact List.sum_toFinset (f := delta T col) hn

-- @node: selected_face_dart_existsUnique
/-- If [adjacent faces have opposite colors](hyp:hcol) and [exactly one selected
edge is incident to the given face](hyp:hf), then [exactly one directed edge
side belongs to a selected edge and has that face on its left](goal). -/
lemma selected_face_dart_existsUnique (T : SphereMap) (col : T.Face → Bool)
    (hcol : PartitionColoring T col) (S : Set T.Edge) (f : T.Face)
    (hf : ∃! e : T.Edge, e ∈ S ∧ T.edgeOnFace e f) :
    ∃! d : T.Dart, T.edgeOf d ∈ S ∧ T.faceOf d = f := by
  obtain ⟨e, ⟨he, d, hed, hdf⟩, hu⟩ := hf
  refine ⟨d, ⟨hed ▸ he, hdf⟩, ?_⟩
  intro a ha
  have hae : T.edgeOf a = e := hu _ ⟨ha.1, a, rfl, ha.2⟩
  rcases (T.edgeOf_eq_iff d a).mp (hed.trans hae.symm) with h | h
  · exact h
  · have hc := hcol d
    rw [hdf, ← h, ha.2] at hc
    exact (hc rfl).elim

-- @node: region_selected_signed_count
/-- If [adjacent faces have opposite colors](hyp:hcol) and [each face in the
region is incident to exactly one selected edge](hyp:hfaces), then [the signed
sum of selected sides in the region equals the number of true-colored faces
minus the number of false-colored faces in that region](goal). -/
lemma region_selected_signed_count (T : SphereMap) (col : T.Face → Bool)
    (hcol : PartitionColoring T col) (S : Set T.Edge) (R : Set T.Face)
    (hfaces : ∀ f ∈ R, ∃! e : T.Edge, e ∈ S ∧ T.edgeOnFace e f) :
    (∑ d ∈ Finset.univ.filter (fun d => T.edgeOf d ∈ S ∧ T.faceOf d ∈ R),
      (if col (T.faceOf d) then 1 else -1 : ℤ)) =
        ((Finset.univ.filter (fun f => f ∈ R ∧ col f = true)).card : ℤ) -
          (Finset.univ.filter (fun f => f ∈ R ∧ col f = false)).card := by
  have hsum : (∑ d ∈ Finset.univ.filter (fun d => T.edgeOf d ∈ S ∧ T.faceOf d ∈ R),
      (if col (T.faceOf d) then 1 else -1 : ℤ)) =
      ∑ f ∈ Finset.univ.filter (fun f => f ∈ R), (if col f then 1 else -1 : ℤ) := by
    apply Finset.sum_bij (fun d _ => T.faceOf d)
    · intro d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2.2⟩
    · intro d hd e he hde
      have hdf := (Finset.mem_filter.mp hd).2
      have hef := (Finset.mem_filter.mp he).2
      obtain ⟨a, ha, hu⟩ := selected_face_dart_existsUnique T col hcol S
        (T.faceOf d) (hfaces _ hdf.2)
      exact (hu d ⟨hdf.1, rfl⟩).trans (hu e ⟨hef.1, hde.symm⟩).symm
    · intro f hf
      obtain ⟨d, hd, _⟩ := selected_face_dart_existsUnique T col hcol S f
        (hfaces f (Finset.mem_filter.mp hf).2)
      exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.1, hd.2 ▸
        (Finset.mem_filter.mp hf).2⟩, hd.2⟩
    · intro d hd
      rfl
  rw [hsum, signed_bool_sum]
  simp only [Finset.filter_filter]

-- @node: cycle_signed_selection_count
/-- Suppose [the map is connected](hyp:hT), [adjacent faces have opposite
colors](hyp:hcol), and [the designated outer face lies outside the cycle's
left region](hyp:hout). If [every cycle edge is selected](hyp:hC) and [each
face in the left region is incident to exactly one selected edge](hyp:hfaces),
then [the number of true-colored faces minus false-colored faces in that
region equals twice the number of cycle sides with a true-colored face on
their left, minus the cycle length](goal). -/
lemma cycle_signed_selection_count (T : SphereMap) (hT : T.IsConnectedMap)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (C : T.Cycle)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C) (S : Set T.Edge)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ S)
    (hfaces : ∀ f ∈ T.leftRegion C, ∃! e : T.Edge, e ∈ S ∧ T.edgeOnFace e f) :
    ((Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧ col f = true)).card : ℤ) -
      (Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧ col f = false)).card =
        2 * ((C.val.filter (fun d => col (T.faceOf d) = true)).length : ℤ) -
          C.val.length := by
  rw [← region_selected_signed_count T col hcol S (T.leftRegion C) hfaces,
    cycle_selected_side_sum T hT col hcol C outer hout S hC,
    delta_sum_eq_boundary_count]

-- @node: cycle_delta_zero_of_unique_selected_faces
/-- Suppose [the map is a sphere triangulation](hyp:hT), [adjacent faces have
opposite colors](hyp:hcol), and [the designated outer face lies outside the
cycle's left region](hyp:hout). If [every cycle edge is selected](hyp:hC) and
[each face in the left region is incident to exactly one selected
edge](hyp:hfaces), then [the cycle's signed boundary sum is zero](goal). -/
lemma cycle_delta_zero_of_unique_selected_faces (T : SphereMap)
    (hT : IsSphereTriangulation T) (col : T.Face → Bool)
    (hcol : PartitionColoring T col) (C : T.Cycle) (outer : T.Face)
    (hout : outer ∉ T.leftRegion C) (S : Set T.Edge)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ S)
    (hfaces : ∀ f ∈ T.leftRegion C, ∃! e : T.Edge, e ∈ S ∧ T.edgeOnFace e f) :
    (C.val.map (delta T col)).sum = 0 := by
  have hselection := cycle_signed_selection_count T hT.props.1 col hcol C outer hout S hC hfaces
  have hsides := cycle_signed_side_count T hT col hcol C outer hout
  rw [delta_sum_eq_boundary_count]
  omega

-- @node: selectedSet_outer_face_existsUnique
/-- If [the map is a sphere triangulation](hyp:hT), [adjacent faces have opposite
colors](hyp:hcol), and [the prescribed edge is incident to the outer
face](hyp:he0), then [exactly one selected edge is incident to the outer
face](goal). -/
lemma selectedSet_outer_face_existsUnique (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (s : State T col t0) (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) :
    ∃! e : T.Edge, e ∈ selectedSet T hT col hcol t0 s e0 he0 ∧ T.edgeOnFace e t0 := by
  refine ⟨e0, ⟨Finset.mem_insert_self _ _, he0⟩, ?_⟩
  intro e he
  rcases Finset.mem_insert.mp he.1 with heq | heq
  · exact heq
  · obtain ⟨t, _, ht⟩ := Finset.mem_image.mp heq
    have hf := black_face_of_edge_unique T (normalizedColoring T col t0)
      (normalizedColoring_partition T col hcol t0) e t.val t0
      (nonOuter_black T col t0 t) (normalizedColoring_self T col t0)
      (ht ▸ selectedDart_edgeOnFace T hT col hcol t0 s e0 he0 t) he.2
    exact ((Finset.mem_filter.mp t.property).2.2 hf).elim

-- @node: selectedSet_black_face_existsUnique_of_color
/-- If [the map is a sphere triangulation](hyp:hT), [adjacent faces have opposite
colors](hyp:hcol), [the prescribed edge lies on the outer face](hyp:he0), and
[the given face is black under the coloring normalized at the outer
face](hyp:hf), then [exactly one selected edge is incident to that face](goal). -/
lemma selectedSet_black_face_existsUnique_of_color (T : SphereMap)
    (hT : IsSphereTriangulation T) (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (t0 : T.Face) (s : State T col t0) (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0)
    (f : T.Face) (hf : normalizedColoring T col t0 f = true) :
    ∃! e : T.Edge, e ∈ selectedSet T hT col hcol t0 s e0 he0 ∧ T.edgeOnFace e f := by
  by_cases houter : f = t0
  · subst f
    exact selectedSet_outer_face_existsUnique T hT col hcol t0 s e0 he0
  · let t : blackNonOuter T col t0 :=
      ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, houter⟩⟩
    exact selectedSet_black_face_existsUnique T hT col hcol t0 s e0 he0 t

-- @node: selectedSet0_cycle_has_bad_white_face
/-- Suppose [the map is a sphere triangulation](hyp:hT), [adjacent faces have
opposite colors](hyp:hcol), and [the prescribed edge lies on the outer
face](hyp:he0). If [every edge of the cycle belongs to the selected set with
the prescribed edge removed](hyp:hC), then [some face is white under the
normalized coloring and fails to be incident to exactly one edge of the
full selected set](goal). -/
lemma selectedSet0_cycle_has_bad_white_face (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (s : State T col t0) (e0 : T.Edge) (he0 : T.edgeOnFace e0 t0) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, T.edgeOf d ∈ selectedSet0 T hT col hcol t0 s e0 he0) :
    ∃ f : T.Face, normalizedColoring T col t0 f = false ∧
      ¬ ∃! e : T.Edge, e ∈ selectedSet T hT col hcol t0 s e0 he0 ∧ T.edgeOnFace e f := by
  by_contra hwhite
  have hw (f : T.Face) (hf : normalizedColoring T col t0 f = false) :
      ∃! e : T.Edge, e ∈ selectedSet T hT col hcol t0 s e0 he0 ∧ T.edgeOnFace e f := by
    by_contra hn
    exact hwhite ⟨f, hf, hn⟩
  obtain ⟨D, hD, hd, hnonzero⟩ :=
    selectedSet0_cycle_nonzero_direction T hT col hcol t0 s e0 he0 C hC
  obtain ⟨outer, hout⟩ := T.exists_face_outside_cycle_leftRegion hT.props.1 D
  apply hnonzero
  apply cycle_delta_zero_of_unique_selected_faces T hT (normalizedColoring T col t0)
    (normalizedColoring_partition T col hcol t0) D outer hout
    {e | e ∈ selectedSet T hT col hcol t0 s e0 he0}
  · intro d hmem
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (hd d hmem)).1
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, Finset.mem_univ _,
      congrArg T.edgeOf ht⟩)
  · intro f hf
    cases hc : normalizedColoring T col t0 f with
    | false => exact hw f hc
    | true => exact selectedSet_black_face_existsUnique_of_color T hT col hcol t0 s e0 he0 f hc

end OaiPairedStatesHamiltonian
