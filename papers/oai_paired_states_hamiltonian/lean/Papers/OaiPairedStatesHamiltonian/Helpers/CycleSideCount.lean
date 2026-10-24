module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleExterior
public import Papers.OaiPairedStatesHamiltonian.Helpers.Density

/-! Signed side counting for a simple cycle with a nonempty opposite side. -/

public section

namespace OaiPairedStatesHamiltonian
set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

-- @node: cycle_internal_signs_cancel
/-- If [the sphere map is connected](hyp:hT) and [adjacent faces have opposite
Boolean colors](hyp:hcol), then [the sum of signs over darts on noncycle edges
whose faces lie in the cycle's left region is zero, assigning positive one to
true-colored faces and negative one to false-colored faces](goal). -/
lemma cycle_internal_signs_cancel (T : SphereMap) (hT : T.IsConnectedMap)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (C : T.Cycle) :
    (∑ d ∈ Finset.univ.filter (fun d => T.edgeOf d ∉ C.val.map T.edgeOf ∧
      T.faceOf d ∈ T.leftRegion C), (if col (T.faceOf d) then 1 else -1 : ℤ)) = 0 := by
  apply Finset.sum_involution (fun d _ => T.edgeInv d)
  · intro d hd
    have hc := hcol d
    cases h : col (T.faceOf d) <;>
      cases hi : col (T.faceOf (T.edgeInv d)) <;> simp_all
  · intro d hd hn
    exact T.edgeInv_fixedPointFree d
  · intro d hd
    obtain ⟨_, he, hf⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hi : T.edgeOf (T.edgeInv d) = T.edgeOf d :=
        (T.edgeOf_eq_iff (T.edgeInv d) d).mpr (Or.inr (T.edgeInv_involutive d).symm)
      simpa only [hi] using he
    · exact (T.leftRegion_across_noncycle hT C d he).mp hf
  · intro d hd
    exact T.edgeInv_involutive d

-- @node: cycle_region_boundary_darts
/-- If [the sphere map is connected](hyp:hT) and [the designated outer face lies
outside the cycle's left region](hyp:hout), then [the darts whose faces lie in
the left region and whose edges occur in the cycle are exactly the cycle's darts](goal). -/
lemma cycle_region_boundary_darts (T : SphereMap) (hT : T.IsConnectedMap)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C) :
    Finset.univ.filter (fun d => T.faceOf d ∈ T.leftRegion C ∧
      T.edgeOf d ∈ C.val.map T.edgeOf) = C.val.toFinset := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨hd, he⟩
    obtain ⟨e, he, heq⟩ := List.mem_map.mp he
    rcases (T.edgeOf_eq_iff e d).mp heq with h | h
    · exact h ▸ he
    · exact (T.cycle_boundary_opposite_outside hT C outer hout e he (h ▸ hd)).elim
  · intro hd
    exact ⟨T.cycle_face_mem_leftRegion C d hd, List.mem_map.mpr ⟨d, hd, rfl⟩⟩

-- @node: cycle_signed_side_count
/-- For [a sphere triangulation](hyp:hT) with [oppositely colored adjacent
faces](hyp:hcol), if [the designated outer face lies outside the cycle's left
region](hyp:hout), then [three times the number of true-colored faces minus
false-colored faces in that region equals twice the number of cycle darts with
true-colored faces minus the cycle length](goal). -/
lemma cycle_signed_side_count (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (C : T.Cycle)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C) :
    3 * (((Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧ col f = true)).card : ℤ) -
      (Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧ col f = false)).card) =
      2 * ((C.val.filter (fun d => col (T.faceOf d) = true)).length : ℤ) - C.val.length := by
  have hfull := signed_bool_sum
    (Finset.univ.filter (fun d => T.faceOf d ∈ T.leftRegion C)) (fun d => col (T.faceOf d))
  simp only [Finset.filter_filter] at hfull
  rw [region_colored_dart_count T hT col _ true,
    region_colored_dart_count T hT col _ false] at hfull
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun d => T.faceOf d ∈ T.leftRegion C))
    (fun d => T.edgeOf d ∈ C.val.map T.edgeOf)
    (fun d => (if col (T.faceOf d) then 1 else -1 : ℤ))
  simp only [Finset.filter_filter] at hsplit
  rw [cycle_region_boundary_darts T hT.props.1 C outer hout] at hsplit
  have hi : (Finset.univ.filter (fun d => T.faceOf d ∈ T.leftRegion C ∧
      T.edgeOf d ∉ C.val.map T.edgeOf)) =
      Finset.univ.filter (fun d => T.edgeOf d ∉ C.val.map T.edgeOf ∧
        T.faceOf d ∈ T.leftRegion C) := by
    ext d
    simp [and_comm]
  rw [hi, cycle_internal_signs_cancel T hT.props.1 col hcol C, add_zero, hfull] at hsplit
  have hboundary := signed_bool_sum_twice C.val.toFinset (fun d => col (T.faceOf d))
  have hn : C.val.Nodup := C.property.2.of_map T.vert
  have hfilter : (C.val.toFinset.filter (fun d => col (T.faceOf d) = true)).card =
      (C.val.filter (fun d => col (T.faceOf d) = true)).length := by
    rw [← List.toFinset_filter]
    simpa using List.toFinset_card_of_nodup (hn.filter (fun d => col (T.faceOf d)))
  rw [hfilter, List.toFinset_card_of_nodup hn] at hboundary
  rw [hsplit] at hboundary
  push_cast at hboundary
  omega

end OaiPairedStatesHamiltonian
