module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleGluing
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleSeparation

/-! Euler counts for a triangulated cycle-side disk, independent of density. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable

-- @node: cycle_disk_euler_count
/-- If [the map is a triangulation of the sphere](hyp:hT) and [the chosen outer
face lies outside the cycle's left region](hyp:hout), then [the number of true-colored
faces plus the number of false-colored faces in that region equals twice the number
of vertices strictly on that side, plus the cycle length, minus two](goal). -/
lemma cycle_disk_euler_count (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (C : T.Cycle) (outer : T.Face)
    (hout : outer ∉ T.leftRegion C) :
    (Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧ col f = true)).card +
      (Finset.univ.filter (fun f => f ∈ T.leftRegion C ∧ col f = false)).card =
        2 * (Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)).card + C.val.length - 2 := by
  have hgenus : (T.cycleLeftRotation C).componentEuler :=
    T.cycleLeftRotation_componentEuler hT C outer hout
  let N := (T.cycleLeftRotation C).connectedSphereMap
    (T.cycleLeftRotation_connected hT C) hgenus
  have hN : N.IsConnectedMap :=
    (T.cycleLeftRotation C).connectedSphereMap_connected _ hgenus
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  let : Nonempty N.Dart := ⟨T.cycleRegionDart C d hd⟩
  obtain ⟨qN, hqN⟩ := N.exists_faceEquivOrbit hN
  obtain ⟨q, hfaces, hboundary, hcap⟩ := T.exists_cycle_face_orbit_equiv hT C outer hout
  let outer : N.Face := qN.symm (q (Sum.inr ()))
  have houter : qN outer = q (Sum.inr ()) := qN.apply_symm_apply _
  have length_eq (f : N.Face) : N.faceLength f =
      (Finset.univ.filter (fun e : N.Dart => orbitOf N.facePerm e = qN f)).card := by
    rw [N.faceLength_eq_card_faceDarts]
    change (Finset.univ.filter (fun e => N.faceOf e = f)).card = _
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun he => (hqN e).symm.trans (congrArg qN he),
      fun he => qN.injective ((hqN e).trans he)⟩
  have houter_length : N.faceLength outer = C.val.length := by
    rw [length_eq, houter]
    exact hcap
  have htriangles (f : N.Face) (hf : f ≠ outer) : N.faceLength f = 3 := by
    obtain ⟨g, hg⟩ := q.surjective (qN f)
    cases g with
    | inr u =>
      have he : f = outer := qN.injective (hg.symm.trans houter.symm)
      exact (hf he).elim
    | inl g =>
      obtain ⟨e, he⟩ := N.faceOf_surjective hN f
      have heq : orbitOf N.facePerm e = q (Sum.inl g) := (hqN e).symm.trans
        ((congrArg qN he).trans hg.symm)
      have hface : T.faceOf e.val = g.val := (hfaces g e).mp heq
      rw [length_eq, ← hg]
      have hlength := T.region_face_orbit_length hT.props.1 (T.leftRegion C) e
        (hface.symm ▸ g.property)
      have horbit : q (Sum.inl g) = orbitOf N.facePerm e := heq.symm
      rw [horbit]
      exact hlength.trans (by rw [hface]; exact (hT.props.2.2.2 g.val).1)
  have hvertices : Fintype.card N.Vertex =
      (Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)).card + N.faceLength outer := by
    rw [houter_length]
    exact T.cycle_left_vertex_card hT C
  have heuler := N.triangular_disk_euler hN outer
    (Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)).card htriangles hvertices
  have hface_card : Fintype.card N.Face =
      (Finset.univ.filter (fun f => f ∈ T.leftRegion C)).card + 1 := by
    have hqcard := Fintype.card_congr q
    rw [Fintype.card_sum, Fintype.card_subtype, Fintype.card_unit] at hqcard
    exact (Fintype.card_congr qN).trans hqcard.symm
  have hnonouter : (Finset.univ.filter (fun f : N.Face => f ≠ outer)).card + 1 =
      Fintype.card N.Face := by
    have he : (Finset.univ : Finset N.Face).erase outer =
        Finset.univ.filter (fun f => f ≠ outer) := by
      ext f
      simp
    rw [← he]
    exact Finset.card_erase_add_one (Finset.mem_univ outer)
  have hcolors := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun f => f ∈ T.leftRegion C))
    (fun f => col f = true)
  simp only [Finset.filter_filter, Bool.not_eq_true] at hcolors
  rw [houter_length] at heuler
  omega


end OaiPairedStatesHamiltonian
