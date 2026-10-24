module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleCap

/-! Exterior darts of a cycle-side restriction and their inherited face walk. -/

public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

variable (M : SphereMap)

-- @node: SphereMap.leftRegion_iff_local
/-- In [a connected map](hyp:hM), [a directed edge's face belongs to the cycle's
left region exactly when its facial orbit, viewed as a local boundary, belongs
to the cycle's local left region](goal). -/
lemma leftRegion_iff_local (hM : M.IsConnectedMap) (C : M.Cycle) (d : M.Dart) :
    M.faceOf d ∈ M.leftRegion C ↔
      Sum.inl (orbitOf M.facePerm d) ∈ M.leftLocalRegion C := by
  constructor
  · rintro ⟨b, hb, hf⟩
    have he := M.faceBehind_connected hM (M.compOf b) b (M.faceOf d) hf
    have heq : b = Sum.inl (orbitOf M.facePerm d) :=
      M.boundary_unique_in_component _ _
        (hM.preconnected.subsingleton_connectedComponent.elim _ _) he
    exact heq ▸ hb
  · exact M.leftLocalRegion_face_mem C _

-- @node: SphereMap.leftRegion_across_noncycle
/-- If [the map is connected](hyp:hM) and [an undirected edge does not occur in
the cycle](hyp:hd), then [the faces on its two sides either both belong to the
cycle's left region or both lie outside it](goal). -/
lemma leftRegion_across_noncycle (hM : M.IsConnectedMap) (C : M.Cycle)
    (d : M.Dart) (hd : M.edgeOf d ∉ C.val.map M.edgeOf) :
    M.faceOf d ∈ M.leftRegion C ↔ M.faceOf (M.edgeInv d) ∈ M.leftRegion C := by
  rw [M.leftRegion_iff_local hM C d, M.leftRegion_iff_local hM C (M.edgeInv d)]
  constructor
  · rintro ⟨e, he, hp⟩
    exact ⟨e, he, hp.tail ⟨d, hd, rfl, rfl⟩⟩
  · rintro ⟨e, he, hp⟩
    refine ⟨e, he, hp.tail ⟨M.edgeInv d, ?_, rfl, ?_⟩⟩
    · have hi : M.edgeOf (M.edgeInv d) = M.edgeOf d :=
        (M.edgeOf_eq_iff (M.edgeInv d) d).mpr (Or.inr (M.edgeInv_involutive d).symm)
      simpa only [hi] using hd
    · rw [M.edgeInv_involutive]

-- @node: SphereMap.cycle_exterior_dart_boundary
/-- If [the map is connected](hyp:hM) and [a retained directed edge has its
original face outside the cycle's left region](hyp:hd), then [its reverse is a
directed edge of the cycle](goal). -/
lemma cycle_exterior_dart_boundary (hM : M.IsConnectedMap) (C : M.Cycle)
    (d : M.RegionDart (M.leftRegion C)) (hd : M.faceOf d.val ∉ M.leftRegion C) :
    M.edgeInv d.val ∈ C.val := by
  have hin : M.faceOf (M.edgeInv d.val) ∈ M.leftRegion C := d.property.resolve_left hd
  have hedge : M.edgeOf d.val ∈ C.val.map M.edgeOf := by
    by_contra he
    exact hd ((M.leftRegion_across_noncycle hM C d.val he).mpr hin)
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hedge
  rcases (M.edgeOf_eq_iff e d.val).mp heq with h | h
  · exact (hd (h ▸ M.cycle_face_mem_leftRegion C e he)).elim
  · rw [h, M.edgeInv_involutive e]
    exact he

-- @node: SphereMap.cycle_exterior_facePerm
/-- If [the map is connected](hyp:hM) and [a retained directed edge has its
original face outside the cycle's left region](hyp:hd), then [the next directed
edge in the restricted facial walk also has its original face outside that
region](goal). -/
lemma cycle_exterior_facePerm (hM : M.IsConnectedMap) (C : M.Cycle)
    (d : M.RegionDart (M.leftRegion C)) (hd : M.faceOf d.val ∉ M.leftRegion C) :
    M.faceOf (((M.cycleLeftRotation C).facePerm d).val) ∉ M.leftRegion C := by
  intro hin
  have hc : (M.regionRotation (M.leftRegion C)).facePerm.SameCycle
      ((M.cycleLeftRotation C).facePerm d) d :=
    Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _)
  have hf := (M.region_face_sameCycle_iff hM _ _ d hin).mp hc
  exact hd (hf ▸ hin)

-- @node: SphereMap.cycle_exterior_sameCycle
/-- If [the map is connected](hyp:hM), [two retained directed edges lie in the
same restricted facial orbit](hyp:hc), and [the first has its original face
outside the cycle's left region](hyp:hd), then [the second also has its original
face outside that region](goal). -/
lemma cycle_exterior_sameCycle (hM : M.IsConnectedMap) (C : M.Cycle)
    (d e : M.RegionDart (M.leftRegion C))
    (hc : (M.cycleLeftRotation C).facePerm.SameCycle d e)
    (hd : M.faceOf d.val ∉ M.leftRegion C) : M.faceOf e.val ∉ M.leftRegion C := by
  intro he
  have hf := (M.region_face_sameCycle_iff hM _ e d he).mp hc.symm
  exact hd (hf ▸ he)

-- @node: SphereMap.exists_cycle_exterior_dart
/-- If [the map is connected](hyp:hM) and [a chosen face lies outside the cycle's
left region](hyp:hout), then [there is a directed edge retained by that region
whose original face lies outside it](goal). -/
lemma exists_cycle_exterior_dart (hM : M.IsConnectedMap) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) :
    ∃ d : M.RegionDart (M.leftRegion C), M.faceOf d.val ∉ M.leftRegion C := by
  by_contra hn
  have hall (d : M.RegionDart (M.leftRegion C)) : M.faceOf d.val ∈ M.leftRegion C := by
    by_contra hd
    exact hn ⟨d, hd⟩
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  have hcomponent : (M.dualRotation hM).toSimpleGraph.connectedComponentMk (M.faceOf d) =
      (M.dualRotation hM).toSimpleGraph.connectedComponentMk outer :=
    (M.dual_component_subsingleton hM).elim _ _
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hcomponent
  have propagate {f g : M.Face} (p : (M.dualRotation hM).toSimpleGraph.Walk f g) :
      f ∈ M.leftRegion C → g ∈ M.leftRegion C := by
    induction p with
    | nil => exact id
    | cons h p ih =>
      intro hf
      obtain ⟨_, e, he, hg⟩ := h
      apply ih
      change M.faceOf e = _ at he
      change M.faceOf (M.edgeInv e) = _ at hg
      have hin : M.faceOf e ∈ M.leftRegion C := he.symm ▸ hf
      let e' : M.RegionDart (M.leftRegion C) := ⟨M.edgeInv e, Or.inr (by
        rw [M.edgeInv_involutive]
        exact hin)⟩
      exact hg ▸ hall e'
  exact hout (propagate p (M.cycle_face_mem_leftRegion C d hd))

-- @node: SphereMap.cycle_exterior_facePerm_symm_step
/-- Suppose [the map is connected](hyp:hM), [a retained directed edge has its
original face outside the cycle's left region](hyp:hd), and [it is the reverse
of the cycle's directed edge at the chosen position](hyp:hi). Then [its
predecessor in the restricted facial walk is the reverse of the next cycle edge,
with the position taken cyclically](goal). -/
lemma cycle_exterior_facePerm_symm_step (hM : M.IsConnectedMap) (C : M.Cycle)
    (d : M.RegionDart (M.leftRegion C)) (hd : M.faceOf d.val ∉ M.leftRegion C)
    (i : Fin C.val.length) (hi : d.val = M.edgeInv (C.val.get i)) :
    (((M.cycleLeftRotation C).facePerm.symm d).val) =
      M.edgeInv (C.val.get ⟨(i.val + 1) % C.val.length, M.nextIndex_lt C.val i⟩) := by
  let e := (M.cycleLeftRotation C).facePerm.symm d
  have hc : (M.cycleLeftRotation C).facePerm.SameCycle e d :=
    Equiv.Perm.sameCycle_symm_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _)
  have he := M.cycle_exterior_sameCycle hM C d e hc.symm hd
  have hb := M.cycle_exterior_dart_boundary hM C e he
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
  have hej : e.val = M.edgeInv (C.val.get j) := by
    rw [hj, M.edgeInv_involutive]
  have hstep : (M.cycleLeftRotation C).vert d = (M.cycleLeftRotation C).head e := by
    rw [← (M.cycleLeftRotation C).facePerm.apply_symm_apply d]
    exact (M.cycleLeftRotation C).rot_vertex _
  have hv : M.vert (C.val.get j) =
      M.vert (C.val.get ⟨(i.val + 1) % C.val.length, M.nextIndex_lt C.val i⟩) := by
    have hv' := congrArg Subtype.val hstep
    change M.vert d.val = M.vert (M.edgeInv e.val) at hv'
    rw [hi, hej, M.edgeInv_involutive] at hv'
    exact hv'.symm.trans (C.property.1.2.2 i)
  have hjnext : C.val.get j =
      C.val.get ⟨(i.val + 1) % C.val.length, M.nextIndex_lt C.val i⟩ :=
    List.inj_on_of_nodup_map C.property.2 (List.get_mem _ _) (List.get_mem _ _) hv
  exact hej.trans (congrArg M.edgeInv hjnext)

-- @node: SphereMap.cycle_exterior_orbit_iff
/-- If [the map is connected](hyp:hM) and [a retained directed edge has its
original face outside the cycle's left region](hyp:hd), then [another retained
directed edge belongs to its restricted facial orbit exactly when the reverse
of that other edge occurs in the cycle](goal). -/
lemma cycle_exterior_orbit_iff (hM : M.IsConnectedMap) (C : M.Cycle)
    (d : M.RegionDart (M.leftRegion C)) (hd : M.faceOf d.val ∉ M.leftRegion C)
    (e : M.RegionDart (M.leftRegion C)) :
    (M.cycleLeftRotation C).facePerm.SameCycle d e ↔ M.edgeInv e.val ∈ C.val := by
  constructor
  · intro hc
    exact M.cycle_exterior_dart_boundary hM C e
      (M.cycle_exterior_sameCycle hM C d e hc hd)
  · intro he
    let p := (M.cycleLeftRotation C).facePerm
    have hpos : 0 < C.val.length := List.length_pos_iff.mpr C.property.1.1
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp (M.cycle_exterior_dart_boundary hM C d hd)
    have hdk : d.val = M.edgeInv (C.val.get k) := by
      rw [hk, M.edgeInv_involutive]
    have walk (n : ℕ) : p.SameCycle d ((p.symm ^ n) d) ∧
        (((p.symm ^ n) d).val) =
          M.edgeInv (C.val.get ⟨(k.val + n) % C.val.length, Nat.mod_lt _ hpos⟩) := by
      induction n with
      | zero =>
        constructor
        · exact Equiv.Perm.SameCycle.refl _ _
        · simpa only [pow_zero, Equiv.Perm.one_apply, Nat.add_zero,
            Nat.mod_eq_of_lt k.isLt] using hdk
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        constructor
        · exact Equiv.Perm.sameCycle_symm_apply_right.mpr ih.1
        · have hout := M.cycle_exterior_sameCycle hM C d ((p.symm ^ n) d) ih.1 hd
          have hs := M.cycle_exterior_facePerm_symm_step hM C _ hout
            ⟨(k.val + n) % C.val.length, Nat.mod_lt _ hpos⟩ ih.2
          exact hs.trans (congrArg (fun i : Fin C.val.length => M.edgeInv (C.val.get i))
            (Fin.ext (by simp only [Nat.mod_add_mod, Nat.add_assoc])))
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
    have hej : e.val = M.edgeInv (C.val.get j) := by
      rw [hj, M.edgeInv_involutive]
    have hmod : (k.val + (C.val.length - k.val + j.val)) % C.val.length = j.val := by
      rw [show k.val + (C.val.length - k.val + j.val) = C.val.length + j.val by omega]
      simp [Nat.mod_eq_of_lt j.isLt]
    have hw := walk (C.val.length - k.val + j.val)
    have heq : (p.symm ^ (C.val.length - k.val + j.val)) d = e := by
      apply Subtype.ext
      exact hw.2.trans ((congrArg (fun i : Fin C.val.length => M.edgeInv (C.val.get i))
        (Fin.ext hmod)).trans hej.symm)
    exact heq ▸ hw.1

-- @node: SphereMap.cycle_exterior_orbit_length
/-- If [the map is connected](hyp:hM) and [a retained directed edge has its
original face outside the cycle's left region](hyp:hd), then [the number of
directed edges in its restricted facial orbit equals the cycle length](goal). -/
lemma cycle_exterior_orbit_length (hM : M.IsConnectedMap) (C : M.Cycle)
    (d : M.RegionDart (M.leftRegion C)) (hd : M.faceOf d.val ∉ M.leftRegion C) :
    (Finset.univ.filter (fun e : (M.cycleLeftRotation C).Dart =>
      orbitOf (M.cycleLeftRotation C).facePerm e =
        orbitOf (M.cycleLeftRotation C).facePerm d)).card = C.val.length := by
  have hcard : C.val.toFinset.card = C.val.length :=
    List.toFinset_card_of_nodup (C.property.2.of_map M.vert)
  rw [← hcard]
  apply Finset.card_bij (fun e _ => M.edgeInv e.val)
  · intro e he
    apply List.mem_toFinset.mpr
    exact (M.cycle_exterior_orbit_iff hM C d hd e).mp
      (Quotient.exact (Finset.mem_filter.mp he).2).symm
  · intro e he f hf hef
    exact Subtype.ext (M.edgeInv.injective hef)
  · intro e he
    have he' := List.mem_toFinset.mp he
    let e' : M.RegionDart (M.leftRegion C) := ⟨M.edgeInv e, Or.inr (by
      rw [M.edgeInv_involutive]
      exact M.cycle_face_mem_leftRegion C e he')⟩
    refine ⟨e', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, M.edgeInv_involutive e⟩
    apply Quotient.sound
    apply ((M.cycle_exterior_orbit_iff hM C d hd e').mpr ?_).symm
    change M.edgeInv (M.edgeInv e) ∈ C.val
    rw [M.edgeInv_involutive]
    exact he'

-- @node: SphereMap.cycle_boundary_opposite_outside
/-- If [the map is connected](hyp:hM), [a chosen face lies outside the cycle's
left region](hyp:hout), and [a directed edge occurs in the cycle](hyp:he), then
[the face of its reverse lies outside the cycle's left region](goal). -/
lemma cycle_boundary_opposite_outside (hM : M.IsConnectedMap) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) (e : M.Dart) (he : e ∈ C.val) :
    M.faceOf (M.edgeInv e) ∉ M.leftRegion C := by
  obtain ⟨d, hd⟩ := M.exists_cycle_exterior_dart hM C outer hout
  let e' : M.RegionDart (M.leftRegion C) := ⟨M.edgeInv e, Or.inr (by
    rw [M.edgeInv_involutive]
    exact M.cycle_face_mem_leftRegion C e he)⟩
  have hc := (M.cycle_exterior_orbit_iff hM C d hd e').mpr (by
    change M.edgeInv (M.edgeInv e) ∈ C.val
    rw [M.edgeInv_involutive]
    exact he)
  exact M.cycle_exterior_sameCycle hM C d e' hc hd

-- @node: SphereMap.exists_cycle_face_orbit_equiv
/-- If [the map is a triangulation of the sphere](hyp:hM) and [a chosen face
lies outside the cycle's left region](hyp:hout), then [the faces in that region
together with one extra element correspond bijectively to the restricted facial
orbits: a region face corresponds exactly to the directed edges having that
original face, the extra element corresponds exactly to the reverses of cycle
edges, and its orbit contains as many directed edges as the cycle length](goal). -/
lemma exists_cycle_face_orbit_equiv (hM : IsSphereTriangulation M) (C : M.Cycle)
    (outer : M.Face) (hout : outer ∉ M.leftRegion C) :
    ∃ q : ({f : M.Face // f ∈ M.leftRegion C} ⊕ Unit) ≃ (M.cycleLeftRotation C).FaceOrbit,
      (∀ (f : {f : M.Face // f ∈ M.leftRegion C}) (d : M.RegionDart (M.leftRegion C)),
        orbitOf (M.cycleLeftRotation C).facePerm d = q (Sum.inl f) ↔ M.faceOf d.val = f.val) ∧
      (∀ d : M.RegionDart (M.leftRegion C),
        orbitOf (M.cycleLeftRotation C).facePerm d = q (Sum.inr ()) ↔ M.edgeInv d.val ∈ C.val) ∧
      (Finset.univ.filter (fun d : (M.cycleLeftRotation C).Dart =>
        orbitOf (M.cycleLeftRotation C).facePerm d = q (Sum.inr ()))).card = C.val.length := by
  obtain ⟨q, hq, hiff, hlength⟩ := M.exists_region_interior_faces hM (M.leftRegion C)
  obtain ⟨d, hd⟩ := M.exists_cycle_exterior_dart hM.props.1 C outer hout
  let exterior := orbitOf (M.cycleLeftRotation C).facePerm d
  have hne (f : {f : M.Face // f ∈ M.leftRegion C}) : q f ≠ exterior := by
    intro heq
    have hf := (hiff f d).mp heq.symm
    exact hd (hf.symm ▸ f.property)
  let lift : ({f : M.Face // f ∈ M.leftRegion C} ⊕ Unit) →
      (M.cycleLeftRotation C).FaceOrbit := Sum.elim q (fun _ => exterior)
  have hbij : Function.Bijective lift := by
    constructor
    · intro a b hab
      cases a with
      | inl f =>
        cases b with
        | inl g => exact congrArg Sum.inl (hq hab)
        | inr u => exact (hne f hab).elim
      | inr u =>
        cases b with
        | inl f => exact (hne f hab.symm).elim
        | inr v => exact congrArg Sum.inr (Subsingleton.elim _ _)
    · intro o
      obtain ⟨e, rfl⟩ := Quotient.exists_rep o
      by_cases he : M.faceOf e.val ∈ M.leftRegion C
      · exact ⟨Sum.inl ⟨M.faceOf e.val, he⟩, ((hiff _ e).mpr rfl).symm⟩
      · refine ⟨Sum.inr (), ?_⟩
        apply Quotient.sound
        exact (M.cycle_exterior_orbit_iff hM.props.1 C d hd e).mpr
          (M.cycle_exterior_dart_boundary hM.props.1 C e he)
  refine ⟨Equiv.ofBijective lift hbij, hiff, ?_, ?_⟩
  · intro e
    change orbitOf _ e = orbitOf _ d ↔ _
    constructor
    · intro he
      exact (M.cycle_exterior_orbit_iff hM.props.1 C d hd e).mp (Quotient.exact he).symm
    · intro he
      exact Quotient.sound ((M.cycle_exterior_orbit_iff hM.props.1 C d hd e).mpr he).symm
  · exact M.cycle_exterior_orbit_length hM.props.1 C d hd

-- @node: SphereMap.counterclockwise_face_orbit_equiv
/-- If [the map is a triangulation of the sphere](hyp:hM) and [the cycle is
counterclockwise relative to the chosen outer face](hyp:hccw), then [there exists
a bijection from its left-region faces together with one extra element to the
facial orbits of the left-region restriction](goal). -/
lemma counterclockwise_face_orbit_equiv (hM : IsSphereTriangulation M) (C : M.Cycle)
    (outer : M.Face) (hccw : M.IsCounterclockwise outer C) :
    Nonempty (({f : M.Face // f ∈ M.leftRegion C} ⊕ Unit) ≃
      (M.cycleLeftRotation C).FaceOrbit) := by
  have hout : outer ∉ M.leftRegion C := fun hin =>
    Set.disjoint_left.mp (M.cycle_sides_partition C).1 hin hccw
  obtain ⟨q, _⟩ := M.exists_cycle_face_orbit_equiv hM C outer hout
  exact ⟨q⟩

end SphereMap
end OaiPairedStatesHamiltonian
