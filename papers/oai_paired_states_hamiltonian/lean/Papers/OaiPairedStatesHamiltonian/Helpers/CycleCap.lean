module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleDisk

/-! Connectivity of a cycle-side restriction. This uses inherited incidences;
no separation, genus-zero, disk count, or cap assertion is an added hypothesis. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable

namespace SphereMap
variable (M : SphereMap)

-- @node: SphereMap.faceBehind_connected
/-- If [the map is connected](hyp:hM) and [a face lies behind a local boundary relative
to a component](hyp:h), [that face is the face assigned to the boundary](goal). -/
lemma faceBehind_connected (hM : M.IsConnectedMap) (K : M.Component)
    (b : M.LocalBoundary) (f : M.Face) (h : M.FaceBehind K b f) : M.boundaryFace b = f := by
  have hs : Subsingleton M.Component := hM.preconnected.subsingleton_connectedComponent
  have no_step (x y : M.Component ⊕ M.Face)
      (hxy : x ≠ Sum.inl K ∧ y ≠ Sum.inl K ∧ M.placementGraph.Adj x y) : False := by
    cases x with
    | inl L => exact hxy.1 (congrArg Sum.inl (hs.elim L K))
    | inr g =>
      cases y with
      | inl L => exact hxy.2.1 (congrArg Sum.inl (hs.elim L K))
      | inr f => exact hxy.2.2
  have path_eq {x y : M.Component ⊕ M.Face}
      (p : Relation.ReflTransGen (fun a b => a ≠ Sum.inl K ∧ b ≠ Sum.inl K ∧
        M.placementGraph.Adj a b) x y) : x = y := by
    induction p with
    | refl => rfl
    | tail _ hstep _ => exact False.elim (no_step _ _ hstep)
  exact Sum.inr.inj (path_eq h.2)

-- @node: SphereMap.leftLocalRegion_face_mem
/-- If [a local boundary belongs to a cycle's left local region](hyp:hb),
[its assigned face belongs to the cycle's left face region](goal). -/
lemma leftLocalRegion_face_mem (C : M.Cycle) (b : M.LocalBoundary)
    (hb : b ∈ M.leftLocalRegion C) : M.boundaryFace b ∈ M.leftRegion C := by
  exact ⟨b, hb, rfl, Relation.ReflTransGen.refl⟩

/-- In [a sphere map](hyp:M), for [a selected set of faces](hyp:R) and
[a retained dart](hyp:d), the [region component](goal) is the connected component
of the dart's initial vertex in the restricted rotation system. -/
noncomputable def regionComponent (R : Set M.Face) (d : M.RegionDart R) :
    (M.regionRotation R).Component :=
  (M.regionRotation R).toSimpleGraph.connectedComponentMk ((M.regionRotation R).vert d)

-- @node: SphereMap.region_component_inv
/-- [Reversing a retained dart leaves its component in the region restriction
unchanged](goal). -/
lemma region_component_inv (R : Set M.Face) (d : M.RegionDart R) :
    M.regionComponent R (M.regionInv R d) = M.regionComponent R d := by
  exact ((M.regionRotation R).dart_component_eq_head d).symm

-- @node: SphereMap.region_component_same_face
/-- If [the map is connected](hyp:hM), [the face of the first retained dart is
selected](hyp:hd), and [two retained darts have the same original face](hyp:hf),
[the darts belong to the same component of the region restriction](goal). -/
lemma region_component_same_face (hM : M.IsConnectedMap) (R : Set M.Face)
    (d e : M.RegionDart R) (hd : M.faceOf d.val ∈ R)
    (hf : M.faceOf d.val = M.faceOf e.val) :
    M.regionComponent R d = M.regionComponent R e := by
  exact (M.regionRotation R).boundary_component_wellDefined d e
    ((M.region_face_sameCycle_iff hM R d e hd).mpr hf)

/-- In [a sphere map](hyp:M), given [a cycle](hyp:C), [a dart](hyp:d), and
[its membership in the cycle](hyp:hd), the [corresponding retained dart](goal)
is the same dart viewed in the restriction to the cycle's left region. -/
noncomputable def cycleRegionDart (C : M.Cycle) (d : M.Dart) (hd : d ∈ C.val) :
    M.RegionDart (M.leftRegion C) := ⟨d, Or.inl (M.cycle_face_mem_leftRegion C d hd)⟩

-- @node: SphereMap.cycle_region_component_eq
/-- If [the first dart lies on the cycle](hyp:hd) and [the second dart also lies
on the cycle](hyp:he), [their retained versions belong to the same component
of the restriction to the cycle's left region](goal). -/
lemma cycle_region_component_eq (C : M.Cycle) (d e : M.Dart)
    (hd : d ∈ C.val) (he : e ∈ C.val) :
    M.regionComponent (M.leftRegion C) (M.cycleRegionDart C d hd) =
      M.regionComponent (M.leftRegion C) (M.cycleRegionDart C e he) := by
  have hpos : 0 < C.val.length := List.length_pos_iff.mpr C.property.1.1
  let cd (i : Fin C.val.length) : M.RegionDart (M.leftRegion C) :=
    M.cycleRegionDart C (C.val.get i) (List.get_mem _ _)
  have hindex (n : ℕ) (hn : n < C.val.length) :
      M.regionComponent (M.leftRegion C) (cd ⟨n, hn⟩) =
        M.regionComponent (M.leftRegion C) (cd ⟨0, hpos⟩) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hprev := ih (by omega)
      have hs := C.property.1.2.2 ⟨n, by omega⟩
      simp only [Nat.mod_eq_of_lt hn] at hs
      have heq : (M.regionRotation (M.leftRegion C)).head (cd ⟨n, by omega⟩) =
          (M.regionRotation (M.leftRegion C)).vert (cd ⟨n + 1, hn⟩) := by
        apply Subtype.ext
        exact hs
      have ht := (M.regionRotation (M.leftRegion C)).dart_component_eq_head (cd ⟨n, by omega⟩)
      exact ((ht.trans (congrArg (M.regionRotation (M.leftRegion C)).toSimpleGraph.connectedComponentMk
        heq)).symm).trans hprev
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
  subst d e
  exact (hindex i.val i.isLt).trans (hindex j.val j.isLt).symm

set_option backward.isDefEq.respectTransparency false in
/-- If [the map is connected](hyp:hM), [a dart lies on a cycle](hyp:hd), and
[a local boundary can be reached from that dart's facial boundary by a walk
avoiding the cycle edges](hyp:hb), [every retained dart whose facial boundary
is the reached boundary belongs to the same restricted component as the starting
cycle dart](goal). -/
-- @node: SphereMap.left_local_region_component
lemma left_local_region_component (hM : M.IsConnectedMap) (C : M.Cycle)
    (d : M.Dart) (hd : d ∈ C.val) (b : M.LocalBoundary)
    (hb : M.localBoundariesJoinedAvoiding C.val (Sum.inl (orbitOf M.facePerm d)) b) :
    ∀ e : M.RegionDart (M.leftRegion C),
      Sum.inl (orbitOf M.facePerm e.val) = b →
      M.regionComponent (M.leftRegion C) e =
        M.regionComponent (M.leftRegion C) (M.cycleRegionDart C d hd) := by
  induction hb with
  | refl =>
    intro e he
    have hf : M.faceOf d = M.faceOf e.val := congrArg M.boundaryFace he.symm
    exact (M.region_component_same_face hM _ (M.cycleRegionDart C d hd) e
      (M.cycle_face_mem_leftRegion C d hd) hf).symm
  | @tail a b hprev hstep ih =>
    intro e he
    obtain ⟨x, hx, ha, hb⟩ := hstep
    have hlocal : b ∈ M.leftLocalRegion C := ⟨d, hd, hprev.tail ⟨x, hx, ha, hb⟩⟩
    have hinside : M.faceOf (M.edgeInv x) ∈ M.leftRegion C := by
      change M.boundaryFace (Sum.inl (orbitOf M.facePerm (M.edgeInv x))) ∈ _
      rw [hb]
      exact M.leftLocalRegion_face_mem C b hlocal
    let x' : M.RegionDart (M.leftRegion C) := ⟨x, Or.inr hinside⟩
    have hf : M.faceOf (M.edgeInv x) = M.faceOf e.val :=
      congrArg M.boundaryFace (hb.trans he.symm)
    have hc := M.region_component_same_face hM _ (M.regionInv _ x') e hinside hf
    exact hc.symm.trans ((M.region_component_inv _ x').trans (ih x' ha))

-- @node: SphereMap.cycleLeftRotation_connected
/-- If [the map is a sphere triangulation](hyp:hM), [the underlying graph of
the restriction to any cycle's left region is connected](goal). -/
lemma cycleLeftRotation_connected (hM : IsSphereTriangulation M) (C : M.Cycle) :
    (M.cycleLeftRotation C).toSimpleGraph.Connected := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  let base := M.cycleRegionDart C d hd
  have selected (e : M.RegionDart (M.leftRegion C)) (he : M.faceOf e.val ∈ M.leftRegion C) :
      M.regionComponent (M.leftRegion C) e = M.regionComponent (M.leftRegion C) base := by
    obtain ⟨b, hb, hbehind⟩ := he
    have hf := M.faceBehind_connected hM.props.1 (M.compOf b) b (M.faceOf e.val) hbehind
    have hbe : Sum.inl (orbitOf M.facePerm e.val) = b :=
      M.boundary_unique_in_component _ b
        (hM.props.1.preconnected.subsingleton_connectedComponent.elim _ _) hf.symm
    obtain ⟨s, hs, hpath⟩ := hb
    exact (M.left_local_region_component hM.props.1 C s hs b hpath e hbe).trans
      (M.cycle_region_component_eq C s d hs hd)
  have all_darts (e : M.RegionDart (M.leftRegion C)) :
      M.regionComponent (M.leftRegion C) e = M.regionComponent (M.leftRegion C) base := by
    rcases e.property with h | h
    · exact selected e h
    · exact (M.region_component_inv _ e).symm.trans (selected (M.regionInv _ e) h)
  let : Nonempty (M.cycleLeftRotation C).Vertex := ⟨(M.cycleLeftRotation C).vert base⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨e, he, hu⟩ := u.property
  obtain ⟨f, hf, hv⟩ := v.property
  let e' : M.RegionDart (M.leftRegion C) := ⟨e, he⟩
  let f' : M.RegionDart (M.leftRegion C) := ⟨f, hf⟩
  have hcomp := (all_darts e').trans (all_darts f').symm
  have heu : (M.cycleLeftRotation C).vert e' = u := Subtype.ext hu
  have hfv : (M.cycleLeftRotation C).vert f' = v := Subtype.ext hv
  apply SimpleGraph.ConnectedComponent.exact
  change (M.cycleLeftRotation C).toSimpleGraph.connectedComponentMk
      ((M.cycleLeftRotation C).vert e') =
    (M.cycleLeftRotation C).toSimpleGraph.connectedComponentMk
      ((M.cycleLeftRotation C).vert f') at hcomp
  rwa [heu, hfv] at hcomp

end SphereMap

namespace RotationSystem
variable (R : RotationSystem)

/-- If [a rotation system's underlying graph is connected](hyp:hR), [its
placement graph, assigning each local boundary to itself, is connected](goal). -/
-- @node: RotationSystem.local_placement_connected
lemma local_placement_connected (hR : R.toSimpleGraph.Connected) :
    (R.placementGraph R.LocalBoundary id).Connected := by
  let : Nonempty R.Vertex := hR.nonempty
  let G := R.placementGraph R.LocalBoundary id
  let K : R.Component := R.toSimpleGraph.connectedComponentMk (Classical.arbitrary R.Vertex)
  have hs : Subsingleton R.Component := hR.preconnected.subsingleton_connectedComponent
  have reaches : ∀ x, G.Reachable (Sum.inl K) x := by
    intro x
    cases x with
    | inl L =>
      have heq : L = K := hs.elim _ _
      subst L
      exact SimpleGraph.Reachable.refl _
    | inr b =>
      exact (show G.Adj (Sum.inl K) (Sum.inr b) from ⟨b, hs.elim _ _, rfl⟩).reachable
  exact ⟨fun x y => (reaches x).symm.trans (reaches y)⟩

-- @node: RotationSystem.local_placement_card
/-- If [a rotation system's underlying graph is connected](hyp:hR), [the total
number of components and local boundaries equals the number of local boundaries
plus one](goal). -/
lemma local_placement_card (hR : R.toSimpleGraph.Connected) :
    Nat.card (R.Component ⊕ R.LocalBoundary) = Nat.card R.LocalBoundary + 1 := by
  let : Nonempty R.Vertex := hR.nonempty
  let : Subsingleton R.Component := hR.preconnected.subsingleton_connectedComponent
  let : Unique R.Component := uniqueOfSubsingleton
    (R.toSimpleGraph.connectedComponentMk (Classical.arbitrary R.Vertex))
  have hc : Nat.card R.Component = 1 := Nat.card_unique
  rw [Nat.card_sum, hc]
  omega

/-- Given [a rotation system](hyp:R), [connectivity of its underlying graph](hyp:hR),
and [its componentwise genus-zero Euler identities](hyp:hgenus), the
[canonical sphere map](goal) uses the original rotation system and takes its
local boundaries as faces, assigning each boundary to itself. -/
noncomputable def connectedSphereMap (hR : R.toSimpleGraph.Connected)
    (hgenus : R.componentEuler) : SphereMap where
  toRotationSystem := R
  genusZero := hgenus
  Face := R.LocalBoundary
  faceFintype := Fintype.ofFinite _
  faceDecidableEq := Classical.decEq _
  boundaryFace := id
  placement_connected := R.local_placement_connected hR
  placement_card := R.local_placement_card hR

-- @node: RotationSystem.connectedSphereMap_rotation
/-- Given [connectivity of the rotation system](hyp:hR) and [its componentwise
genus-zero Euler identities](hyp:hgenus), [the canonical sphere map has exactly
the original rotation system](goal). -/
lemma connectedSphereMap_rotation (hR : R.toSimpleGraph.Connected)
    (hgenus : R.componentEuler) :
    (R.connectedSphereMap hR hgenus).toRotationSystem = R := rfl

-- @node: RotationSystem.connectedSphereMap_connected
/-- Given [connectivity of the rotation system](hyp:hR) and [its componentwise
genus-zero Euler identities](hyp:hgenus), [the canonical sphere map is connected](goal). -/
lemma connectedSphereMap_connected (hR : R.toSimpleGraph.Connected)
    (hgenus : R.componentEuler) : (R.connectedSphereMap hR hgenus).IsConnectedMap := hR

end RotationSystem
end OaiPairedStatesHamiltonian
