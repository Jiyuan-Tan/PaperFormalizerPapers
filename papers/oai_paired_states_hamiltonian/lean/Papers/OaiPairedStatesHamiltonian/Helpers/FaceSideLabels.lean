module

public import Papers.OaiPairedStatesHamiltonian.Helpers.ComponentMaps
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleSeparation

/-! Side labels on component boundaries and their transport through placements. -/

public section
namespace OaiPairedStatesHamiltonian.SphereMap

open Classical
attribute [local instance] propDecidable
set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false

variable (M : SphereMap)

/-- If [the map is connected](hyp:hM) and [a face label has the same truth value
on both sides of every edge](hyp:hP), then [it has the same truth value on any
two faces](goal). -/
-- @node: SphereMap.connected_face_label_iff
lemma connected_face_label_iff (hM : M.IsConnectedMap) (P : M.Face → Prop)
    (hP : ∀ d, P (M.faceOf d) ↔ P (M.faceOf (M.edgeInv d))) (f g : M.Face) :
    P f ↔ P g := by
  by_cases hd : Nonempty M.Dart
  · letI := hd
    have hc : (M.dualRotation hM).toSimpleGraph.connectedComponentMk f =
        (M.dualRotation hM).toSimpleGraph.connectedComponentMk g :=
      (M.dual_component_subsingleton hM).elim _ _
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hc
    clear hc
    induction p with
    | nil => exact Iff.rfl
    | cons h p ih =>
      obtain ⟨_, d, rfl, rfl⟩ := h
      exact (hP d).trans ih
  · letI : IsEmpty M.Dart := ⟨fun d => hd ⟨d⟩⟩
    have h := M.face_subsingleton_of_no_darts hM
    exact (h.elim f g) ▸ Iff.rfl

/-- Suppose [a face label has the same truth value across every edge in a chosen
component](hyp:hP), [one local boundary belongs to that component](hyp:hb), and
[another local boundary also belongs to it](hyp:hc). Then [the label has the same
truth value on the faces assigned to those two boundaries](goal). -/
-- @node: SphereMap.component_boundary_label_iff
lemma component_boundary_label_iff (K : M.Component) (P : M.Face → Prop)
    (hP : ∀ d, M.toSimpleGraph.connectedComponentMk (M.vert d) = K →
      (P (M.faceOf d) ↔ P (M.faceOf (M.edgeInv d))))
    (b c : M.LocalBoundary) (hb : M.compOf b = K) (hc : M.compOf c = K) :
    P (M.boundaryFace b) ↔ P (M.boundaryFace c) := by
  let N := M.componentMap K
  let q := M.componentFaceEquiv K
  let Q := fun f : N.Face => P (M.boundaryFace (q f).val)
  have hd (d : N.Dart) : (q (N.faceOf d)).val = Sum.inl (orbitOf M.facePerm d.val) :=
    M.componentBoundaryEquiv_dart K d
  have hi (d : N.Dart) : Q (N.faceOf d) ↔ Q (N.faceOf (N.edgeInv d)) := by
    dsimp only [Q]
    rw [hd, hd]
    change P (M.faceOf d.val) ↔ P (M.faceOf ((M.inducedInv _ d).val))
    rw [show (M.inducedInv _ d).val = M.edgeInv d.val from
      Classical.choose_spec (M.exists_inducedInv _) d]
    exact hP d.val d.property.1
  have h := N.connected_face_label_iff (M.componentMap_connected K) Q hi
    (q.symm ⟨b, hb⟩) (q.symm ⟨c, hc⟩)
  simpa only [Q, q.apply_symm_apply] using h

/-- If [a face label has the same truth value across every edge outside a chosen
component](hyp:hP) and [a face lies behind a specified boundary of that component
in the placement graph](hyp:hf), then [the label has the same truth value on that
face and on the face assigned to the boundary](goal). -/
-- @node: SphereMap.faceBehind_label_iff
lemma faceBehind_label_iff (K : M.Component) (P : M.Face → Prop)
    (hP : ∀ d, M.toSimpleGraph.connectedComponentMk (M.vert d) ≠ K →
      (P (M.faceOf d) ↔ P (M.faceOf (M.edgeInv d))))
    (b : M.LocalBoundary) (f : M.Face) (hf : M.FaceBehind K b f) :
    P (M.boundaryFace b) ↔ P f := by
  let label : M.Component ⊕ M.Face → Prop := Sum.elim
    (fun L => P (M.boundaryFace (M.boundaryBehind L f).val)) P
  have step (x y : M.Component ⊕ M.Face)
      (h : x ≠ Sum.inl K ∧ y ≠ Sum.inl K ∧ M.placementGraph.Adj x y) :
      label x ↔ label y := by
    have incident (L : M.Component) (g : M.Face) (hL : L ≠ K)
        (hadj : M.placementGraph.Adj (Sum.inl L) (Sum.inr g)) :
        label (Sum.inl L) ↔ label (Sum.inr g) := by
      obtain ⟨c, hc, rfl⟩ := hadj
      exact M.component_boundary_label_iff L P
        (fun d hd => hP d (fun he => hL (hd.symm.trans he)))
        _ c (M.boundaryBehind L f).property hc
    cases x with
    | inl L =>
      cases y with
      | inl J => exact False.elim h.2.2
      | inr g => exact incident L g (fun he => h.1 (congrArg Sum.inl he)) h.2.2
    | inr g =>
      cases y with
      | inr g' => exact False.elim h.2.2
      | inl L => exact (incident L g (fun he => h.2.1 (congrArg Sum.inl he))
          (h.2.2.symm)).symm
  have transport {x y : M.Component ⊕ M.Face}
      (p : Relation.ReflTransGen (fun x y => x ≠ Sum.inl K ∧ y ≠ Sum.inl K ∧
        M.placementGraph.Adj x y) x y) : label x ↔ label y := by
    induction p with
    | refl => exact Iff.rfl
    | tail p h ih => exact ih.trans (step _ _ h)
  exact transport hf.2

/-- Suppose [the map is connected](hyp:hM), [a face label is true on the face of
each directed cycle dart and false on the face of its reverse](hyp:hboundary),
and [the label has the same truth value across every edge outside the cycle](hyp:hacross).
Then [a face has the label if and only if it lies in the cycle's left region](goal). -/
-- @node: SphereMap.connected_cycle_side_label
lemma connected_cycle_side_label (hM : M.IsConnectedMap) (C : M.Cycle)
    (P : M.Face → Prop)
    (hboundary : ∀ d ∈ C.val, P (M.faceOf d) ∧ ¬ P (M.faceOf (M.edgeInv d)))
    (hacross : ∀ d, M.edgeOf d ∉ C.val.map M.edgeOf →
      (P (M.faceOf d) ↔ P (M.faceOf (M.edgeInv d)))) (f : M.Face) :
    P f ↔ f ∈ M.leftRegion C := by
  obtain ⟨outer, hout⟩ := M.exists_face_outside_cycle_leftRegion hM C
  let Q := fun g => (P g ↔ g ∈ M.leftRegion C)
  have hi (d : M.Dart) : Q (M.faceOf d) ↔ Q (M.faceOf (M.edgeInv d)) := by
    by_cases he : M.edgeOf d ∈ C.val.map M.edgeOf
    · obtain ⟨e, he, hed⟩ := List.mem_map.mp he
      have hl := M.cycle_face_mem_leftRegion C e he
      have hr := M.cycle_boundary_opposite_outside hM C outer hout e he
      have hp := hboundary e he
      have ql : Q (M.faceOf e) := ⟨fun _ => hl, fun _ => hp.1⟩
      have qr : Q (M.faceOf (M.edgeInv e)) :=
        ⟨fun h => (hp.2 h).elim, fun h => (hr h).elim⟩
      rcases (M.edgeOf_eq_iff e d).mp hed with h | h
      · rw [h]
        exact ⟨fun _ => qr, fun _ => ql⟩
      · rw [h, M.edgeInv_involutive]
        exact ⟨fun _ => ql, fun _ => qr⟩
    · exact iff_congr (hacross d he) (M.leftRegion_across_noncycle hM C d he)
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  exact (M.connected_face_label_iff hM Q hi (M.faceOf d) f).mp
    ⟨fun _ => M.cycle_face_mem_leftRegion C d hd, fun _ => (hboundary d hd).1⟩

-- @node: SphereMap.connected_leftRegion_iff_boundary
/-- If [the map is connected](hyp:hM), then [the face assigned to a local boundary
lies in a cycle's left region if and only if that boundary lies in the cycle's
left local region](goal). -/
lemma connected_leftRegion_iff_boundary (hM : M.IsConnectedMap) (C : M.Cycle)
    (b : M.LocalBoundary) :
    M.boundaryFace b ∈ M.leftRegion C ↔ b ∈ M.leftLocalRegion C := by
  constructor
  · rintro ⟨c, hc, hf⟩
    have he := M.faceBehind_connected hM _ c _ hf
    have hcb := M.boundary_unique_in_component c b
      (hM.preconnected.subsingleton_connectedComponent.elim _ _) he
    exact hcb ▸ hc
  · exact M.leftLocalRegion_face_mem C b

/-- If [a face label is true on the face of each directed cycle dart and false on
the face of its reverse](hyp:hboundary), and [the label has the same truth value
across every edge outside the cycle](hyp:hacross), then [a face has the label if
and only if it lies in the cycle's left region](goal). -/
-- @node: SphereMap.cycle_side_label
lemma cycle_side_label (C : M.Cycle) (P : M.Face → Prop)
    (hboundary : ∀ d ∈ C.val, P (M.faceOf d) ∧ ¬ P (M.faceOf (M.edgeInv d)))
    (hacross : ∀ d, M.edgeOf d ∉ C.val.map M.edgeOf →
      (P (M.faceOf d) ↔ P (M.faceOf (M.edgeInv d)))) (f : M.Face) :
    P f ↔ f ∈ M.leftRegion C := by
  obtain ⟨K, D, rfl⟩ := M.cycle_in_component C
  let N := M.componentMap K
  let C := M.ofComponentCycle K D
  let q := M.componentFaceEquiv K
  let Q := fun g : N.Face => P (M.boundaryFace (q g).val)
  have hd (d : N.Dart) : (q (N.faceOf d)).val = Sum.inl (orbitOf M.facePerm d.val) :=
    M.componentBoundaryEquiv_dart K d
  have hinv (d : N.Dart) : (N.edgeInv d).val = M.edgeInv d.val :=
    Classical.choose_spec (M.exists_inducedInv _) d
  have hb (d : N.Dart) (hm : d ∈ D.val) :
      Q (N.faceOf d) ∧ ¬ Q (N.faceOf (N.edgeInv d)) := by
    dsimp only [Q]
    rw [hd, hd, hinv]
    exact hboundary d.val (List.mem_map.mpr ⟨d, hm, rfl⟩)
  have ha (d : N.Dart) (hm : N.edgeOf d ∉ D.val.map N.edgeOf) :
      Q (N.faceOf d) ↔ Q (N.faceOf (N.edgeInv d)) := by
    dsimp only [Q]
    rw [hd, hd, hinv]
    exact hacross d.val (fun he => hm ((M.component_cycle_edge_mem K D d).mpr he))
  have local_label (b : M.LocalBoundary) (hbK : M.compOf b = K) :
      P (M.boundaryFace b) ↔ b ∈ M.leftLocalRegion C := by
    let b' := (M.componentBoundaryEquiv K).symm ⟨b, hbK⟩
    have hbb : (M.componentBoundaryEquiv K b').val = b :=
      congrArg Subtype.val ((M.componentBoundaryEquiv K).apply_symm_apply ⟨b, hbK⟩)
    have hs := N.connected_cycle_side_label (M.componentMap_connected K) D Q hb ha
      (N.boundaryFace b')
    have hq : (q (N.boundaryFace b')).val = b := hbb
    dsimp only [Q] at hs
    rw [hq, N.connected_leftRegion_iff_boundary (M.componentMap_connected K)] at hs
    exact hs.trans ((M.component_leftLocalRegion_iff K D b').trans
      (by rw [hbb]))
  have other (d : M.Dart) (hne : M.toSimpleGraph.connectedComponentMk (M.vert d) ≠ K) :
      P (M.faceOf d) ↔ P (M.faceOf (M.edgeInv d)) := by
    apply hacross d
    intro hm
    obtain ⟨e, he, hed⟩ := List.mem_map.mp hm
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    apply hne
    rcases (M.edgeOf_eq_iff e'.val d).mp hed with h | h
    · rw [h]
      exact e'.property.1
    · rw [h]
      exact (M.head_component e'.val).trans e'.property.1
  let b := (M.boundaryBehind K f).val
  have hbf : M.FaceBehind K b f :=
    (Classical.choose_spec (M.faceBehind_existsUnique K f)).1
  have hlabel := M.faceBehind_label_iff K P other b f hbf
  constructor
  · intro hp
    refine ⟨b, (local_label b hbf.1).mp (hlabel.mpr hp), ?_⟩
    simpa only [hbf.1] using hbf
  · rintro ⟨c, hc, hcf⟩
    obtain ⟨d, hdmem⟩ := List.exists_mem_of_ne_nil D.val D.property.1.1
    have hcK : M.compOf c = K :=
      (M.leftLocalRegion_compOf C d.val (List.mem_map.mpr ⟨d, hdmem, rfl⟩) c hc).trans
        d.property.1
    have hcf' : M.FaceBehind K c f := by simpa only [hcK] using hcf
    have hcb : c = b := (M.faceBehind_existsUnique K f).unique hcf' hbf
    exact hlabel.mp ((local_label b hbf.1).mpr (hcb ▸ hc))

-- @node: SphereMap.rightRegion_iff_not_leftRegion
/-- [A face lies in a cycle's right region if and only if it does not lie in the
cycle's left region](goal). -/
lemma rightRegion_iff_not_leftRegion (C : M.Cycle) (f : M.Face) :
    f ∈ M.rightRegion C ↔ f ∉ M.leftRegion C := by
  constructor
  · intro hr hl
    exact Set.disjoint_left.mp (M.cycle_sides_partition C).1 hl hr
  · intro hn
    have hcover : f ∈ M.leftRegion C ∪ M.rightRegion C :=
      (M.cycle_sides_partition C).2.symm ▸ Set.mem_univ f
    exact hcover.resolve_left hn

end OaiPairedStatesHamiltonian.SphereMap
