module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleGluing
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleSideCount
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleSeparation
public import Papers.OaiPairedStatesHamiltonian.Helpers.PairPhases

/-! Inherited coloring and vertex bounds for capping a separating triangle. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

variable (T : SphereMap)

/-- If [T is a sphere triangulation](hyp:hT), [the face coloring assigns
different colors across every edge](hyp:hcol), and [C has length three](hyp:hthree),
then [there is a single color shared by the faces to the left of all oriented
edges of C](goal). -/
-- @node: SphereMap.triangle_boundary_color_constant
lemma triangle_boundary_color_constant (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (C : T.Cycle) (hthree : C.val.length = 3) :
    ∃ b : Bool, ∀ d ∈ C.val, col (T.faceOf d) = b := by
  obtain ⟨outer, hout⟩ := T.exists_face_outside_cycle_leftRegion hT.props.1 C
  have hs := cycle_signed_side_count T hT col hcol C outer hout
  have hle := List.length_filter_le (fun d => col (T.faceOf d) = true) C.val
  have hk : (C.val.filter (fun d => col (T.faceOf d) = true)).length = 0 ∨
      (C.val.filter (fun d => col (T.faceOf d) = true)).length = C.val.length := by
    rw [hthree] at hs hle ⊢
    omega
  rcases hk with hk | hk
  · refine ⟨false, ?_⟩
    have hempty := List.length_eq_zero_iff.mp hk
    intro d hd
    have hn : col (T.faceOf d) ≠ true := by
      intro hb
      have hm : d ∈ C.val.filter (fun e => col (T.faceOf e) = true) :=
        List.mem_filter.mpr ⟨hd, by simpa using hb⟩
      simp only [hempty, List.not_mem_nil] at hm
    exact Bool.eq_false_iff.mpr hn
  · refine ⟨true, ?_⟩
    have hall := List.length_filter_eq_length_iff.mp hk
    intro d hd
    simpa using hall d hd

/-- For [a map T](hyp:T) [that is a sphere triangulation](hyp:hT), [a cycle
C in T](hyp:C), and [a chosen outer face](hyp:outer) [outside the left region
of C](hyp:hout), [the capped sphere map](goal) is obtained by retaining the
rotation on the left of C and closing its boundary with a cap face. -/
-- @node: SphereMap.cycleCappedMap
noncomputable def cycleCappedMap (hT : IsSphereTriangulation T) (C : T.Cycle)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C) : SphereMap :=
  (T.cycleLeftRotation C).connectedSphereMap
    (T.cycleLeftRotation_connected hT C)
    (T.cycleLeftRotation_componentEuler hT C outer hout)

/-- Suppose [T is a sphere triangulation](hyp:hT) and [retained oriented edges d
and e belong to the same face cycle of the retained rotation](hyp:h). Then
[the color assignment that uses the original face color in the left region
and the opposite of b outside that region assigns the same color to d and
e](goal). -/
-- @node: SphereMap.cycle_cap_color_invariant
lemma cycle_cap_color_invariant (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (C : T.Cycle) (b : Bool)
    (d e : T.RegionDart (T.leftRegion C))
    (h : (T.cycleLeftRotation C).facePerm.SameCycle d e) :
    (if T.faceOf d.val ∈ T.leftRegion C then col (T.faceOf d.val) else !b) =
      (if T.faceOf e.val ∈ T.leftRegion C then col (T.faceOf e.val) else !b) := by
  by_cases hd : T.faceOf d.val ∈ T.leftRegion C
  · have hf := (T.region_face_sameCycle_iff hT.props.1 _ d e hd).mp h
    rw [← hf]
  · have he := T.cycle_exterior_sameCycle hT.props.1 C d e h hd
    rw [if_neg hd, if_neg he]

/-- Suppose [T is a sphere triangulation](hyp:hT), [the original face coloring
assigns different colors across every edge](hyp:hcol), [the chosen outer face
lies outside the left region of C](hyp:hout), and [every face to the left of
an oriented edge of C has color b](hyp:hb). Then [the capped map admits a face
coloring with different colors across every edge, using the original color
for retained original faces and the opposite of b for the cap face](goal). -/
-- @node: SphereMap.exists_cycle_cap_coloring
lemma exists_cycle_cap_coloring (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (C : T.Cycle) (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (b : Bool) (hb : ∀ d ∈ C.val, col (T.faceOf d) = b) :
    ∃ c : (T.cycleCappedMap hT C outer hout).Face → Bool,
      PartitionColoring (T.cycleCappedMap hT C outer hout) c ∧
      ∀ d : T.RegionDart (T.leftRegion C),
        c ((T.cycleCappedMap hT C outer hout).faceOf d) =
          if T.faceOf d.val ∈ T.leftRegion C then col (T.faceOf d.val) else !b := by
  let colorOrbit : (T.cycleLeftRotation C).FaceOrbit → Bool :=
    Quotient.lift (fun d =>
      if T.faceOf d.val ∈ T.leftRegion C then col (T.faceOf d.val) else !b)
      (T.cycle_cap_color_invariant hT col C b)
  let c : (T.cycleCappedMap hT C outer hout).Face → Bool :=
    Sum.elim colorOrbit (fun _ => false)
  have hc (d : T.RegionDart (T.leftRegion C)) :
      c ((T.cycleCappedMap hT C outer hout).faceOf d) =
        if T.faceOf d.val ∈ T.leftRegion C then col (T.faceOf d.val) else !b := rfl
  refine ⟨c, ?_, hc⟩
  intro d
  rw [hc, hc]
  change (if T.faceOf d.val ∈ T.leftRegion C then col (T.faceOf d.val) else !b) ≠
    (if T.faceOf (T.edgeInv d.val) ∈ T.leftRegion C then
      col (T.faceOf (T.edgeInv d.val)) else !b)
  by_cases hd : T.faceOf d.val ∈ T.leftRegion C
  · rw [if_pos hd]
    by_cases hi : T.faceOf (T.edgeInv d.val) ∈ T.leftRegion C
    · rw [if_pos hi]
      exact hcol d.val
    · rw [if_neg hi]
      have hboundary : d.val ∈ C.val := by
        have h := T.cycle_exterior_dart_boundary hT.props.1 C
          ((T.cycleLeftRotation C).edgeInv d) hi
        change T.edgeInv (T.edgeInv d.val) ∈ C.val at h
        rwa [T.edgeInv_involutive] at h
      rw [hb d.val hboundary]
      cases b <;> decide
  · rw [if_neg hd]
    have hi := d.property.resolve_left hd
    rw [if_pos hi, hb _ (T.cycle_exterior_dart_boundary hT.props.1 C d hd)]
    cases b <;> decide

/-- If [T is a sphere triangulation](hyp:hT) and [the chosen outer face lies
outside the left region of C](hyp:hout), then [the capped map is simple: it has
no loops and distinct edges cannot share the same endpoint pair](goal). -/
-- @node: SphereMap.cycleCappedMap_isSimple
lemma cycleCappedMap_isSimple (hT : IsSphereTriangulation T) (C : T.Cycle)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C) :
    (T.cycleCappedMap hT C outer hout).IsSimple := by
  constructor
  · intro d he
    exact hT.props.2.1.1 d.val (congrArg Subtype.val he)
  · intro d e he
    apply T.regionEdgeMap_injective (T.leftRegion C)
    apply hT.props.2.1.2 d.val e.val
    exact congrArg (Sym2.map Subtype.val) he

/-- If [T is a sphere triangulation](hyp:hT) and [the chosen outer face lies
outside the left region of C](hyp:hout), then [every vertex v of the capped map
is the tail of some oriented edge of that map](goal). -/
-- @node: SphereMap.cycleCappedMap_has_dart
lemma cycleCappedMap_has_dart (hT : IsSphereTriangulation T) (C : T.Cycle)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (v : (T.cycleCappedMap hT C outer hout).Vertex) :
    ∃ d : (T.cycleCappedMap hT C outer hout).Dart,
      (T.cycleCappedMap hT C outer hout).vert d = v := by
  obtain ⟨d, hd, hv⟩ := v.property
  exact ⟨⟨d, hd⟩, Subtype.ext hv⟩

/-- If [T is a sphere triangulation](hyp:hT), [C has length three](hyp:hthree),
and [the chosen outer face lies outside the left region of C](hyp:hout), then
[every face of the capped map has exactly three incident oriented edges](goal). -/
-- @node: SphereMap.triangleCap_face_darts_card
lemma triangleCap_face_darts_card (hT : IsSphereTriangulation T) (C : T.Cycle)
    (hthree : C.val.length = 3) (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (f : (T.cycleCappedMap hT C outer hout).Face) :
    ((T.cycleCappedMap hT C outer hout).faceDarts f).card = 3 := by
  cases f with
  | inl o =>
    obtain ⟨d, rfl⟩ := Quotient.exists_rep o
    simp only [faceDarts, faceOf, cycleCappedMap, RotationSystem.connectedSphereMap,
      id_eq, Sum.inl.injEq]
    by_cases hd : T.faceOf d.val ∈ T.leftRegion C
    · exact (T.region_face_orbit_length hT.props.1 _ d hd).trans
        (hT.props.2.2.2 _).1
    · exact (T.cycle_exterior_orbit_length hT.props.1 C d hd).trans hthree
  | inr v =>
    obtain ⟨d, hd⟩ := T.cycleCappedMap_has_dart hT C outer hout v.val
    exact (v.property d hd).elim

/-- Suppose [T is a sphere triangulation](hyp:hT) and [the chosen outer face
lies outside the left region of C](hyp:hout). If [two oriented edges of the
capped map belong to the same face](hyp:hf) and [have the same tail
vertex](hyp:hv), then [they are the same oriented edge](goal). -/
-- @node: SphereMap.cycleCap_face_tail_injective
lemma cycleCap_face_tail_injective (hT : IsSphereTriangulation T) (C : T.Cycle)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (d e : (T.cycleCappedMap hT C outer hout).Dart)
    (hf : (T.cycleCappedMap hT C outer hout).faceOf d =
      (T.cycleCappedMap hT C outer hout).faceOf e)
    (hv : (T.cycleCappedMap hT C outer hout).vert d =
      (T.cycleCappedMap hT C outer hout).vert e) : d = e := by
  have ho : orbitOf (T.cycleLeftRotation C).facePerm d =
      orbitOf (T.cycleLeftRotation C).facePerm e := Sum.inl.inj hf
  have hc := Quotient.exact ho
  apply Subtype.ext
  have hv' : T.vert d.val = T.vert e.val := congrArg Subtype.val hv
  by_cases hd : T.faceOf d.val ∈ T.leftRegion C
  · have hfe := (T.region_face_sameCycle_iff hT.props.1 _ d e hd).mp hc
    have hinj : Set.InjOn T.vert (↑(T.faceDarts (T.faceOf d.val)) : Set T.Dart) := by
      apply Finset.card_image_iff.mp
      rw [← triangulation_faceVertices_eq_image T hT]
      rw [(hT.props.2.2.2 _).2,
        ← T.faceLength_eq_card_faceDarts, (hT.props.2.2.2 _).1]
    exact hinj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfe.symm⟩) hv'
  · have he := T.cycle_exterior_sameCycle hT.props.1 C d e hc hd
    have hid := T.cycle_exterior_dart_boundary hT.props.1 C d hd
    have hie := T.cycle_exterior_dart_boundary hT.props.1 C e he
    apply T.edgeInv.injective
    apply List.inj_on_of_nodup_map (cycle_heads_nodup T C) hid hie
    change T.vert (T.edgeInv (T.edgeInv d.val)) =
      T.vert (T.edgeInv (T.edgeInv e.val))
    rw [T.edgeInv_involutive, T.edgeInv_involutive]
    exact hv'

/-- If [T is a sphere triangulation](hyp:hT), [C has length three](hyp:hthree),
[the chosen outer face lies outside the left region of C](hyp:hout), and
[there is a vertex strictly on the left side of C](hyp:hin), then [the capped
map is a sphere triangulation](goal). -/
-- @node: SphereMap.triangleCap_isSphereTriangulation
lemma triangleCap_isSphereTriangulation (hT : IsSphereTriangulation T) (C : T.Cycle)
    (hthree : C.val.length = 3) (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (hin : ∃ v, T.strictlyOnSide (T.leftRegion C) C v) :
    IsSphereTriangulation (T.cycleCappedMap hT C outer hout) := by
  let N := T.cycleCappedMap hT C outer hout
  refine ⟨T.cycleLeftRotation_connected hT C,
    T.cycleCappedMap_isSimple hT C outer hout, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hin
    have hpos : 0 < (Finset.univ.filter (T.strictlyOnSide (T.leftRegion C) C)).card :=
      Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
    have hcard := T.cycle_left_vertex_card hT C
    change 4 ≤ Fintype.card (T.cycleLeftRotation C).Vertex
    omega
  · intro f
    have hcard := T.triangleCap_face_darts_card hT C hthree outer hout f
    refine ⟨(N.faceLength_eq_card_faceDarts f).trans hcard, ?_⟩
    have hempty : (Finset.univ.filter (fun v : N.Vertex =>
        ∃ hv : ∀ d, N.vert d ≠ v, N.boundaryFace (Sum.inr ⟨v, hv⟩) = f)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hn, _⟩ := (Finset.mem_filter.mp hv).2
      obtain ⟨d, hd⟩ := T.cycleCappedMap_has_dart hT C outer hout v
      exact hn d hd
    change ((N.faceDarts f).image N.vert ∪ _).card = 3
    rw [hempty, Finset.union_empty, Finset.card_image_iff.mpr]
    · exact hcard
    · intro d hd e he hv
      exact T.cycleCap_face_tail_injective hT C outer hout d e
        ((Finset.mem_filter.mp hd).2.trans (Finset.mem_filter.mp he).2.symm) hv

/-- If [T is a sphere triangulation](hyp:hT), [the chosen outer face lies outside
the left region of C](hyp:hout), and [there is a vertex strictly on the right
side of C](hyp:hother), then [the capped map has strictly fewer vertices than
T](goal). -/
-- @node: SphereMap.triangleCap_vertex_card_lt
lemma triangleCap_vertex_card_lt (hT : IsSphereTriangulation T) (C : T.Cycle)
    (outer : T.Face) (hout : outer ∉ T.leftRegion C)
    (hother : ∃ v, T.strictlyOnSide (T.rightRegion C) C v) :
    Fintype.card (T.cycleCappedMap hT C outer hout).Vertex < Fintype.card T.Vertex := by
  obtain ⟨v, hv⟩ := hother
  apply Fintype.card_subtype_lt (x := v)
  intro hin
  obtain ⟨f, hf, hfv⟩ := (T.regionVertexSet_iff_face_incidence hT _ v).mp hin
  obtain ⟨_, g, hg, hgv⟩ := Finset.mem_filter.mp hv.2
  have hgl := (T.cycle_nonboundary_face_side hT C v hv.1 f g hfv hgv).mp hf
  exact Set.disjoint_left.mp (T.cycle_sides_partition C).1 hgl hg

/-- If [T is a sphere triangulation](hyp:hT), [its face coloring assigns different
colors across every edge](hyp:hcol), and [C is a separating triangle](hyp:hsep),
then [one can choose an outer face outside the left region of C so that the
capped map is a sphere triangulation with strictly fewer vertices and admits
a face coloring with different colors across every edge that preserves the
color of every retained original face](goal). -/
-- @node: SphereMap.exists_colored_triangle_cap
lemma exists_colored_triangle_cap (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (C : T.Cycle) (hsep : IsSeparatingTriangle T C) :
    ∃ (outer : T.Face) (hout : outer ∉ T.leftRegion C),
      IsSphereTriangulation (T.cycleCappedMap hT C outer hout) ∧
      Fintype.card (T.cycleCappedMap hT C outer hout).Vertex < Fintype.card T.Vertex ∧
      ∃ c : (T.cycleCappedMap hT C outer hout).Face → Bool,
        PartitionColoring (T.cycleCappedMap hT C outer hout) c ∧
        ∀ (d : T.RegionDart (T.leftRegion C)) (_hd : T.faceOf d.val ∈ T.leftRegion C),
          c ((T.cycleCappedMap hT C outer hout).faceOf d) = col (T.faceOf d.val) := by
  obtain ⟨outer, hout⟩ := T.exists_face_outside_cycle_leftRegion hT.props.1 C
  obtain ⟨b, hb⟩ := T.triangle_boundary_color_constant hT col hcol C hsep.props.1
  obtain ⟨c, hc, hfaces⟩ := T.exists_cycle_cap_coloring hT col hcol C outer hout b hb
  refine ⟨outer, hout,
    T.triangleCap_isSphereTriangulation hT C hsep.props.1 outer hout hsep.props.2.1,
    T.triangleCap_vertex_card_lt hT C outer hout hsep.props.2.2, c, hc, ?_⟩
  intro d hd
  rw [hfaces, if_pos hd]

end SphereMap
end OaiPairedStatesHamiltonian
