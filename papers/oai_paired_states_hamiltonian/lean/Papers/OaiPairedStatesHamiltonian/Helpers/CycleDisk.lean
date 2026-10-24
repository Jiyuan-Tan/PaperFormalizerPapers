module

public import Papers.OaiPairedStatesHamiltonian.Helpers.States

/-! Canonical restriction to one side of a cycle, and Euler counting after capping.
The restriction below is rotation data, not an assertion that the cut has a disk
embedding. Consumers must construct that embedding with the inherited boundaries.
The counting lemmas prove its Euler consequence without accepting Euler as a field. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable

namespace SphereMap
variable (M : SphereMap)

/-- In [a sphere map](hyp:M), for [a selected face region](hyp:R) and [a dart](hyp:d),
the [edge retention condition](goal) holds when at least one of the dart's two
incident faces belongs to the region. -/
noncomputable def regionKeeps (R : Set M.Face) (d : M.Dart) : Prop :=
  M.faceOf d ∈ R ∨ M.faceOf (M.edgeInv d) ∈ R

-- @node: SphereMap.regionKeeps_inv
/-- [A dart is retained by a face region if and only if its reverse is
retained](goal). -/
lemma regionKeeps_inv (R : Set M.Face) (d : M.Dart) :
    M.regionKeeps R (M.edgeInv d) ↔ M.regionKeeps R d := by
  unfold regionKeeps
  rw [M.edgeInv_involutive d]
  exact or_comm

/-- For [a sphere map](hyp:M) and [a selected face region](hyp:R), the
[region's vertex set](goal) consists of the initial vertices of retained darts,
equivalently the endpoints of retained edges. -/
noncomputable def regionVertexSet (R : Set M.Face) : Set M.Vertex :=
  {v | ∃ d, M.regionKeeps R d ∧ M.vert d = v}

/-- For [a sphere map](hyp:M) and [a selected face region](hyp:R), the
[type of region darts](goal) consists of the darts whose edge has at least one
incident face in the region. -/
abbrev RegionDart (R : Set M.Face) := {d : M.Dart // M.regionKeeps R d}

/-- In [a sphere map](hyp:M), for [a selected face region](hyp:R) and
[a retained dart](hyp:d), the [restricted initial vertex](goal) is the dart's
original initial vertex, viewed as a vertex of the region. -/
noncomputable def regionVert (R : Set M.Face) (d : M.RegionDart R) : M.regionVertexSet R :=
  ⟨M.vert d.val, d.val, d.property, rfl⟩

/-- For [a sphere map](hyp:M) and [a selected face region](hyp:R), the
[restricted edge reversal permutation](goal) reverses each retained dart using
the original edge reversal. -/
noncomputable def regionInv (R : Set M.Face) : Equiv.Perm (M.RegionDart R) where
  toFun d := ⟨M.edgeInv d.val, (M.regionKeeps_inv R d.val).mpr d.property⟩
  invFun d := ⟨M.edgeInv d.val, (M.regionKeeps_inv R d.val).mpr d.property⟩
  left_inv d := Subtype.ext (M.edgeInv_involutive d.val)
  right_inv d := Subtype.ext (M.edgeInv_involutive d.val)

/-- For [a sphere map](hyp:M) and [a selected face region](hyp:R), the
[restricted vertex rotation](goal) sends each retained dart to the first retained
dart encountered by repeatedly applying the original vertex rotation. -/
noncomputable def regionRot (R : Set M.Face) : Equiv.Perm (M.RegionDart R) :=
  firstReturnPerm M.rot {d | M.regionKeeps R d}

-- @node: SphereMap.regionInv_involutive
/-- [Reversing a retained dart twice returns the original dart](goal). -/
lemma regionInv_involutive (R : Set M.Face) : Function.Involutive (M.regionInv R) := by
  intro d
  exact Subtype.ext (M.edgeInv_involutive d.val)

-- @node: SphereMap.regionInv_fixedPointFree
/-- [The reverse of a retained dart is different from that dart](goal). -/
lemma regionInv_fixedPointFree (R : Set M.Face) (d : M.RegionDart R) :
    M.regionInv R d ≠ d := by
  intro h
  exact M.edgeInv_fixedPointFree d.val (congrArg Subtype.val h)

-- @node: SphereMap.regionRot_vertex
/-- [Restricted vertex rotation preserves the initial vertex of every retained
dart](goal). -/
lemma regionRot_vertex (R : Set M.Face) (d : M.RegionDart R) :
    M.regionVert R (M.regionRot R d) = M.regionVert R d := by
  apply Subtype.ext
  obtain ⟨n, hn, heq, hfirst⟩ := Classical.choose_spec
    (exists_firstReturnPerm M.rot {d | M.regionKeeps R d}) d
  change (firstReturnPerm M.rot _ d).val = (M.rot ^ n) d.val at heq
  change M.vert ((firstReturnPerm M.rot _ d).val) = M.vert d.val
  rw [heq]
  clear hn heq hfirst
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, M.rot_vertex]
    exact ih

-- @node: SphereMap.regionRot_fibre
/-- [Restricted vertex rotation forms a single cycle on the retained darts
with any given initial vertex](goal). -/
lemma regionRot_fibre (R : Set M.Face) (v : M.regionVertexSet R) :
    (M.regionRot R).IsCycleOn {d | M.regionVert R d = v} := by
  refine ⟨⟨?_, (M.regionRot R).injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (M.regionRot_vertex R d).trans hd
  · intro d hd
    refine ⟨(M.regionRot R).symm d, ?_, (M.regionRot R).apply_symm_apply d⟩
    change M.regionVert R ((M.regionRot R).symm d) = v
    rw [← M.regionRot_vertex R ((M.regionRot R).symm d),
      (M.regionRot R).apply_symm_apply]
    exact hd
  · intro d hd e he
    apply sameCycle_firstReturnPerm
    apply (M.rot_fibre v.val).2
    · exact congrArg Subtype.val hd
    · exact congrArg Subtype.val he

/-- For [a sphere map](hyp:M) and [a selected face region](hyp:R), the
[restricted rotation system](goal) consists of the edges incident to selected
faces and their endpoints, with the original edge reversal and vertex rotations
inherited by first return to retained darts. -/
noncomputable def regionRotation (R : Set M.Face) : RotationSystem where
  Vertex := M.regionVertexSet R
  Dart := M.RegionDart R
  vert := M.regionVert R
  edgeInv := M.regionInv R
  edgeInv_involutive := M.regionInv_involutive R
  edgeInv_fixedPointFree := M.regionInv_fixedPointFree R
  rot := M.regionRot R
  rot_vertex := M.regionRot_vertex R
  rot_fibre := M.regionRot_fibre R

/-- For [a sphere map](hyp:M) and [a cycle](hyp:C), the [left-side rotation
system](goal) is the restriction to edges incident to faces in the cycle's left
region. -/
noncomputable def cycleLeftRotation (C : M.Cycle) : RotationSystem :=
  M.regionRotation (M.leftRegion C)

/-- If [a permutation sends an element of the selected set back into that
set in one step](hyp:hd), [its first-return permutation at that element equals
the original one-step successor](goal). -/
-- @node: SphereMap.firstReturnPerm_apply_of_mem
lemma firstReturnPerm_apply_of_mem {D : Type} [Fintype D] (p : Equiv.Perm D)
    (U : Set D) (d : U) (hd : p d.val ∈ U) :
    (firstReturnPerm p U d).val = p d.val := by
  obtain ⟨n, hn, heq, hfirst⟩ := Classical.choose_spec (exists_firstReturnPerm p U) d
  change (firstReturnPerm p U d).val = (p ^ n) d.val at heq
  have hn1 : n = 1 := by
    by_contra hne
    have hnot := hfirst 1 (by omega) (by omega)
    exact hnot (by simpa using hd)
  simpa [hn1] using heq

/-- If [a retained dart's original face belongs to the selected region](hyp:hd),
[one facial step in the restricted rotation system gives the same underlying
dart as one facial step in the original map](goal). -/
-- @node: SphereMap.region_facePerm_val
lemma region_facePerm_val (R : Set M.Face) (d : M.RegionDart R)
    (hd : M.faceOf d.val ∈ R) :
    ((M.regionRotation R).facePerm d).val = M.facePerm d.val := by
  change (firstReturnPerm M.rot {e | M.regionKeeps R e} (M.regionInv R d)).val = _
  apply firstReturnPerm_apply_of_mem
  change M.regionKeeps R (M.facePerm d.val)
  exact Or.inl ((M.dual_rot_vertex d.val).symm ▸ hd)

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.region_facePerm_pow_val
/-- If [a retained dart's original face belongs to the selected region](hyp:hd),
[any number of restricted facial steps agrees with the same number of original
facial steps and preserves the dart's original face](goal). -/
lemma region_facePerm_pow_val (R : Set M.Face) (d : M.RegionDart R)
    (hd : M.faceOf d.val ∈ R) (n : ℕ) :
    (((M.regionRotation R).facePerm ^ n) d).val = (M.facePerm ^ n) d.val ∧
      M.faceOf ((((M.regionRotation R).facePerm ^ n) d).val) = M.faceOf d.val := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, M.region_facePerm_val R _ (ih.2.symm ▸ hd)]
    constructor
    · rw [ih.1, pow_succ', Equiv.Perm.mul_apply]
    · exact (M.dual_rot_vertex _).trans ih.2

/-- If [the map is connected](hyp:hM) and [the first retained dart's original
face is selected](hyp:hd), [two retained darts share a restricted facial orbit
if and only if they have the same original face](goal). -/
-- @node: SphereMap.region_face_sameCycle_iff
lemma region_face_sameCycle_iff (hM : M.IsConnectedMap) (R : Set M.Face)
    (d e : M.RegionDart R) (hd : M.faceOf d.val ∈ R) :
    (M.regionRotation R).facePerm.SameCycle d e ↔ M.faceOf d.val = M.faceOf e.val := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    exact (M.region_facePerm_pow_val R d hd n).2.symm
  · intro h
    have hcycle := (M.dual_rot_fibre hM (M.faceOf d.val)).2 rfl h.symm
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    have heq : ((M.regionRotation R).facePerm ^ n) d = e := by
      apply Subtype.ext
      exact (M.region_facePerm_pow_val R d hd n).1.trans hn
    rw [← heq]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)

set_option backward.isDefEq.respectTransparency false in
/-- If [the map is connected](hyp:hM) and [a retained dart's original face
is selected](hyp:hd), [the number of darts in its restricted facial orbit equals
the length of its original face](goal). -/
-- @node: SphereMap.region_face_orbit_length
lemma region_face_orbit_length (hM : M.IsConnectedMap) (R : Set M.Face)
    (d : M.RegionDart R) (hd : M.faceOf d.val ∈ R) :
    (Finset.univ.filter (fun e : (M.regionRotation R).Dart =>
      orbitOf (M.regionRotation R).facePerm e =
        orbitOf (M.regionRotation R).facePerm d)).card = M.faceLength (M.faceOf d.val) := by
  rw [M.faceLength_eq_card_faceDarts]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    have ho := (Finset.mem_filter.mp he).2
    have hc := Quotient.exact ho
    have hf := (M.region_face_sameCycle_iff hM R d e hd).mp hc.symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf.symm⟩
  · intro e he e' he' h
    exact Subtype.ext h
  · intro e he
    have hf : M.faceOf e = M.faceOf d.val := (Finset.mem_filter.mp he).2
    let e' : M.RegionDart R := ⟨e, Or.inl (hf.symm ▸ hd)⟩
    refine ⟨e', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact Quotient.sound ((M.region_face_sameCycle_iff hM R d e' hd).mpr hf.symm).symm

set_option backward.isDefEq.respectTransparency false in
/-- If [the map is a sphere triangulation](hyp:hM), [there is an injective
assignment of selected faces to restricted facial orbits such that a retained
dart belongs to a face's assigned orbit exactly when its original face is that
face, and every assigned orbit contains exactly three darts](goal). -/
-- @node: SphereMap.exists_region_interior_faces
lemma exists_region_interior_faces (hM : IsSphereTriangulation M) (R : Set M.Face) :
    ∃ q : {f : M.Face // f ∈ R} → (M.regionRotation R).FaceOrbit,
      Function.Injective q ∧
      (∀ (f : {f : M.Face // f ∈ R}) (d : M.RegionDart R),
        orbitOf (M.regionRotation R).facePerm d = q f ↔ M.faceOf d.val = f.val) ∧
      (∀ f, (Finset.univ.filter (fun d : (M.regionRotation R).Dart =>
        orbitOf (M.regionRotation R).facePerm d = q f)).card = 3) := by
  have hex (f : {f : M.Face // f ∈ R}) : ∃ d : M.RegionDart R, M.faceOf d.val = f.val := by
    have hc : (M.faceDarts f.val).card = 3 :=
      (M.faceLength_eq_card_faceDarts f.val).symm.trans (hM.props.2.2.2 f.val).1
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (by omega : 0 < (M.faceDarts f.val).card)
    have hf : M.faceOf d = f.val := (Finset.mem_filter.mp hd).2
    exact ⟨⟨d, Or.inl (hf.symm ▸ f.property)⟩, hf⟩
  choose rep hrep using hex
  let q := fun f => orbitOf (M.regionRotation R).facePerm (rep f)
  have hiff (f : {f : M.Face // f ∈ R}) (d : M.RegionDart R) :
      orbitOf (M.regionRotation R).facePerm d = q f ↔ M.faceOf d.val = f.val := by
    change orbitOf _ d = orbitOf _ (rep f) ↔ _
    rw [show M.faceOf d.val = f.val ↔ M.faceOf (rep f).val = M.faceOf d.val by
      rw [hrep]; exact eq_comm]
    constructor
    · intro h
      exact (M.region_face_sameCycle_iff hM.props.1 R (rep f) d
        ((hrep f).symm ▸ f.property)).mp (Quotient.exact h).symm
    · intro h
      exact Quotient.sound ((M.region_face_sameCycle_iff hM.props.1 R (rep f) d
        ((hrep f).symm ▸ f.property)).mpr h).symm
  refine ⟨q, ?_, hiff, ?_⟩
  · intro f g h
    apply Subtype.ext
    exact (hrep f).symm.trans ((hiff g (rep f)).mp h)
  · intro f
    change (Finset.univ.filter (fun d : (M.regionRotation R).Dart =>
      orbitOf (M.regionRotation R).facePerm d =
        orbitOf (M.regionRotation R).facePerm (rep f))).card = 3
    rw [M.region_face_orbit_length hM.props.1 R (rep f) ((hrep f).symm ▸ f.property),
      hrep f]
    exact (hM.props.2.2.2 f.val).1

-- @node: SphereMap.cycle_face_mem_leftRegion
/-- If [a dart belongs to a cycle](hyp:hd), [its face belongs to the cycle's
left region](goal). -/
lemma cycle_face_mem_leftRegion (C : M.Cycle) (d : M.Dart) (hd : d ∈ C.val) :
    M.faceOf d ∈ M.leftRegion C := by
  refine ⟨Sum.inl (orbitOf M.facePerm d), ⟨d, hd, Relation.ReflTransGen.refl⟩, ?_⟩
  exact ⟨rfl, Relation.ReflTransGen.refl⟩

-- @node: SphereMap.regionVertexSet_iff_face_incidence
/-- If [the map is a sphere triangulation](hyp:hM), [a vertex belongs to the
region's retained vertex set if and only if it is incident to a selected face](goal). -/
lemma regionVertexSet_iff_face_incidence (hM : IsSphereTriangulation M)
    (R : Set M.Face) (v : M.Vertex) :
    M.regionVertexSet R v ↔ ∃ f ∈ R, v ∈ M.faceVertices f := by
  have incident (d : M.Dart) : M.vert d ∈ M.faceVertices (M.faceOf d) := by
    rw [triangulation_faceVertices_eq_image M hM]
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases hd with hd | hd
    · exact ⟨M.faceOf d, hd, incident d⟩
    · have hf : M.faceOf (M.rot d) = M.faceOf (M.edgeInv d) := by
        have h := M.dual_rot_vertex (M.edgeInv d)
        change M.faceOf (M.rot (M.edgeInv (M.edgeInv d))) = M.faceOf (M.edgeInv d) at h
        rw [M.edgeInv_involutive d] at h
        exact h
      refine ⟨M.faceOf (M.rot d), hf.symm ▸ hd, ?_⟩
      simpa only [M.rot_vertex] using incident (M.rot d)
  · rintro ⟨f, hf, hv⟩
    rw [triangulation_faceVertices_eq_image M hM] at hv
    obtain ⟨d, hd, hv⟩ := Finset.mem_image.mp hv
    have hd' : M.faceOf d = f := (Finset.mem_filter.mp hd).2
    exact ⟨d, Or.inl (hd'.symm ▸ hf), hv⟩

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.cycle_left_vertex_card
/-- If [the map is a sphere triangulation](hyp:hM), [the number of vertices in
the restriction to a cycle's left region equals the number of vertices strictly
on that side plus the cycle length](goal). -/
lemma cycle_left_vertex_card (hM : IsSphereTriangulation M) (C : M.Cycle) :
    Fintype.card (M.cycleLeftRotation C).Vertex =
      (Finset.univ.filter (M.strictlyOnSide (M.leftRegion C) C)).card + C.val.length := by
  classical
  let interior := Finset.univ.filter (M.strictlyOnSide (M.leftRegion C) C)
  let boundary := (C.val.map M.vert).toFinset
  have hb (v : M.Vertex) (hv : v ∈ boundary) : M.regionVertexSet (M.leftRegion C) v := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    exact ⟨d, Or.inl (M.cycle_face_mem_leftRegion C d hd), rfl⟩
  have hs : Finset.univ.filter (fun v => M.regionVertexSet (M.leftRegion C) v) = interior ∪ boundary := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hv
      by_cases hbound : v ∈ boundary
      · exact Or.inr hbound
      · apply Or.inl
        have hi := (M.regionVertexSet_iff_face_incidence hM (M.leftRegion C) v).mp hv
        simpa [interior, strictlyOnSide, boundary] using
          (show v ∉ C.val.map M.vert ∧ ∃ f ∈ M.leftRegion C, v ∈ M.faceVertices f from
            ⟨by simpa [boundary] using hbound, hi⟩)
    · rintro (hv | hv)
      · have hi : ∃ f ∈ M.leftRegion C, v ∈ M.faceVertices f := by
          simpa [interior, strictlyOnSide] using
            (show M.strictlyOnSide (M.leftRegion C) C v from (Finset.mem_filter.mp hv).2).2
        exact (M.regionVertexSet_iff_face_incidence hM (M.leftRegion C) v).mpr hi
      · exact hb v hv
  have hdisjoint : Disjoint interior boundary := by
    apply Finset.disjoint_left.mpr
    intro v hi hb
    exact (Finset.mem_filter.mp hi).2.1 (List.mem_toFinset.mp hb)
  have hboundary : boundary.card = C.val.length := by
    rw [List.toFinset_card_of_nodup C.property.2, List.length_map]
  change Fintype.card {v : M.Vertex // M.regionVertexSet (M.leftRegion C) v} = _
  rw [Fintype.card_subtype, hs, Finset.card_union_of_disjoint hdisjoint, hboundary]

-- @node: SphereMap.dart_card_eq_twice_edge_card
/-- [The number of darts is twice the number of edges](goal). -/
lemma dart_card_eq_twice_edge_card : Fintype.card M.Dart = 2 * Fintype.card M.Edge := by
  have hf (e : M.Edge) : (Finset.univ.filter (fun d => M.edgeOf d = e)).card = 2 := by
    obtain ⟨d, rfl⟩ := Quotient.exists_rep e
    have hset : Finset.univ.filter (fun x => M.edgeOf x = M.edgeOf d) =
        {d, M.edgeInv d} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [eq_comm, M.edgeOf_eq_iff]
    change (Finset.univ.filter (fun x => M.edgeOf x = M.edgeOf d)).card = 2
    rw [hset, Finset.card_pair (M.edgeInv_fixedPointFree d).symm]
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset M.Dart) (Finset.univ : Finset M.Edge) M.edgeOf
  simp only [Finset.mem_univ, Finset.filter_true, hf, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at h
  omega

-- @node: SphereMap.sum_face_lengths_eq_twice_edges
/-- [The sum of all face lengths equals twice the number of edges](goal). -/
lemma sum_face_lengths_eq_twice_edges :
    (∑ f : M.Face, M.faceLength f) = 2 * Fintype.card M.Edge := by
  simp_rw [M.faceLength_eq_card_faceDarts]
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset M.Dart) (Finset.univ : Finset M.Face) M.faceOf
  simp only [Finset.mem_univ, Finset.filter_true] at h
  change (∑ f : M.Face, (Finset.univ.filter (fun d => M.faceOf d = f)).card) = _
  exact h.trans M.dart_card_eq_twice_edge_card

-- @node: SphereMap.connected_euler
/-- If [the sphere map is connected](hyp:hM), [its number of vertices plus its
number of faces equals its number of edges plus two](goal). -/
lemma connected_euler (hM : M.IsConnectedMap) :
    Fintype.card M.Vertex + Fintype.card M.Face = Fintype.card M.Edge + 2 := by
  let : Nonempty M.Vertex := hM.nonempty
  let : Subsingleton M.Component := hM.preconnected.subsingleton_connectedComponent
  let : Unique M.Component := uniqueOfSubsingleton
    (M.toSimpleGraph.connectedComponentMk (Classical.arbitrary M.Vertex))
  have h := M.global_euler
  have hc : Fintype.card M.Component = 1 := Fintype.card_unique
  rw [hc] at h
  omega

/-- If [the sphere map is connected](hyp:hM), [every face other than the
designated outer face has length three](hyp:hfaces), and [the vertex count equals
the given interior count plus the outer face length](hyp:hvertices), [the number
of non-outer faces plus two equals twice the interior count plus the outer face
length](goal). -/
-- @node: SphereMap.triangular_disk_euler
lemma triangular_disk_euler (hM : M.IsConnectedMap) (outer : M.Face) (I : ℕ)
    (hfaces : ∀ f, f ≠ outer → M.faceLength f = 3)
    (hvertices : Fintype.card M.Vertex = I + M.faceLength outer) :
    (Finset.univ.filter (fun f : M.Face => f ≠ outer)).card + 2 =
      2 * I + M.faceLength outer := by
  let fs := Finset.univ.filter (fun f : M.Face => f ≠ outer)
  have hcard : fs.card + 1 = Fintype.card M.Face := by
    have he : (Finset.univ : Finset M.Face).erase outer = fs := by
      ext f
      simp [fs, ne_comm]
    rw [← he]
    exact Finset.card_erase_add_one (Finset.mem_univ outer)
  have hsum : (∑ f : M.Face, M.faceLength f) = 3 * fs.card + M.faceLength outer := by
    have he : (Finset.univ : Finset M.Face).erase outer = fs := by
      ext f
      simp [fs, ne_comm]
    have h := Finset.sum_erase_add (Finset.univ : Finset M.Face)
      (fun f => M.faceLength f) (Finset.mem_univ outer)
    rw [he] at h
    rw [← h]
    have ht : (∑ f ∈ fs, M.faceLength f) = 3 * fs.card := by
      calc
        _ = ∑ _f ∈ fs, 3 := Finset.sum_congr rfl (fun f hf =>
          hfaces f (Finset.mem_filter.mp hf).2)
        _ = _ := by simp [Nat.mul_comm]
    rw [ht]
  have heuler := M.connected_euler hM
  have hsides := M.sum_face_lengths_eq_twice_edges
  change fs.card + 2 = _
  omega

end SphereMap
end OaiPairedStatesHamiltonian
