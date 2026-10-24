module

public import Papers.OaiPairedStatesHamiltonian.Helpers.DensityRegions
public import Papers.OaiPairedStatesHamiltonian.Helpers.EulerBound
public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleDiskEuler
public import Papers.OaiPairedStatesHamiltonian.Helpers.ReverseCycleSides

/-! Short facial walks in connected simple maps. These facts retain both
occurrences of a bridge; no two-connectivity assumption is used. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (M : SphereMap)

-- @node: SphereMap.facePerm_tail
/-- [The next directed edge along a face starts at the endpoint of the current directed edge](goal). -/
lemma facePerm_tail (d : M.Dart) : M.vert (M.facePerm d) = M.head d :=
  M.rot_vertex _

-- @node: SphereMap.facePerm_ne_self
/-- If [the map is simple](hyp:hs), then [advancing a directed edge once along its face
never returns the same directed edge](goal). -/
lemma facePerm_ne_self (hs : M.IsSimple) (d : M.Dart) : M.facePerm d ≠ d := by
  intro h
  exact hs.1 d ((congrArg M.vert h).symm.trans (M.facePerm_tail d))

-- @node: SphereMap.dart_eq_of_rot_fixed
/-- If [rotation around a vertex fixes a directed edge](hyp:hd) and [another directed
edge starts at that same vertex](hyp:he), then [the two directed edges coincide](goal). -/
lemma dart_eq_of_rot_fixed (d e : M.Dart) (hd : M.rot d = d)
    (he : M.vert e = M.vert d) : e = d := by
  obtain ⟨n, hn⟩ := ((M.rot_fibre (M.vert d)).2 rfl he).exists_nat_pow_eq
  have hp (n : ℕ) : (M.rot ^ n) d = d := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hd]
  exact hn.symm.trans (hp n)

-- @node: SphereMap.vertex_card_le_two_of_facePerm_sq
/-- If [the map is connected](hyp:hc) and [simple](hyp:hs), and [advancing a directed
edge twice along its face returns to that edge](hyp:hdd), then [the map has at most
two vertices](goal). -/
lemma vertex_card_le_two_of_facePerm_sq (hc : M.IsConnectedMap) (hs : M.IsSimple)
    (d : M.Dart) (hdd : M.facePerm (M.facePerm d) = d) :
    Fintype.card M.Vertex ≤ 2 := by
  let e := M.facePerm d
  have hev : M.vert e = M.head d := M.facePerm_tail d
  have heh : M.head e = M.vert d := (M.facePerm_tail e).symm.trans (congrArg M.vert hdd)
  have hedge : M.edgeOf d = M.edgeOf e := by
    apply hs.2
    rw [hev, heh, Sym2.eq_swap]
  have heinv : e = M.edgeInv d := by
    rcases (M.edgeOf_eq_iff d e).mp hedge with h | h
    · exact False.elim (M.facePerm_ne_self hs d h)
    · exact h
  have hrd : M.rot d = d := by
    have h := hdd
    change M.rot (M.edgeInv e) = d at h
    rw [heinv, M.edgeInv_involutive] at h
    exact h
  have hre : M.rot (M.edgeInv d) = M.edgeInv d := heinv
  have hstep {u v : M.Vertex} (h : M.toSimpleGraph.Adj u v)
      (hu : u = M.vert d ∨ u = M.head d) : v = M.vert d ∨ v = M.head d := by
    obtain ⟨_, a, ha, hb⟩ := h
    rcases hu with hu | hu
    · have heq : a = d := M.dart_eq_of_rot_fixed d a hrd (ha.trans hu)
      exact Or.inr (hb.symm.trans (congrArg M.head heq))
    · have heq : a = M.edgeInv d := M.dart_eq_of_rot_fixed _ a hre (ha.trans hu)
      left
      rw [← hb, heq]
      exact congrArg M.vert (M.edgeInv_involutive d)
  have hall (v : M.Vertex) : v = M.vert d ∨ v = M.head d := by
    obtain ⟨p⟩ := hc.preconnected (M.vert d) v
    have walk {u v : M.Vertex} (p : M.toSimpleGraph.Walk u v) :
        (u = M.vert d ∨ u = M.head d) → (v = M.vert d ∨ v = M.head d) := by
      induction p with
      | nil => exact id
      | cons h p ih => exact fun hu => ih (hstep h hu)
    exact walk p (Or.inl rfl)
  have hsub : (Finset.univ : Finset M.Vertex) ⊆ {M.vert d, M.head d} := by
    intro v _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hall v
  have hle := Finset.card_le_card hsub
  have hpair : ({M.vert d, M.head d} : Finset M.Vertex).card ≤ 2 :=
    by
      have h := Finset.card_insert_le (M.vert d) ({M.head d} : Finset M.Vertex)
      simpa using h
  simpa using hle.trans hpair

-- @node: SphereMap.faceLength_three_le
/-- In [a connected map](hyp:hc) that [is simple](hyp:hs) and [has at least three
vertices](hyp:hv), [every face has boundary length at least three](goal). -/
lemma faceLength_three_le (hc : M.IsConnectedMap) (hs : M.IsSimple)
    (hv : 3 ≤ Fintype.card M.Vertex) (f : M.Face) : 3 ≤ M.faceLength f := by
  have hne : Nonempty M.Dart := by
    by_contra h
    letI : IsEmpty M.Dart := not_nonempty_iff.mp h
    letI : Subsingleton M.Vertex := M.vertex_subsingleton_of_no_darts hc
    have hle := Fintype.card_le_of_injective (fun _ : M.Vertex => ())
      (show Function.Injective (fun _ : M.Vertex => ()) from fun _ _ _ => Subsingleton.elim _ _)
    norm_num at hle
    omega
  letI := hne
  obtain ⟨d, hd⟩ := M.faceOf_surjective hc f
  have hmem : d ∈ M.faceDarts f := by simp [faceDarts, hd]
  have hpos : 0 < (M.faceDarts f).card := Finset.card_pos.mpr ⟨d, hmem⟩
  have hcyc : M.facePerm.IsCycleOn (↑(M.faceDarts f) : Set M.Dart) := by
    simpa [faceDarts] using M.dual_rot_fibre hc f
  have hpow := hcyc.pow_card_apply hmem
  rw [← M.faceLength_eq_card_faceDarts f] at hpow hpos
  by_contra h
  have hcases : M.faceLength f = 1 ∨ M.faceLength f = 2 := by omega
  rcases hcases with hlen | hlen
  · rw [hlen, pow_one] at hpow
    exact M.facePerm_ne_self hs d hpow
  · rw [hlen, pow_two, Equiv.Perm.mul_apply] at hpow
    have hle := M.vertex_card_le_two_of_facePerm_sq hc hs d hpow
    omega

-- @node: SphereMap.simpleCycle_of_facePerm_cube
/-- In [a simple map](hyp:hs), if [three successive advances along a face return a
directed edge to itself](hyp:hthree), then [that edge and its next two facial successors,
in order, form a simple cycle](goal). -/
lemma simpleCycle_of_facePerm_cube (hs : M.IsSimple) (d : M.Dart)
    (hthree : M.facePerm (M.facePerm (M.facePerm d)) = d) :
    M.IsSimpleCycle [d, M.facePerm d, M.facePerm (M.facePerm d)] := by
  let a := d
  let b := M.facePerm a
  let c := M.facePerm b
  have hab : M.head a = M.vert b := (M.facePerm_tail a).symm
  have hbc : M.head b = M.vert c := (M.facePerm_tail b).symm
  have hca : M.head c = M.vert a := (M.facePerm_tail c).symm.trans (congrArg M.vert hthree)
  have habv : M.vert a ≠ M.vert b := fun h => hs.1 a (h.trans hab.symm)
  have hbcv : M.vert b ≠ M.vert c := fun h => hs.1 b (h.trans hbc.symm)
  have hcav : M.vert c ≠ M.vert a := fun h => hs.1 c (h.trans hca.symm)
  have edge_ne (x y : M.Dart) (hxy : M.vert x ≠ M.vert y)
      (hxhy : M.vert x ≠ M.head y) : M.edgeOf x ≠ M.edgeOf y := by
    intro h
    rcases (M.edgeOf_eq_iff x y).mp h with he | he
    · exact hxy (congrArg M.vert he.symm)
    · apply hxhy
      rw [he]
      exact (congrArg M.vert (M.edgeInv_involutive x)).symm
  have habe : M.edgeOf a ≠ M.edgeOf b := edge_ne a b habv (by rw [hbc]; exact hcav.symm)
  have hbce : M.edgeOf b ≠ M.edgeOf c := edge_ne b c hbcv (by rw [hca]; exact habv.symm)
  have hcae : M.edgeOf c ≠ M.edgeOf a := edge_ne c a hcav (by rw [hab]; exact hbcv.symm)
  change M.IsSimpleCycle [a, b, c]
  refine ⟨⟨by simp, ?_, ?_⟩, ?_⟩
  · simpa using And.intro (And.intro habe hcae.symm) hbce
  · intro i
    fin_cases i
    · simpa using hab
    · simpa using hbc
    · simpa using hca
  · simpa using And.intro (And.intro habv hcav.symm) hbcv

-- @node: SphereMap.exists_face_triangle_cycle
/-- In [a connected map](hyp:hc) that [is simple](hyp:hs), if [a face has boundary length
three](hyp:hthree), then [there is a simple cycle of length three whose directed edges
are exactly the directed edges of that face](goal). -/
lemma exists_face_triangle_cycle (hc : M.IsConnectedMap) (hs : M.IsSimple)
    (f : M.Face) (hthree : M.faceLength f = 3) :
    ∃ C : M.Cycle, C.val.length = 3 ∧
      ∀ d, d ∈ C.val ↔ d ∈ M.faceDarts f := by
  have hcard : (M.faceDarts f).card = 3 := by
    rw [← M.faceLength_eq_card_faceDarts, hthree]
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < (M.faceDarts f).card by omega)
  letI : Nonempty M.Dart := ⟨d⟩
  have hcyc : M.facePerm.IsCycleOn (↑(M.faceDarts f) : Set M.Dart) := by
    simpa [faceDarts] using M.dual_rot_fibre hc f
  have hp := hcyc.pow_card_apply hd
  rw [hcard] at hp
  have hcube : M.facePerm (M.facePerm (M.facePerm d)) = d := by
    simpa [pow_succ, Equiv.Perm.mul_apply] using hp
  let C : M.Cycle := ⟨[d, M.facePerm d, M.facePerm (M.facePerm d)],
    M.simpleCycle_of_facePerm_cube hs d hcube⟩
  refine ⟨C, rfl, ?_⟩
  intro e
  have hset : M.facePerm.IsCycleOn (↑(M.faceDarts f) : Set M.Dart) := hcyc
  constructor
  · intro he
    change e ∈ [d, M.facePerm d, M.facePerm (M.facePerm d)] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact hd
    · exact hset.1.1 hd
    · exact hset.1.1 (hset.1.1 hd)
  · intro he
    obtain ⟨n, hn, heq⟩ := hset.exists_pow_eq hd he
    rw [hcard] at hn
    have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    change e ∈ [d, M.facePerm d, M.facePerm (M.facePerm d)]
    rcases hn' with rfl | rfl | rfl <;>
      simp_all [pow_succ, Equiv.Perm.mul_apply]

-- @node: SphereMap.triangle_leftRegion_singleton_of_no_interior
/-- In [a sphere triangulation](hyp:hT), if [a cycle has length three](hyp:hlen) and
[no vertex lies strictly on its left side](hyp:hempty), then [its left region consists
of a single face](goal). -/
lemma triangle_leftRegion_singleton_of_no_interior (hT : IsSphereTriangulation M)
    (C : M.Cycle) (hlen : C.val.length = 3)
    (hempty : ¬ ∃ v, M.strictlyOnSide (M.leftRegion C) C v) :
    ∃ f : M.Face, M.leftRegion C = {f} := by
  obtain ⟨outer, hout⟩ := M.exists_face_outside_cycle_leftRegion hT.props.1 C
  have hz : (Finset.univ.filter (M.strictlyOnSide (M.leftRegion C) C)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hempty ⟨v, (Finset.mem_filter.mp hv).2⟩
  have hcount := cycle_disk_euler_count M hT (fun _ => true) C outer hout
  simp only [Bool.true_eq_false, and_false, Finset.filter_false, Finset.card_empty,
    and_true, add_zero, hz, hlen] at hcount
  norm_num at hcount
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcount
  refine ⟨f, ?_⟩
  ext g
  have hg := congrArg (fun s : Finset M.Face => g ∈ s) hf
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, Set.mem_singleton_iff] using Eq.to_iff hg

-- @node: SphereMap.triangle_has_singleton_side
/-- In [a sphere triangulation](hyp:hT) with [no separating triangles](hyp:hsep),
[any cycle of length three](hyp:hlen) has [a side whose region consists of a single
face, either on the left or on the right](goal). -/
lemma triangle_has_singleton_side (hT : IsSphereTriangulation M)
    (hsep : PairsNoSeparatingTriangle M) (C : M.Cycle) (hlen : C.val.length = 3) :
    (∃ f : M.Face, M.leftRegion C = {f}) ∨
      (∃ f : M.Face, M.rightRegion C = {f}) := by
  by_cases hl : ∃ v, M.strictlyOnSide (M.leftRegion C) C v
  · have hr : ¬ ∃ v, M.strictlyOnSide (M.rightRegion C) C v := by
      intro hr
      exact hsep C ⟨hlen, hl, hr⟩
    have hrev : ¬ ∃ v, M.strictlyOnSide (M.leftRegion (reverseCycle M C))
        (reverseCycle M C) v := by
      intro h
      obtain ⟨v, hv⟩ := h
      apply hr
      refine ⟨v, ?_⟩
      have hv' := (M.reverseCycle_strictlyOnSide C _ v).mp hv
      rwa [M.reverseCycle_leftRegion hT C, ← M.cycle_rightRegion_eq_compl C] at hv'
    have hlen' : (reverseCycle M C).val.length = 3 := by
      simpa [reverseCycle, reverseDarts] using hlen
    obtain ⟨f, hf⟩ := M.triangle_leftRegion_singleton_of_no_interior hT _ hlen' hrev
    right
    refine ⟨f, ?_⟩
    rwa [M.reverseCycle_leftRegion hT C, ← M.cycle_rightRegion_eq_compl C] at hf
  · exact Or.inl (M.triangle_leftRegion_singleton_of_no_interior hT C hlen hl)

-- @node: SphereMap.cycle_vertices_eq_face_of_singleton_left
/-- In [a sphere triangulation](hyp:hT), if [a cycle has length three](hyp:hlen) and
[its left region consists of a given face alone](hyp:hf), then [the cycle's vertices
are exactly the vertices of that face](goal). -/
lemma cycle_vertices_eq_face_of_singleton_left (hT : IsSphereTriangulation M)
    (C : M.Cycle) (hlen : C.val.length = 3) (f : M.Face)
    (hf : M.leftRegion C = {f}) :
    (C.val.map M.vert).toFinset = M.faceVertices f := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hdf : M.faceOf d = f := by
      have h := M.cycle_face_mem_leftRegion C d hd
      rwa [hf, Set.mem_singleton_iff] at h
    rw [triangulation_faceVertices_eq_image M hT]
    exact Finset.mem_image.mpr ⟨d, by simp [faceDarts, hdf], rfl⟩
  · rw [List.toFinset_card_of_nodup C.property.2, List.length_map, hlen]
    exact le_of_eq (hT.props.2.2.2 f).2

-- @node: SphereMap.triangle_bounds_original_face
/-- In [a sphere triangulation](hyp:hT) with [no separating triangles](hyp:hsep),
if [a cycle has length three](hyp:hlen), then [some original face has exactly the
same vertex set as that cycle](goal). -/
lemma triangle_bounds_original_face (hT : IsSphereTriangulation M)
    (hsep : PairsNoSeparatingTriangle M) (C : M.Cycle) (hlen : C.val.length = 3) :
    ∃ f : M.Face, M.faceVertices f = (C.val.map M.vert).toFinset := by
  rcases M.triangle_has_singleton_side hT hsep C hlen with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact ⟨f, (M.cycle_vertices_eq_face_of_singleton_left hT C hlen f hf).symm⟩
  · have hrev : M.leftRegion (reverseCycle M C) = {f} := by
      rwa [M.reverseCycle_leftRegion hT C, ← M.cycle_rightRegion_eq_compl C]
    have hlen' : (reverseCycle M C).val.length = 3 := by
      simpa [reverseCycle, reverseDarts] using hlen
    refine ⟨f, ?_⟩
    rw [← M.cycle_vertices_eq_face_of_singleton_left hT _ hlen' f hrev,
      M.reverseCycle_vertices C]

-- @node: SphereMap.exists_dart_at_vertex_of_connected
/-- In [a connected map](hyp:hc), given one directed edge, [every vertex is the starting
vertex of some directed edge](goal). -/
lemma exists_dart_at_vertex_of_connected (hc : M.IsConnectedMap)
    (d0 : M.Dart) (v : M.Vertex) : ∃ d, M.vert d = v := by
  by_cases hv : v = M.vert d0
  · exact ⟨d0, hv.symm⟩
  · obtain ⟨p⟩ := hc.preconnected v (M.vert d0)
    obtain ⟨_, d, hd, _⟩ := p.adj_snd (p.not_nil_of_ne hv)
    exact ⟨d, hd⟩

-- @node: SphereMap.vertex_card_le_of_closed_dart_set
/-- In [a connected map](hyp:hc), suppose a set of directed edges [is nonempty](hyp:hne),
[contains a rotated directed edge exactly when it contains the original edge](hyp:hrot),
and [contains a reversed directed edge exactly when it contains the original edge](hyp:hinv).
Then [the number of vertices in the map is at most the number of distinct starting
vertices represented in that set](goal). -/
lemma vertex_card_le_of_closed_dart_set (hc : M.IsConnectedMap)
    (s : Finset M.Dart) (hne : s.Nonempty)
    (hrot : ∀ d, M.rot d ∈ s ↔ d ∈ s)
    (hinv : ∀ d, M.edgeInv d ∈ s ↔ d ∈ s) :
    Fintype.card M.Vertex ≤ (s.image M.vert).card := by
  obtain ⟨d0, hd0⟩ := hne
  letI : Nonempty M.Dart := ⟨d0⟩
  have hall (d : M.Dart) : d ∈ s := by
    have h := M.toRotationSystem.dart_invariant_constant hc (fun d => d ∈ s)
      (fun d => propext (hrot d)) (fun d => propext (hinv d)) d d0
    exact h.mpr hd0
  have hsub : (Finset.univ : Finset M.Vertex) ⊆ s.image M.vert := by
    intro v _
    obtain ⟨d, hd⟩ := M.exists_dart_at_vertex_of_connected hc d0 v
    exact Finset.mem_image.mpr ⟨d, hall d, hd⟩
  simpa using Finset.card_le_card hsub

end SphereMap
end OaiPairedStatesHamiltonian
