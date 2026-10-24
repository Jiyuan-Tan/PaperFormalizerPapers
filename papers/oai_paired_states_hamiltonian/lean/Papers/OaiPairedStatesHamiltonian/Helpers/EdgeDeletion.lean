module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SwapOrbitCounts
public import Papers.OaiPairedStatesHamiltonian.Helpers.ComponentEulerExact
public import Mathlib.Logic.Equiv.Sum

/-! Deleting one undirected edge by first return, retaining all vertices and
counting the punctures that replace vanished rotation orbits. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace RotationSystem

set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (R : RotationSystem)

-- @node: RotationSystem.rot_pow_vertex
/-- [Any number of successive rotations leaves the vertex of a dart unchanged](goal). -/
lemma rot_pow_vertex (n : ℕ) (d : R.Dart) : R.vert ((R.rot ^ n) d) = R.vert d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, R.rot_vertex, ih]

-- @node: RotationSystem.rotOrbitActiveVertex
/-- For [a rotation system](hyp:R), the [map from rotation orbits to vertices incident
to at least one dart](goal) assigns each orbit the vertex of any of its darts. -/
noncomputable def rotOrbitActiveVertex : orbitType R.rot → {v : R.Vertex // ∃ d, R.vert d = v} :=
  Quotient.lift (fun d => ⟨R.vert d, d, rfl⟩) (by
    intro d e h
    apply Subtype.ext
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    exact (R.rot_pow_vertex n d).symm)

-- @node: RotationSystem.rotOrbitActiveVertex_bijective
/-- [Mapping each rotation orbit to its incident vertex is a bijection onto the
vertices incident to at least one dart](goal). -/
lemma rotOrbitActiveVertex_bijective : Function.Bijective R.rotOrbitActiveVertex := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h d =>
      induction b using Quotient.inductionOn with
      | h e =>
        intro h
        have he : R.vert d = R.vert e := congrArg Subtype.val h
        exact Quotient.sound ((R.rot_fibre (R.vert d)).2 rfl he.symm)
  · rintro ⟨v, d, hd⟩
    exact ⟨orbitOf R.rot d, Subtype.ext hd⟩

-- @node: RotationSystem.vertex_card_rot_orbits_add_punctures
/-- [The number of vertices equals the number of rotation orbits plus the number
of punctures, that is, vertices with no incident darts](goal). -/
lemma vertex_card_rot_orbits_add_punctures :
    Nat.card R.Vertex = Nat.card (orbitType R.rot) + Nat.card R.Puncture := by
  have ha := Nat.card_congr (Equiv.ofBijective R.rotOrbitActiveVertex R.rotOrbitActiveVertex_bijective)
  have hc := Nat.card_congr (Equiv.sumCompl (fun v : R.Vertex => ∃ d, R.vert d = v))
  have hp : Nat.card {v : R.Vertex // ¬ ∃ d, R.vert d = v} = Nat.card R.Puncture :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => by simp [Puncture]))
  rw [Nat.card_sum, hp, ← ha] at hc
  exact hc.symm

-- @node: RotationSystem.deleteEdgeRot_vertex
/-- [After deleting an edge, first return under rotation sends each surviving dart
to another dart at the same vertex](goal). -/
lemma deleteEdgeRot_vertex (a : R.Dart) (d : R.deleteEdgeDarts a) :
    R.vert (firstReturnPerm R.rot (R.deleteEdgeDarts a) d).val = R.vert d.val := by
  obtain ⟨n, hn, he, hfirst⟩ := Classical.choose_spec
    (exists_firstReturnPerm R.rot (R.deleteEdgeDarts a)) d
  change (firstReturnPerm R.rot (R.deleteEdgeDarts a) d).val = (R.rot ^ n) d.val at he
  rw [he]
  exact R.rot_pow_vertex n d.val

-- @node: RotationSystem.deleteEdgeRot_fibre
/-- [After deleting an edge, first return under rotation forms a single cycle on
the surviving darts at each vertex](goal). -/
lemma deleteEdgeRot_fibre (a : R.Dart) (v : R.Vertex) :
    (firstReturnPerm R.rot (R.deleteEdgeDarts a)).IsCycleOn
      {d : R.deleteEdgeDarts a | R.vert d.val = v} := by
  let q := firstReturnPerm R.rot (R.deleteEdgeDarts a)
  refine ⟨⟨?_, q.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (R.deleteEdgeRot_vertex a d).trans hd
  · intro d hd
    refine ⟨q.symm d, ?_, q.apply_symm_apply d⟩
    change R.vert (q.symm d).val = v
    rw [← R.deleteEdgeRot_vertex a (q.symm d), q.apply_symm_apply]
    exact hd
  · intro d hd e he
    exact sameCycle_firstReturnPerm R.rot (R.deleteEdgeDarts a) d e
      ((R.rot_fibre v).2 hd he)

-- @node: RotationSystem.deleteEdgeRotation
/-- For [a rotation system](hyp:R) and [a dart identifying the edge to delete](hyp:a),
the [rotation system after edge deletion](goal) retains all vertices, removes the
two darts of that edge, restricts edge reversal, and rotates by first return among
surviving darts. -/
noncomputable def deleteEdgeRotation (a : R.Dart) : RotationSystem where
  Vertex := R.Vertex
  Dart := R.deleteEdgeDarts a
  vert d := R.vert d.val
  edgeInv := R.deleteEdgeInv a
  edgeInv_involutive := by
    intro d
    apply Subtype.ext
    exact R.edgeInv_involutive d.val
  edgeInv_fixedPointFree := by
    intro d h
    exact R.edgeInv_fixedPointFree d.val (congrArg Subtype.val h)
  rot := firstReturnPerm R.rot (R.deleteEdgeDarts a)
  rot_vertex := R.deleteEdgeRot_vertex a
  rot_fibre := R.deleteEdgeRot_fibre a

-- @node: RotationSystem.deleteEdge_puncture_count
/-- [Deleting an edge increases the puncture count by one for each of its darts
that is fixed by rotation, and by one more if rotation exchanges its two darts](goal). -/
lemma deleteEdge_puncture_count (a : R.Dart) :
    Nat.card (R.deleteEdgeRotation a).Puncture = Nat.card R.Puncture +
      (if R.rot a = a then 1 else 0) +
      (if R.rot (R.edgeInv a) = R.edgeInv a then 1 else 0) +
      (if R.rot a = R.edgeInv a ∧ R.rot (R.edgeInv a) = a then 1 else 0) := by
  have hv := R.vertex_card_rot_orbits_add_punctures
  have hn := (R.deleteEdgeRotation a).vertex_card_rot_orbits_add_punctures
  have hr := card_firstReturn_delete_pair R.rot a (R.edgeInv a)
    (R.edgeInv_fixedPointFree a).symm
  change Nat.card R.Vertex =
    Nat.card (orbitType (firstReturnPerm R.rot (R.deleteEdgeDarts a))) +
      Nat.card (R.deleteEdgeRotation a).Puncture at hn
  change Nat.card (orbitType (firstReturnPerm R.rot (R.deleteEdgeDarts a))) + _ + _ + _ = _ at hr
  split_ifs at hr ⊢ <;> omega

-- @node: RotationSystem.deleteEdge_localBoundary_count
/-- [The number of local boundaries after edge deletion equals the number of
orbits obtained by swapping the deleted darts before applying the original face
permutation, plus the original puncture count](goal). -/
lemma deleteEdge_localBoundary_count (a : R.Dart) :
    Nat.card (R.deleteEdgeRotation a).LocalBoundary =
      Nat.card (orbitType (R.facePerm * Equiv.swap a (R.edgeInv a))) + Nat.card R.Puncture := by
  have hp := R.deleteEdge_puncture_count a
  have hf := R.deleteEdgeFacePerm_orbit_count a
  have hn : Nat.card (R.deleteEdgeRotation a).LocalBoundary =
      Nat.card (orbitType (R.deleteEdgeFacePerm a)) + Nat.card (R.deleteEdgeRotation a).Puncture :=
    Nat.card_sum
  omega

-- @node: RotationSystem.deleteEdge_localBoundary_transition
/-- [Deleting an edge increases the local boundary count by one when its two darts
lie in the same face orbit, and decreases it by one otherwise](goal). -/
lemma deleteEdge_localBoundary_transition (a : R.Dart) :
    Nat.card (R.deleteEdgeRotation a).LocalBoundary +
        (if R.facePerm.SameCycle a (R.edgeInv a) then 0 else 1) =
      Nat.card R.LocalBoundary +
        (if R.facePerm.SameCycle a (R.edgeInv a) then 1 else 0) := by
  rw [R.deleteEdge_localBoundary_count]
  have hs := card_orbits_mul_swap R.facePerm a (R.edgeInv a)
    (R.edgeInv_fixedPointFree a).symm
  have hb : Nat.card R.LocalBoundary =
      Nat.card (orbitType R.facePerm) + Nat.card R.Puncture := Nat.card_sum
  split_ifs at hs ⊢ <;> omega

-- @node: RotationSystem.deleteEdge_localBoundary_split
/-- If [the two darts of an edge lie in the same face orbit](hyp:h), then
[deleting that edge increases the local boundary count by one](goal). -/
lemma deleteEdge_localBoundary_split (a : R.Dart)
    (h : R.facePerm.SameCycle a (R.edgeInv a)) :
    Nat.card (R.deleteEdgeRotation a).LocalBoundary = Nat.card R.LocalBoundary + 1 := by
  have ht := R.deleteEdge_localBoundary_transition a
  simpa only [h, if_true, Nat.add_zero] using ht

-- @node: RotationSystem.deleteEdge_localBoundary_merge
/-- If [the two darts of an edge lie in different face orbits](hyp:h), then
[deleting that edge decreases the local boundary count by one](goal). -/
lemma deleteEdge_localBoundary_merge (a : R.Dart)
    (h : ¬ R.facePerm.SameCycle a (R.edgeInv a)) :
    Nat.card (R.deleteEdgeRotation a).LocalBoundary + 1 = Nat.card R.LocalBoundary := by
  have ht := R.deleteEdge_localBoundary_transition a
  simpa only [h, if_false, Nat.add_zero] using ht

-- @node: RotationSystem.deleteEdgeInv_eq_firstReturn
/-- [Edge reversal restricted to the darts surviving edge deletion equals first
return under the original edge reversal](goal). -/
lemma deleteEdgeInv_eq_firstReturn (a : R.Dart) :
    R.deleteEdgeInv a = firstReturnPerm R.edgeInv (R.deleteEdgeDarts a) := by
  apply firstReturnPerm_unique
  intro d
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · simp only [pow_one]
    rfl
  · intro m hm hm1
    omega

-- @node: RotationSystem.deleteEdge_edge_count
/-- [Deleting an edge reduces the number of edges by exactly one](goal). -/
lemma deleteEdge_edge_count (a : R.Dart) :
    Nat.card (R.deleteEdgeRotation a).Edge + 1 = Nat.card R.Edge := by
  have ht := card_firstReturn_delete_pair R.edgeInv a (R.edgeInv a)
    (R.edgeInv_fixedPointFree a).symm
  change Nat.card (orbitType (R.deleteEdgeInv a)) + 1 = Nat.card R.Edge
  rw [R.deleteEdgeInv_eq_firstReturn]
  have ha := R.edgeInv_fixedPointFree a
  have hb := R.edgeInv_fixedPointFree (R.edgeInv a)
  simpa only [deleteEdgeDarts, R.edgeInv_involutive a, ha, ha.symm, hb, if_false, true_and,
    and_self, if_true, Nat.add_zero] using ht

-- @node: RotationSystem.deleteEdge_toSimpleGraph_le
/-- [Every adjacency in the simple graph after edge deletion was already an
adjacency in the original simple graph](goal). -/
lemma deleteEdge_toSimpleGraph_le (a : R.Dart) :
    (R.deleteEdgeRotation a).toSimpleGraph ≤ R.toSimpleGraph := by
  intro v w h
  obtain ⟨hne, d, hd, he⟩ := h
  exact ⟨hne, d.val, hd, he⟩

-- @node: RotationSystem.deleteEdge_adjacency_or_endpoints
/-- If [two vertices are adjacent before edge deletion](hyp:h), then
[they remain adjacent afterwards or are the endpoints of the deleted edge in
one of the two possible orders](goal). -/
lemma deleteEdge_adjacency_or_endpoints (a : R.Dart) (v w : R.Vertex)
    (h : R.toSimpleGraph.Adj v w) :
    (R.deleteEdgeRotation a).toSimpleGraph.Adj v w ∨
      (v = R.vert a ∧ w = R.head a) ∨ (v = R.head a ∧ w = R.vert a) := by
  obtain ⟨hne, d, hd, he⟩ := h
  by_cases ha : d = a
  · subst d
    exact Or.inr (Or.inl ⟨hd.symm, he.symm⟩)
  by_cases hb : d = R.edgeInv a
  · subst d
    right; right
    refine ⟨hd.symm, ?_⟩
    simpa only [head, R.edgeInv_involutive a] using he.symm
  · exact Or.inl ⟨hne, ⟨d, ha, hb⟩, hd, he⟩

-- @node: RotationSystem.deleteEdge_toSimpleGraph_sup_edge
/-- [The original simple graph is the union of the simple graph after edge
deletion and the single edge joining the deleted edge's endpoints](goal). -/
lemma deleteEdge_toSimpleGraph_sup_edge (a : R.Dart) :
    R.toSimpleGraph = (R.deleteEdgeRotation a).toSimpleGraph ⊔
      SimpleGraph.edge (R.vert a) (R.head a) := by
  ext v w
  constructor
  · intro h
    rcases R.deleteEdge_adjacency_or_endpoints a v w h with hr | he
    · exact Or.inl hr
    · exact Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨he, h.1⟩)
  · rintro (hr | he)
    · exact R.deleteEdge_toSimpleGraph_le a hr
    · obtain ⟨he, hne⟩ := (SimpleGraph.edge_adj _ _ _ _).mp he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hne, a, rfl, rfl⟩
      · exact R.adjacency_symm _ _ ⟨hne.symm, a, rfl, rfl⟩

-- @node: RotationSystem.deleteEdge_component_count
/-- [Deleting an edge preserves the component count if its endpoints remain
connected by a path, and increases the count by one otherwise](goal). -/
lemma deleteEdge_component_count (a : R.Dart) :
    Nat.card (R.deleteEdgeRotation a).Component = Nat.card R.Component +
      (if (R.deleteEdgeRotation a).toSimpleGraph.Reachable (R.vert a) (R.head a)
        then 0 else 1) := by
  have ht := card_components_sup_edge (R.deleteEdgeRotation a).toSimpleGraph
    (R.vert a) (R.head a)
  rw [← R.deleteEdge_toSimpleGraph_sup_edge a] at ht
  exact ht.symm

-- @node: RotationSystem.deleteEdge_component_face_step
/-- If [a dart survives deletion of the chosen edge](hyp:hd), then
[one step of the original face permutation leaves its incident vertex in the
same component of the graph after deletion](goal). -/
lemma deleteEdge_component_face_step (a d : R.Dart) (hd : d ∈ R.deleteEdgeDarts a) :
    (R.deleteEdgeRotation a).toSimpleGraph.connectedComponentMk (R.vert (R.facePerm d)) =
      (R.deleteEdgeRotation a).toSimpleGraph.connectedComponentMk (R.vert d) := by
  change (R.deleteEdgeRotation a).toSimpleGraph.connectedComponentMk
      (R.vert (R.rot (R.edgeInv d))) = _
  rw [R.rot_vertex]
  exact ((R.deleteEdgeRotation a).dart_component_eq_head ⟨d, hd⟩).symm

-- @node: RotationSystem.deleteEdge_bridge_sameFace
/-- If [deleting an edge leaves its endpoints disconnected](hyp:hbridge), then
[the edge's two darts lie in the same original face orbit](goal). -/
lemma deleteEdge_bridge_sameFace (a : R.Dart)
    (hbridge : ¬ (R.deleteEdgeRotation a).toSimpleGraph.Reachable (R.vert a) (R.head a)) :
    R.facePerm.SameCycle a (R.edgeInv a) := by
  by_contra hnot
  let U : Set R.Dart := {x | x = a ∨ x = R.edgeInv a}
  let aa : U := ⟨a, Or.inl rfl⟩
  let bb : U := ⟨R.edgeInv a, Or.inr rfl⟩
  let q := firstReturnPerm R.facePerm U
  have hreturn : (q aa).val = a := by
    rcases (q aa).property with ha | hb
    · exact ha
    · exfalso
      apply hnot
      apply (sameCycle_firstReturnPerm_iff R.facePerm U aa bb).mp
      exact (pairPerm_sameCycle_iff a (R.edgeInv a)
        (R.edgeInv_fixedPointFree a).symm q).mpr (Subtype.ext hb)
  obtain ⟨n, hn, he, hmin⟩ := Classical.choose_spec
    (exists_firstReturnPerm R.facePerm U) aa
  change (q aa).val = (R.facePerm ^ n) a at he
  have walk (m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
      (R.deleteEdgeRotation a).toSimpleGraph.connectedComponentMk
          (R.vert ((R.facePerm ^ m) a)) =
        (R.deleteEdgeRotation a).toSimpleGraph.connectedComponentMk (R.head a) := by
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hz : m = 0
      · subst m
        simp only [Nat.zero_add, pow_one, facePerm, Equiv.Perm.mul_apply, R.rot_vertex]
        rfl
      · have hp : 0 < m := Nat.pos_of_ne_zero hz
        rw [pow_succ', Equiv.Perm.mul_apply]
        have hdel : (R.facePerm ^ m) a ∈ R.deleteEdgeDarts a :=
          ⟨fun h => hmin m hp (by omega) (Or.inl h),
            fun h => hmin m hp (by omega) (Or.inr h)⟩
        exact (R.deleteEdge_component_face_step a _ hdel).trans (ih hp (by omega))
  apply hbridge
  apply SimpleGraph.ConnectedComponent.exact
  have h := walk n hn le_rfl
  rwa [← he, hreturn] at h

-- @node: RotationSystem.deleteEdge_sameFace_bridge
/-- If [each component satisfies the Euler equality](hyp:hR) and
[an edge's two darts lie in the same face orbit](hyp:hface), then
[deleting that edge leaves its endpoints disconnected](goal). -/
lemma deleteEdge_sameFace_bridge (a : R.Dart) (hR : R.componentEuler)
    (hface : R.facePerm.SameCycle a (R.edgeInv a)) :
    ¬ (R.deleteEdgeRotation a).toSimpleGraph.Reachable (R.vert a) (R.head a) := by
  intro hpath
  have hb := R.deleteEdge_localBoundary_split a hface
  have hc := R.deleteEdge_component_count a
  have he := R.deleteEdge_edge_count a
  have ho := R.componentEuler_global_card hR
  have hn := (R.deleteEdgeRotation a).euler_bound_all_components
  simp only [hpath, if_true, Nat.add_zero] at hc
  simp only [← Nat.card_eq_fintype_card] at hn
  change Nat.card R.Vertex + Nat.card (R.deleteEdgeRotation a).LocalBoundary ≤
    Nat.card (R.deleteEdgeRotation a).Edge + 2 * Nat.card (R.deleteEdgeRotation a).Component at hn
  omega

-- @node: RotationSystem.deleteEdge_sameFace_iff_bridge
/-- If [each component satisfies the Euler equality](hyp:hR), then
[an edge's two darts lie in the same face orbit if and only if deleting that edge
leaves its endpoints disconnected](goal). -/
lemma deleteEdge_sameFace_iff_bridge (a : R.Dart) (hR : R.componentEuler) :
    R.facePerm.SameCycle a (R.edgeInv a) ↔
      ¬ (R.deleteEdgeRotation a).toSimpleGraph.Reachable (R.vert a) (R.head a) :=
  ⟨R.deleteEdge_sameFace_bridge a hR, R.deleteEdge_bridge_sameFace a⟩

-- @node: RotationSystem.deleteEdge_global_euler
/-- If [each original component satisfies the Euler equality](hyp:hR), then
[after deleting an edge, the vertex count plus the local boundary count equals
the edge count plus twice the component count](goal). -/
lemma deleteEdge_global_euler (a : R.Dart) (hR : R.componentEuler) :
    Nat.card (R.deleteEdgeRotation a).Vertex + Nat.card (R.deleteEdgeRotation a).LocalBoundary =
      Nat.card (R.deleteEdgeRotation a).Edge + 2 * Nat.card (R.deleteEdgeRotation a).Component := by
  have ho := R.componentEuler_global_card hR
  have he := R.deleteEdge_edge_count a
  have hc := R.deleteEdge_component_count a
  change Nat.card R.Vertex + Nat.card (R.deleteEdgeRotation a).LocalBoundary = _
  by_cases hface : R.facePerm.SameCycle a (R.edgeInv a)
  · have hb := R.deleteEdge_localBoundary_split a hface
    have hbridge := R.deleteEdge_sameFace_bridge a hR hface
    simp only [hbridge, if_false] at hc
    omega
  · have hb := R.deleteEdge_localBoundary_merge a hface
    have hpath : (R.deleteEdgeRotation a).toSimpleGraph.Reachable (R.vert a) (R.head a) := by
      by_contra h
      exact hface (R.deleteEdge_bridge_sameFace a h)
    simp only [hpath, if_true, Nat.add_zero] at hc
    omega

-- @node: RotationSystem.deleteEdge_componentEuler
/-- If [each original component satisfies the Euler equality](hyp:hR), then
[each component after deleting an edge also satisfies the Euler equality](goal). -/
lemma deleteEdge_componentEuler (a : R.Dart) (hR : R.componentEuler) :
    (R.deleteEdgeRotation a).componentEuler := by
  apply (R.deleteEdgeRotation a).componentEuler_of_global_card
  exact R.deleteEdge_global_euler a hR

end RotationSystem
end OaiPairedStatesHamiltonian
