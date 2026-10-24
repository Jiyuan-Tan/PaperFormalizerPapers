module

public import Papers.OaiPairedStatesHamiltonian.Helpers.DartRestriction
public import Papers.OaiPairedStatesHamiltonian.Helpers.IsolatedVertexRemoval
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! Inherited induced embeddings and retained-edge maps. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
open Classical
attribute [local instance] propDecidable




namespace SphereMap
variable (M : SphereMap) (U : Set M.Vertex)
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[retained darts](goal) are the directed edges whose tail and head both belong
to that set. -/
abbrev KeptDart := {d : M.Dart // M.vert d ∈ U ∧ M.head d ∈ U}

-- @node: SphereMap.exists_inducedInv
/-- [There is a permutation of the retained darts that reverses each dart
exactly as edge reversal does in the original map](goal). -/
lemma exists_inducedInv : ∃ p : Equiv.Perm (M.KeptDart U),
    ∀ d, (p d).val = M.edgeInv d.val := by
  let inv : M.KeptDart U → M.KeptDart U := fun d =>
    ⟨M.edgeInv d.val, d.property.2, by
      simpa only [head, RotationSystem.head, M.edgeInv_involutive d.val] using d.property.1⟩
  have hinv : Function.Involutive inv := by
    intro d
    apply Subtype.ext
    exact M.edgeInv_involutive d.val
  exact ⟨⟨inv, inv, hinv, hinv⟩, fun _ => rfl⟩

/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[induced edge reversal](goal) is a permutation of the retained darts that
reverses their underlying directed edges. -/
noncomputable def inducedInv : Equiv.Perm (M.KeptDart U) := Classical.choose (M.exists_inducedInv U)
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[induced rotation](goal) sends each retained dart to the first retained dart
encountered by repeatedly rotating around its tail in the original map. -/
noncomputable def inducedRot : Equiv.Perm (M.KeptDart U) :=
  firstReturnPerm M.rot {d | M.vert d ∈ U ∧ M.head d ∈ U}
/-- For [a sphere map](hyp:M), [a chosen vertex set](hyp:U), and [a retained
dart](hyp:d), the [induced tail vertex](goal) is its original tail, regarded
as a member of the chosen set. -/
noncomputable def inducedVert (d : M.KeptDart U) : U := ⟨M.vert d.val, d.property.1⟩

-- @node: SphereMap.inducedInv_involutive
/-- [Reversing a retained dart twice returns the original retained dart](goal). -/
lemma inducedInv_involutive : Function.Involutive (M.inducedInv U) := by
  intro d
  apply Subtype.ext
  simp only [inducedInv, Classical.choose_spec (M.exists_inducedInv U)]
  exact M.edgeInv_involutive d.val
-- @node: SphereMap.inducedInv_fixedPointFree
/-- [Reversing a retained dart always gives a different dart](goal). -/
lemma inducedInv_fixedPointFree (d : M.KeptDart U) : M.inducedInv U d ≠ d := by
  intro h
  apply M.edgeInv_fixedPointFree d.val
  have hval := congrArg Subtype.val h
  simpa only [inducedInv, Classical.choose_spec (M.exists_inducedInv U)] using hval
-- @node: SphereMap.inducedRot_vertex
/-- [The induced rotation preserves the tail vertex of every retained dart](goal). -/
lemma inducedRot_vertex (d : M.KeptDart U) :
    M.inducedVert U (M.inducedRot U d) = M.inducedVert U d := by
  apply Subtype.ext
  obtain ⟨n, hn, heq, hfirst⟩ :=
    Classical.choose_spec (exists_firstReturnPerm M.rot
      {d | M.vert d ∈ U ∧ M.head d ∈ U}) d
  change M.vert ((M.inducedRot U d).val) = M.vert d.val
  change M.vert ((firstReturnPerm M.rot _ d).val) = M.vert d.val
  rw [show (firstReturnPerm M.rot _ d).val = (M.rot ^ n) d.val from heq]
  clear hn heq hfirst
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, M.rot_vertex]
    exact ih
-- @node: SphereMap.inducedRot_fibre
/-- [The induced rotation acts as a single cyclic ordering on the retained
darts with any specified tail vertex in the chosen set](goal). -/
lemma inducedRot_fibre (v : U) :
    (M.inducedRot U).IsCycleOn {d | M.inducedVert U d = v} := by
  refine ⟨⟨?_, (M.inducedRot U).injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (M.inducedRot_vertex U d).trans hd
  · intro d hd
    refine ⟨(M.inducedRot U).symm d, ?_, (M.inducedRot U).apply_symm_apply d⟩
    change M.inducedVert U ((M.inducedRot U).symm d) = v
    rw [← M.inducedRot_vertex U ((M.inducedRot U).symm d),
      (M.inducedRot U).apply_symm_apply]
    exact hd
  · intro d hd e he
    apply sameCycle_firstReturnPerm
    apply (M.rot_fibre v.val).2
    · exact congrArg Subtype.val hd
    · exact congrArg Subtype.val he
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[induced rotation system](goal) retains every chosen vertex, including those
isolated after deletion, and precisely the darts whose endpoints both remain,
with inherited edge reversal and cyclic order. -/
noncomputable def inducedRotation : RotationSystem where
  Vertex := U -- @realizes U(all vertices of U retained, including isolated vertices)
  Dart := M.KeptDart U
  vert := M.inducedVert U
  edgeInv := M.inducedInv U
  edgeInv_involutive := M.inducedInv_involutive U
  edgeInv_fixedPointFree := M.inducedInv_fixedPointFree U
  rot := M.inducedRot U
  rot_vertex := M.inducedRot_vertex U
  rot_fibre := M.inducedRot_fibre U

/-- For [a sphere map](hyp:M), [a chosen vertex set](hyp:U), and original
faces [on one side](hyp:f) and [on the other side](hyp:g), the
[face-merging relation](goal) holds when there is a dart [whose endpoints do
not both remain](step:1), [whose incident face is the first face](step:2), and
[whose reverse is incident to the second face](step:3). -/
noncomputable def inducedFaceRelation (f g : M.Face) : Prop :=
  ∃ d : M.Dart, ¬ (M.vert d ∈ U ∧ M.head d ∈ U) ∧
    M.faceOf d = f ∧ M.faceOf (M.edgeInv d) = g
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[induced faces](goal) are the classes of original faces obtained by identifying
the two sides of every deleted edge and closing these identifications under
reflexivity, symmetry, and transitivity. -/
abbrev InducedFace := Quotient (Relation.EqvGen.setoid (M.inducedFaceRelation U))
/-- For [a sphere map](hyp:M), [a chosen vertex set](hyp:U), and [an original
face](hyp:f), its [induced face class](goal) is its image after merging faces
across deleted edges. -/
noncomputable def inducedFaceClass (f : M.Face) : M.InducedFace U := Quotient.mk _ f
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), this
[finite enumeration of the induced faces](goal) comes from the finiteness of
the original face set. -/
noncomputable instance : Fintype (M.InducedFace U) := Fintype.ofFinite _
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), this
[decision procedure for equality of induced faces](goal) uses classical logic. -/
noncomputable instance : DecidableEq (M.InducedFace U) := Classical.decEq _

/-- For [a sphere map](hyp:M), [a chosen vertex set](hyp:U), and [an original
vertex](hyp:v), the [induced face containing its original neighborhood](goal)
is [the class of the face of a chosen outgoing dart, if one exists](step:1),
or [the class of the face assigned to its isolated-vertex boundary otherwise](step:2). -/
noncomputable def inducedVertexFace (v : M.Vertex) : M.InducedFace U :=
  if h : ∃ d, M.vert d = v then
    M.inducedFaceClass U (M.faceOf (Classical.choose h))
  else M.inducedFaceClass U (M.boundaryFace (Sum.inr ⟨v, fun d hd => h ⟨d, hd⟩⟩))

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.inducedFaceClass_rot_deleted
/-- If [a dart is deleted because its endpoints do not both belong to the
chosen vertex set](hyp:hd), then [its incident face and the face incident to
the next dart around its tail have the same induced face class](goal). -/
lemma inducedFaceClass_rot_deleted (d : M.Dart)
    (hd : ¬ (M.vert d ∈ U ∧ M.head d ∈ U)) :
    M.inducedFaceClass U (M.faceOf (M.rot d)) = M.inducedFaceClass U (M.faceOf d) := by
  have hf : M.faceOf (M.rot d) = M.faceOf (M.edgeInv d) := by
    have h := M.dual_rot_vertex (M.edgeInv d)
    change M.faceOf (M.rot (M.edgeInv (M.edgeInv d))) = M.faceOf (M.edgeInv d) at h
    rw [M.edgeInv_involutive] at h
    exact h
  rw [hf]
  exact (Quotient.sound (Relation.EqvGen.rel _ _ ⟨d, hd, rfl, rfl⟩)).symm

-- @node: SphereMap.inducedFaceClass_skip
/-- If [the number of rotations is positive](hyp:hn) and [every dart reached
at a positive intermediate rotation is deleted](hyp:hdel), then [the face
class after all those rotations equals the face class after the first
rotation](goal). -/
lemma inducedFaceClass_skip (d : M.Dart) (n : ℕ) (hn : 0 < n)
    (hdel : ∀ m, 0 < m → m < n → ¬ (M.vert ((M.rot ^ m) d) ∈ U ∧
      M.head ((M.rot ^ m) d) ∈ U)) :
    M.inducedFaceClass U (M.faceOf ((M.rot ^ n) d)) =
      M.inducedFaceClass U (M.faceOf (M.rot d)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      simp
    · have hp : 0 < n := Nat.pos_of_ne_zero hz
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (M.inducedFaceClass_rot_deleted U _ (hdel n hp (by omega))).trans
        (ih hp (fun m hm hmn => hdel m hm (by omega)))

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.induced_facePerm_class
/-- [Advancing a retained dart by one step along its induced facial boundary
preserves the induced class of its original incident face](goal). -/
lemma induced_facePerm_class (d : M.KeptDart U) :
    M.inducedFaceClass U (M.faceOf (((M.inducedRotation U).facePerm d).val)) =
      M.inducedFaceClass U (M.faceOf d.val) := by
  let a := M.inducedInv U d
  obtain ⟨n, hn, heq, hdel⟩ := Classical.choose_spec
    (exists_firstReturnPerm M.rot {d | M.vert d ∈ U ∧ M.head d ∈ U}) a
  change (firstReturnPerm M.rot _ a).val = (M.rot ^ n) a.val at heq
  change M.inducedFaceClass U (M.faceOf ((firstReturnPerm M.rot _ a).val)) = _
  rw [heq, M.inducedFaceClass_skip U a.val n hn hdel]
  have hi : a.val = M.edgeInv d.val := Classical.choose_spec (M.exists_inducedInv U) d
  rw [hi]
  exact congrArg (M.inducedFaceClass U) (M.dual_rot_vertex d.val)

set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.exists_inducedBoundaryFace
/-- [There is an assignment of induced local boundaries to induced faces
that sends each retained dart's facial orbit to its original face class and
each isolated retained vertex to the induced face of its original neighborhood](goal). -/
lemma exists_inducedBoundaryFace :
    ∃ place : (M.inducedRotation U).LocalBoundary → M.InducedFace U,
      (∀ d : M.KeptDart U,
        place (Sum.inl (orbitOf (M.inducedRotation U).facePerm d)) =
          M.inducedFaceClass U (M.faceOf d.val)) ∧
      (∀ v : (M.inducedRotation U).Puncture,
        place (Sum.inr v) = M.inducedVertexFace U v.val.val) := by
  have invariant (d e : M.KeptDart U)
      (h : (M.inducedRotation U).facePerm.SameCycle d e) :
      M.inducedFaceClass U (M.faceOf d.val) = M.inducedFaceClass U (M.faceOf e.val) := by
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans (M.induced_facePerm_class U _).symm
  exact ⟨Sum.elim (Quotient.lift (fun d : M.KeptDart U =>
    M.inducedFaceClass U (M.faceOf d.val)) invariant)
      (fun v => M.inducedVertexFace U v.val.val), fun _ => rfl, fun _ => rfl⟩
/-- For [a sphere map](hyp:M) and [a chosen vertex set](hyp:U), the
[induced boundary placement](goal) assigns each induced facial orbit to the
class of its original incident face and each isolated retained vertex to the
induced face of its original neighborhood. -/
noncomputable def inducedBoundaryFace :
    (M.inducedRotation U).LocalBoundary → M.InducedFace U :=
  Classical.choose (M.exists_inducedBoundaryFace U)
-- @node: SphereMap.inducedVertexFace_independent
/-- If [an original dart has its tail at a vertex isolated in the induced
rotation system](hyp:hd), then [the induced face of that vertex's original
neighborhood equals the induced face class of the dart's incident face](goal). -/
lemma inducedVertexFace_independent (v : (M.inducedRotation U).Puncture)
    (d : M.Dart) (hd : M.vert d = v.val.val) :
    M.inducedVertexFace U v.val.val = M.inducedFaceClass U (M.faceOf d) := by
  have hdel (e : M.Dart) (he : M.vert e = v.val.val) :
      ¬ (M.vert e ∈ U ∧ M.head e ∈ U) := by
    intro h
    exact v.property ⟨e, h⟩ (Subtype.ext he)
  have step (e : M.Dart) (he : M.vert e = v.val.val) :
      M.inducedFaceClass U (M.faceOf (M.rot e)) =
        M.inducedFaceClass U (M.faceOf e) := by
    have hface : M.faceOf (M.rot e) = M.faceOf (M.edgeInv e) := by
      have h := M.dual_rot_vertex (M.edgeInv e)
      change M.faceOf (M.rot (M.edgeInv (M.edgeInv e))) = M.faceOf (M.edgeInv e) at h
      rw [M.edgeInv_involutive] at h
      exact h
    rw [hface]
    exact (Quotient.sound (Relation.EqvGen.rel _ _
      ⟨e, hdel e he, rfl, rfl⟩)).symm
  have hex : ∃ e, M.vert e = v.val.val := ⟨d, hd⟩
  unfold inducedVertexFace
  rw [dif_pos hex]
  let a := Classical.choose hex
  have ha : M.vert a = v.val.val := Classical.choose_spec hex
  obtain ⟨n, hn⟩ := ((M.rot_fibre v.val.val).2 ha hd).exists_nat_pow_eq
  have hp (n : ℕ) : M.vert ((M.rot ^ n) a) = v.val.val ∧
      M.inducedFaceClass U (M.faceOf ((M.rot ^ n) a)) =
        M.inducedFaceClass U (M.faceOf a) := by
    induction n with
    | zero => exact ⟨ha, rfl⟩
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨(M.rot_vertex _).trans ih.1, (step _ ih.1).trans ih.2⟩
  exact ((congrArg (fun e => M.inducedFaceClass U (M.faceOf e)) hn).symm.trans (hp n).2).symm

-- @node: SphereMap.induced_genus
/-- [In every connected component of the induced rotation system, the number
of vertices plus the number of local boundaries equals the number of edges
plus two](goal). Isolated vertices contribute one local boundary. -/
lemma induced_genus : (M.inducedRotation U).componentEuler := by
  let kept : Set M.Dart := {d | M.vert d ∈ U ∧ M.head d ∈ U}
  have hkeep : ∀ d, M.edgeInv d ∈ kept ↔ d ∈ kept := by
    intro d
    change (M.vert (M.edgeInv d) ∈ U ∧ M.vert (M.edgeInv (M.edgeInv d)) ∈ U) ↔
      (M.vert d ∈ U ∧ M.vert (M.edgeInv d) ∈ U)
    rw [M.edgeInv_involutive]
    exact and_comm
  let Q := M.toRotationSystem.restrictDarts kept hkeep
  have hQ : Q.componentEuler :=
    M.toRotationSystem.restrictDarts_componentEuler kept M.genusZero hkeep
  have tails (d : Q.Dart) : Q.vert d ∈ U := d.property.1
  let N := Q.restrictVertices U tails
  have hN : N.componentEuler := Q.restrictVertices_componentEuler U tails hQ
  let e : N.Relabel (M.inducedRotation U) :=
    { vertex := Equiv.refl _
      dart := Equiv.refl _
      vert := fun _ => rfl
      inv := by
        intro d
        apply Subtype.ext
        exact (Classical.choose_spec (M.exists_inducedInv U) d).symm
      rot := fun _ => rfl }
  exact e.componentEuler hN
set_option backward.isDefEq.respectTransparency false in
-- @node: SphereMap.induced_placement_connected
/-- [The incidence graph joining induced connected components to induced
faces through their assigned local boundaries is connected](goal). -/
lemma induced_placement_connected :
    ((M.inducedRotation U).placementGraph (M.InducedFace U) (M.inducedBoundaryFace U)).Connected := by
  classical
  let N := M.inducedRotation U
  let place := M.inducedBoundaryFace U
  let G := N.placementGraph (M.InducedFace U) place
  let q (f : M.Face) := G.connectedComponentMk (Sum.inr (M.inducedFaceClass U f))
  let g (v : M.Vertex) := G.connectedComponentMk (Sum.inr (M.inducedVertexFace U v))
  have dart_place (d : M.KeptDart U) :
      place (Sum.inl (orbitOf N.facePerm d)) = M.inducedFaceClass U (M.faceOf d.val) :=
    (Classical.choose_spec (M.exists_inducedBoundaryFace U)).1 d
  have retained (d : M.KeptDart U) :
      G.connectedComponentMk (Sum.inl (N.toSimpleGraph.connectedComponentMk (N.vert d))) =
        q (M.faceOf d.val) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    exact ⟨Sum.inl (orbitOf N.facePerm d), rfl, dart_place d⟩
  have across (d : M.Dart) : q (M.faceOf d) = q (M.faceOf (M.edgeInv d)) := by
    by_cases hd : M.vert d ∈ U ∧ M.head d ∈ U
    · let e : M.KeptDart U := ⟨d, hd⟩
      have hi : (M.inducedInv U e).val = M.edgeInv d :=
        Classical.choose_spec (M.exists_inducedInv U) e
      have hc := N.dart_component_eq_head e
      have ha := retained e
      have hb := retained (N.edgeInv e)
      change N.toSimpleGraph.connectedComponentMk (N.vert e) =
        N.toSimpleGraph.connectedComponentMk (N.vert (N.edgeInv e)) at hc
      rw [← hc] at hb
      exact ha.symm.trans (hb.trans (congrArg (fun a => q (M.faceOf a)) hi))
    · exact congrArg (fun f => G.connectedComponentMk (Sum.inr f))
        (Quotient.sound (Relation.EqvGen.rel _ _ ⟨d, hd, rfl, rfl⟩))
  have rotate (d : M.Dart) : q (M.faceOf (M.rot d)) = q (M.faceOf d) := by
    have hf := M.dual_rot_vertex (M.edgeInv d)
    change M.faceOf (M.rot (M.edgeInv (M.edgeInv d))) = M.faceOf (M.edgeInv d) at hf
    rw [M.edgeInv_involutive] at hf
    exact (congrArg q hf).trans (across d).symm
  have at_vertex (d : M.Dart) : g (M.vert d) = q (M.faceOf d) := by
    have hex : ∃ e, M.vert e = M.vert d := ⟨d, rfl⟩
    change G.connectedComponentMk (Sum.inr (M.inducedVertexFace U (M.vert d))) = _
    unfold inducedVertexFace
    rw [dif_pos hex]
    obtain ⟨n, hn⟩ := ((M.rot_fibre (M.vert d)).2 (Classical.choose_spec hex) rfl).exists_nat_pow_eq
    have hp (n : ℕ) : q (M.faceOf ((M.rot ^ n) (Classical.choose hex))) =
        q (M.faceOf (Classical.choose hex)) := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact (rotate _).trans ih
    exact (hp n).symm.trans (congrArg (fun e => q (M.faceOf e)) hn)
  have edge (d : M.Dart) : g (M.vert d) = g (M.head d) :=
    (at_vertex d).trans ((across d).trans (at_vertex (M.edgeInv d)).symm)
  have vertex_eq {u v : M.Vertex}
      (h : M.toSimpleGraph.connectedComponentMk u = M.toSimpleGraph.connectedComponentMk v) :
      g u = g v := by
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact h
    clear h
    induction p with
    | nil => rfl
    | @cons u w v h p ih =>
      obtain ⟨hne, d, hd, hw⟩ := h
      have he : g u = g w := by simpa only [hd, hw] using edge d
      exact he.trans ih
  let representative (K : M.Component) : M.Vertex := Classical.choose K.exists_rep
  have representative_spec (K : M.Component) :
      M.toSimpleGraph.connectedComponentMk (representative K) = K :=
    Classical.choose_spec K.exists_rep
  have boundary (b : M.LocalBoundary) :
      g (representative (M.compOf b)) = q (M.boundaryFace b) := by
    cases b with
    | inl o =>
      obtain ⟨d, rfl⟩ := Quotient.exists_rep o
      exact (vertex_eq (representative_spec _)).trans (at_vertex d)
    | inr v =>
      apply (vertex_eq (representative_spec _)).trans
      dsimp only [g, inducedVertexFace]
      rw [dif_neg (show ¬ ∃ d, M.vert d = v.val from fun ⟨d, hd⟩ => v.property d hd)]
  let old (x : M.Component ⊕ M.Face) : G.ConnectedComponent :=
    Sum.elim (fun K => g (representative K)) q x
  have old_adj {x y} (h : M.placementGraph.Adj x y) : old x = old y := by
    cases x with
    | inl K =>
      cases y with
      | inl J => exact h.elim
      | inr f =>
        obtain ⟨b, rfl, rfl⟩ := h
        exact boundary b
    | inr f =>
      cases y with
      | inr j => exact h.elim
      | inl K =>
        obtain ⟨b, rfl, rfl⟩ := h
        exact (boundary b).symm
  have faces (f k : M.Face) : q f = q k := by
    obtain ⟨p⟩ := M.placement_connected.preconnected (Sum.inr f) (Sum.inr k)
    have walk {x y} (p : M.placementGraph.Walk x y) : old x = old y := by
      induction p with
      | nil => rfl
      | cons h p ih => exact (old_adj h).trans ih
    exact walk p
  have target (x : N.Component ⊕ M.InducedFace U) :
      ∃ f : M.Face, G.connectedComponentMk x = q f := by
    cases x with
    | inr f =>
      obtain ⟨f, rfl⟩ := Quotient.exists_rep f
      exact ⟨f, rfl⟩
    | inl K =>
      obtain ⟨v, hv⟩ := K.exists_rep
      by_cases hd : ∃ d : N.Dart, N.vert d = v
      · obtain ⟨d, hd⟩ := hd
        refine ⟨M.faceOf d.val, ?_⟩
        have ha := retained d
        rw [hd] at ha
        exact (congrArg (fun k => G.connectedComponentMk (Sum.inl k)) hv.symm).trans ha
      · let b : N.Puncture := ⟨v, fun d he => hd ⟨d, he⟩⟩
        have hp := (Classical.choose_spec (M.exists_inducedBoundaryFace U)).2 b
        have ha : G.Adj (Sum.inl K) (Sum.inr (M.inducedVertexFace U v.val)) :=
          ⟨Sum.inr b, hv, hp⟩
        obtain ⟨f, hf⟩ := Quotient.exists_rep (M.inducedVertexFace U v.val)
        exact ⟨f, (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha).trans (congrArg
          (fun a => G.connectedComponentMk (Sum.inr a)) hf.symm)⟩
  have nonempty_face : Nonempty M.Face := by
    obtain ⟨x⟩ := M.placement_connected.nonempty
    cases x with
    | inr f => exact ⟨f⟩
    | inl K =>
      let v := representative K
      by_cases hd : ∃ d, M.vert d = v
      · exact ⟨M.faceOf (Classical.choose hd)⟩
      · exact ⟨M.boundaryFace (Sum.inr ⟨v, fun d he => hd ⟨d, he⟩⟩)⟩
  let : Nonempty (N.Component ⊕ M.InducedFace U) :=
    ⟨Sum.inr (M.inducedFaceClass U (Classical.choice nonempty_face))⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨f, hf⟩ := target x
  obtain ⟨k, hk⟩ := target y
  exact SimpleGraph.ConnectedComponent.exact (hf.trans ((faces f k).trans hk.symm))


-- @node: SphereMap.inducedInv_pow_val
/-- [Applying induced edge reversal any natural number of times to a
retained dart gives the same underlying dart as applying original edge
reversal that many times](goal). -/
lemma inducedInv_pow_val (n : ℕ) (d : M.KeptDart U) :
    (((M.inducedInv U) ^ n) d).val = (M.edgeInv ^ n) d.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact (Classical.choose_spec (M.exists_inducedInv U) _).trans
      (congrArg M.edgeInv ih)

-- @node: SphereMap.inducedInv_sameCycle_iff
/-- [Two retained darts lie in the same orbit of induced edge reversal
exactly when their underlying original darts lie in the same orbit of
original edge reversal](goal). -/
lemma inducedInv_sameCycle_iff (d e : M.KeptDart U) :
    (M.inducedInv U).SameCycle d e ↔ M.edgeInv.SameCycle d.val e.val := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    simpa only [zpow_natCast] using
      (M.inducedInv_pow_val U n d).symm.trans (congrArg Subtype.val hn)
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    exact Subtype.ext ((M.inducedInv_pow_val U n d).trans hn)


end SphereMap
end OaiPairedStatesHamiltonian
