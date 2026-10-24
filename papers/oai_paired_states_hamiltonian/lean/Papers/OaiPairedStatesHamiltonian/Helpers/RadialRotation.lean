module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleDisk
public import Papers.OaiPairedStatesHamiltonian.Helpers.InducedCore

/-! The radial rotation joins every vertex to its incident face centers.
Its quadrilateral boundary orbits correspond to the original edges. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.longLine false
set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
variable (T : SphereMap)

-- @node: radialVert
/-- For [a sphere map](hyp:T) and [an original dart with a Boolean side
label](hyp:d), its [radial vertex](goal) is the dart's initial vertex when the
label is true and its incident face center when the label is false. -/
noncomputable def radialVert (d : T.Dart × Bool) : T.Vertex ⊕ T.Face :=
  if d.2 then Sum.inl (T.vert d.1) else Sum.inr (T.faceOf d.1)

-- @node: radialInv
/-- For [a sphere map](hyp:T), [radial edge reversal](goal) keeps the original
dart and switches its Boolean side label, exchanging the vertex and face ends
of the corresponding incidence edge. -/
noncomputable def radialInv : Equiv.Perm (T.Dart × Bool) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨d, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨d, b⟩; cases b <;> rfl

-- @node: radialRot
/-- For [a sphere map](hyp:T), the [radial rotation](goal) preserves the Boolean
side label and advances the original vertex rotation on the true side, while
moving backward around the original face on the false side. -/
noncomputable def radialRot : Equiv.Perm (T.Dart × Bool) where
  toFun d := if d.2 then (T.rot d.1, true) else (T.facePerm.symm d.1, false)
  invFun d := if d.2 then (T.rot.symm d.1, true) else (T.facePerm d.1, false)
  left_inv := by rintro ⟨d, b⟩; cases b <;> simp
  right_inv := by rintro ⟨d, b⟩; cases b <;> simp

-- @node: radialRot_pow
/-- [Applying the radial rotation n times preserves the side label and applies
the original vertex rotation n times on the true side or the inverse face
permutation n times on the false side](goal). -/
lemma radialRot_pow (d : T.Dart) (b : Bool) (n : ℕ) :
    (radialRot T ^ n) (d, b) =
      if b then ((T.rot ^ n) d, true) else ((T.facePerm⁻¹ ^ n) d, false) := by
  induction n with
  | zero => cases b <;> rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    cases b <;> simp [radialRot, pow_succ', Equiv.Perm.mul_apply]

-- @node: radialRot_vertex
/-- [Radial rotation leaves the radial vertex of every labeled dart
unchanged](goal). -/
lemma radialRot_vertex (d : T.Dart × Bool) :
    radialVert T (radialRot T d) = radialVert T d := by
  rcases d with ⟨d, b⟩
  cases b
  · simp only [radialRot, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte, radialVert]
    rw [← T.dual_rot_vertex (T.facePerm.symm d), T.facePerm.apply_symm_apply]
  · simpa [radialRot, radialVert] using congrArg (Sum.inl : T.Vertex → T.Vertex ⊕ T.Face) (T.rot_vertex d)

-- @node: radialRot_fibre
/-- If [the original map is a sphere triangulation](hyp:hT), then [radial
rotation acts as a single cycle on all labeled darts attached to any given
original vertex or face center](goal). -/
lemma radialRot_fibre (hT : IsSphereTriangulation T) (v : T.Vertex ⊕ T.Face) :
    (radialRot T).IsCycleOn {d | radialVert T d = v} := by
  refine ⟨⟨?_, (radialRot T).injective.injOn, ?_⟩, ?_⟩
  · intro d hd; exact (radialRot_vertex T d).trans hd
  · intro d hd
    refine ⟨(radialRot T).symm d, ?_, (radialRot T).apply_symm_apply d⟩
    change radialVert T ((radialRot T).symm d) = v
    rw [← radialRot_vertex T ((radialRot T).symm d), (radialRot T).apply_symm_apply]
    exact hd
  · rintro ⟨d, b⟩ hd ⟨e, c⟩ he
    cases v with
    | inl v =>
      have hb : b = true := by cases b <;> simp_all [radialVert]
      have hc : c = true := by cases c <;> simp_all [radialVert]
      subst b; subst c
      have hdv : T.vert d = v := by simpa [radialVert] using hd
      have hev : T.vert e = v := by simpa [radialVert] using he
      obtain ⟨n, hn⟩ := ((T.rot_fibre v).2 hdv hev).exists_nat_pow_eq
      exact ⟨(n : ℤ), by simp only [zpow_natCast, radialRot_pow, ↓reduceIte, hn]⟩
    | inr f =>
      have hb : b = false := by cases b <;> simp_all [radialVert]
      have hc : c = false := by cases c <;> simp_all [radialVert]
      subst b; subst c
      have hdv : T.faceOf d = f := by simpa [radialVert] using hd
      have hev : T.faceOf e = f := by simpa [radialVert] using he
      obtain ⟨n, hn⟩ := (((T.dual_rot_fibre hT.props.1 f).2 hdv hev).inv).exists_nat_pow_eq
      exact ⟨(n : ℤ), by simp only [zpow_natCast, radialRot_pow, Bool.false_eq_true,
        ↓reduceIte, hn]⟩

-- @node: radialRotation
/-- For [a sphere map](hyp:T) with [a sphere triangulation
structure](hyp:hT), the [radial rotation system](goal) has the original vertices
and face centers as vertices, original darts with Boolean labels as darts,
edge reversal that switches the labels, and rotation given by the vertex
rotation on the true side and the inverse face permutation on the false side. -/
noncomputable def radialRotation (hT : IsSphereTriangulation T) : RotationSystem where
  Vertex := T.Vertex ⊕ T.Face
  Dart := T.Dart × Bool
  vert := radialVert T
  edgeInv := radialInv T
  edgeInv_involutive := by rintro ⟨d, b⟩; cases b <;> rfl
  edgeInv_fixedPointFree := by
    rintro ⟨d, b⟩ h
    have hb := congrArg Prod.snd h
    cases b <;> simp [radialInv] at hb
  rot := radialRot T
  rot_vertex := radialRot_vertex T
  rot_fibre := radialRot_fibre T hT

-- @node: radialRotation_face_false
/-- If [the original map is a sphere triangulation](hyp:hT), then [one radial
face step from a false-labeled dart advances its original vertex rotation and
changes its label to true](goal). -/
lemma radialRotation_face_false (hT : IsSphereTriangulation T) (d : T.Dart) :
    (radialRotation T hT).facePerm (d, false) = (T.rot d, true) := rfl

-- @node: radialRotation_face_true
/-- If [the original map is a sphere triangulation](hyp:hT), then [one radial
face step from a true-labeled dart moves backward around its original face and
changes its label to false](goal). -/
lemma radialRotation_face_true (hT : IsSphereTriangulation T) (d : T.Dart) :
    (radialRotation T hT).facePerm (d, true) = (T.facePerm.symm d, false) := rfl

-- @node: radialRotation_face_square
/-- If [the original map is a sphere triangulation](hyp:hT), then [two radial
face steps from a false-labeled dart reverse the original edge and leave the
label false](goal). -/
lemma radialRotation_face_square (hT : IsSphereTriangulation T) (d : T.Dart) :
    ((radialRotation T hT).facePerm ^ 2) (d, false) = (T.edgeInv d, false) := by
  rw [pow_two, Equiv.Perm.mul_apply, radialRotation_face_false, radialRotation_face_true]
  apply congrArg (fun e : T.Dart => (e, false))
  apply T.facePerm.injective
  simp only [T.facePerm.apply_symm_apply]
  change T.rot d = T.rot (T.edgeInv (T.edgeInv d))
  rw [T.edgeInv_involutive]

-- @node: radialBoundaryIndex
/-- For [a sphere map](hyp:T) and [a Boolean-labeled original dart](hyp:d), the
[edge indexing its radial boundary](goal) is the original edge of that dart
when the label is false, and the original edge reached by one inverse vertex
rotation when the label is true. -/
noncomputable def radialBoundaryIndex (d : T.Dart × Bool) : T.Edge :=
  if d.2 then T.edgeOf (T.rot.symm d.1) else T.edgeOf d.1

-- @node: radialBoundaryIndex_face
/-- If [the original map is a sphere triangulation](hyp:hT), then [a radial
face step preserves the original edge indexing the boundary](goal). -/
lemma radialBoundaryIndex_face (hT : IsSphereTriangulation T) (d : T.Dart × Bool) :
    radialBoundaryIndex T ((radialRotation T hT).facePerm d) = radialBoundaryIndex T d := by
  rcases d with ⟨d, b⟩
  cases b
  · simp [radialRotation_face_false, radialBoundaryIndex]
  · change T.edgeOf (T.facePerm.symm d) = T.edgeOf (T.rot.symm d)
    have he : T.facePerm.symm d = T.edgeInv (T.rot.symm d) := by
      apply T.facePerm.injective
      simp only [T.facePerm.apply_symm_apply]
      change d = T.rot (T.edgeInv (T.edgeInv (T.rot.symm d)))
      rw [T.edgeInv_involutive, T.rot.apply_symm_apply]
    rw [he]
    exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr
      (Equiv.Perm.SameCycle.refl T.edgeInv _))

-- @node: radialBoundaryIndex_sameCycle
/-- If [the original map is a sphere triangulation](hyp:hT) and [two labeled
darts lie on the same radial face cycle](hyp:h), then [their radial boundary
indices are the same original edge](goal). -/
lemma radialBoundaryIndex_sameCycle (hT : IsSphereTriangulation T) (d e : T.Dart × Bool)
    (h : (radialRotation T hT).facePerm.SameCycle d e) :
    radialBoundaryIndex T d = radialBoundaryIndex T e := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (radialBoundaryIndex_face T hT _).symm

-- @node: radialBoundaryEquiv
/-- For [a sphere map](hyp:T) with [a sphere triangulation
structure](hyp:hT), the [bijection from radial face cycles to original
edges](goal) is obtained by [taking the radial face permutation](step:1) and
[assigning each of its cycles the original edge given by the radial boundary
index of any representative](step:2). -/
noncomputable def radialBoundaryEquiv (hT : IsSphereTriangulation T) :
    (radialRotation T hT).FaceOrbit ≃ T.Edge := by
  let p := (radialRotation T hT).facePerm
  let f : orbitType p → T.Edge := Quotient.lift (radialBoundaryIndex T)
    (radialBoundaryIndex_sameCycle T hT)
  have norm (d : T.Dart × Bool) : p.SameCycle d
      ((if d.2 then T.rot.symm d.1 else d.1), false) := by
    rcases d with ⟨d, b⟩
    cases b
    · exact Equiv.Perm.SameCycle.refl _ _
    · have h : p (T.rot.symm d, false) = (d, true) := by
        simp [p, radialRotation_face_false]
      change p.SameCycle (d, true) (T.rot.symm d, false)
      rw [← h]
      exact (Equiv.Perm.sameCycle_apply_right.mpr
        (Equiv.Perm.SameCycle.refl p (T.rot.symm d, false))).symm
  apply Equiv.ofBijective f
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h d =>
      induction b using Quotient.inductionOn with
      | h e =>
        intro h
        let d' := if d.2 then T.rot.symm d.1 else d.1
        let e' := if e.2 then T.rot.symm e.1 else e.1
        have hd : p.SameCycle d (d', false) := by
          simpa only [d'] using norm d
        have he : p.SameCycle e (e', false) := by
          simpa only [e'] using norm e
        have hi : T.edgeOf d' = T.edgeOf e' := by
          change radialBoundaryIndex T d = radialBoundaryIndex T e at h
          dsimp only [radialBoundaryIndex] at h
          simpa only [d', e', apply_ite] using h
        apply Quotient.sound
        apply hd.trans
        apply Equiv.Perm.SameCycle.trans _ he.symm
        rcases (T.edgeOf_eq_iff d' e').mp hi with h | h
        · rw [h]
        · rw [h]
          exact (show p.SameCycle (d', false) (T.edgeInv d', false) from
            ⟨(2 : ℕ), by simpa only [zpow_natCast] using radialRotation_face_square T hT d'⟩)
  · intro e
    induction e using Quotient.inductionOn with
    | h d => exact ⟨orbitOf p (d, false), rfl⟩


-- @node: radialEdgeEquiv
/-- For [a sphere map](hyp:T) with [a sphere triangulation
structure](hyp:hT), the [bijection from radial edges to original darts](goal)
is obtained by [forming the radial rotation system](step:1) and [assigning to
each radial edge the original dart shared by its two labeled
representatives](step:2). -/
noncomputable def radialEdgeEquiv (hT : IsSphereTriangulation T) :
    (radialRotation T hT).Edge ≃ T.Dart := by
  let R := radialRotation T hT
  let f : R.Edge → T.Dart := Quotient.lift Prod.fst (by
    intro d e h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih)
  apply Equiv.ofBijective f
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h d =>
      induction b using Quotient.inductionOn with
      | h e =>
        intro h
        change d.1 = e.1 at h
        rcases d with ⟨d, b⟩
        rcases e with ⟨e, c⟩
        dsimp only at h
        subst e
        apply Quotient.sound
        cases b <;> cases c
        · exact Equiv.Perm.SameCycle.refl _ _
        · exact ⟨(1 : ℕ), rfl⟩
        · exact ⟨(1 : ℕ), rfl⟩
        · exact Equiv.Perm.SameCycle.refl _ _
  · intro d; exact ⟨R.edgeOf (d, false), rfl⟩

-- @node: radialRotation_corner_reachable
/-- If [the original map is a sphere triangulation](hyp:hT), then [the initial
vertex of any original dart is connected by a path in the radial graph to the
center of its incident face](goal). -/
lemma radialRotation_corner_reachable (hT : IsSphereTriangulation T) (d : T.Dart) :
    (radialRotation T hT).toSimpleGraph.Reachable
      (Sum.inl (T.vert d)) (Sum.inr (T.faceOf d)) := by
  apply SimpleGraph.Adj.reachable
  exact ⟨Sum.inl_ne_inr, (d, true), rfl, rfl⟩

-- @node: radialRotation_connected
/-- If [the original map is a sphere triangulation](hyp:hT), then [its radial
graph is connected](goal). -/
lemma radialRotation_connected (hT : IsSphereTriangulation T) :
    (radialRotation T hT).toSimpleGraph.Connected := by
  let R := radialRotation T hT
  have path (v w : T.Vertex) :
      R.toSimpleGraph.Reachable (Sum.inl v) (Sum.inl w) := by
    obtain ⟨p⟩ := hT.props.1.preconnected v w
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons v w z hadj p ih =>
      obtain ⟨hne, d, hd, hh⟩ := hadj
      have he : T.vert (T.facePerm d) = T.head d := T.rot_vertex _
      have hf := T.dual_rot_vertex d
      have step := (radialRotation_corner_reachable T hT d).trans
        (by simpa only [he, hf] using
          (radialRotation_corner_reachable T hT (T.facePerm d)).symm)
      change R.toSimpleGraph.Reachable (Sum.inl (T.vert d)) (Sum.inl (T.head d)) at step
      subst v
      subst w
      exact step.trans ih
  let v0 : T.Vertex := Classical.choice hT.props.1.nonempty
  have to_base (v : R.Vertex) : R.toSimpleGraph.Reachable v (Sum.inl v0) := by
    cases v with
    | inl v => exact path v v0
    | inr f =>
      have hc : 0 < (T.faceDarts f).card := by
        rw [← T.faceLength_eq_card_faceDarts, (hT.props.2.2.2 f).1]
        omega
      obtain ⟨d, hd⟩ := Finset.card_pos.mp hc
      have hf : T.faceOf d = f := (Finset.mem_filter.mp hd).2
      exact hf ▸ (radialRotation_corner_reachable T hT d).symm.trans (path _ _)
  let : Nonempty R.Vertex := ⟨Sum.inl v0⟩
  exact ⟨fun v w => (to_base v).trans (to_base w).symm⟩

-- @node: radialRotation_no_puncture
/-- If [the original map is a sphere triangulation](hyp:hT), then [an isolated
vertex in its radial rotation system](hyp:v) [cannot exist](goal). -/
lemma radialRotation_no_puncture (hT : IsSphereTriangulation T)
    (v : (radialRotation T hT).Puncture) : False := by
  cases hv : v.val with
  | inl w =>
    obtain ⟨d, hd⟩ := triangulation_has_dart_at_vertex T hT w
    exact v.property (d, true) ((congrArg Sum.inl hd).trans hv.symm)
  | inr f =>
    have hc : 0 < (T.faceDarts f).card := by
      rw [← T.faceLength_eq_card_faceDarts, (hT.props.2.2.2 f).1]
      omega
    obtain ⟨d, hd⟩ := Finset.card_pos.mp hc
    have hf : T.faceOf d = f := (Finset.mem_filter.mp hd).2
    exact v.property (d, false) ((congrArg Sum.inr hf).trans hv.symm)

-- @node: radialLocalBoundaryEquiv
/-- For [a sphere map](hyp:T) with [a sphere triangulation
structure](hyp:hT), the [bijection from radial local boundaries to original
edges](goal) assigns each radial face cycle its boundary index; there are no
isolated radial vertices to contribute additional boundaries. -/
noncomputable def radialLocalBoundaryEquiv (hT : IsSphereTriangulation T) :
    (radialRotation T hT).LocalBoundary ≃ T.Edge where
  toFun := Sum.elim (radialBoundaryEquiv T hT) (fun v => (radialRotation_no_puncture T hT v).elim)
  invFun e := Sum.inl ((radialBoundaryEquiv T hT).symm e)
  left_inv b := by
    cases b with
    | inl o => simp
    | inr v => exact (radialRotation_no_puncture T hT v).elim
  right_inv e := (radialBoundaryEquiv T hT).apply_symm_apply e

-- @node: radialRotation_componentEuler
/-- If [the original map is a sphere triangulation](hyp:hT), then [in each
radial component the number of vertices plus the number of local boundaries
equals the number of edges plus two](goal). -/
lemma radialRotation_componentEuler (hT : IsSphereTriangulation T) :
    (radialRotation T hT).componentEuler := by
  let R := radialRotation T hT
  let : Nonempty R.Vertex := (radialRotation_connected T hT).nonempty
  let : Subsingleton R.Component :=
    (radialRotation_connected T hT).preconnected.subsingleton_connectedComponent
  have hc : Nat.card R.Component = 1 := Nat.card_unique
  have hb := Nat.card_congr (radialLocalBoundaryEquiv T hT)
  have he := Nat.card_congr (radialEdgeEquiv T hT)
  have hg := T.global_euler
  let : Nonempty T.Vertex := hT.props.1.nonempty
  let : Subsingleton T.Component := hT.props.1.preconnected.subsingleton_connectedComponent
  have ht : Nat.card T.Component = 1 := Nat.card_unique
  have hd := T.dart_card_eq_twice_edge_card
  apply R.componentEuler_of_global_card
  change Nat.card (T.Vertex ⊕ T.Face) + Nat.card R.LocalBoundary =
    Nat.card R.Edge + 2 * Nat.card R.Component
  rw [Nat.card_sum, hc, hb, he]
  simp only [Nat.card_eq_fintype_card] at *
  omega


-- @node: radialMap
/-- For [a sphere map](hyp:T) with [a sphere triangulation
structure](hyp:hT), the [radial sphere map](goal) joins original vertices to
incident face centers using the radial rotation system and labels its faces
by the corresponding original edges. -/
noncomputable def radialMap (hT : IsSphereTriangulation T) : SphereMap where
  toRotationSystem := radialRotation T hT
  genusZero := radialRotation_componentEuler T hT
  Face := T.Edge
  boundaryFace := radialLocalBoundaryEquiv T hT
  placement_connected := by
    let R := radialRotation T hT
    let G := R.placementGraph T.Edge (radialLocalBoundaryEquiv T hT)
    let v0 : R.Vertex := Classical.choice (radialRotation_connected T hT).nonempty
    let K0 := R.toSimpleGraph.connectedComponentMk v0
    let : Subsingleton R.Component :=
      (radialRotation_connected T hT).preconnected.subsingleton_connectedComponent
    have to_base (a : R.Component ⊕ T.Edge) : G.Reachable a (Sum.inl K0) := by
      cases a with
      | inl K =>
        have h : K = K0 := Subsingleton.elim _ _
        exact h ▸ SimpleGraph.Reachable.refl _
      | inr e =>
        apply SimpleGraph.Adj.reachable
        exact ⟨(radialLocalBoundaryEquiv T hT).symm e, Subsingleton.elim _ _,
          (radialLocalBoundaryEquiv T hT).apply_symm_apply e⟩
    let : Nonempty (R.Component ⊕ T.Edge) := ⟨Sum.inl K0⟩
    exact ⟨fun a b => (to_base a).trans (to_base b).symm⟩
  placement_card := by
    let R := radialRotation T hT
    let : Nonempty R.Vertex := (radialRotation_connected T hT).nonempty
    let : Subsingleton R.Component :=
      (radialRotation_connected T hT).preconnected.subsingleton_connectedComponent
    have hc : Nat.card R.Component = 1 := Nat.card_unique
    have hb := Nat.card_congr (radialLocalBoundaryEquiv T hT)
    rw [Nat.card_sum, hc, hb]
    omega

-- @node: radialMap_face_false
/-- If [the original map is a sphere triangulation](hyp:hT), then [the radial
face containing a false-labeled dart is labeled by that dart's original
edge](goal). -/
lemma radialMap_face_false (hT : IsSphereTriangulation T) (d : T.Dart) :
    (radialMap T hT).faceOf (d, false) = T.edgeOf d := rfl

-- @node: radialMap_face_true
/-- If [the original map is a sphere triangulation](hyp:hT), then [the radial
face containing a true-labeled dart is labeled by the original edge reached
by one inverse vertex rotation of that dart](goal). -/
lemma radialMap_face_true (hT : IsSphereTriangulation T) (d : T.Dart) :
    (radialMap T hT).faceOf (d, true) = T.edgeOf (T.rot.symm d) := rfl

end OaiPairedStatesHamiltonian
