module

public import Mathlib.Data.Fintype.Sum
public import Papers.OaiPairedStatesHamiltonian.Helpers.States

/-! Inherited spoke embeddings, their cycle projections, and signed incidence weights. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


variable (T : SphereMap)
/-- For [a sphere map](hyp:T) and [a selected set of faces](hyp:faces), a
[spoke corner](goal) is a directed edge whose incident face is selected. -/
abbrev SpokeCorner (faces : Finset T.Face) := {d : T.Dart // T.faceOf d ∈ faces}
/-- For [a sphere map](hyp:T) and [a selected set of faces](hyp:faces), a
[spoke dart](goal) is a selected corner together with a Boolean indicating which
end of the spoke it starts from. -/
abbrev SpokeDart (faces : Finset T.Face) := SpokeCorner T faces × Bool
/-- For [a sphere map](hyp:T) and [a selected set of faces](hyp:faces), the
[spoke vertices](goal) consist of all original vertices and one center for each
selected face. -/
abbrev SpokeVertex (faces : Finset T.Face) := T.Vertex ⊕ faces

/-- For [a sphere map](hyp:T), [selected faces](hyp:faces), and [a spoke dart](hyp:d),
its [starting vertex](goal) is the corner's original vertex when its Boolean is
true, and the selected face's center when its Boolean is false. -/
noncomputable def spokeVert (faces : Finset T.Face) (d : SpokeDart T faces) : SpokeVertex T faces :=
  if d.2 then Sum.inl (T.vert d.1.val) else Sum.inr ⟨T.faceOf d.1.val, d.1.property⟩

/-- For [a sphere map](hyp:T), [selected faces](hyp:faces), and [a permutation of
spoke darts](hyp:rot), the [spoke rotation requirement](goal) says that
[darts starting at original vertices keep their Boolean and move to the next
selected corner in the original vertex rotation](step:1), while [darts starting
at face centers keep their Boolean and move backward around their face](step:2). -/
noncomputable def SpokeRotationSpec (faces : Finset T.Face) (rot : Equiv.Perm (SpokeDart T faces)) : Prop :=
  ∀ d, if d.2 then (rot d).2 = true ∧
      (rot d).1 = firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d.1
    else (rot d).2 = false ∧ (rot d).1.val = T.facePerm.symm d.1.val

/-- For [a sphere map](hyp:T), [selected faces](hyp:faces), and [a pair of spoke-dart
permutations](hyp:p), the [spoke permutation requirements](goal) are that
[edge reversal changes only the Boolean end indicator](step:1), [rotation follows
the inherited vertex order and reverse facial order](step:2), [edge reversal is
an involution](step:3), [edge reversal fixes no dart](step:4), [rotation preserves
each dart's starting vertex](step:5), and [rotation forms a single cycle on the
darts at each vertex](step:6). -/
noncomputable def SpokePermProperties (faces : Finset T.Face)
    (p : Equiv.Perm (SpokeDart T faces) × Equiv.Perm (SpokeDart T faces)) : Prop :=
  (∀ d, p.1 d = (d.1, !d.2)) ∧ SpokeRotationSpec T faces p.2 ∧
  Function.Involutive p.1 ∧ (∀ d, p.1 d ≠ d) ∧
  (∀ d, spokeVert T faces (p.2 d) = spokeVert T faces d) ∧
  (∀ v, p.2.IsCycleOn {d | spokeVert T faces d = v})

-- @node: spokePrevPerm
/-- For [a sphere map](hyp:T) and [selected faces](hyp:faces), the
[predecessor permutation on selected corners](goal) moves each corner one step
backward around its face. -/
noncomputable def spokePrevPerm (faces : Finset T.Face) : Equiv.Perm (SpokeCorner T faces) :=
  T.facePerm⁻¹.subtypePerm (by
    intro d
    have h : T.faceOf (T.facePerm.symm d) = T.faceOf d := by
      rw [← T.dual_rot_vertex (T.facePerm.symm d), T.facePerm.apply_symm_apply]
    change T.faceOf (T.facePerm.symm d) ∈ faces ↔ T.faceOf d ∈ faces
    rw [h])

-- @node: spokeRotPerm
/-- For [a sphere map](hyp:T) and [selected faces](hyp:faces), the [spoke rotation
permutation](goal) moves darts at original vertices to the next selected corner
in the original rotation and darts at face centers backward around their face,
preserving the end indicator in both cases. -/
noncomputable def spokeRotPerm (faces : Finset T.Face) : Equiv.Perm (SpokeDart T faces) where
  toFun d := if d.2 then (firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d.1, true)
    else (spokePrevPerm T faces d.1, false)
  invFun d := if d.2 then ((firstReturnPerm T.rot {d | T.faceOf d ∈ faces}).symm d.1, true)
    else ((spokePrevPerm T faces).symm d.1, false)
  left_inv := by rintro ⟨d, b⟩; cases b <;> simp
  right_inv := by rintro ⟨d, b⟩; cases b <;> simp

-- @node: spokeRotPerm_vertex
/-- For a sphere map, [selected faces](hyp:faces), and [a spoke dart](hyp:d),
[the spoke rotation preserves the dart's starting vertex](goal). -/
lemma spokeRotPerm_vertex (faces : Finset T.Face) (d : SpokeDart T faces) :
    spokeVert T faces (spokeRotPerm T faces d) = spokeVert T faces d := by
  rcases d with ⟨d, b⟩
  cases b
  · simp only [spokeRotPerm, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte, spokeVert]
    congr 1
    apply Subtype.ext
    change T.faceOf (T.facePerm.symm d.val) = T.faceOf d.val
    rw [← T.dual_rot_vertex (T.facePerm.symm d.val), T.facePerm.apply_symm_apply]
  · simp only [spokeRotPerm, Equiv.coe_fn_mk, ↓reduceIte, spokeVert]
    congr 1
    obtain ⟨n, hn, heq, hfirst⟩ := Classical.choose_spec
      (exists_firstReturnPerm T.rot {d | T.faceOf d ∈ faces}) d
    change (firstReturnPerm T.rot _ d).val = (T.rot ^ n) d.val at heq
    rw [show (firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d).val =
      (T.rot ^ n) d.val from heq]
    clear hn heq hfirst
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, T.rot_vertex]
      exact ih

-- @node: spokeRotPerm_pow
/-- For a sphere map, [selected faces](hyp:faces), [a selected corner](hyp:d),
[a Boolean end indicator](hyp:b), and [a nonnegative number of steps](hyp:n),
[iterating the spoke rotation that many times iterates the first-return vertex
rotation when the indicator is true and the facial predecessor when it is false,
leaving the indicator unchanged](goal). -/
lemma spokeRotPerm_pow (faces : Finset T.Face) (d : SpokeCorner T faces) (b : Bool) (n : ℕ) :
    (spokeRotPerm T faces ^ n) (d, b) =
      (if b then ((firstReturnPerm T.rot {d | T.faceOf d ∈ faces} ^ n) d, true)
        else ((spokePrevPerm T faces ^ n) d, false)) := by
  induction n with
  | zero => cases b <;> rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    cases b <;> simp [spokeRotPerm, pow_succ', Equiv.Perm.mul_apply]

-- @node: spokeRotPerm_fibre
/-- For a sphere map [that is a sphere triangulation](hyp:hT),
[selected faces](hyp:faces), and [a spoke vertex](hyp:v), [the spoke rotation
forms a single cycle on the darts starting at that vertex](goal). -/
lemma spokeRotPerm_fibre (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (v : SpokeVertex T faces) :
    (spokeRotPerm T faces).IsCycleOn {d | spokeVert T faces d = v} := by
  refine ⟨⟨?_, (spokeRotPerm T faces).injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (spokeRotPerm_vertex T faces d).trans hd
  · intro d hd
    refine ⟨(spokeRotPerm T faces).symm d, ?_, (spokeRotPerm T faces).apply_symm_apply d⟩
    change spokeVert T faces ((spokeRotPerm T faces).symm d) = v
    rw [← spokeRotPerm_vertex T faces ((spokeRotPerm T faces).symm d),
      (spokeRotPerm T faces).apply_symm_apply]
    exact hd
  · rintro ⟨d, b⟩ hd ⟨e, c⟩ he
    cases v with
    | inl v =>
      have hb : b = true := by cases b <;> simp_all [spokeVert]
      have hc : c = true := by cases c <;> simp_all [spokeVert]
      subst b; subst c
      have hdv : T.vert d.val = v := by simpa [spokeVert] using hd
      have hev : T.vert e.val = v := by simpa [spokeVert] using he
      have h := sameCycle_firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d e
        ((T.rot_fibre v).2 hdv hev)
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      exact ⟨(n : ℤ), by simpa only [zpow_natCast, spokeRotPerm_pow, ↓reduceIte, hn]⟩
    | inr f =>
      have hb : b = false := by cases b <;> simp_all [spokeVert]
      have hc : c = false := by cases c <;> simp_all [spokeVert]
      subst b; subst c
      have hdv : T.faceOf d.val = f.val := by
        have h : (⟨T.faceOf d.val, d.property⟩ : faces) = f := by simpa [spokeVert] using hd
        exact congrArg Subtype.val h
      have hev : T.faceOf e.val = f.val := by
        have h : (⟨T.faceOf e.val, e.property⟩ : faces) = f := by simpa [spokeVert] using he
        exact congrArg Subtype.val h
      have h : (spokePrevPerm T faces).SameCycle d e :=
        (((T.dual_rot_fibre hT.props.1 f.val).2 hdv hev).inv).subtypePerm
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      exact ⟨(n : ℤ), by simpa only [zpow_natCast, spokeRotPerm_pow, Bool.false_eq_true,
        ↓reduceIte, hn]⟩

-- @node: exists_spokePerms
/-- For a sphere map [that is a sphere triangulation](hyp:hT) and
[selected faces](hyp:faces), if [no edge has selected faces on both sides](hyp:hfaces),
[there exist edge-reversal and rotation permutations satisfying all spoke
permutation requirements](goal). -/
lemma exists_spokePerms (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    ∃ p, SpokePermProperties T faces p := by
  let inv : Equiv.Perm (SpokeDart T faces) :=
    { toFun := fun d => (d.1, !d.2)
      invFun := fun d => (d.1, !d.2)
      left_inv := by rintro ⟨d, b⟩; cases b <;> rfl
      right_inv := by rintro ⟨d, b⟩; cases b <;> rfl }
  refine ⟨(inv, spokeRotPerm T faces), (fun _ => rfl), ?_, ?_, ?_,
    spokeRotPerm_vertex T faces, spokeRotPerm_fibre T hT faces⟩
  · rintro ⟨d, b⟩
    cases b <;> simp [SpokeRotationSpec, spokeRotPerm, spokePrevPerm]
  · rintro ⟨d, b⟩
    cases b <;> rfl
  · rintro ⟨d, b⟩ h
    have hbool := congrArg Prod.snd h
    cases b <;> simp [inv] at hbool

/-- For [a sphere map](hyp:T) [that is a sphere triangulation](hyp:hT) and
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
the [chosen spoke permutations](goal) are a pair of edge-reversal and rotation
permutations satisfying the spoke permutation requirements. -/
noncomputable def spokePerms (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :=
  Classical.choose (exists_spokePerms T hT faces hfaces)

/-- For [a sphere map](hyp:T) [that is a sphere triangulation](hyp:hT) and
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
the [spoke rotation system](goal) joins each selected face center to its corners,
using the inherited rotation at original vertices and reverse facial order at centers. -/
noncomputable def spokeRotation (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) : RotationSystem where
  Vertex := SpokeVertex T faces
  Dart := SpokeDart T faces
  vert := spokeVert T faces
  edgeInv := (spokePerms T hT faces hfaces).1
  edgeInv_involutive := (Classical.choose_spec (exists_spokePerms T hT faces hfaces)).2.2.1
  edgeInv_fixedPointFree := (Classical.choose_spec (exists_spokePerms T hT faces hfaces)).2.2.2.1
  rot := (spokePerms T hT faces hfaces).2
  rot_vertex := (Classical.choose_spec (exists_spokePerms T hT faces hfaces)).2.2.2.2.1
  rot_fibre := (Classical.choose_spec (exists_spokePerms T hT faces hfaces)).2.2.2.2.2

-- @node: spokeRotation_edgeInv
/-- For a sphere map [that is a sphere triangulation](hyp:hT),
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
and [a spoke dart](hyp:d), [edge reversal keeps its corner and flips its Boolean
end indicator](goal). -/
lemma spokeRotation_edgeInv (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (d : SpokeDart T faces) :
    (spokeRotation T hT faces hfaces).edgeInv d = (d.1, !d.2) :=
  (Classical.choose_spec (exists_spokePerms T hT faces hfaces)).1 d

-- @node: spoke_corner_component
/-- For a sphere map [that is a sphere triangulation](hyp:hT),
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
and [a selected corner](hyp:d), [the corner's original vertex and its face center
belong to the same connected component of the spoke graph](goal). -/
lemma spoke_corner_component (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (d : SpokeCorner T faces) :
    (spokeRotation T hT faces hfaces).toSimpleGraph.connectedComponentMk
        (Sum.inl (T.vert d.val)) =
      (spokeRotation T hT faces hfaces).toSimpleGraph.connectedComponentMk
        (Sum.inr ⟨T.faceOf d.val, d.property⟩) := by
  have h := (spokeRotation T hT faces hfaces).dart_component_eq_head (d, true)
  change _ = (spokeRotation T hT faces hfaces).toSimpleGraph.connectedComponentMk
    ((spokeRotation T hT faces hfaces).vert
      ((spokeRotation T hT faces hfaces).edgeInv (d, true))) at h
  rw [spokeRotation_edgeInv] at h
  exact h

-- @node: spoke_side_component
/-- For a sphere map [that is a sphere triangulation](hyp:hT),
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
and [an original directed edge](hyp:d) [whose incident face is selected](hyp:hd),
[its tail and head belong to the same connected component of the spoke graph](goal). -/
lemma spoke_side_component (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (d : T.Dart) (hd : T.faceOf d ∈ faces) :
    (spokeRotation T hT faces hfaces).toSimpleGraph.connectedComponentMk
        (Sum.inl (T.vert d)) =
      (spokeRotation T hT faces hfaces).toSimpleGraph.connectedComponentMk
        (Sum.inl (T.head d)) := by
  have hn : T.faceOf (T.facePerm d) ∈ faces := (T.dual_rot_vertex d).symm ▸ hd
  have hc := spoke_corner_component T hT faces hfaces ⟨d, hd⟩
  have hc' := spoke_corner_component T hT faces hfaces ⟨T.facePerm d, hn⟩
  have hv : T.vert (T.facePerm d) = T.head d := T.rot_vertex _
  have hf : (⟨T.faceOf (T.facePerm d), hn⟩ : faces) = ⟨T.faceOf d, hd⟩ :=
    Subtype.ext (T.dual_rot_vertex d)
  rw [hv, hf] at hc'
  exact hc.trans hc'.symm


end OaiPairedStatesHamiltonian
