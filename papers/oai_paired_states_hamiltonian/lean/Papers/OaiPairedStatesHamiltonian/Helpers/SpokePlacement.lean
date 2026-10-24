module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SpokeRegions
public import Papers.OaiPairedStatesHamiltonian.Helpers.InducedMaps

/-! Spoke regions are the actual induced radial faces. This identification
transports the induced placement count, including isolated original vertices. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (T : SphereMap)

-- @node: spokeInduced_kept_iff
/-- If [the sphere map is a triangulation](hyp:hT), then [a radial dart has both
endpoints among the original vertices and selected face centers exactly when its
underlying original dart belongs to a selected face](goal). -/
lemma spokeInduced_kept_iff (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (d : (radialMap T hT).Dart) :
    ((radialMap T hT).vert d ∈ spokeRadialVertices T faces ∧
      (radialMap T hT).head d ∈ spokeRadialVertices T faces) ↔ T.faceOf d.1 ∈ faces := by
  rcases d with ⟨d, b⟩
  cases b <;> simp [radialMap, radialRotation, radialVert, radialInv,
    RotationSystem.head, SphereMap.head, spokeRadialVertices]

-- @node: spokeInducedDartEquiv
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT) and
[a set of selected faces](hyp:faces), the [bijection between retained radial darts
and spoke darts](goal) [keeps the original dart and its direction flag](step:1)
and [reinterprets these as a retained radial dart in the reverse direction](step:2),
with [the reverse map undoing the forward map](step:3) and
[the forward map undoing the reverse map](step:4). -/
noncomputable def spokeInducedDartEquiv (hT : IsSphereTriangulation T) (faces : Finset T.Face) :
    (radialMap T hT).KeptDart (spokeRadialVertices T faces) ≃ SpokeDart T faces where
  toFun d := (⟨d.val.1, (spokeInduced_kept_iff T hT faces d.val).mp d.property⟩, d.val.2)
  invFun d := ⟨(d.1.val, d.2), (spokeInduced_kept_iff T hT faces _).mpr d.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- @node: spokeInduced_relabel
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT) and
[selected faces](hyp:faces) such that [no edge has selected faces on both sides](hyp:hfaces),
the [relabeling of the induced radial rotation system as the spoke rotation
system](goal) identifies their vertices and darts while preserving incidence,
edge reversal, and cyclic order around vertices. -/
noncomputable def spokeInduced_relabel (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    ((radialMap T hT).inducedRotation (spokeRadialVertices T faces)).Relabel
      (spokeRotation T hT faces hfaces) := by
  let M := radialMap T hT
  let U := spokeRadialVertices T faces
  have hset : {d : M.Dart | M.vert d ∈ U ∧ M.head d ∈ U} =
      {d : T.Dart × Bool | T.faceOf d.1 ∈ faces} :=
    Set.ext (spokeInduced_kept_iff T hT faces)
  refine ⟨spokeRadialVertexEquiv T faces, spokeInducedDartEquiv T hT faces, ?_, ?_, ?_⟩
  · rintro ⟨⟨d, b⟩, hd⟩
    cases b <;> rfl
  · intro d
    have hi := Classical.choose_spec (M.exists_inducedInv U) d
    change (M.inducedInv U d).val = (d.val.1, !d.val.2) at hi
    rw [spokeRotation_edgeInv]
    apply Prod.ext
    · apply Subtype.ext
      change (M.inducedInv U d).val.1 = d.val.1
      have hfirst := congrArg Prod.fst hi
      exact hfirst
    · change (M.inducedInv U d).val.2 = !d.val.2
      exact congrArg Prod.snd hi
  · rintro ⟨⟨d, b⟩, hd⟩
    have hd' := (spokeInduced_kept_iff T hT faces (d, b)).mp hd
    have hr : (M.inducedRot U ⟨(d, b), hd⟩).val =
        (firstReturnPerm (radialRot T) {d | T.faceOf d.1 ∈ faces} ⟨(d, b), hd'⟩).val := by
      unfold SphereMap.inducedRot
      change (firstReturnPerm (radialRot T) {d : M.Dart | M.vert d ∈ U ∧ M.head d ∈ U}
        ⟨(d, b), hd⟩).val = _
      exact firstReturnPerm_equiv_apply (radialRot T) (radialRot T) (Equiv.refl _)
        (fun _ => rfl) {d : M.Dart | M.vert d ∈ U ∧ M.head d ∈ U}
        {d : T.Dart × Bool | T.faceOf d.1 ∈ faces} (spokeInduced_kept_iff T hT faces) _
    have hs := (Classical.choose_spec (exists_spokePerms T hT faces hfaces)).2.1
      ((⟨d, hd'⟩ : SpokeCorner T faces), b)
    apply Prod.ext
    · apply Subtype.ext
      change (M.inducedRot U ⟨(d, b), hd⟩).val.1 = _
      rw [hr]
      cases b
      · exact (congrArg Prod.fst (radial_firstReturn_false T faces ⟨d, hd'⟩)).trans hs.2.symm
      · exact (congrArg Prod.fst (radial_firstReturn_true T faces ⟨d, hd'⟩)).trans
          (congrArg Subtype.val hs.2).symm
    · change (M.inducedRot U ⟨(d, b), hd⟩).val.2 = _
      rw [hr]
      cases b
      · exact (congrArg Prod.snd (radial_firstReturn_false T faces ⟨d, hd'⟩)).trans hs.1.symm
      · exact (congrArg Prod.snd (radial_firstReturn_true T faces ⟨d, hd'⟩)).trans hs.1.symm


-- @node: spokeRadialFaceClass
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT),
[selected faces](hyp:faces), and [an original edge](hyp:e), the
[induced radial face class associated with that edge](goal) is the class of its
radial face after retaining all original vertices and the selected face centers. -/
noncomputable def spokeRadialFaceClass (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (e : T.Edge) : (radialMap T hT).InducedFace (spokeRadialVertices T faces) :=
  (radialMap T hT).inducedFaceClass (spokeRadialVertices T faces) e

-- @node: spokeRadialFaceClass_step
/-- If [the sphere map is a triangulation](hyp:hT) and
[the face incident to a dart is unselected](hyp:hd), then
[the dart's edge and the next edge around that face have the same induced radial
face class](goal). -/
lemma spokeRadialFaceClass_step (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (d : T.Dart) (hd : T.faceOf d ∉ faces) :
    spokeRadialFaceClass T hT faces (T.edgeOf (T.facePerm d)) =
      spokeRadialFaceClass T hT faces (T.edgeOf d) := by
  let M := radialMap T hT
  let U := spokeRadialVertices T faces
  have he : M.faceOf (T.facePerm d, true) = T.edgeOf d := by
    rw [radialMap_face_true]
    change T.edgeOf (T.rot.symm (T.rot (T.edgeInv d))) = T.edgeOf d
    rw [T.rot.symm_apply_apply]
    exact (T.toRotationSystem.edgeOf_eq_iff _ _).mpr (Or.inr rfl) |>.symm
  have hdel : ¬ (M.vert (T.facePerm d, false) ∈ U ∧ M.head (T.facePerm d, false) ∈ U) := by
    rw [spokeInduced_kept_iff, T.dual_rot_vertex]
    exact hd
  exact Quotient.sound (Relation.EqvGen.rel _ _
    ⟨(T.facePerm d, false), hdel, rfl, he⟩)

-- @node: spokeRadialFaceClass_fibre
/-- If [the sphere map is a triangulation](hyp:hT), [a face is unselected](hyp:hf),
[one dart belongs to that face](hyp:hd), and [another dart belongs to it](hyp:he), then
[their edges have the same induced radial face class](goal). -/
lemma spokeRadialFaceClass_fibre (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (f : T.Face) (hf : f ∉ faces) (d e : T.Dart)
    (hd : T.faceOf d = f) (he : T.faceOf e = f) :
    spokeRadialFaceClass T hT faces (T.edgeOf d) =
      spokeRadialFaceClass T hT faces (T.edgeOf e) := by
  obtain ⟨n, rfl⟩ := ((T.dual_rot_fibre hT.props.1 f).2 hd he).exists_nat_pow_eq
  clear he
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    apply ih.trans
    apply (spokeRadialFaceClass_step T hT faces _ _).symm
    have hpow : T.faceOf ((T.facePerm ^ n) d) = T.faceOf d := by
      clear ih
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, T.dual_rot_vertex, ih]
    rwa [hpow, hd]

-- @node: exists_spokeFaceDart
/-- If [the sphere map is a triangulation](hyp:hT), then
[every face has an incident dart](goal). -/
lemma exists_spokeFaceDart (hT : IsSphereTriangulation T) (f : T.Face) :
    ∃ d, T.faceOf d = f := by
  have hc : 0 < (T.faceDarts f).card := by
    rw [← T.faceLength_eq_card_faceDarts, (hT.props.2.2.2 f).1]
    omega
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hc
  exact ⟨d, (Finset.mem_filter.mp hd).2⟩

-- @node: spokeUnselectedDart
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT) and
[a face](hyp:f), the [chosen representative dart](goal) is any dart incident to
that face. -/
noncomputable def spokeUnselectedDart (hT : IsSphereTriangulation T) (f : T.Face) : T.Dart :=
  Classical.choose (exists_spokeFaceDart T hT f)

-- @node: spokeUnselectedDart_spec
/-- If [the sphere map is a triangulation](hyp:hT), then
[the chosen representative dart of a face belongs to that face](goal). -/
lemma spokeUnselectedDart_spec (hT : IsSphereTriangulation T) (f : T.Face) :
    T.faceOf (spokeUnselectedDart T hT f) = f :=
  Classical.choose_spec (exists_spokeFaceDart T hT f)

-- @node: spokePieceToRadial
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT) and
[selected faces](hyp:faces), the [map from spoke region pieces to induced radial
faces](goal) sends [an unselected face to the class of an edge of its chosen
representative dart](step:1) and [a sector of a selected face to the class of
its defining edge](step:2). -/
noncomputable def spokePieceToRadial (hT : IsSphereTriangulation T) (faces : Finset T.Face) :
    SpokePiece T faces → (radialMap T hT).InducedFace (spokeRadialVertices T faces) :=
  Sum.elim (fun f => spokeRadialFaceClass T hT faces
      (T.edgeOf (spokeUnselectedDart T hT f.val)))
    (fun d => spokeRadialFaceClass T hT faces (T.edgeOf d.val))

-- @node: spokePieceToRadial_at
/-- If [the sphere map is a triangulation](hyp:hT), then
[the spoke piece at any dart maps to the induced radial face class of that dart's
edge](goal). -/
lemma spokePieceToRadial_at (hT : IsSphereTriangulation T) (faces : Finset T.Face) (d : T.Dart) :
    spokePieceToRadial T hT faces (spokePieceAt T faces d) =
      spokeRadialFaceClass T hT faces (T.edgeOf d) := by
  unfold spokePieceAt
  split
  · rfl
  · rename_i hd
    exact spokeRadialFaceClass_fibre T hT faces _ hd _ _
      (spokeUnselectedDart_spec T hT _) rfl

-- @node: spokeFaceToRadial
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT) and
[selected faces](hyp:faces), the [map from glued spoke faces to induced radial
faces](goal) assigns each glued region the common induced radial face class of
its pieces. -/
noncomputable def spokeFaceToRadial (hT : IsSphereTriangulation T) (faces : Finset T.Face) :
    SpokeFace T faces → (radialMap T hT).InducedFace (spokeRadialVertices T faces) :=
  Quotient.lift (spokePieceToRadial T hT faces) (by
    intro a b h
    induction h with
    | rel a b h =>
      obtain ⟨d, rfl, rfl⟩ := h
      rw [spokePieceToRadial_at, spokePieceToRadial_at]
      exact congrArg (spokeRadialFaceClass T hT faces)
        ((T.toRotationSystem.edgeOf_eq_iff _ _).mpr (Or.inr rfl))
    | refl => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h k ih jk => exact ih.trans jk)

-- @node: radialEdgeToSpoke
/-- For [a sphere map](hyp:T) and [selected faces](hyp:faces), the
[map from original edges to glued spoke faces](goal) assigns an edge the glued
region containing the spoke piece on either side of that edge. -/
noncomputable def radialEdgeToSpoke (faces : Finset T.Face) : T.Edge → SpokeFace T faces :=
  Quotient.lift (fun d => spokeFaceClass T faces (spokePieceAt T faces d)) (by
    intro d e h
    have he : T.edgeOf d = T.edgeOf e := Quotient.sound h
    rcases (T.toRotationSystem.edgeOf_eq_iff d e).mp he with rfl | rfl
    · rfl
    · exact spokeFaceClass_across T faces d)

-- @node: radialEdgeToSpoke_unselected
/-- If [the face incident to a dart is unselected](hyp:hd), then
[the dart's edge and the edge preceding it in the cyclic order at its starting
vertex map to the same glued spoke face](goal). -/
lemma radialEdgeToSpoke_unselected (faces : Finset T.Face) (d : T.Dart)
    (hd : T.faceOf d ∉ faces) :
    radialEdgeToSpoke T faces (T.edgeOf d) =
      radialEdgeToSpoke T faces (T.edgeOf (T.rot.symm d)) := by
  have hf : T.faceOf (T.facePerm.symm d) = T.faceOf d := by
    rw [← T.dual_rot_vertex (T.facePerm.symm d), T.facePerm.apply_symm_apply]
  have he : T.facePerm.symm d = T.edgeInv (T.rot.symm d) := by
    apply T.facePerm.injective
    simp only [T.facePerm.apply_symm_apply]
    change d = T.rot (T.edgeInv (T.edgeInv (T.rot.symm d)))
    rw [T.edgeInv_involutive, T.rot.apply_symm_apply]
  have hp : spokePieceAt T faces d = spokePieceAt T faces (T.facePerm.symm d) := by
    simp only [spokePieceAt, dif_neg hd, dif_neg (show T.faceOf (T.facePerm.symm d) ∉ faces by rwa [hf])]
    exact congrArg Sum.inl (Subtype.ext hf.symm)
  change spokeFaceClass T faces (spokePieceAt T faces d) =
    spokeFaceClass T faces (spokePieceAt T faces (T.rot.symm d))
  rw [hp, he]
  exact (spokeFaceClass_across T faces (T.rot.symm d)).symm

-- @node: radialFaceToSpoke
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT) and
[selected faces](hyp:faces), the [map from induced radial faces to glued spoke
faces](goal) assigns each induced face the spoke region associated with any
original edge representing it. -/
noncomputable def radialFaceToSpoke (hT : IsSphereTriangulation T) (faces : Finset T.Face) :
    (radialMap T hT).InducedFace (spokeRadialVertices T faces) → SpokeFace T faces :=
  Quotient.lift (radialEdgeToSpoke T faces) (by
    intro a b h
    induction h with
    | rel a b h =>
      obtain ⟨⟨d, b⟩, hd, rfl, rfl⟩ := h
      have hd' : T.faceOf d ∉ faces := by
        exact fun h => hd ((spokeInduced_kept_iff T hT faces (d, b)).mpr h)
      cases b
      · exact radialEdgeToSpoke_unselected T faces d hd'
      · exact (radialEdgeToSpoke_unselected T faces d hd').symm
    | refl => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h k ih jk => exact ih.trans jk)

-- @node: spokeFaceRadialEquiv
/-- For [a sphere map](hyp:T) that [is a triangulation](hyp:hT) and
[selected faces](hyp:faces), the [bijection between glued spoke faces and induced
radial faces](goal) [maps a spoke region to its induced radial face](step:1) and
[maps an induced radial face back to its spoke region](step:2), with
[the reverse map undoing the forward map](step:3) and
[the forward map undoing the reverse map](step:4). -/
noncomputable def spokeFaceRadialEquiv (hT : IsSphereTriangulation T) (faces : Finset T.Face) :
    SpokeFace T faces ≃ (radialMap T hT).InducedFace (spokeRadialVertices T faces) where
  toFun := spokeFaceToRadial T hT faces
  invFun := radialFaceToSpoke T hT faces
  left_inv f := by
    induction f using Quotient.inductionOn with
    | h a =>
      cases a with
      | inr d =>
        change spokeFaceClass T faces (spokePieceAt T faces d.val) = _
        rw [spokePieceAt, dif_pos d.property]
        rfl
      | inl f =>
        change spokeFaceClass T faces (spokePieceAt T faces (spokeUnselectedDart T hT f.val)) = _
        rw [spokePieceAt, dif_neg (by rw [spokeUnselectedDart_spec]; exact f.property)]
        congr 1
        exact congrArg Sum.inl (Subtype.ext (spokeUnselectedDart_spec T hT f.val))
  right_inv f := by
    induction f using Quotient.inductionOn with
    | h e =>
      induction e using Quotient.inductionOn with
      | h d => exact spokePieceToRadial_at T hT faces d

-- @node: spoke_placement_card
/-- If [the sphere map is a triangulation](hyp:hT) and
[no edge has selected faces on both sides](hyp:hfaces), then
[the number of spoke graph components plus the number of glued spoke faces equals
the number of local boundaries plus one](goal). Isolated original vertices are
included in this count. -/
lemma spoke_placement_card (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    Nat.card ((spokeRotation T hT faces hfaces).Component ⊕ SpokeFace T faces) =
      Nat.card (spokeRotation T hT faces hfaces).LocalBoundary + 1 := by
  let M := radialMap T hT
  let U := spokeRadialVertices T faces
  let e := spokeInduced_relabel T hT faces hfaces
  have h := M.induced_placement_card U
  have hc := Nat.card_congr e.graphIso.connectedComponentEquiv
  have hf := Nat.card_congr (spokeFaceRadialEquiv T hT faces)
  have hb := Nat.card_congr (Equiv.sumCongr
    (permOrbitEquiv _ _ e.dart e.face) e.punctureEquiv)
  rw [Nat.card_sum] at h ⊢
  rw [← hc, hf, ← hb]
  exact h

end OaiPairedStatesHamiltonian
