module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SpokeCore
public import Papers.OaiPairedStatesHamiltonian.Helpers.RadialRotation

/-! Spokes inherit genus zero by deleting radial edges at unselected centers,
then removing precisely the isolated unselected centers. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (T : SphereMap)

-- @node: spokeRadialVertices
/-- For [a sphere map](hyp:T) and [selected faces](hyp:faces), the [retained radial
vertices](goal) consist of all original vertices together with the centers of
the selected faces. -/
noncomputable def spokeRadialVertices (faces : Finset T.Face) : Set (T.Vertex ⊕ T.Face) :=
  {v | Sum.elim (fun _ => True) (fun f => f ∈ faces) v}

-- @node: spokeRestrictedRadial
/-- For [a sphere map](hyp:T) [that is a sphere triangulation](hyp:hT) and
[selected faces](hyp:faces), the [restricted radial rotation system](goal) is
obtained by [first retaining only darts incident with selected faces](step:1),
then [retaining all original vertices and only the selected face centers](step:2). -/
noncomputable def spokeRestrictedRadial (hT : IsSphereTriangulation T)
    (faces : Finset T.Face) : RotationSystem :=
  let Q := (radialRotation T hT).restrictDarts {d | T.faceOf d.1 ∈ faces} (fun _ => Iff.rfl)
  Q.restrictVertices (spokeRadialVertices T faces) (by
    rintro ⟨⟨d, b⟩, hd⟩
    cases b
    · exact hd
    · trivial)

-- @node: spokeRestrictedRadial_componentEuler
/-- For a sphere map [that is a sphere triangulation](hyp:hT) and
[selected faces](hyp:faces), [every connected component of the restricted radial
system has its number of vertices plus its number of local boundaries equal to
its number of edges plus two](goal). -/
lemma spokeRestrictedRadial_componentEuler (hT : IsSphereTriangulation T)
    (faces : Finset T.Face) : (spokeRestrictedRadial T hT faces).componentEuler := by
  apply RotationSystem.restrictVertices_componentEuler
  exact (radialRotation T hT).restrictDarts_componentEuler _
    (radialRotation_componentEuler T hT) _

-- @node: spokeRadialVertexEquiv
/-- For [a sphere map](hyp:T) and [selected faces](hyp:faces), the [bijection from
retained radial vertices to spoke vertices](goal) identifies original vertices
with themselves and selected face centers with the corresponding spoke centers. -/
noncomputable def spokeRadialVertexEquiv (faces : Finset T.Face) :
    spokeRadialVertices T faces ≃ SpokeVertex T faces where
  toFun v := match v with
    | ⟨Sum.inl w, _⟩ => Sum.inl w
    | ⟨Sum.inr f, hf⟩ => Sum.inr ⟨f, hf⟩
  invFun v := match v with
    | Sum.inl w => ⟨Sum.inl w, trivial⟩
    | Sum.inr f => ⟨Sum.inr f.val, f.property⟩
  left_inv := by rintro ⟨v, hv⟩; cases v <;> rfl
  right_inv := by intro v; cases v <;> rfl

-- @node: spokeRadialDartEquiv
/-- For [a sphere map](hyp:T) and [selected faces](hyp:faces), the [bijection from
retained radial darts to spoke darts](goal) pairs the underlying selected corner
with the same Boolean end indicator. -/
noncomputable def spokeRadialDartEquiv (faces : Finset T.Face) :
    {d : T.Dart × Bool // T.faceOf d.1 ∈ faces} ≃ SpokeDart T faces where
  toFun d := (⟨d.val.1, d.property⟩, d.val.2)
  invFun d := ⟨(d.1.val, d.2), d.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- @node: radial_firstReturn_true
/-- For a sphere map, [selected faces](hyp:faces), and [a selected corner](hyp:d),
[the radial rotation's first return to selected faces from the corner's
original-vertex end equals the original vertex rotation's first return to selected
corners, with the end indicator remaining true](goal). -/
lemma radial_firstReturn_true (faces : Finset T.Face) (d : SpokeCorner T faces) :
    (firstReturnPerm (radialRot T) {d | T.faceOf d.1 ∈ faces}
      ⟨(d.val, true), d.property⟩).val =
        ((firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d).val, true) := by
  obtain ⟨n, hn, he, hmin⟩ := Classical.choose_spec
    (exists_firstReturnPerm T.rot {d | T.faceOf d ∈ faces}) d
  change (firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d).val = (T.rot ^ n) d.val at he
  have hend : (radialRot T ^ n) (d.val, true) ∈ {d | T.faceOf d.1 ∈ faces} := by
    simp only [radialRot_pow, ↓reduceIte, Set.mem_ofPred_eq]
    rw [← he]
    exact (firstReturnPerm T.rot {d | T.faceOf d ∈ faces} d).property
  rw [firstReturnPerm_apply_of_spec (radialRot T) _ _ n hn hend (by
    intro m hm hmn
    simpa only [radialRot_pow, ↓reduceIte, Set.mem_ofPred_eq] using hmin m hm hmn)]
  simpa only [radialRot_pow, ↓reduceIte] using congrArg (fun e : T.Dart => (e, true)) he.symm

-- @node: radial_firstReturn_false
/-- For a sphere map, [selected faces](hyp:faces), and [a selected corner](hyp:d),
[the radial rotation's first return to selected faces from the corner's face-center
end is the preceding corner around that face, with the end indicator remaining false](goal). -/
lemma radial_firstReturn_false (faces : Finset T.Face) (d : SpokeCorner T faces) :
    (firstReturnPerm (radialRot T) {d | T.faceOf d.1 ∈ faces}
      ⟨(d.val, false), d.property⟩).val = (T.facePerm.symm d.val, false) := by
  have hf : T.faceOf (T.facePerm.symm d.val) = T.faceOf d.val := by
    rw [← T.dual_rot_vertex (T.facePerm.symm d.val), T.facePerm.apply_symm_apply]
  have hend : (radialRot T ^ 1) (d.val, false) ∈ {d | T.faceOf d.1 ∈ faces} := by
    simpa only [pow_one, radialRot, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte,
      Set.mem_ofPred_eq, hf] using d.property
  exact firstReturnPerm_apply_of_spec (radialRot T) _ _ 1 (by omega) hend
    (by intro m hm hmn; omega)

-- @node: spokeRestrictedRadial_relabel
/-- For [a sphere map](hyp:T) [that is a sphere triangulation](hyp:hT) and
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
the [relabeling from the restricted radial system to the spoke system](goal)
identifies their vertices and darts while preserving starting vertices, edge
reversal, and rotation. -/
noncomputable def spokeRestrictedRadial_relabel (hT : IsSphereTriangulation T)
    (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    (spokeRestrictedRadial T hT faces).Relabel (spokeRotation T hT faces hfaces) := by
  refine ⟨spokeRadialVertexEquiv T faces, spokeRadialDartEquiv T faces, ?_, ?_, ?_⟩
  · rintro ⟨⟨d, b⟩, hd⟩
    cases b <;> rfl
  · intro d
    rw [spokeRotation_edgeInv]
    rfl
  · rintro ⟨⟨d, b⟩, hd⟩
    have hs := (Classical.choose_spec (exists_spokePerms T hT faces hfaces)).2.1
      ((⟨d, hd⟩ : SpokeCorner T faces), b)
    change spokeRadialDartEquiv T faces
      (firstReturnPerm (radialRot T) _ ⟨(d, b), hd⟩) = _
    cases b
    · change _ = false ∧ _ at hs
      apply Prod.ext
      · apply Subtype.ext
        exact (congrArg Prod.fst (radial_firstReturn_false T faces ⟨d, hd⟩)).trans hs.2.symm
      · exact (congrArg Prod.snd (radial_firstReturn_false T faces ⟨d, hd⟩)).trans hs.1.symm
    · change _ = true ∧ _ at hs
      apply Prod.ext
      · apply Subtype.ext
        exact (congrArg Prod.fst (radial_firstReturn_true T faces ⟨d, hd⟩)).trans
          (congrArg Subtype.val hs.2).symm
      · exact (congrArg Prod.snd (radial_firstReturn_true T faces ⟨d, hd⟩)).trans hs.1.symm

-- @node: spoke_genus
/-- For a sphere map [that is a sphere triangulation](hyp:hT) and
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
[every connected component of the spoke system has its number of vertices plus
its number of local boundaries equal to its number of edges plus two](goal). -/
lemma spoke_genus (hT : IsSphereTriangulation T) (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    (spokeRotation T hT faces hfaces).componentEuler :=
  (spokeRestrictedRadial_relabel T hT faces hfaces).componentEuler
    (spokeRestrictedRadial_componentEuler T hT faces)

end OaiPairedStatesHamiltonian
