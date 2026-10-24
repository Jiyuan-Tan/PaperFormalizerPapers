module

public import Papers.OaiPairedStatesHamiltonian.Helpers.Spokes
public import Papers.OaiPairedStatesHamiltonian.Helpers.TreeCardinality
public import Papers.OaiPairedStatesHamiltonian.Helpers.EulerBound

/-! Spoke edges retain exactly one original triangular corner each. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
set_option backward.isDefEq.respectTransparency false

-- @node: spokeEdgeEquiv
/-- For [a sphere map](hyp:T) [that is a sphere triangulation](hyp:hT) and
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
the [bijection between spoke edges and selected corners](goal) assigns each edge
its corner and assigns each corner the spoke edge represented by its face-center dart. -/
noncomputable def spokeEdgeEquiv (T : SphereMap) (hT : IsSphereTriangulation T)
    (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    (spokeRotation T hT faces hfaces).Edge ≃ SpokeCorner T faces where
  toFun := Quotient.lift Prod.fst (by
    intro d e h
    rcases ((spokeRotation T hT faces hfaces).edgeOf_eq_iff d e).mp
      (Quotient.sound h) with rfl | rfl
    · rfl
    · rw [spokeRotation_edgeInv])
  invFun d := (spokeRotation T hT faces hfaces).edgeOf (d, false)
  left_inv := by
    intro e
    induction e using Quotient.inductionOn with
    | h d =>
      rcases d with ⟨d, b⟩
      cases b with
      | false => rfl
      | true =>
        apply ((spokeRotation T hT faces hfaces).edgeOf_eq_iff (d, false) (d, true)).mpr
        exact Or.inr (by rw [spokeRotation_edgeInv]; rfl)
  right_inv _ := rfl

-- @node: spokeEdgeEquiv_edgeOf
/-- For [a sphere map](hyp:T) [that is a sphere triangulation](hyp:hT),
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
and [a spoke dart](hyp:d), [the edge-to-corner bijection sends the dart's edge to
the dart's selected corner](goal). -/
lemma spokeEdgeEquiv_edgeOf (T : SphereMap) (hT : IsSphereTriangulation T)
    (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces))
    (d : SpokeDart T faces) :
    spokeEdgeEquiv T hT faces hfaces ((spokeRotation T hT faces hfaces).edgeOf d) = d.1 := rfl

-- @node: spoke_edge_card
/-- For [a sphere map](hyp:T) [that is a sphere triangulation](hyp:hT) and
[selected faces](hyp:faces) with [no edge having selected faces on both sides](hyp:hfaces),
[the number of spoke edges is three times the number of selected faces](goal). -/
lemma spoke_edge_card (T : SphereMap) (hT : IsSphereTriangulation T)
    (faces : Finset T.Face)
    (hfaces : ∀ d, ¬ (T.faceOf d ∈ faces ∧ T.faceOf (T.edgeInv d) ∈ faces)) :
    Fintype.card (spokeRotation T hT faces hfaces).Edge = 3 * faces.card := by
  rw [Fintype.card_congr (spokeEdgeEquiv T hT faces hfaces), Fintype.card_subtype]
  have hc := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset T.Dart) faces T.faceOf
  have hf (f : T.Face) : (Finset.univ.filter (fun d => T.faceOf d = f)).card = 3 :=
    (T.faceLength_eq_card_faceDarts f).symm.trans (hT.props.2.2.2 f).1
  simp only [hf, Finset.sum_const, smul_eq_mul] at hc
  omega

-- @node: spoke_corner_eq_of_face_tail
/-- For [a sphere map](hyp:T) [that is a sphere triangulation](hyp:hT),
[selected faces](hyp:faces), and [two selected corners](hyp:d,e), if
[the corners lie in the same face](hyp:hf) and [have the same tail vertex](hyp:hv),
then [the corners are equal](goal). -/
lemma spoke_corner_eq_of_face_tail (T : SphereMap) (hT : IsSphereTriangulation T)
    (faces : Finset T.Face) (d e : SpokeCorner T faces)
    (hf : T.faceOf d.val = T.faceOf e.val) (hv : T.vert d.val = T.vert e.val) : d = e := by
  have hinj : Set.InjOn T.vert (↑(T.faceDarts (T.faceOf d.val)) : Set T.Dart) := by
    apply Finset.card_image_iff.mp
    rw [← triangulation_faceVertices_eq_image T hT]
    exact (hT.props.2.2.2 _).2.trans
      ((T.faceLength_eq_card_faceDarts _).symm.trans (hT.props.2.2.2 _).1).symm
  apply Subtype.ext
  apply hinj
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf.symm⟩
  · exact hv

end OaiPairedStatesHamiltonian
