module

public import Papers.OaiPairedStatesHamiltonian.Helpers.RotationEquiv

/-! Removing only isolated vertices preserves componentwise Euler. The counts
include the puncture and component removed with every omitted vertex. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace RotationSystem

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (R : RotationSystem) (U : Set R.Vertex) (hU : ∀ d, R.vert d ∈ U)

-- @node: RotationSystem.restrictVertices
/-- For [a rotation system](hyp:R) and [a vertex set to retain](hyp:U) that
[contains the tail of every directed edge](hyp:hU), the [vertex-restricted rotation
system](goal) removes the other, isolated vertices and keeps all directed edges and rotations. -/
noncomputable def restrictVertices : RotationSystem where
  Vertex := U
  Dart := R.Dart
  vert d := ⟨R.vert d, hU d⟩
  edgeInv := R.edgeInv
  edgeInv_involutive := R.edgeInv_involutive
  edgeInv_fixedPointFree := R.edgeInv_fixedPointFree
  rot := R.rot
  rot_vertex d := Subtype.ext (R.rot_vertex d)
  rot_fibre v := by
    change R.rot.IsCycleOn {d | (⟨R.vert d, hU d⟩ : U) = v}
    simpa only [Subtype.ext_iff] using R.rot_fibre v.val

-- @node: RotationSystem.restrictVertices_componentEquiv
/-- For [a rotation system](hyp:R) and [a retained vertex set](hyp:U) that
[contains every directed-edge tail](hyp:hU), the [component correspondence](goal)
identifies original connected components with either components of the restricted
system or individual omitted vertices. -/
noncomputable def restrictVertices_componentEquiv :
    R.Component ≃ (R.restrictVertices U hU).Component ⊕ {v // v ∉ U} := by
  let N := R.restrictVertices U hU
  let label (v : R.Vertex) : N.Component ⊕ {v // v ∉ U} :=
    if hv : v ∈ U then Sum.inl (N.toSimpleGraph.connectedComponentMk ⟨v, hv⟩)
    else Sum.inr ⟨v, hv⟩
  have adj_label {v w : R.Vertex} (h : R.toSimpleGraph.Adj v w) : label v = label w := by
    obtain ⟨hne, d, hd, hh⟩ := h
    have hv : v ∈ U := hd ▸ hU d
    have hw : w ∈ U := hh ▸ hU (R.edgeInv d)
    dsimp only [label]
    rw [dif_pos hv, dif_pos hw]
    apply congrArg Sum.inl
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := N.toSimpleGraph)
      ⟨fun he => hne (congrArg Subtype.val he), d, Subtype.ext hd, Subtype.ext hh⟩
  let forward : R.Component → N.Component ⊕ {v // v ∉ U} :=
    Quot.lift label (by
      intro v w h
      obtain ⟨p⟩ := h
      induction p with
      | nil => rfl
      | cons h p ih => exact (adj_label h).trans ih)
  let inclusion : N.toSimpleGraph →g R.toSimpleGraph :=
    { toFun := Subtype.val
      map_rel' := by
        rintro v w ⟨hne, d, hd, hh⟩
        exact ⟨fun he => hne (Subtype.ext he), d,
          congrArg Subtype.val hd, congrArg Subtype.val hh⟩ }
  let backward : N.Component ⊕ {v // v ∉ U} → R.Component :=
    Sum.elim (SimpleGraph.ConnectedComponent.map inclusion)
      (fun v => R.toSimpleGraph.connectedComponentMk v.val)
  refine ⟨forward, backward, ?_, ?_⟩
  · intro K
    induction K using Quot.inductionOn with
    | h v =>
      change backward (label v) = _
      dsimp only [label]
      split <;> rfl
  · intro K
    cases K with
    | inl K =>
      induction K using Quot.inductionOn with
      | h v =>
        change label v.val = _
        dsimp only [label]
        rw [dif_pos v.property]
        rfl
    | inr v =>
      change label v.val = _
      dsimp only [label]
      rw [dif_neg v.property]

-- @node: RotationSystem.restrictVertices_punctureEquiv
/-- For [a rotation system](hyp:R) and [a retained vertex set](hyp:U) that
[contains every directed-edge tail](hyp:hU), the [puncture correspondence](goal)
identifies original punctures with either punctures of the restricted system or
individual omitted vertices. -/
noncomputable def restrictVertices_punctureEquiv :
    R.Puncture ≃ (R.restrictVertices U hU).Puncture ⊕ {v // v ∉ U} where
  toFun v := if hv : v.val ∈ U then
    Sum.inl ⟨⟨v.val, hv⟩, fun d hd => v.property d (congrArg Subtype.val hd)⟩
    else Sum.inr ⟨v.val, hv⟩
  invFun := Sum.elim
    (fun v => ⟨v.val.val, fun d hd => v.property d (Subtype.ext hd)⟩)
    (fun v => ⟨v.val, fun d hd => v.property (hd ▸ hU d)⟩)
  left_inv v := by dsimp; split <;> rfl
  right_inv v := by
    cases v with
    | inl v => dsimp; rw [dif_pos v.val.property]; rfl
    | inr v => dsimp; rw [dif_neg v.property]

-- @node: RotationSystem.restrictVertices_componentEuler
/-- If every directed-edge tail lies in the retained vertex set and
[the original rotation system satisfies Euler's formula on each connected component](hyp:hR),
then [the system obtained by removing the omitted isolated vertices also satisfies
Euler's formula on each connected component](goal). -/
lemma restrictVertices_componentEuler (hR : R.componentEuler) :
    (R.restrictVertices U hU).componentEuler := by
  let N := R.restrictVertices U hU
  apply N.componentEuler_of_global_card
  have h := R.componentEuler_global_card hR
  have hv := Nat.card_congr (Equiv.sumCompl (fun v : R.Vertex => v ∈ U))
  have hc := Nat.card_congr (R.restrictVertices_componentEquiv U hU)
  have hp := Nat.card_congr (R.restrictVertices_punctureEquiv U hU)
  rw [Nat.card_sum] at hv hc hp
  change Nat.card R.Puncture = Nat.card N.Puncture + Nat.card {v // v ∉ U} at hp
  change Nat.card R.Component = Nat.card N.Component + Nat.card {v // v ∉ U} at hc
  have hb : Nat.card R.LocalBoundary = Nat.card N.LocalBoundary + Nat.card {v // v ∉ U} := by
    change Nat.card (R.FaceOrbit ⊕ R.Puncture) =
      Nat.card (R.FaceOrbit ⊕ N.Puncture) + Nat.card {v // v ∉ U}
    rw [Nat.card_sum, Nat.card_sum, hp]
    omega
  change Nat.card U + Nat.card N.LocalBoundary = Nat.card R.Edge + 2 * Nat.card N.Component
  change Nat.card U + Nat.card {v // v ∉ U} = Nat.card R.Vertex at hv
  omega

end RotationSystem
end OaiPairedStatesHamiltonian
