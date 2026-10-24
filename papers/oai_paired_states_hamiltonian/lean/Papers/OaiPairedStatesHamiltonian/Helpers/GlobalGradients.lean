module

public import Papers.OaiPairedStatesHamiltonian.Helpers.ComponentEulerBound
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Global facial potentials and the full gradient decomposition on a sphere map.
The placement tree glues the constants on local boundaries, including punctures. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace RotationSystem

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

-- @node: RotationSystem.sum_invInvariant
/-- If [a real value on darts is unchanged by reversing a dart](hyp:hq), then
[the sum over all darts is twice the sum of the values at one representative dart per edge](goal). -/
lemma sum_invInvariant (R : RotationSystem) (q : R.Dart → ℝ)
    (hq : ∀ d, q (R.edgeInv d) = q d) :
    (∑ d, q d) = 2 * ∑ e : R.Edge, q (R.edgeRepresentative e) := by
  have factor (d : R.Dart) : q d = q (R.edgeRepresentative (R.edgeOf d)) := by
    rcases (R.edgeOf_eq_iff (R.edgeRepresentative (R.edgeOf d)) d).mp
      (R.edgeRepresentative_spec _) with h | h
    · exact congrArg q h
    · exact (congrArg q h).trans (hq _)
  have hf (e : R.Edge) : (Finset.univ.filter (fun d => R.edgeOf d = e)).card = 2 := by
    obtain ⟨d, rfl⟩ := Quotient.exists_rep e
    have hset : Finset.univ.filter (fun x => R.edgeOf x = R.edgeOf d) =
        {d, R.edgeInv d} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [eq_comm, R.edgeOf_eq_iff]
    change (Finset.univ.filter (fun x => R.edgeOf x = R.edgeOf d)).card = 2
    rw [hset, Finset.card_pair (R.edgeInv_fixedPointFree d).symm]
  have hs := Finset.sum_fiberwise_eq_sum_filter'
    (Finset.univ : Finset R.Dart) (Finset.univ : Finset R.Edge) R.edgeOf
    (fun e => q (R.edgeRepresentative e))
  simp only [Finset.mem_univ, Finset.filter_true, Finset.sum_const, hf,
    nsmul_eq_mul, Nat.cast_ofNat] at hs
  rw [← Finset.mul_sum] at hs
  exact (Finset.sum_congr rfl (fun d _ => factor d)).trans hs.symm

-- @node: RotationSystem.edgeGradients_orthogonal
/-- For any real vertex and face-orbit potentials, [the sum over edges of the product of
their vertex and facial gradients, evaluated at representative darts, is zero](goal). -/
lemma edgeGradients_orthogonal (R : RotationSystem) (a : R.Vertex → ℝ)
    (b : R.FaceOrbit → ℝ) :
    (∑ e : R.Edge, R.vertexGradient a (R.edgeRepresentative e) *
      R.facialGradient b (R.edgeRepresentative e)) = 0 := by
  have h := R.sum_invInvariant (fun d => R.vertexGradient a d * R.facialGradient b d)
    (by intro d; rw [R.vertexGradient_inv, R.facialGradient_inv, neg_mul_neg])
  rw [R.gradients_orthogonal] at h
  linarith

end RotationSystem

namespace SphereMap

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (M : SphereMap)

-- @node: SphereMap.face_nonempty
/-- [Every sphere map has at least one face](goal). -/
lemma face_nonempty : Nonempty M.Face := by
  obtain ⟨x⟩ := M.placement_connected.nonempty
  cases x with
  | inr f => exact ⟨f⟩
  | inl K =>
    obtain ⟨v, hv⟩ := K.exists_rep
    by_cases hd : ∃ d, M.vert d = v
    · exact ⟨M.faceOf (Classical.choose hd)⟩
    · exact ⟨M.boundaryFace (Sum.inr ⟨v, fun d he => hd ⟨d, he⟩⟩)⟩

-- @node: SphereMap.globalFacialGradient_zero_constant
/-- If [a real potential on the global faces has zero facial gradient on every dart](hyp:hb),
then [its values at any two global faces are equal](goal). -/
lemma globalFacialGradient_zero_constant (b : M.Face → ℝ)
    (hb : ∀ d, M.facialGradient (fun f => b (M.boundaryFace (Sum.inl f))) d = 0)
    (f g : M.Face) : b f = b g := by
  let label : M.Component ⊕ M.Face → ℝ := Sum.elim
    (fun K => b (M.boundaryFace (M.componentBoundaryRepresentative K))) b
  have boundary (a : M.LocalBoundary) : label (Sum.inl (M.compOf a)) =
      label (Sum.inr (M.boundaryFace a)) := by
    exact M.boundaryPotential_zero_sameComponent (fun a => b (M.boundaryFace a)) hb
      _ a (M.componentBoundaryRepresentative_spec _)
  have adj {x y} (h : M.placementGraph.Adj x y) : label x = label y := by
    cases x with
    | inl K =>
      cases y with
      | inl L => exact h.elim
      | inr f => obtain ⟨a, rfl, rfl⟩ := h; exact boundary a
    | inr f =>
      cases y with
      | inr g => exact h.elim
      | inl K => obtain ⟨a, rfl, rfl⟩ := h; exact (boundary a).symm
  obtain ⟨p⟩ := M.placement_connected.preconnected (Sum.inr f) (Sum.inr g)
  have walk {x y} (p : M.placementGraph.Walk x y) : label x = label y := by
    induction p with
    | nil => rfl
    | cons h p ih => exact (adj h).trans ih
  exact walk p

-- @node: SphereMap.globalMixedGradient
/-- For a [sphere map](hyp:M), the [global mixed-gradient linear map](goal) sends a pair of
real vertex and global-face potentials to their summed vertex and facial gradients on edges,
using the global face incident to each local face boundary. -/
noncomputable def globalMixedGradient :
    ((M.Vertex → ℝ) × (M.Face → ℝ)) →ₗ[ℝ] (M.Edge → ℝ) where
  toFun x := M.mixedGradient (x.1, fun f => x.2 (M.boundaryFace (Sum.inl f)))
  map_add' x y := by
    funext e
    simp only [RotationSystem.mixedGradient, RotationSystem.vertexGradient,
      RotationSystem.facialGradient, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    ring
  map_smul' c x := by
    funext e
    simp only [RotationSystem.mixedGradient, RotationSystem.vertexGradient,
      RotationSystem.facialGradient, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring

-- @node: SphereMap.globalMixedGradient_surjective
/-- [Every real assignment to the edges of a sphere map is the sum of a vertex gradient and
a facial gradient arising from a potential on its global faces](goal). -/
lemma globalMixedGradient_surjective : Function.Surjective M.globalMixedGradient := by
  let : Nonempty M.Face := M.face_nonempty
  let f0 : M.Face := Classical.arbitrary _
  let ev : LinearMap.ker M.globalMixedGradient →ₗ[ℝ] ((M.Component → ℝ) × ℝ) :=
    { toFun := fun x => (fun K => x.val.1 (M.componentVertexRepresentative K), x.val.2 f0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hevinj : Function.Injective ev := by
    intro x y he
    have hx := M.mixedGradient_ker_gradients_zero
      (x.val.1, fun f => x.val.2 (M.boundaryFace (Sum.inl f))) x.property
    have hy := M.mixedGradient_ker_gradients_zero
      (y.val.1, fun f => y.val.2 (M.boundaryFace (Sum.inl f))) y.property
    apply Subtype.ext
    apply Prod.ext
    · funext v
      let K := M.toSimpleGraph.connectedComponentMk v
      have hK : M.toSimpleGraph.connectedComponentMk v =
          M.toSimpleGraph.connectedComponentMk (M.componentVertexRepresentative K) :=
        (M.componentVertexRepresentative_spec K).symm
      exact (M.vertexGradient_zero_sameComponent x.val.1 hx.1 _ _ hK).trans
        ((congrFun (congrArg Prod.fst he) K).trans
          (M.vertexGradient_zero_sameComponent y.val.1 hy.1 _ _ hK).symm)
    · funext f
      exact (M.globalFacialGradient_zero_constant x.val.2 hx.2 f f0).trans
        ((congrArg Prod.snd he).trans
          (M.globalFacialGradient_zero_constant y.val.2 hy.2 f0 f))
  have hk := LinearMap.finrank_le_finrank_of_injective hevinj
  have hr := Submodule.finrank_le M.globalMixedGradient.range
  have hn := LinearMap.finrank_range_add_finrank_ker M.globalMixedGradient
  have he := M.global_euler
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi] at hk hr hn
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simp only [Module.finrank_pi]
  omega

end SphereMap
end OaiPairedStatesHamiltonian
