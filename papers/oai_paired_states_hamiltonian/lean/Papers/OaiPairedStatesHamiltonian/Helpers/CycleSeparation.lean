module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CycleGluing
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! A simple cycle has a nonempty opposite side, by finite sphere cohomology. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

open Classical
attribute [local instance] propDecidable
set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false

namespace RotationSystem

-- @node: RotationSystem.mixedGradient_surjective_of_euler
/-- For a rotation system with at least one dart, if [the underlying graph is connected](hyp:hR)
and [the number of vertices plus
the number of face orbits equals the number of edges plus two](hyp:he), then
[every real edge assignment is the sum of a vertex gradient and a facial gradient](goal). -/
lemma mixedGradient_surjective_of_euler (R : RotationSystem) [Nonempty R.Dart]
    (hR : R.toSimpleGraph.Connected)
    (he : Fintype.card R.Vertex + Fintype.card R.FaceOrbit = Fintype.card R.Edge + 2) :
    Function.Surjective R.mixedGradient := by
  let : Nonempty R.Vertex := hR.nonempty
  let v0 := Classical.arbitrary R.Vertex
  let f0 : R.FaceOrbit := orbitOf R.facePerm (Classical.arbitrary R.Dart)
  let ev : LinearMap.ker R.mixedGradient →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun x => (x.val.1 v0, x.val.2 f0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hevinj : Function.Injective ev := by
    intro x y h
    have hx := R.mixedGradient_ker_constants hR x.val x.property
    have hy := R.mixedGradient_ker_constants hR y.val y.property
    apply Subtype.ext
    apply Prod.ext
    · funext v
      exact (hx.1 v v0).trans ((congrArg Prod.fst h).trans (hy.1 v0 v))
    · funext f
      exact (hx.2 f f0).trans ((congrArg Prod.snd h).trans (hy.2 f0 f))
  have hk := LinearMap.finrank_le_finrank_of_injective hevinj
  have hr := Submodule.finrank_le R.mixedGradient.range
  have hn := LinearMap.finrank_range_add_finrank_ker R.mixedGradient
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi] at hk hr hn ⊢
  omega

end RotationSystem
namespace SphereMap
variable (M : SphereMap)

-- @node: SphereMap.cycle_vertexGradient_sum
/-- [The sum of any real vertex potential's gradient around a simple cycle is zero](goal). -/
lemma cycle_vertexGradient_sum (C : M.Cycle) (a : M.Vertex → ℝ) :
    (∑ d ∈ C.val.toFinset, M.toRotationSystem.vertexGradient a d) = 0 := by
  have sum_get (f : M.Dart → ℝ) :
      (∑ d ∈ C.val.toFinset, f d) = ∑ i : Fin C.val.length, f (C.val.get i) := by
    symm
    apply Finset.sum_bij (fun i _ => C.val.get i)
    · intro i hi
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · intro i hi j hj hij
      exact (C.property.2.of_map M.vert).injective_get hij
    · intro d hd
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hd)
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · intro i hi
      rfl
  rw [sum_get]
  simp only [RotationSystem.vertexGradient, Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  have hstep (i : Fin C.val.length) :
      M.head (C.val.get i) = M.vert (C.val.get (finRotate C.val.length i)) := by
    have hn : finRotate C.val.length i =
        ⟨(i.val + 1) % C.val.length, M.nextIndex_lt C.val i⟩ := by
      apply Fin.ext
      simp [finRotate_apply, Fin.val_add, Nat.add_mod]
    rw [hn]
    exact C.property.1.2.2 i
  simp_rw [hstep]
  exact Equiv.sum_comp (finRotate C.val.length) (fun i => a (M.vert (C.val.get i)))

-- @node: SphereMap.cycleFlow
/-- For [a sphere map](hyp:M), [a simple cycle](hyp:C), and [a dart](hyp:d),
the [cycle flow at that dart](goal) counts its occurrence in the cycle positively
and its reverse's occurrence negatively. -/
noncomputable def cycleFlow (C : M.Cycle) (d : M.Dart) : ℝ :=
  ∑ e ∈ C.val.toFinset, ((if d = e then 1 else 0) - (if d = M.edgeInv e then 1 else 0))

-- @node: SphereMap.cycleFlow_inv
/-- [Reversing a dart negates its cycle flow](goal). -/
lemma cycleFlow_inv (C : M.Cycle) (d : M.Dart) :
    M.cycleFlow C (M.edgeInv d) = -M.cycleFlow C d := by
  have h (e : M.Dart) : M.edgeInv d = e ↔ d = M.edgeInv e := by
    constructor <;> intro he
    · exact (congrArg M.edgeInv he).symm.trans (M.edgeInv_involutive d) |>.symm
    · rw [he, M.edgeInv_involutive]
  have h' (e : M.Dart) : M.edgeInv d = M.edgeInv e ↔ d = e := M.edgeInv.injective.eq_iff
  simp only [cycleFlow, h, h', ← Finset.sum_neg_distrib, neg_sub]
  apply Finset.sum_congr rfl
  intro e he
  rw [M.edgeInv_involutive]

-- @node: SphereMap.cycleFlow_vertexGradient_orthogonal
/-- [The sum over all darts of the product of a vertex gradient and a cycle flow is zero](goal). -/
lemma cycleFlow_vertexGradient_orthogonal (C : M.Cycle) (a : M.Vertex → ℝ) :
    (∑ d : M.Dart, M.toRotationSystem.vertexGradient a d * M.cycleFlow C d) = 0 := by
  simp only [cycleFlow, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (e : M.Dart) :
      (∑ d : M.Dart, M.toRotationSystem.vertexGradient a d *
        ((if d = e then 1 else 0) - (if d = M.edgeInv e then 1 else 0))) =
        2 * M.toRotationSystem.vertexGradient a e := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, RotationSystem.vertexGradient_inv]
    ring
  simp_rw [h]
  rw [← Finset.mul_sum, M.cycle_vertexGradient_sum, mul_zero]


-- @node: SphereMap.cycleFlow_eq
/-- [The cycle flow at a dart equals the indicator that the dart belongs to the
cycle minus the indicator that its reverse belongs to the cycle](goal). -/
lemma cycleFlow_eq (C : M.Cycle) (d : M.Dart) :
    M.cycleFlow C d = (if d ∈ C.val then 1 else 0) -
      (if M.edgeInv d ∈ C.val then 1 else 0) := by
  have hi (e : M.Dart) : d = M.edgeInv e ↔ e = M.edgeInv d := by
    constructor <;> intro h
    · exact ((congrArg M.edgeInv h).trans (M.edgeInv_involutive e)).symm
    · rw [h, M.edgeInv_involutive]
  simp only [cycleFlow, Finset.sum_sub_distrib, hi]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

-- @node: SphereMap.cycle_inv_not_mem
/-- If [a dart belongs to a simple cycle](hyp:hd), then
[its reverse does not belong to that cycle](goal). -/
lemma cycle_inv_not_mem (C : M.Cycle) (d : M.Dart) (hd : d ∈ C.val) :
    M.edgeInv d ∉ C.val := by
  intro hi
  have he := (M.edgeOf_eq_iff d (M.edgeInv d)).mpr (Or.inr rfl)
  have hn := List.inj_on_of_nodup_map C.property.1.2.1 hd hi he
  exact M.edgeInv_fixedPointFree d hn.symm

-- @node: SphereMap.cycleFlow_eq_one
/-- If [a dart belongs to a simple cycle](hyp:hd), then
[the cycle flow at that dart is one](goal). -/
lemma cycleFlow_eq_one (C : M.Cycle) (d : M.Dart) (hd : d ∈ C.val) :
    M.cycleFlow C d = 1 := by
  rw [M.cycleFlow_eq, if_pos hd, if_neg (M.cycle_inv_not_mem C d hd), sub_zero]

-- @node: SphereMap.cycleFlow_eq_zero
/-- If [the edge underlying a dart does not occur in the cycle](hyp:hd), then
[the cycle flow at that dart is zero](goal). -/
lemma cycleFlow_eq_zero (C : M.Cycle) (d : M.Dart)
    (hd : M.edgeOf d ∉ C.val.map M.edgeOf) : M.cycleFlow C d = 0 := by
  have hn : d ∉ C.val := fun h => hd (List.mem_map.mpr ⟨d, h, rfl⟩)
  have hi : M.edgeInv d ∉ C.val := by
    intro h
    apply hd
    exact List.mem_map.mpr ⟨M.edgeInv d, h,
      (M.edgeOf_eq_iff (M.edgeInv d) d).mpr (Or.inr (M.edgeInv_involutive d).symm)⟩
  rw [M.cycleFlow_eq, if_neg hn, if_neg hi, sub_self]

-- @node: SphereMap.cycleFlow_facial_potential
/-- If [the sphere map is connected](hyp:hM), then [there is a real potential on
faces whose value on the face of each dart minus its value on the face of the
reverse dart equals the cycle flow](goal). -/
lemma cycleFlow_facial_potential (hM : M.IsConnectedMap) (C : M.Cycle) :
    ∃ b : M.Face → ℝ, ∀ d,
      b (M.faceOf d) - b (M.faceOf (M.edgeInv d)) = M.cycleFlow C d := by
  obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  let : Nonempty M.Dart := ⟨d0⟩
  obtain ⟨q, hq⟩ := M.exists_faceEquivOrbit hM
  have he : Fintype.card M.Vertex + Fintype.card M.FaceOrbit = Fintype.card M.Edge + 2 := by
    rw [← Fintype.card_congr q]
    exact M.connected_euler hM
  obtain ⟨x, hx⟩ := M.toRotationSystem.mixedGradient_surjective_of_euler hM he
    (fun e => M.cycleFlow C (M.toRotationSystem.edgeRepresentative e))
  have hd (d : M.Dart) : M.toRotationSystem.vertexGradient x.1 d +
      M.toRotationSystem.facialGradient x.2 d = M.cycleFlow C d := by
    let r := M.toRotationSystem.edgeRepresentative (M.edgeOf d)
    have hr : M.edgeOf r = M.edgeOf d := M.toRotationSystem.edgeRepresentative_spec _
    have hz : M.toRotationSystem.vertexGradient x.1 r +
        M.toRotationSystem.facialGradient x.2 r = M.cycleFlow C r := congrFun hx _
    rcases (M.edgeOf_eq_iff r d).mp hr with h | h
    · simpa only [h] using hz
    · rw [h, RotationSystem.vertexGradient_inv, RotationSystem.facialGradient_inv,
        M.cycleFlow_inv]
      linarith
  have hs : (∑ d : M.Dart, (M.toRotationSystem.vertexGradient x.1 d)^2) = 0 := by
    have ho := M.cycleFlow_vertexGradient_orthogonal C x.1
    simp_rw [← hd] at ho
    simp only [mul_add, Finset.sum_add_distrib,
      M.toRotationSystem.gradients_orthogonal, add_zero, ← pow_two] at ho
    exact ho
  have hv (d : M.Dart) : M.toRotationSystem.vertexGradient x.1 d = 0 := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun d _ => sq_nonneg (M.toRotationSystem.vertexGradient x.1 d))).mp hs d
      (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp hz
  refine ⟨fun f => x.2 (q f), ?_⟩
  intro d
  change x.2 (q (M.faceOf d)) - x.2 (q (M.faceOf (M.edgeInv d))) = _
  rw [hq d, hq (M.edgeInv d)]
  have hh := hd d
  rw [hv d, zero_add] at hh
  exact hh


-- @node: SphereMap.exists_face_outside_cycle_leftRegion
/-- If [the sphere map is connected](hyp:hM), then
[some face lies outside the left region of the simple cycle](goal). -/
lemma exists_face_outside_cycle_leftRegion (hM : M.IsConnectedMap) (C : M.Cycle) :
    ∃ f : M.Face, f ∉ M.leftRegion C := by
  obtain ⟨b, hb⟩ := M.cycleFlow_facial_potential hM C
  obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil C.val C.property.1.1
  obtain ⟨f, _, hf⟩ := Finset.exists_min_image (Finset.univ : Finset M.Face) b
    ⟨M.faceOf d0, Finset.mem_univ _⟩
  refine ⟨f, ?_⟩
  rintro ⟨c, ⟨d, hd, hp⟩, hc⟩
  have hprop {u v : M.LocalBoundary} (p : M.localBoundariesJoinedAvoiding C.val u v) :
      b (M.boundaryFace u) = b (M.boundaryFace v) := by
    induction p with
    | refl => rfl
    | tail p h ih =>
      obtain ⟨e, he, hu, hv⟩ := h
      have hz := hb e
      rw [M.cycleFlow_eq_zero C e he] at hz
      have hs := sub_eq_zero.mp hz
      change b (M.boundaryFace (Sum.inl (orbitOf M.facePerm e))) =
        b (M.boundaryFace (Sum.inl (orbitOf M.facePerm (M.edgeInv e)))) at hs
      rw [hu, hv] at hs
      exact ih.trans hs
  have hleft : b (M.faceOf d) = b f :=
    (hprop hp).trans (congrArg b (M.faceBehind_connected hM _ c f hc))
  have hdrop := hb d
  rw [M.cycleFlow_eq_one C d hd, hleft] at hdrop
  have hmin := hf (M.faceOf (M.edgeInv d)) (Finset.mem_univ _)
  linarith

end SphereMap
end OaiPairedStatesHamiltonian
