module

public import Papers.OaiPairedStatesHamiltonian.Helpers.RotationEquiv

/-! Edge-closed dart restrictions retain all vertices. Their rotation is the
single first return, and their componentwise Euler equations follow by deleting
one omitted edge at a time. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace RotationSystem

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (R : RotationSystem) (U : Set R.Dart)

-- @node: RotationSystem.restrictDarts_rot_vertex
/-- [The first return of rotation to a set of darts preserves the dart's vertex](goal). -/
lemma restrictDarts_rot_vertex (d : U) :
    R.vert (firstReturnPerm R.rot U d).val = R.vert d.val := by
  obtain ⟨n, hn, he, hmin⟩ := Classical.choose_spec (exists_firstReturnPerm R.rot U) d
  change (firstReturnPerm R.rot U d).val = (R.rot ^ n) d.val at he
  rw [he, R.rot_pow_vertex]

-- @node: RotationSystem.restrictDarts_rot_fibre
/-- [The first-return rotation acts as a single cycle on the retained darts
at each vertex](goal). -/
lemma restrictDarts_rot_fibre (v : R.Vertex) :
    (firstReturnPerm R.rot U).IsCycleOn {d : U | R.vert d.val = v} := by
  let q := firstReturnPerm R.rot U
  refine ⟨⟨?_, q.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (R.restrictDarts_rot_vertex U d).trans hd
  · intro d hd
    refine ⟨q.symm d, ?_, q.apply_symm_apply d⟩
    change R.vert (q.symm d).val = v
    rw [← R.restrictDarts_rot_vertex U (q.symm d), q.apply_symm_apply]
    exact hd
  · intro d hd e he
    exact sameCycle_firstReturnPerm R.rot U d e ((R.rot_fibre v).2 hd he)

-- @node: RotationSystem.restrictDarts
/-- For [a rotation system](hyp:R) and [a set of retained darts](hyp:U)
[closed under edge reversal](hyp:hU), the [restricted rotation system](goal)
keeps all vertices, restricts edge reversal, and rotates by first return to the
retained darts. -/
noncomputable def restrictDarts (hU : ∀ d, R.edgeInv d ∈ U ↔ d ∈ U) : RotationSystem where
  Vertex := R.Vertex
  Dart := U
  vert d := R.vert d.val
  edgeInv := R.edgeInv.subtypePerm hU
  edgeInv_involutive := by
    intro d
    apply Subtype.ext
    exact R.edgeInv_involutive d.val
  edgeInv_fixedPointFree := by
    intro d h
    exact R.edgeInv_fixedPointFree d.val (congrArg Subtype.val h)
  rot := firstReturnPerm R.rot U
  rot_vertex := R.restrictDarts_rot_vertex U
  rot_fibre := R.restrictDarts_rot_fibre U

-- @node: RotationSystem.restrictDarts_full_relabel
/-- For [a rotation system](hyp:R) and [a retained dart set](hyp:U) that is
[closed under edge reversal](hyp:hU) and [contains every dart](hyp:hall), the
[relabelling from the original system to its restriction](goal) identifies each
vertex and dart with itself. -/
noncomputable def restrictDarts_full_relabel
    (hU : ∀ d, R.edgeInv d ∈ U ↔ d ∈ U) (hall : ∀ d, d ∈ U) :
    R.Relabel (R.restrictDarts U hU) where
  vertex := Equiv.refl _
  dart := Equiv.ofBijective (fun d => (⟨d, hall d⟩ : U))
    ⟨fun a b h => congrArg Subtype.val h, fun d => ⟨d.val, Subtype.ext rfl⟩⟩
  vert _ := rfl
  inv _ := rfl
  rot d := by
    apply Subtype.ext
    change R.rot d = (firstReturnPerm R.rot U ⟨d, hall d⟩).val
    exact (firstReturnPerm_apply_of_spec R.rot U ⟨d, hall d⟩ 1 (by omega)
      (by simpa using hall (R.rot d)) (by intro m hm hmn; omega)).symm

-- @node: RotationSystem.restrictDarts_delete_relabel
/-- For [a rotation system](hyp:R), [a retained dart set](hyp:U)
[closed under edge reversal](hyp:hU), and [a dart marking an edge to delete](hyp:a)
[outside the retained set](hyp:ha), the [relabelling between deletion followed
by restriction and direct restriction](goal) identifies their vertices and darts. -/
noncomputable def restrictDarts_delete_relabel
    (hU : ∀ d, R.edgeInv d ∈ U ↔ d ∈ U) (a : R.Dart) (ha : a ∉ U) :
    ((R.deleteEdgeRotation a).restrictDarts {d | d.val ∈ U}
      (fun d => hU d.val)).Relabel (R.restrictDarts U hU) := by
  have hsub : U ⊆ R.deleteEdgeDarts a := by
    intro d hd
    refine ⟨fun he => ha (he ▸ hd), ?_⟩
    intro he
    have : R.edgeInv a ∈ U := he ▸ hd
    exact ha ((hU a).mp this)
  let e : {d : R.deleteEdgeDarts a // d.val ∈ U} ≃ U :=
    { toFun d := ⟨d.val.val, d.property⟩
      invFun d := ⟨⟨d.val, hsub d.property⟩, d.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  refine ⟨Equiv.refl _, e, fun _ => rfl, fun _ => rfl, ?_⟩
  intro d
  apply Subtype.ext
  exact firstReturnPerm_nested_apply R.rot (R.deleteEdgeDarts a) U hsub d

-- @node: RotationSystem.restrictDarts_componentEuler
/-- If [each component of the rotation system satisfies Euler's formula](hyp:hR)
and [the retained darts are closed under edge reversal](hyp:hU), then
[each component of the restricted system also satisfies Euler's formula](goal). -/
lemma restrictDarts_componentEuler (hR : R.componentEuler)
    (hU : ∀ d, R.edgeInv d ∈ U ↔ d ∈ U) : (R.restrictDarts U hU).componentEuler := by
  suffices ∀ n : ℕ, ∀ S : RotationSystem, Fintype.card S.Dart = n →
      S.componentEuler → ∀ V : Set S.Dart,
      ∀ hV : (∀ d, S.edgeInv d ∈ V ↔ d ∈ V), (S.restrictDarts V hV).componentEuler from
    this (Fintype.card R.Dart) R rfl hR U hU
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn hS V hV
    by_cases hall : ∀ d, d ∈ V
    · exact (S.restrictDarts_full_relabel V hV hall).componentEuler hS
    · obtain ⟨a, ha⟩ := not_forall.mp hall
      have hsmall : Fintype.card (S.deleteEdgeRotation a).Dart < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (fun h => h.1 rfl : a ∉ S.deleteEdgeDarts a)
      have hdel := S.deleteEdge_componentEuler a hS
      have hrec := ih (Fintype.card (S.deleteEdgeRotation a).Dart) hsmall
        (S.deleteEdgeRotation a) rfl hdel {d | d.val ∈ V} (fun d => hV d.val)
      exact (S.restrictDarts_delete_relabel V hV a ha).componentEuler hrec

end RotationSystem
end OaiPairedStatesHamiltonian
