module

public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.GroupAction.Quotient

/-! Counting functions with fixed fiber sizes by orbit-stabilizer. -/

public section

noncomputable section

open scoped BigOperators

namespace Papers.HawkesD75660b

open Classical in
-- @node: countFibers_orbit_iff
/-- [Two functions on a finite domain differ only by a permutation of their
inputs if and only if each output value has the same number of preimages
under both functions](goal). -/
lemma countFibers_orbit_iff {α β : Type*} [Fintype α] [DecidableEq β]
    (f g : α → β) :
    g ∈ MulAction.orbit (Equiv.Perm α)ᵈᵐᵃ f ↔
      ∀ b, Fintype.card {a // g a = b} = Fintype.card {a // f a = b} := by
  classical
  constructor
  · rintro ⟨p, rfl⟩ b
    exact Fintype.card_congr (Equiv.subtypeEquiv (DomMulAct.mk.symm p)
      (fun a => Iff.rfl))
  · intro h
    let e : α ≃ α := Equiv.ofFiberEquiv
      (fun b => Fintype.equivOfCardEq (h b))
    refine ⟨DomMulAct.mk e, ?_⟩
    funext a
    exact Equiv.ofFiberEquiv_map (fun b => Fintype.equivOfCardEq (h b)) a

open Classical in
-- @node: countFibers_card
/-- [The number of functions having the same preimage counts as f, multiplied
by the product of the factorials of those counts over all output values,
equals the factorial of the size of the domain](goal). -/
lemma countFibers_card {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) :
    Fintype.card {g : α → β // ∀ b,
      Fintype.card {a // g a = b} = Fintype.card {a // f a = b}} *
      (∏ b, (Fintype.card {a // f a = b}).factorial) =
        (Fintype.card α).factorial := by
  classical
  let : Fintype (Equiv.Perm α)ᵈᵐᵃ := Fintype.ofEquiv (Equiv.Perm α) DomMulAct.mk
  have ho := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := (Equiv.Perm α)ᵈᵐᵃ) f
  have horbit : Fintype.card (MulAction.orbit (Equiv.Perm α)ᵈᵐᵃ f) =
      Fintype.card {g : α → β // ∀ b,
        Fintype.card {a // g a = b} = Fintype.card {a // f a = b}} :=
    Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (countFibers_orbit_iff f))
  have hstab : Fintype.card (MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ f) =
      ∏ b, (Fintype.card {a // f a = b}).factorial := by
    let e : (MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ f) ≃
        {p : Equiv.Perm α // f ∘ p = f} :=
      Equiv.subtypeEquiv DomMulAct.mk.symm (fun _ => DomMulAct.mem_stabilizer_iff)
    rw [Fintype.card_congr e]
    exact DomMulAct.stabilizer_card f
  rw [horbit, hstab] at ho
  simpa only [Fintype.card_congr DomMulAct.mk.symm, Fintype.card_perm] using ho

open Classical in
-- @node: countFibers_exists
/-- If [the prescribed nonnegative counts k sum to the size of the finite
domain](hyp:hk), then [there exists a function from that domain to the finite
output set with exactly k preimages of each output value](goal). -/
lemma countFibers_exists {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (k : β → ℕ) (hk : ∑ b, k b = Fintype.card α) :
    ∃ f : α → β, ∀ b, Fintype.card {a // f a = b} = k b := by
  classical
  let e : α ≃ (Σ b, Fin (k b)) := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hk.symm)
  refine ⟨fun a => (e a).1, fun b => ?_⟩
  let eb : {a // (e a).1 = b} ≃ {x : (Σ b, Fin (k b)) // x.1 = b} :=
    Equiv.subtypeEquiv e (fun a => Iff.rfl)
  rw [Fintype.card_congr eb]
  let ec : {x : (Σ b, Fin (k b)) // x.1 = b} ≃ Fin (k b) :=
    { toFun := fun x => x.property ▸ x.val.2
      invFun := fun i => ⟨⟨b, i⟩, rfl⟩
      left_inv := by rintro ⟨⟨c, i⟩, h⟩; cases h; rfl
      right_inv := by intro i; rfl }
  simpa only [Fintype.card_fin] using Fintype.card_congr ec

open Classical in
-- @node: countFibers_prescribed_card
/-- If [the prescribed nonnegative counts k sum to the size of the finite
domain](hyp:hk), then [the number of functions with those preimage counts,
multiplied by the product of the factorials of the prescribed counts, equals
the factorial of the size of the domain](goal). -/
lemma countFibers_prescribed_card {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (k : β → ℕ) (hk : ∑ b, k b = Fintype.card α) :
    Fintype.card {f : α → β // ∀ b, Fintype.card {a // f a = b} = k b} *
      (∏ b, (k b).factorial) = (Fintype.card α).factorial := by
  classical
  obtain ⟨f, hf⟩ := countFibers_exists k hk
  simpa only [hf] using countFibers_card f

end Papers.HawkesD75660b
