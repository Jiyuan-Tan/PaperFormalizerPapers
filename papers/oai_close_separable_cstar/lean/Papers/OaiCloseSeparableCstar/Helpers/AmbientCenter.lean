module

public import Papers.OaiCloseSeparableCstar.Helpers.AmbientCommutant
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-! # Scalar center: conjugacy invariance in the regular Hilbert space -/

public section

namespace Papers.OaiCloseSeparableCstar

/-- If [a free-group element is not the identity](hyp:hx) and [the generator with
index n does not occur in its reduced word](hyp:hn), then [conjugating the element
by that generator prepends the positive generator and appends its inverse to the
reduced word, without cancellation](goal). -/
-- @node: fresh_conjugate_toWord
lemma fresh_conjugate_toWord (x : FG) (hx : x ≠ 1) (n : ℕ)
    (hn : n ∉ x.toWord.map Prod.fst) :
    (gen n * x * (gen n)⁻¹).toWord = (n, true) :: (x.toWord ++ [(n, false)]) := by
  have htail : FreeGroup.IsReduced (x.toWord ++ [(n, false)]) := by
    apply List.IsChain.append FreeGroup.isReduced_toWord (.singleton _)
    intro a ha b hb hab
    have hb' : b = (n, false) := by simpa using hb.symm
    subst b
    exact False.elim (hn (List.mem_map.mpr ⟨a, List.mem_of_mem_getLast? ha, hab⟩))
  have hr : FreeGroup.IsReduced ((n, true) :: (x.toWord ++ [(n, false)])) := by
    apply List.IsChain.cons htail
    intro a ha hna
    have hne : x.toWord ≠ [] := fun h => hx (FreeGroup.toWord_eq_nil_iff.mp h)
    have ham : a ∈ x.toWord := by
      cases hw : x.toWord with
      | nil => exact False.elim (hne hw)
      | cons b l =>
        simp only [hw, List.cons_append, List.head?_cons, Option.mem_some_iff] at ha
        subst a
        simp
    exact False.elim (hn (List.mem_map.mpr ⟨a, ham, hna.symm⟩))
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mul, FreeGroup.toWord_of,
    FreeGroup.toWord_inv, FreeGroup.toWord_of]
  change FreeGroup.reduce (FreeGroup.reduce ([(n, true)] ++ x.toWord) ++ [(n, false)]) = _
  calc
    _ = FreeGroup.reduce (([(n, true)] ++ x.toWord) ++ [(n, false)]) := by
      simpa only [FreeGroup.reduce_singleton] using
        (FreeGroup.reduce_append_reduce_reduce (L₁ := [(n, true)] ++ x.toWord)
          (L₂ := [(n, false)]))
    _ = _ := hr.reduce_eq

/-- If [a square-summable function on the free group is invariant under
conjugation](hyp:hv) and [x is not the identity](hyp:hx), then [the function vanishes
at x](goal). -/
-- @node: conjugation_invariant_support
lemma conjugation_invariant_support (v : KSp)
    (hv : ∀ g x : FG, v (g * x * g⁻¹) = v x) (x : FG) (hx : x ≠ 1) : v x = 0 := by
  classical
  let A : Set ℕ := {n | n ∉ x.toWord.map Prod.fst}
  have hA : A.Infinite := by
    exact (List.finite_toSet (x.toWord.map Prod.fst)).infinite_compl
  have : Infinite A := Set.infinite_coe_iff.mpr hA
  let f : A → FG := fun n => gen n.val * x * (gen n.val)⁻¹
  have hf : Function.Injective f := by
    intro n m h
    apply Subtype.ext
    have he := congrArg FreeGroup.toWord h
    rw [fresh_conjugate_toWord x hx n.val n.property,
      fresh_conjugate_toWord x hx m.val m.property] at he
    exact congrArg Prod.fst (List.cons.inj he).1
  have hs := ((lp.memℓp v).summable (by norm_num)).comp_injective hf
  have hc : Summable (fun _ : A => ‖v x‖ ^ (2 : ENNReal).toReal) := by
    simpa only [Function.comp_def, f, hv] using hs
  have hz : ‖v x‖ ^ (2 : ENNReal).toReal = 0 := by
    by_contra hn
    exact Set.infinite_univ (Set.Finite.of_summable_const
      (lt_of_le_of_ne (by positivity) (Ne.symm hn)) hc)
  norm_num at hz
  exact hz

/-- [Left regular translation by any group element commutes with right regular
translation by any group element](goal). -/
-- @node: leftReg_commutes_rightReg
lemma leftReg_commutes_rightReg (g h : FG) :
    (leftReg g : Op KSp) * (rightReg h : Op KSp) =
      (rightReg h : Op KSp) * (leftReg g : Op KSp) := by
  ext v x
  change v ((g⁻¹ * x) * h) = v (g⁻¹ * (x * h))
  rw [mul_assoc]

/-- If [a bounded operator commutes with every left regular translation](hyp:hl)
and [with every right regular translation](hyp:hr), then [its image of the identity
basis vector is invariant under conjugation of the group coordinate](goal). -/
-- @node: regular_bicommuting_column
lemma regular_bicommuting_column (Y : Op KSp)
    (hl : ∀ g, (leftReg g : Op KSp) * Y = Y * (leftReg g : Op KSp))
    (hr : ∀ g, (rightReg g : Op KSp) * Y = Y * (rightReg g : Op KSp)) :
    ∀ g x : FG, (Y (delta 1)) (g * x * g⁻¹) = (Y (delta 1)) x := by
  intro g x
  have hc : (leftReg g : Op KSp) * (rightReg g : Op KSp) * Y =
      Y * ((leftReg g : Op KSp) * (rightReg g : Op KSp)) := by
    rw [mul_assoc, hr, ← mul_assoc, hl, mul_assoc]
  have hd : ((leftReg g : Op KSp) * (rightReg g : Op KSp)) (delta 1) = delta 1 := by
    change (leftReg g : Op KSp) ((rightReg g : Op KSp) (delta 1)) = _
    simp
  have he := congrArg (fun A : Op KSp => A (delta 1) (g * x * g⁻¹)) hc
  change (Y (delta 1)) ((g⁻¹ * (g * x * g⁻¹)) * g) =
    (Y (((leftReg g : Op KSp) * (rightReg g : Op KSp)) (delta 1))) (g * x * g⁻¹) at he
  rw [hd] at he
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
    inv_mul_cancel, mul_one] using he.symm

/-- If [a bounded operator commutes with every left regular translation](hyp:hl)
and [with every right regular translation](hyp:hr), then [it is a complex scalar
multiple of the identity operator](goal). -/
-- @node: regular_bicommuting_scalar
lemma regular_bicommuting_scalar (Y : Op KSp)
    (hl : ∀ g, (leftReg g : Op KSp) * Y = Y * (leftReg g : Op KSp))
    (hr : ∀ g, (rightReg g : Op KSp) * Y = Y * (rightReg g : Op KSp)) :
    ∃ c : ℂ, Y = c • (1 : Op KSp) := by
  let c : ℂ := Y (delta 1) 1
  have hd : Y (delta 1) = c • delta 1 := by
    ext x
    by_cases hx : x = 1
    · subst x; simp [c, delta]
    · rw [conjugation_invariant_support _ (regular_bicommuting_column Y hl hr) x hx]
      simp [delta, lp.single_apply, hx]
  refine ⟨c, ?_⟩
  apply lp.ext_continuousLinearMap (by norm_num)
  intro x
  apply ContinuousLinearMap.ext
  intro z
  apply lp.ext
  funext i
  have hz : (lp.single 2 x z : KSp) = z • delta x := by
    ext j
    by_cases hj : j = x
    · subst j; simp [delta]
    · simp [delta, lp.single_apply, hj]
  have hcol : Y (delta x) = c • delta x := by
    have he := congrArg (fun A : Op KSp => A (delta 1)) (hl x)
    change (leftReg x : Op KSp) (Y (delta 1)) = Y ((leftReg x : Op KSp) (delta 1)) at he
    simpa only [hd, map_smul, leftReg_delta, mul_one] using he.symm
  change (Y (lp.single 2 x z)) i = ((c • (1 : Op KSp)) (lp.single 2 x z)) i
  rw [hz, map_smul, hcol]
  simp [smul_smul, mul_comm]

/-- If [the first-factor extensions of two bounded operators commute on the tensor
Hilbert space](hyp:h), then [the original operators commute](goal). -/
-- @node: firstFactor_commute_reflect
lemma firstFactor_commute_reflect (Y Z : Op KSp)
    (h : (flipOp * constantDiagOp Y * flipOp) *
        (flipOp * constantDiagOp Z * flipOp) =
      (flipOp * constantDiagOp Z * flipOp) *
        (flipOp * constantDiagOp Y * flipOp)) : Y * Z = Z * Y := by
  have he := congrArg (fun A : Op LSp => flipOp * A * flipOp) h
  simp only [mul_assoc, ← mul_assoc flipOp flipOp, flipOp_mul_self,
    one_mul, mul_one] at he
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext i
  exact congrArg (fun A : Op LSp => A (lp.single 2 (1 : FG) v) 1 i) he

/-- [Right regular translation on the first tensor factor commutes with every
element of the ambient algebra associated with any unitary representation](goal). -/
-- @node: firstFactor_rightReg_mem_commutant
lemma firstFactor_rightReg_mem_commutant (π : FG →* unitary (Op KSp)) (g : FG) :
    flipOp * constantDiagOp (rightReg g : Op KSp) * flipOp ∈ commutant (Dalg π) := by
  rw [Dalg_commutant_eq]
  refine ⟨(rightReg g : Op KSp), ?_, rfl⟩
  rintro _ ⟨h, rfl⟩
  exact leftReg_commutes_rightReg h g

/-- [Every element of the ambient algebra that commutes with all its elements is a
complex scalar multiple of the identity operator](goal). -/
-- @node: Dalg_scalar_center
lemma Dalg_scalar_center (π : FG →* unitary (Op KSp)) : SequencesCenter (Dalg π) := by
  intro T hTD hcentral
  have hTc : T ∈ commutant (Dalg π) := by
    intro a ha
    exact (hcentral a ha).symm
  rw [Dalg_commutant_eq] at hTc
  obtain ⟨Y, hY, rfl⟩ := hTc
  have hl (g : FG) : (leftReg g : Op KSp) * Y = Y * (leftReg g : Op KSp) :=
    hY _ ⟨g, rfl⟩
  have hr (g : FG) : (rightReg g : Op KSp) * Y = Y * (rightReg g : Op KSp) := by
    apply firstFactor_commute_reflect
    exact ((firstFactor_rightReg_mem_commutant π g) _ hTD).symm
  obtain ⟨c, hc⟩ := regular_bicommuting_scalar Y hl hr
  refine ⟨c, ?_⟩
  rw [hc]
  ext v x y
  rfl

end Papers.OaiCloseSeparableCstar
