module

public import Papers.OaiNearInclusionsVon.Helpers.CircleLaurent
public import Mathlib.Data.Nat.Dist

/-! Coordinate formulas and geometric decay on the finite root path. -/

public section

namespace Papers.OaiNearInclusionsVon

open Papers.OaiNearInclusionsVon.ReusedTree

-- @node: circle_treeVector_coordinate
/-- If [the row vertex's reduced word is a prefix of the column vertex's reduced
word](hyp:hxy), then [the tree vector's row coordinate is one half raised to the
difference in word lengths, multiplied by one at the identity row and by the
square root of three quarters at every other row](goal). -/
lemma circle_treeVector_coordinate (x y : FreeGrp)
    (hxy : x.toWord.IsPrefix y.toWord) :
    treeVector tParam circle_deformation_range y x =
      (tParam : ℂ) ^ (y.toWord.length - x.toWord.length) *
        (if x = 1 then 1 else (rValue tParam circle_deformation_range : ℂ)) := by
  classical
  induction hn : y.toWord.length using Nat.strong_induction_on generalizing y with
  | h n ih =>
    by_cases he : x = y
    · subst y
      by_cases hx : x = 1
      · subst x
        simp [treeVector_one, delta, lp.single_apply, ← hn]
      · simp [treeVector_apply_self tParam circle_deformation_range hx, hx, ← hn]
    · have hp := treePrefix_parent hxy he
      have hy : y ≠ 1 := by
        intro hy
        subst y
        have hx : x = 1 := by simpa using hxy
        exact he hx
      have hl := hp.length_le
      have hd : y.toWord.length - x.toWord.length =
          (treeParent y).toWord.length - x.toWord.length + 1 := by
        rw [treeParent_toWord, List.length_dropLast] at hl ⊢
        have := treeParent_length_lt hy
        omega
      rw [treeVector_recursion tParam circle_deformation_range hy]
      simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, delta, lp.single_apply_ne 2 _ _ he, mul_zero, add_zero]
      rw [ih _ (hn ▸ treeParent_length_lt hy) (treeParent y) hp rfl, ← hn, hd, pow_succ]
      ring

-- @node: circle_treeVector_coordinate_norm_le
/-- [The absolute value of a tree vector coordinate is at most one half raised to
the column word length minus the row word length, with negative differences
replaced by zero](goal). -/
lemma circle_treeVector_coordinate_norm_le (x y : FreeGrp) :
    ‖treeVector tParam circle_deformation_range y x‖ ≤
      tParam ^ (y.toWord.length - x.toWord.length) := by
  have htpos := circle_deformation_range.1
  by_cases hp : x.toWord.IsPrefix y.toWord
  · rw [circle_treeVector_coordinate x y hp, norm_mul, norm_pow]
    have ht : ‖(tParam : ℂ)‖ = tParam := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos circle_deformation_range.1]
    rw [ht]
    apply mul_le_of_le_one_right (by positivity)
    split_ifs
    · simp
    · simpa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (rValue_pos tParam circle_deformation_range)] using
        rValue_le_one tParam circle_deformation_range
  · rw [treeVector_apply_eq_zero_of_not_prefix tParam circle_deformation_range y x hp,
      norm_zero]
    positivity

-- @node: circle_perturbation_coordinate_decay
/-- If [the column vertex's reduced word is a prefix of the group element's reduced
word](hyp:hy), then [the absolute value of the tree perturbation's matrix entry is
at most one half raised to the absolute difference between the row and column
word lengths](goal). -/
lemma circle_perturbation_coordinate_decay (g x y : FreeGrp)
    (hy : y.toWord.IsPrefix g.toWord) :
    ‖treePerturbation tParam circle_deformation_range g (treeBasis y) x‖ ≤
      tParam ^ (Nat.dist x.toWord.length y.toWord.length) := by
  have ht := circle_deformation_range.1
  have hr := rValue_pos tParam circle_deformation_range
  have hr1 := rValue_le_one tParam circle_deformation_range
  change ‖treePerturbation tParam circle_deformation_range g (delta y) x‖ ≤ _
  by_cases he : y = g
  · subst y
    rw [treePerturbation_delta_endpoint]
    by_cases hxy : x.toWord.IsPrefix g.toWord
    · rw [Nat.dist_eq_sub_of_le hxy.length_le]
      exact circle_treeVector_coordinate_norm_le x g
    · rw [treeVector_apply_eq_zero_of_not_prefix tParam circle_deformation_range g x hxy,
        norm_zero]
      positivity
  · rw [treePerturbation_delta_of_prefix tParam circle_deformation_range g y hy he]
    obtain ⟨hp, hn, hpath⟩ := treeParent_next_of_prefix g y hy he
    let v := g * treeParent (g⁻¹ * y)
    have hvlen : v.toWord.length = y.toWord.length + 1 := by
      have h := congrArg (fun a : FreeGrp => a.toWord.length) hp
      rw [treeParent_toWord, List.length_dropLast] at h
      have := treeParent_length_lt hn
      change (treeParent v).toWord.length < v.toWord.length at this
      rw [treeParent_toWord, List.length_dropLast] at this
      change v.toWord.length - 1 = y.toWord.length at h
      omega
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hxv : x = v
    · subst x
      have hnot : ¬ v.toWord.IsPrefix y.toWord := by
        intro h
        have := h.length_le
        omega
      rw [treeVector_apply_eq_zero_of_not_prefix tParam circle_deformation_range y v hnot]
      change ‖(rValue tParam circle_deformation_range : ℂ) * 0 -
        (tParam : ℂ) * delta v v‖ ≤ _
      simp only [mul_zero, zero_sub, delta, lp.single_apply_self, mul_one, norm_neg]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        Nat.dist_eq_sub_of_le_right (by omega), hvlen]
      simp
    · rw [show delta v x = 0 from by simp [delta, lp.single_apply, hxv], mul_zero, sub_zero,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      by_cases hxy : x.toWord.IsPrefix y.toWord
      · rw [Nat.dist_eq_sub_of_le hxy.length_le]
        exact (mul_le_mul_of_nonneg_left (circle_treeVector_coordinate_norm_le x y)
          hr.le).trans (mul_le_of_le_one_left (by positivity) hr1)
      · rw [treeVector_apply_eq_zero_of_not_prefix tParam circle_deformation_range y x hxy,
          norm_zero, mul_zero]
        positivity

-- @node: circlePathEntry_diagonal
/-- If [the vertex's reduced word is a prefix of the group element's reduced word](hyp:hy),
then [its diagonal path entry is the product of two factors minus one: the first
factor is one at the group endpoint and the square root of three quarters otherwise,
and the second is one at the identity and the square root of three quarters otherwise](goal). -/
lemma circlePathEntry_diagonal (g y : FreeGrp)
    (hy : y.toWord.IsPrefix g.toWord) :
    circlePathEntry g y y =
      (((if y = g then 1 else rValue tParam circle_deformation_range) *
        (if y = 1 then 1 else rValue tParam circle_deformation_range) : ℝ) : ℂ) - 1 := by
  classical
  change (treePerturbation tParam circle_deformation_range g (delta y) - delta y) y = _
  have hdelta : delta y y = 1 := by simp [delta, lp.single_apply]
  simp only [lp.coeFn_sub, Pi.sub_apply, hdelta]
  have hself : treeVector tParam circle_deformation_range y y =
      ((if y = 1 then 1 else rValue tParam circle_deformation_range : ℝ) : ℂ) := by
    simpa only [Nat.sub_self, pow_zero, one_mul, apply_ite, Complex.ofReal_one] using
      circle_treeVector_coordinate y y (by rfl)
  by_cases he : y = g
  · rw [if_pos he]
    subst y
    rw [treePerturbation_delta_endpoint, hself]
    simp
  · rw [if_neg he, treePerturbation_delta_of_prefix tParam circle_deformation_range g y hy he]
    have hn : y ≠ g * treeParent (g⁻¹ * y) := by
      intro h
      obtain ⟨hp, hn, _⟩ := treeParent_next_of_prefix g y hy he
      have hl := treeParent_length_lt hn
      rw [hp, ← h] at hl
      exact (lt_irrefl _ hl)
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      delta, lp.single_apply_ne 2 _ _ hn, mul_zero, sub_zero, hself, Complex.ofReal_mul]

-- @node: circlePathEntry_diagonal_norm_le
/-- If [the vertex's reduced word is a prefix of the group element's reduced word](hyp:hy),
then [the absolute value of its diagonal path entry is at most one](goal). -/
lemma circlePathEntry_diagonal_norm_le (g y : FreeGrp)
    (hy : y.toWord.IsPrefix g.toWord) : ‖circlePathEntry g y y‖ ≤ 1 := by
  rw [circlePathEntry_diagonal g y hy]
  let a : ℝ := (if y = g then 1 else rValue tParam circle_deformation_range) *
    (if y = 1 then 1 else rValue tParam circle_deformation_range)
  have hr := (rValue_pos tParam circle_deformation_range).le
  have hr1 := rValue_le_one tParam circle_deformation_range
  have ha0 : 0 ≤ a := by unfold a; positivity
  have ha1 : a ≤ 1 := by
    apply mul_le_one₀
    · split_ifs <;> first | assumption | exact le_rfl
    · split_ifs <;> first | assumption | norm_num
    · split_ifs <;> first | assumption | exact le_rfl
  change ‖(a : ℂ) - 1‖ ≤ 1
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ha1)]
  linarith

-- @node: circlePathEntry_decay
/-- If [the column vertex's reduced word is a prefix of the group element's reduced
word](hyp:hy), then [the absolute value of the path remainder entry is at most one
half raised to the absolute difference between the row and column word lengths](goal). -/
lemma circlePathEntry_decay (g x y : FreeGrp)
    (hy : y.toWord.IsPrefix g.toWord) :
    ‖circlePathEntry g x y‖ ≤ tParam ^ (Nat.dist x.toWord.length y.toWord.length) := by
  by_cases he : x = y
  · subst x
    simpa using circlePathEntry_diagonal_norm_le g y hy
  · change ‖(treePerturbation tParam circle_deformation_range g (delta y) - delta y) x‖ ≤ _
    simp only [lp.coeFn_sub, Pi.sub_apply, delta, lp.single_apply_ne 2 _ _ he, sub_zero]
    exact circle_perturbation_coordinate_decay g x y hy

-- @node: circleExponent_mk_cons
/-- [Prepending a signed generator to a word increases its circle exponent by one
for a positive generator and decreases it by one for an inverse generator](goal). -/
lemma circleExponent_mk_cons (a : ℕ × Bool) (w : List (ℕ × Bool)) :
    circleExponent (FreeGroup.mk (a :: w)) =
      (if a.2 then 1 else -1) + circleExponent (FreeGroup.mk w) := by
  simp only [circleExponent, FreeGroup.lift_mk, List.map_cons, List.prod_cons]
  cases a with
  | mk j b => cases b <;> rfl

-- @node: circleExponent_mk_natAbs_le
/-- [The absolute circle exponent of the group element represented by a word is
at most the number of letters in that word](goal). -/
lemma circleExponent_mk_natAbs_le (w : List (ℕ × Bool)) :
    (circleExponent (FreeGroup.mk w)).natAbs ≤ w.length := by
  induction w with
  | nil => simp [circleExponent, FreeGroup.lift_mk]
  | cons a w ih =>
    rw [circleExponent_mk_cons]
    cases a.2 <;> simp only [Bool.false_eq_true, if_false, if_true,
      List.length_cons] <;> omega

-- @node: circleExponent_sub_natAbs_le_of_prefix
/-- If [the first vertex's reduced word is a prefix of the second vertex's reduced
word](hyp:hxy), then [the absolute difference of their circle exponents is at most
the second word length minus the first word length](goal). -/
lemma circleExponent_sub_natAbs_le_of_prefix (x y : FreeGrp)
    (hxy : x.toWord.IsPrefix y.toWord) :
    (circleExponent y - circleExponent x).natAbs ≤ y.toWord.length - x.toWord.length := by
  obtain ⟨w, hw⟩ := hxy
  have hprod : y = x * FreeGroup.mk w := by
    rw [← FreeGroup.mk_toWord (x := x), FreeGroup.mul_mk, hw, FreeGroup.mk_toWord]
  have hlen := congrArg List.length hw
  simp only [List.length_append] at hlen
  rw [show circleExponent y - circleExponent x = circleExponent (FreeGroup.mk w) by
    rw [hprod, circleExponent_mul, add_sub_cancel_left]]
  exact (circleExponent_mk_natAbs_le w).trans (by omega)

-- @node: circleExponent_path_distance
/-- If [the row vertex's reduced word is a prefix of the group element's reduced word](hyp:hx)
and [the column vertex's reduced word is also a prefix of that word](hyp:hy), then
[the absolute difference of their circle exponents is at most the absolute
difference of their word lengths](goal). -/
lemma circleExponent_path_distance (g x y : FreeGrp)
    (hx : x.toWord.IsPrefix g.toWord) (hy : y.toWord.IsPrefix g.toWord) :
    (circleExponent y - circleExponent x).natAbs ≤
      Nat.dist x.toWord.length y.toWord.length := by
  rcases List.prefix_or_prefix_of_prefix hx hy with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy.length_le]
    exact circleExponent_sub_natAbs_le_of_prefix x y hxy
  · rw [Nat.dist_eq_sub_of_le_right hyx.length_le, ← Int.natAbs_neg,
      neg_sub]
    exact circleExponent_sub_natAbs_le_of_prefix y x hyx

end Papers.OaiNearInclusionsVon
