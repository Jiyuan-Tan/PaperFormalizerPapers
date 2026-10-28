module

public import Papers.OaiCloseSeparableCstar.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-! # Root-path vectors for the tree deformation

Words are traversed from their last letter, so the vector recursion is structural.
The resulting vectors recover every coordinate vector and have dense linear span.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Papers.OaiCloseSeparableCstar

-- @node: treeParent
/-- For [a group element x](hyp:x), [its parent toward the root](goal) is obtained
by deleting the last letter of its reduced word. -/
def treeParent (x : FG) : FG := FreeGroup.mk x.toWord.dropLast

-- @node: treeParent_toWord
/-- [The reduced word of the parent of x is the reduced word of x with its last
letter removed](goal). -/
lemma treeParent_toWord (x : FG) : (treeParent x).toWord = x.toWord.dropLast := by
  rw [treeParent, FreeGroup.toWord_mk]
  apply FreeGroup.IsReduced.reduce_eq
  exact (FreeGroup.isReduced_toWord (x := x)).prefix (List.dropLast_prefix _)

-- @node: treeParent_length_lt
/-- If [x is not the group identity](hyp:hx), [the reduced word of its parent is
strictly shorter than the reduced word of x](goal). -/
lemma treeParent_length_lt {x : FG} (hx : x ≠ 1) :
    (treeParent x).toWord.length < x.toWord.length := by
  rw [treeParent_toWord, List.length_dropLast]
  have h : x.toWord ≠ [] := by simpa using hx
  have : 0 < x.toWord.length := List.length_pos_iff.mpr h
  omega

-- @node: treeWordVector
/-- For [a real recursion weight t](hyp:t) and [a real coordinate weight r](hyp:r),
[the auxiliary root-path vector](goal) is defined on reversed letter lists:
[the empty list gives the identity coordinate vector](step:1), and
[a nonempty list gives t times the vector for its tail plus r times the coordinate
vector at the group element represented by the reversed full list](step:2). -/
noncomputable def treeWordVector (t r : ℝ) : List (ℕ × Bool) → KSp
  | [] => delta 1
  | a :: w => (t : ℂ) • treeWordVector t r w +
      (r : ℂ) • delta (FreeGroup.mk (a :: w).reverse)

-- @node: treeVector
/-- For [a real deformation parameter t](hyp:t) [strictly between zero and one](hyp:ht)
and [a group element x](hyp:x), [the root-path vector at x](goal) is obtained by
applying the reversed-word recursion to the reduced word of x, with weights t and
the positive square root of one minus t squared. -/
noncomputable def treeVector (t : ℝ) (ht : DeformationRange t) (x : FG) : KSp :=
  treeWordVector t (rValue t ht) x.toWord.reverse

-- @node: treeVector_one
/-- If [t lies strictly between zero and one](hyp:ht), [the root-path vector at
the group identity is the identity coordinate vector](goal). -/
lemma treeVector_one (t : ℝ) (ht : DeformationRange t) :
    treeVector t ht 1 = delta 1 := by
  simp [treeVector, treeWordVector]

-- @node: treeVector_recursion
/-- If [t lies strictly between zero and one](hyp:ht) and [x is not the group
identity](hyp:hx), [the root-path vector at x equals t times the vector at its
parent plus the positive square root of one minus t squared times the coordinate
vector at x](goal). -/
lemma treeVector_recursion (t : ℝ) (ht : DeformationRange t) {x : FG} (hx : x ≠ 1) :
    treeVector t ht x = (t : ℂ) • treeVector t ht (treeParent x) +
      (rValue t ht : ℂ) • delta x := by
  have h : x.toWord.reverse ≠ [] := by simpa using hx
  obtain ⟨a, w, hw⟩ := List.exists_cons_of_ne_nil h
  have hp : (treeParent x).toWord.reverse = w := by
    rw [treeParent_toWord]
    have he : x.toWord = (a :: w).reverse := by
      simpa using congrArg List.reverse hw
    simp [he]
  unfold treeVector
  rw [hw, treeWordVector, hp]
  congr 2
  rw [← hw, List.reverse_reverse, FreeGroup.mk_toWord]

-- @node: rValue_pos
/-- If [t lies strictly between zero and one](hyp:ht), [the square-root weight
given by the square root of one minus t squared is strictly positive](goal). -/
lemma rValue_pos (t : ℝ) (ht : DeformationRange t) : 0 < rValue t ht := by
  apply Real.sqrt_pos.mpr
  have := ht.1
  have := ht.2
  nlinarith

-- @node: delta_mem_span_treeVector
/-- If [t lies strictly between zero and one](hyp:ht), [every coordinate vector
belongs to the complex linear span of the root-path vectors](goal). -/
lemma delta_mem_span_treeVector (t : ℝ) (ht : DeformationRange t) (x : FG) :
    delta x ∈ Submodule.span ℂ (Set.range (treeVector t ht)) := by
  by_cases hx : x = 1
  · subst x
    rw [← treeVector_one t ht]
    exact Submodule.subset_span (Set.mem_range_self _)
  · have hp : treeVector t ht (treeParent x) ∈
        Submodule.span ℂ (Set.range (treeVector t ht)) :=
      Submodule.subset_span (Set.mem_range_self _)
    have hv : treeVector t ht x ∈ Submodule.span ℂ (Set.range (treeVector t ht)) :=
      Submodule.subset_span (Set.mem_range_self _)
    have hd := (Submodule.span ℂ (Set.range (treeVector t ht))).sub_mem hv
      ((Submodule.span ℂ (Set.range (treeVector t ht))).smul_mem (t : ℂ) hp)
    rw [treeVector_recursion t ht hx, add_sub_cancel_left] at hd
    have hr : (rValue t ht : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (rValue_pos t ht))
    have := (Submodule.span ℂ (Set.range (treeVector t ht))).smul_mem
      (rValue t ht : ℂ)⁻¹ hd
    rw [smul_smul, inv_mul_cancel₀ hr, one_smul] at this
    exact this

-- @node: treeVector_dense_span
/-- If [t lies strictly between zero and one](hyp:ht), [the closure of the complex
linear span of the root-path vectors is the entire square-summable Hilbert space
on the group](goal). -/
lemma treeVector_dense_span (t : ℝ) (ht : DeformationRange t) :
    (Submodule.span ℂ (Set.range (treeVector t ht))).topologicalClosure = ⊤ := by
  apply top_unique
  intro v _
  have hs := lp.hasSum_single (p := 2) (by norm_num) v
  apply (Submodule.span ℂ (Set.range (treeVector t ht))).isClosed_topologicalClosure.mem_of_tendsto
    hs
  filter_upwards [] with s
  apply Submodule.sum_mem
  intro x _
  have hd := (Submodule.span ℂ (Set.range (treeVector t ht))).smul_mem (v x)
    (delta_mem_span_treeVector t ht x)
  apply Submodule.le_topologicalClosure
  simpa only [delta, ← lp.single_smul, smul_eq_mul, mul_one] using hd

-- @node: treeWordVector_apply_eq_zero_of_length_lt
/-- If [the reduced word of y is longer than the letter list w](hyp:hy), [the
auxiliary root-path vector for w has zero coordinate at y, for any real weights
t and r](goal). -/
lemma treeWordVector_apply_eq_zero_of_length_lt (t r : ℝ)
    (w : List (ℕ × Bool)) (y : FG) (hy : w.length < y.toWord.length) :
    treeWordVector t r w y = 0 := by
  induction w with
  | nil =>
    have hy1 : y ≠ 1 := by
      intro h
      simp [h] at hy
    simp [treeWordVector, delta, lp.single_apply, Ne.symm hy1]
  | cons a w ih =>
    have hwy : w.length < y.toWord.length := by simpa using Nat.lt_of_succ_lt hy
    have hne : y ≠ FreeGroup.mk (a :: w).reverse := by
      intro he
      have hl := (FreeGroup.reduce.red (L := (a :: w).reverse)).length_le
      rw [he, FreeGroup.toWord_mk] at hy
      simp only [List.length_reverse, List.length_cons] at hl hy
      omega
    simp only [treeWordVector, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply,
      Pi.smul_apply, ih hwy, smul_zero, zero_add, delta, lp.single_apply_ne 2 _ _ hne,
      smul_zero]

-- @node: treeVector_parent_apply_self
/-- If [t lies strictly between zero and one](hyp:ht) and [x is not the group
identity](hyp:hx), [the root-path vector at the parent of x has zero coordinate
at x](goal). -/
lemma treeVector_parent_apply_self (t : ℝ) (ht : DeformationRange t)
    {x : FG} (hx : x ≠ 1) : treeVector t ht (treeParent x) x = 0 := by
  apply treeWordVector_apply_eq_zero_of_length_lt
  simpa using treeParent_length_lt hx

-- @node: treeVector_apply_eq_zero_of_not_prefix
/-- If [t lies strictly between zero and one](hyp:ht) and [the reduced word of y
is not a prefix of the reduced word of x](hyp:hxy), [the root-path vector at x
has zero coordinate at y](goal). -/
lemma treeVector_apply_eq_zero_of_not_prefix (t : ℝ) (ht : DeformationRange t)
    (x y : FG) (hxy : ¬ y.toWord.IsPrefix x.toWord) : treeVector t ht x y = 0 := by
  induction hn : x.toWord.length using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have hy : y ≠ 1 := by
      rintro rfl
      simp at hxy
    by_cases hx : x = 1
    · subst x
      simp [treeVector_one, delta, lp.single_apply, Ne.symm hy]
    · have hpy : ¬ y.toWord.IsPrefix (treeParent x).toWord := by
        intro h
        apply hxy
        rw [treeParent_toWord] at h
        exact h.trans (List.dropLast_prefix _)
      have hp := ih (treeParent x).toWord.length
        (hn ▸ treeParent_length_lt hx) (treeParent x) hpy rfl
      have hyx : y ≠ x := by
        rintro rfl
        exact hxy (by simp)
      rw [treeVector_recursion t ht hx]
      simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, hp,
        smul_zero, zero_add, delta, lp.single_apply_ne 2 _ _ hyx, smul_zero]

-- @node: treeVector_apply_self
/-- If [t lies strictly between zero and one](hyp:ht) and [x is not the group
identity](hyp:hx), [the coordinate at x of its own root-path vector is the
positive square root of one minus t squared](goal). -/
lemma treeVector_apply_self (t : ℝ) (ht : DeformationRange t) {x : FG} (hx : x ≠ 1) :
    treeVector t ht x x = (rValue t ht : ℂ) := by
  rw [treeVector_recursion t ht hx]
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    treeVector_parent_apply_self t ht hx, delta,
    lp.single_apply_self, smul_eq_mul, mul_zero, zero_add, mul_one]

-- @node: delta_norm
/-- [Every coordinate vector in the square-summable Hilbert space on the group
has norm one](goal). -/
lemma delta_norm (x : FG) : ‖delta x‖ = 1 := by
  simp [delta, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

-- @node: treeVector_norm
/-- If [t lies strictly between zero and one](hyp:ht), [every root-path vector
has norm one](goal). -/
lemma treeVector_norm (t : ℝ) (ht : DeformationRange t) (x : FG) :
    ‖treeVector t ht x‖ = 1 := by
  induction hn : x.toWord.length using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hx : x = 1
    · subst x
      rw [treeVector_one, delta_norm]
    · have hp := ih (treeParent x).toWord.length
        (hn ▸ treeParent_length_lt hx) (treeParent x) rfl
      have ho : ⟪treeVector t ht (treeParent x), delta x⟫_ℂ = 0 := by
        simp [delta, lp.inner_single_right, treeVector_parent_apply_self t ht hx]
      have hsq := @norm_add_sq ℂ _ _ _ _
        ((t : ℂ) • treeVector t ht (treeParent x)) ((rValue t ht : ℂ) • delta x)
      rw [← treeVector_recursion t ht hx] at hsq
      have hr := rValue_pos t ht
      have hr2 : rValue t ht ^ 2 = 1 - t ^ 2 := by
        apply Real.sq_sqrt
        have := ht.1
        have := ht.2
        nlinarith
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1,
        abs_of_pos hr, hp, delta_norm, mul_one, inner_smul_left, inner_smul_right,
        ho, mul_zero, map_zero, mul_zero, add_zero] at hsq
      have hn0 := norm_nonneg (treeVector t ht x)
      nlinarith

-- @node: treeVector_gen
/-- If [t lies strictly between zero and one](hyp:ht), [the root-path vector at
any free generator equals t times the identity coordinate vector plus the positive
square root of one minus t squared times that generator's coordinate vector](goal). -/
lemma treeVector_gen (t : ℝ) (ht : DeformationRange t) (i : ℕ) :
    treeVector t ht (gen i) = (t : ℂ) • delta 1 +
      (rValue t ht : ℂ) • delta (gen i) := by
  unfold treeVector
  simp only [gen, FreeGroup.toWord_of, List.reverse_cons, List.reverse_nil,
    List.nil_append, treeWordVector]
  rw [← FreeGroup.toWord_of i, FreeGroup.mk_toWord]

-- @node: treeVector_gen_coefficient
/-- If [t lies strictly between zero and one](hyp:ht), [the inner product of
the root-path vector at any free generator with the identity coordinate vector
equals t](goal). -/
lemma treeVector_gen_coefficient (t : ℝ) (ht : DeformationRange t) (i : ℕ) :
    ⟪treeVector t ht (gen i), delta 1⟫_ℂ = (t : ℂ) := by
  rw [treeVector_gen]
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  simp [delta, lp.inner_single_right, lp.single_apply, gen]

end Papers.OaiCloseSeparableCstar
