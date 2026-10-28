module

public import Papers.OaiNearInclusionsVon.ReusedTree.Helpers.TreeVectors

/-! # Inner products of root-path vectors

The Gram calculation strips the terminal vertices beyond the last common ancestor.
At each step the new coordinate is orthogonal to the other root path.
-/

public section

open scoped InnerProductSpace

namespace Papers.OaiNearInclusionsVon.ReusedTree

/-- If [z lies on the root path to x](hyp:hzx) and [z differs from x](hyp:hne),
[z still lies on the root path to the parent of x](goal). -/
lemma treePrefix_parent {z x : FG} (hzx : z.toWord.IsPrefix x.toWord) (hne : z ≠ x) :
    z.toWord.IsPrefix (treeParent x).toWord := by
  have hlt : z.toWord.length < x.toWord.length := by
    have hle := hzx.length_le
    have hneWord : z.toWord ≠ x.toWord := by
      intro h
      apply hne
      simpa only [FreeGroup.mk_toWord] using congrArg FreeGroup.mk h
    by_contra h
    exact hneWord (hzx.eq_of_length (by omega))
  rw [treeParent_toWord]
  rcases List.prefix_or_prefix_of_prefix hzx (List.dropLast_prefix x.toWord) with h | h
  · exact h
  · have he : x.toWord.dropLast = z.toWord := h.eq_of_length_le (by
      simp only [List.length_dropLast]
      omega)
    rw [he]

/-- For [t strictly between zero and one](hyp:ht), if [x is not the root](hyp:hx)
and [x lies outside the root path to y](hyp:hxy), [the inner product of the
root-path vectors at x and y equals t times the inner product at the parent of x
and y](goal). -/
lemma treeVector_inner_recursion_of_not_prefix (t : ℝ) (ht : DeformationRange t)
    {x y : FG} (hx : x ≠ 1) (hxy : ¬ x.toWord.IsPrefix y.toWord) :
    ⟪treeVector t ht x, treeVector t ht y⟫_ℂ =
      (t : ℂ) * ⟪treeVector t ht (treeParent x), treeVector t ht y⟫_ℂ := by
  have hz := treeVector_apply_eq_zero_of_not_prefix t ht y x hxy
  rw [treeVector_recursion t ht hx, inner_add_left, inner_smul_left, inner_smul_left]
  simp [delta, lp.inner_single_left, hz]

/-- For [t strictly between zero and one](hyp:ht), if [z lies on the root path
to x](hyp:hzx), [the inner product of the root-path vectors at x and z equals
t raised to the difference of their reduced-word lengths](goal). -/
lemma treeVector_inner_of_prefix (t : ℝ) (ht : DeformationRange t) {x z : FG}
    (hzx : z.toWord.IsPrefix x.toWord) :
    ⟪treeVector t ht x, treeVector t ht z⟫_ℂ =
      (t : ℂ) ^ (x.toWord.length - z.toWord.length) := by
  induction hn : x.toWord.length using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hxe : x = z
    · subst x
      simp [inner_self_eq_norm_sq_to_K, treeVector_norm, ← hn]
    · have hzx' := treePrefix_parent hzx (Ne.symm hxe)
      have hx : x ≠ 1 := by
        intro he
        subst x
        have hz : z = 1 := by simpa using hzx
        exact hxe hz.symm
      have hlt : z.toWord.length < x.toWord.length := by
        have hle := hzx.length_le
        by_contra h
        have hw := hzx.eq_of_length (by omega)
        have he : z = x := by simpa only [FreeGroup.mk_toWord] using congrArg FreeGroup.mk hw
        exact hxe he.symm
      have hnot : ¬ x.toWord.IsPrefix z.toWord := by
        intro h
        have := h.length_le
        omega
      rw [treeVector_inner_recursion_of_not_prefix t ht hx hnot,
        ih _ (hn ▸ treeParent_length_lt hx) hzx' rfl]
      have hp : x.toWord.length - z.toWord.length =
          (treeParent x).toWord.length - z.toWord.length + 1 := by
        rw [treeParent_toWord, List.length_dropLast]
        omega
      rw [← hn, hp, pow_succ]
      exact mul_comm _ _

/-- For [t strictly between zero and one](hyp:ht), suppose [z lies on the root
path to x](hyp:hzx), [z lies on the root path to y](hyp:hzy), and [every common
ancestor of x and y has reduced-word length at most that of z](hyp:hmax).
Then [the inner product of the root-path vectors at x and y equals t raised to
the sum of their reduced-word lengths minus twice the length of z](goal). -/
lemma treeVector_inner_of_last_common_ancestor (t : ℝ) (ht : DeformationRange t)
    {x y z : FG} (hzx : z.toWord.IsPrefix x.toWord) (hzy : z.toWord.IsPrefix y.toWord)
    (hmax : ∀ w : FG, w.toWord.IsPrefix x.toWord → w.toWord.IsPrefix y.toWord →
      w.toWord.length ≤ z.toWord.length) :
    ⟪treeVector t ht x, treeVector t ht y⟫_ℂ =
      (t : ℂ) ^ (x.toWord.length - z.toWord.length +
        (y.toWord.length - z.toWord.length)) := by
  induction hn : x.toWord.length using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hxe : x = z
    · subst x
      rw [← inner_conj_symm, treeVector_inner_of_prefix t ht hzy]
      simp [← hn]
    · have hzx' := treePrefix_parent hzx (Ne.symm hxe)
      have hx : x ≠ 1 := by
        intro he
        subst x
        have hz : z = 1 := by simpa using hzx
        exact hxe hz.symm
      have hlt : z.toWord.length < x.toWord.length := by
        have hle := hzx.length_le
        by_contra h
        have hw := hzx.eq_of_length (by omega)
        have he : z = x := by simpa only [FreeGroup.mk_toWord] using congrArg FreeGroup.mk hw
        exact hxe he.symm
      have hnot : ¬ x.toWord.IsPrefix y.toWord := by
        intro h
        have := hmax x (by rfl) h
        omega
      have hmax' : ∀ w : FG, w.toWord.IsPrefix (treeParent x).toWord →
          w.toWord.IsPrefix y.toWord → w.toWord.length ≤ z.toWord.length := by
        intro w hw hy
        apply hmax w _ hy
        exact hw.trans (by rw [treeParent_toWord]; exact List.dropLast_prefix _)
      rw [treeVector_inner_recursion_of_not_prefix t ht hx hnot,
        ih _ (hn ▸ treeParent_length_lt hx) hzx' hmax' rfl]
      have hp : x.toWord.length - z.toWord.length + (y.toWord.length - z.toWord.length) =
          ((treeParent x).toWord.length - z.toWord.length +
            (y.toWord.length - z.toWord.length)) + 1 := by
        rw [treeParent_toWord, List.length_dropLast]
        omega
      rw [← hn, hp, pow_succ]
      exact mul_comm _ _

/-- For any vertices x and y, [there is a vertex z on both root paths such that
every vertex on both paths has reduced-word length at most that of z](goal). -/
lemma exists_tree_last_common_ancestor (x y : FG) :
    ∃ z : FG, z.toWord.IsPrefix x.toWord ∧ z.toWord.IsPrefix y.toWord ∧
      ∀ w : FG, w.toWord.IsPrefix x.toWord → w.toWord.IsPrefix y.toWord →
        w.toWord.length ≤ z.toWord.length := by
  induction hn : x.toWord.length using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hxy : x.toWord.IsPrefix y.toWord
    · exact ⟨x, by rfl, hxy, fun w hw _ => hw.length_le⟩
    · have hx : x ≠ 1 := by
        rintro rfl
        exact hxy (by simp)
      obtain ⟨z, hzx, hzy, hmax⟩ := ih _ (hn ▸ treeParent_length_lt hx) (treeParent x) rfl
      refine ⟨z, hzx.trans ?_, hzy, ?_⟩
      · rw [treeParent_toWord]
        exact List.dropLast_prefix _
      · intro w hwx hwy
        apply hmax w _ hwy
        apply treePrefix_parent hwx
        rintro rfl
        exact hxy hwy

/-- If [u is a reduced word](hyp:hu), [reversing u and inverting each letter
produces a reduced word](goal). -/
lemma treeReduced_invRev {u : List (ℕ × Bool)} (hu : FreeGroup.IsReduced u) :
    FreeGroup.IsReduced (FreeGroup.invRev u) := by
  apply FreeGroup.IsReduced.of_reduce_eq
  rw [FreeGroup.reduce_invRev, hu.reduce_eq]

/-- If [u is reduced](hyp:hu), [v is reduced](hyp:hv), and [their first letters
differ whenever both words are nonempty](hyp:hhead), [concatenating the reversed,
letterwise inverse of u with v produces a reduced word](goal). -/
lemma treeReduced_invRev_append_of_head_ne {u v : List (ℕ × Bool)}
    (hu : FreeGroup.IsReduced u) (hv : FreeGroup.IsReduced v)
    (hhead : ∀ a ∈ u.head?, ∀ b ∈ v.head?, a ≠ b) :
    FreeGroup.IsReduced (FreeGroup.invRev u ++ v) := by
  apply List.IsChain.append (treeReduced_invRev hu) hv
  cases u with
  | nil => simp [FreeGroup.invRev]
  | cons a u =>
    cases v with
    | nil => simp
    | cons b v =>
      simp only [FreeGroup.invRev, List.getLast?_reverse, List.map_cons, List.head?_cons,
        Option.mem_def, Option.some.injEq]
      intro c hc d hd
      subst c d
      have hab : a ≠ b := hhead a (by simp) b (by simp)
      rcases a with ⟨i, a⟩
      rcases b with ⟨j, b⟩
      dsimp
      intro hij
      subst j
      cases a <;> cases b <;> simp_all

/-- Suppose [z lies on the root path to x](hyp:hzx), [z lies on the root path
to y](hyp:hzy), and [every common ancestor of x and y has reduced-word length
at most that of z](hyp:hmax). Then [the reduced-word length of x inverse times y
equals the sum of the lengths of x and y minus twice the length of z](goal). -/
lemma tree_distance_of_last_common_ancestor {x y z : FG}
    (hzx : z.toWord.IsPrefix x.toWord) (hzy : z.toWord.IsPrefix y.toWord)
    (hmax : ∀ w : FG, w.toWord.IsPrefix x.toWord → w.toWord.IsPrefix y.toWord →
      w.toWord.length ≤ z.toWord.length) :
    (x⁻¹ * y).toWord.length = x.toWord.length - z.toWord.length +
      (y.toWord.length - z.toWord.length) := by
  obtain ⟨u, hu⟩ := hzx
  obtain ⟨v, hv⟩ := hzy
  have hur : FreeGroup.IsReduced u := by
    have hr := FreeGroup.isReduced_toWord (x := x)
    rw [← hu] at hr
    exact List.IsChain.right_of_append hr
  have hvr : FreeGroup.IsReduced v := by
    have hr := FreeGroup.isReduced_toWord (x := y)
    rw [← hv] at hr
    exact List.IsChain.right_of_append hr
  have hhead : ∀ a ∈ u.head?, ∀ b ∈ v.head?, a ≠ b := by
    intro a ha b hb hab
    subst b
    cases u with
    | nil => simp at ha
    | cons c u =>
      cases v with
      | nil => simp at hb
      | cons d v =>
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha hb
        subst c d
        have hpx : (z.toWord ++ [a]).IsPrefix x.toWord :=
          ⟨u, by simpa only [List.append_assoc, List.singleton_append] using hu⟩
        have hpy : (z.toWord ++ [a]).IsPrefix y.toWord :=
          ⟨v, by simpa only [List.append_assoc, List.singleton_append] using hv⟩
        have hr : FreeGroup.IsReduced (z.toWord ++ [a]) :=
          (FreeGroup.isReduced_toWord (x := x)).prefix hpx
        have hw : (FreeGroup.mk (z.toWord ++ [a])).toWord = z.toWord ++ [a] := by
          rw [FreeGroup.toWord_mk, hr.reduce_eq]
        have hl := hmax (FreeGroup.mk (z.toWord ++ [a]))
          (by rw [hw]; exact hpx) (by rw [hw]; exact hpy)
        rw [hw, List.length_append, List.length_singleton] at hl
        omega
  have hr := treeReduced_invRev_append_of_head_ne hur hvr hhead
  have hx : x = z * FreeGroup.mk u := by
    have he := congrArg FreeGroup.mk hu
    rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord] at he
    exact he.symm
  have hy : y = z * FreeGroup.mk v := by
    have he := congrArg FreeGroup.mk hv
    rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord] at he
    exact he.symm
  have hprod : x⁻¹ * y = FreeGroup.mk (FreeGroup.invRev u ++ v) := by
    calc
      x⁻¹ * y = (FreeGroup.mk u)⁻¹ * FreeGroup.mk v := by rw [hx, hy]; group
      _ = _ := by rw [FreeGroup.inv_mk, FreeGroup.mul_mk]
  rw [hprod, FreeGroup.toWord_mk, hr.reduce_eq, List.length_append, FreeGroup.invRev_length,
    ← hu, ← hv, List.length_append, List.length_append]
  omega

/-- For [t strictly between zero and one](hyp:ht), [the inner product of the
root-path vectors at x and y equals t raised to their tree distance, the
reduced-word length of x inverse times y](goal). -/
lemma treeVector_inner (t : ℝ) (ht : DeformationRange t) (x y : FG) :
    ⟪treeVector t ht x, treeVector t ht y⟫_ℂ = (t : ℂ) ^ (x⁻¹ * y).toWord.length := by
  obtain ⟨z, hzx, hzy, hmax⟩ := exists_tree_last_common_ancestor x y
  rw [treeVector_inner_of_last_common_ancestor t ht hzx hzy hmax,
    tree_distance_of_last_common_ancestor hzx hzy hmax]

/-- For [t strictly between zero and one](hyp:ht), [multiplying x and y on the
left by the same group element g preserves the inner product of their
root-path vectors](goal). -/
lemma treeVector_inner_left_translate (t : ℝ) (ht : DeformationRange t) (g x y : FG) :
    ⟪treeVector t ht (g * x), treeVector t ht (g * y)⟫_ℂ =
      ⟪treeVector t ht x, treeVector t ht y⟫_ℂ := by
  rw [treeVector_inner, treeVector_inner]
  congr 2
  group

end Papers.OaiNearInclusionsVon.ReusedTree
