module

public import Papers.OaiNearInclusionsVon.ReusedTree.Helpers.TreeUnitary
public import Papers.OaiNearInclusionsVon.ReusedTree.Helpers.LpOperators

/-! # Basis action of the tree perturbation

The conjugated perturbation fixes the basis off the root path. Its remaining columns
are given by the root-path recursion, ready for the finite path norm estimate.
-/

@[expose] public section

namespace Papers.OaiNearInclusionsVon.ReusedTree

/-- For [a real deformation parameter t](hyp:t) [strictly between zero and one](hyp:ht)
and [a group element g](hyp:g), [the tree perturbation at g](goal) is the tree unitary
representation at g composed with left translation by the inverse of g. -/
noncomputable def treePerturbation (t : ℝ) (ht : DeformationRange t) (g : FG) : Op KSp :=
  (treeUnitaryRep t ht g : Op KSp) * (leftReg g⁻¹ : Op KSp)

/-- If [t is strictly between zero and one](hyp:ht) and [x is not the root](hyp:hx),
[the basis vector at x equals the recursive tree vector at x minus t times the
recursive tree vector at its parent, all divided by the square root of one minus
t squared](goal). -/
lemma delta_eq_treeVector_sub (t : ℝ) (ht : DeformationRange t) {x : FG} (hx : x ≠ 1) :
    delta x = (rValue t ht : ℂ)⁻¹ •
      (treeVector t ht x - (t : ℂ) • treeVector t ht (treeParent x)) := by
  have hr : (rValue t ht : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (rValue_pos t ht))
  rw [treeVector_recursion t ht hx, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ hr, one_smul]

/-- If [t is strictly between zero and one](hyp:ht) and [y differs from g](hyp:hy),
[the tree perturbation at g sends the basis vector at y to the recursive tree vector
at y minus t times the recursive tree vector at its neighbor toward g, all divided
by the square root of one minus t squared](goal).

The neighbor toward g is obtained by translating y by the inverse of g, taking its
parent in the rooted tree, and translating back by g. -/
lemma treePerturbation_delta (t : ℝ) (ht : DeformationRange t) (g y : FG) (hy : y ≠ g) :
    treePerturbation t ht g (delta y) = (rValue t ht : ℂ)⁻¹ •
      (treeVector t ht y - (t : ℂ) • treeVector t ht (g * treeParent (g⁻¹ * y))) := by
  have hx : g⁻¹ * y ≠ 1 := by
    intro h
    apply hy
    simpa using congrArg (fun x => g * x) h
  change (treeUnitaryRep t ht g : Op KSp) ((leftReg g⁻¹ : Op KSp) (delta y)) = _
  rw [leftReg_delta, delta_eq_treeVector_sub t ht hx, map_smul, map_sub,
    map_smul, treeUnitaryRep_treeVector, treeUnitaryRep_treeVector]
  simp only [mul_inv_cancel_left]

/-- If [t is strictly between zero and one](hyp:ht), [the tree perturbation at g sends
the basis vector at g to the recursive tree vector at g](goal). -/
lemma treePerturbation_delta_endpoint (t : ℝ) (ht : DeformationRange t) (g : FG) :
    treePerturbation t ht g (delta g) = treeVector t ht g := by
  change (treeUnitaryRep t ht g : Op KSp) ((leftReg g⁻¹ : Op KSp) (delta g)) = _
  rw [leftReg_delta, inv_mul_cancel, ← treeVector_one t ht,
    treeUnitaryRep_treeVector, mul_one]

/-- If [t is strictly between zero and one](hyp:ht), [y differs from g](hyp:hy),
[y is not the root](hyp:hy1), and [the neighbor of y toward g equals its parent
toward the root](hyp:hp), [the tree perturbation at g fixes the basis vector at y](goal). -/
lemma treePerturbation_delta_of_parent_eq (t : ℝ) (ht : DeformationRange t)
    (g y : FG) (hy : y ≠ g) (hy1 : y ≠ 1)
    (hp : g * treeParent (g⁻¹ * y) = treeParent y) :
    treePerturbation t ht g (delta y) = delta y := by
  rw [treePerturbation_delta t ht g y hy, hp]
  exact (delta_eq_treeVector_sub t ht hy1).symm

/-- If [concatenating the words u and v produces a reduced word](hyp:hr) and
[v is nonempty](hyp:hv), [the parent of the group element represented by that
concatenation equals the element represented by u multiplied by the element
represented by v with its last letter removed](goal). -/
lemma treeParent_mk_append (u v : List (ℕ × Bool))
    (hr : FreeGroup.IsReduced (u ++ v)) (hv : v ≠ []) :
    treeParent (FreeGroup.mk (u ++ v)) = FreeGroup.mk u * FreeGroup.mk v.dropLast := by
  simp only [treeParent, FreeGroup.toWord_mk, hr.reduce_eq,
    List.dropLast_append_of_ne_nil hv, FreeGroup.mul_mk]

/-- If [y lies off the root path to g](hyp:hy), [translating y by the inverse of g,
taking its parent, and translating back by g gives the parent of y](goal). -/
lemma treeParent_translate_of_not_prefix (g y : FG)
    (hy : ¬ y.toWord.IsPrefix g.toWord) :
    g * treeParent (g⁻¹ * y) = treeParent y := by
  obtain ⟨z, hzg, hzy, hmax⟩ := exists_tree_last_common_ancestor g y
  obtain ⟨u, hu⟩ := hzg
  obtain ⟨v, hv⟩ := hzy
  have hur : FreeGroup.IsReduced u := by
    have hr := FreeGroup.isReduced_toWord (x := g)
    rw [← hu] at hr
    exact List.IsChain.right_of_append hr
  have hvr : FreeGroup.IsReduced v := by
    have hr := FreeGroup.isReduced_toWord (x := y)
    rw [← hv] at hr
    exact List.IsChain.right_of_append hr
  have hvne : v ≠ [] := by
    intro h
    apply hy
    rw [← hv, h, List.append_nil]
    exact ⟨u, hu⟩
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
        have hpg : (z.toWord ++ [a]).IsPrefix g.toWord :=
          ⟨u, by simpa only [List.append_assoc, List.singleton_append] using hu⟩
        have hpy : (z.toWord ++ [a]).IsPrefix y.toWord :=
          ⟨v, by simpa only [List.append_assoc, List.singleton_append] using hv⟩
        have hr : FreeGroup.IsReduced (z.toWord ++ [a]) :=
          (FreeGroup.isReduced_toWord (x := g)).prefix hpg
        have hw : (FreeGroup.mk (z.toWord ++ [a])).toWord = z.toWord ++ [a] := by
          rw [FreeGroup.toWord_mk, hr.reduce_eq]
        have hl := hmax (FreeGroup.mk (z.toWord ++ [a]))
          (by rw [hw]; exact hpg) (by rw [hw]; exact hpy)
        rw [hw, List.length_append, List.length_singleton] at hl
        omega
  have hg : g = z * FreeGroup.mk u := by
    have he := congrArg FreeGroup.mk hu
    rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord] at he
    exact he.symm
  have hy' : y = FreeGroup.mk (z.toWord ++ v) := by
    rw [hv, FreeGroup.mk_toWord]
  have hprod : g⁻¹ * y = FreeGroup.mk (FreeGroup.invRev u ++ v) := by
    rw [hy', ← FreeGroup.mul_mk, FreeGroup.mk_toWord, hg,
      mul_inv_rev, mul_assoc, inv_mul_cancel_left, FreeGroup.inv_mk, FreeGroup.mul_mk]
  rw [hprod, treeParent_mk_append _ _
    (treeReduced_invRev_append_of_head_ne hur hvr hhead) hvne]
  have hr : FreeGroup.IsReduced (z.toWord ++ v) := by
    rw [hv]
    exact FreeGroup.isReduced_toWord
  rw [hy', treeParent_mk_append _ _ hr hvne, FreeGroup.mk_toWord, ← FreeGroup.inv_mk, hg]
  group

/-- If [t is strictly between zero and one](hyp:ht) and [y lies off the root path
to g](hyp:hy), [the tree perturbation at g fixes the basis vector at y](goal). -/
lemma treePerturbation_delta_of_not_prefix (t : ℝ) (ht : DeformationRange t)
    (g y : FG) (hy : ¬ y.toWord.IsPrefix g.toWord) :
    treePerturbation t ht g (delta y) = delta y := by
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hy (by simp)
  have hyg : y ≠ g := by
    rintro rfl
    exact hy (by rfl)
  exact treePerturbation_delta_of_parent_eq t ht g y hyg hy1
    (treeParent_translate_of_not_prefix g y hy)

/-- If [y lies on the root path to g](hyp:hy) and [y differs from the endpoint g](hyp:hne),
[the neighbor of y toward g has parent y, is not the root, and lies on the root path
to g](goal).

This neighbor is obtained by translating y by the inverse of g, taking its parent,
and translating back by g. -/
lemma treeParent_next_of_prefix (g y : FG) (hy : y.toWord.IsPrefix g.toWord)
    (hne : y ≠ g) :
    treeParent (g * treeParent (g⁻¹ * y)) = y ∧
      g * treeParent (g⁻¹ * y) ≠ 1 ∧
      (g * treeParent (g⁻¹ * y)).toWord.IsPrefix g.toWord := by
  obtain ⟨v, hv⟩ := hy
  have hvne : v ≠ [] := by
    intro h
    apply hne
    have he : y.toWord = g.toWord := by simpa [h] using hv
    simpa only [FreeGroup.mk_toWord] using congrArg FreeGroup.mk he
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hvne
  have hr : FreeGroup.IsReduced (a :: w) := by
    have h := FreeGroup.isReduced_toWord (x := g)
    rw [← hv] at h
    exact List.IsChain.right_of_append h
  have hg : g = y * FreeGroup.mk (a :: w) := by
    have he := congrArg FreeGroup.mk hv
    rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord] at he
    exact he.symm
  have hprod : g⁻¹ * y = FreeGroup.mk (FreeGroup.invRev (a :: w)) := by
    rw [hg, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, FreeGroup.inv_mk]
  have hp : treeParent (g⁻¹ * y) = (FreeGroup.mk w)⁻¹ := by
    rw [hprod, treeParent, FreeGroup.toWord_mk, (treeReduced_invRev hr).reduce_eq]
    simp only [FreeGroup.invRev, List.map_cons, List.reverse_cons, List.dropLast_concat]
    exact FreeGroup.inv_mk.symm
  have hn : g * treeParent (g⁻¹ * y) = FreeGroup.mk (y.toWord ++ [a]) := by
    rw [hp, hg]
    have hm : FreeGroup.mk (a :: w) = FreeGroup.mk [a] * FreeGroup.mk w := by
      rw [FreeGroup.mul_mk, List.singleton_append]
    rw [hm, mul_assoc, mul_assoc, mul_inv_cancel, mul_one,
      ← (FreeGroup.mk_toWord (x := y)), FreeGroup.mul_mk]
    simp only [FreeGroup.mk_toWord]
  have hprefix : (y.toWord ++ [a]).IsPrefix g.toWord :=
    ⟨w, by simpa only [List.append_assoc, List.singleton_append] using hv⟩
  have hred : FreeGroup.IsReduced (y.toWord ++ [a]) :=
    (FreeGroup.isReduced_toWord (x := g)).prefix hprefix
  have hword : (g * treeParent (g⁻¹ * y)).toWord = y.toWord ++ [a] := by
    rw [hn, FreeGroup.toWord_mk, hred.reduce_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [treeParent, hword, List.dropLast_concat, FreeGroup.mk_toWord]
  · intro h
    have hl := congrArg (fun x : FG => x.toWord.length) h
    rw [hword] at hl
    simp at hl
  · rw [hword]
    exact hprefix

/-- If [t is strictly between zero and one](hyp:ht), [y lies on the root path to g](hyp:hy),
and [y differs from the endpoint g](hyp:hne), [the tree perturbation at g sends the
basis vector at y to the recursive tree vector at y scaled by the square root of
one minus t squared, minus t times the basis vector at its neighbor toward g](goal).

The neighbor toward g is obtained by translating y by the inverse of g, taking its
parent, and translating back by g. -/
lemma treePerturbation_delta_of_prefix (t : ℝ) (ht : DeformationRange t)
    (g y : FG) (hy : y.toWord.IsPrefix g.toWord) (hne : y ≠ g) :
    treePerturbation t ht g (delta y) =
      (rValue t ht : ℂ) • treeVector t ht y -
        (t : ℂ) • delta (g * treeParent (g⁻¹ * y)) := by
  obtain ⟨hp, hn, _⟩ := treeParent_next_of_prefix g y hy hne
  have hr : (rValue t ht : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (rValue_pos t ht))
  have hrsq : (rValue t ht : ℂ) ^ 2 = 1 - (t : ℂ) ^ 2 := by
    have h : rValue t ht ^ 2 = 1 - t ^ 2 := by
      apply Real.sq_sqrt
      have := ht.1
      have := ht.2
      nlinarith
    exact_mod_cast h
  rw [treePerturbation_delta t ht g y hne, treeVector_recursion t ht hn, hp]
  have hc : (rValue t ht : ℂ)⁻¹ - (rValue t ht : ℂ)⁻¹ * (t : ℂ) ^ 2 =
      (rValue t ht : ℂ) := by
    field_simp
    linear_combination -hrsq
  have hc' : (rValue t ht : ℂ)⁻¹ * ((t : ℂ) * (rValue t ht : ℂ)) = (t : ℂ) := by
    field_simp
  simp only [smul_sub, smul_add, smul_smul]
  rw [← sub_sub, ← sub_smul, ← pow_two, hc, hc']

end Papers.OaiNearInclusionsVon.ReusedTree
