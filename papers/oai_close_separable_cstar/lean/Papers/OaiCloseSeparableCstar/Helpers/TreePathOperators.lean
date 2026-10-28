module

public import Papers.OaiCloseSeparableCstar.Helpers.TreePathDiagonal

/-! # Finite root-path column operators

The column operator is a finite rank modification of the identity. Its columns
are the recursive tree vectors on the path and the usual basis vectors elsewhere.
-/

@[expose] public section

namespace Papers.OaiCloseSeparableCstar

/-- For [an endpoint g](hyp:g), [the finite set of vertices on the path from the root to g](goal)
consists of the group elements represented by prefixes of its reduced word. -/
-- @node: treePathVertices
noncomputable def treePathVertices (g : FG) : Finset FG := by
  classical
  exact (g.toWord.inits.map FreeGroup.mk).toFinset

-- @node: mem_treePathVertices
/-- [A vertex y belongs to the root path ending at g exactly when its reduced word is a
prefix of the reduced word of g](goal). -/
lemma mem_treePathVertices (g y : FG) :
    y ∈ treePathVertices g ↔ y.toWord.IsPrefix g.toWord := by
  classical
  simp only [treePathVertices, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hp := (List.mem_inits _ _).mp hw
    have hr : FreeGroup.IsReduced w := (FreeGroup.isReduced_toWord (x := g)).prefix hp
    rw [FreeGroup.toWord_mk, hr.reduce_eq]
    exact hp
  · intro hy
    exact ⟨y.toWord, (List.mem_inits _ _).mpr hy, FreeGroup.mk_toWord⟩

/-- For [a real deformation parameter t](hyp:t) [strictly between zero and one](hyp:ht) and
[an endpoint g](hyp:g), [the path column operator](goal) sends each basis vector on the
root path to its recursive tree vector and fixes every basis vector off that path. -/
-- @node: treePathColumnOperator
noncomputable def treePathColumnOperator (t : ℝ) (ht : DeformationRange t) (g : FG) :
    Op KSp :=
  1 + ∑ y ∈ treePathVertices g,
    (lp.evalCLM ℂ (fun _ : FG => ℂ) 2 y).smulRight (treeVector t ht y - delta y)

-- @node: treePathColumnOperator_delta
/-- If [t is strictly between zero and one](hyp:ht), [the path column operator ending at g
sends the basis vector at y to its recursive tree vector when y lies on the root path
to g, and otherwise leaves it unchanged](goal). -/
lemma treePathColumnOperator_delta (t : ℝ) (ht : DeformationRange t) (g y : FG) :
    treePathColumnOperator t ht g (delta y) =
      if y.toWord.IsPrefix g.toWord then treeVector t ht y else delta y := by
  classical
  have heval (x : FG) (v : KSp) :
      ((lp.evalCLM ℂ (fun _ : FG => ℂ) 2 x).smulRight v) (delta y) =
        if x = y then v else 0 := by
    change delta y x • v = _
    by_cases h : x = y
    · subst x
      simp [delta]
    · simp [delta, lp.single_apply, h]
  simp only [treePathColumnOperator, add_apply,
    one_apply_eq_self, sum_apply, heval]
  by_cases hy : y.toWord.IsPrefix g.toWord
  · simp [hy, mem_treePathVertices]
  · simp [hy, mem_treePathVertices]

-- @node: treePathColumnOperator_delta_of_prefix
/-- If [t is strictly between zero and one](hyp:ht) and [y lies on the root path to g](hyp:hy),
[the path column operator ending at g sends the basis vector at y to its recursive
tree vector](goal). -/
lemma treePathColumnOperator_delta_of_prefix (t : ℝ) (ht : DeformationRange t)
    (g y : FG) (hy : y.toWord.IsPrefix g.toWord) :
    treePathColumnOperator t ht g (delta y) = treeVector t ht y := by
  rw [treePathColumnOperator_delta, if_pos hy]

-- @node: treePathColumnOperator_delta_of_not_prefix
/-- If [t is strictly between zero and one](hyp:ht) and [y lies off the root path to g](hyp:hy),
[the path column operator ending at g fixes the basis vector at y](goal). -/
lemma treePathColumnOperator_delta_of_not_prefix (t : ℝ) (ht : DeformationRange t)
    (g y : FG) (hy : ¬ y.toWord.IsPrefix g.toWord) :
    treePathColumnOperator t ht g (delta y) = delta y := by
  rw [treePathColumnOperator_delta, if_neg hy]

/-- If [y lies on the root path to g](hyp:hy), [its parent also lies on that path](goal). -/
-- @node: treeParent_prefix_of_prefix
lemma treeParent_prefix_of_prefix (g y : FG) (hy : y.toWord.IsPrefix g.toWord) :
    (treeParent y).toWord.IsPrefix g.toWord := by
  rw [treeParent_toWord]
  exact (List.dropLast_prefix _).trans hy

/-- If [t is strictly between zero and one](hyp:ht), [y lies on the root path to g](hyp:hy),
and [y is not the root](hyp:hne), [the path column operator sends the basis vector at y
minus t times the basis vector at its parent to the basis vector at y scaled by
the square root of one minus t squared](goal). -/
-- @node: treePathColumnOperator_recursion_delta
lemma treePathColumnOperator_recursion_delta (t : ℝ) (ht : DeformationRange t)
    (g y : FG) (hy : y.toWord.IsPrefix g.toWord) (hne : y ≠ 1) :
    treePathColumnOperator t ht g
      (delta y - (t : ℂ) • delta (treeParent y)) =
        (rValue t ht : ℂ) • delta y := by
  rw [map_sub, map_smul, treePathColumnOperator_delta_of_prefix t ht g y hy,
    treePathColumnOperator_delta_of_prefix t ht g _ (treeParent_prefix_of_prefix g y hy),
    treeVector_recursion t ht hne, add_sub_cancel_left]

/-- If [x lies on the root path to g](hyp:hx), [y lies on that same path](hyp:hy), and
[their reduced words have the same length](hyp:hl), [x and y are equal](goal). -/
-- @node: treePathVertex_eq_of_length
lemma treePathVertex_eq_of_length (g x y : FG)
    (hx : x.toWord.IsPrefix g.toWord) (hy : y.toWord.IsPrefix g.toWord)
    (hl : x.toWord.length = y.toWord.length) : x = y := by
  have hw : x.toWord = y.toWord := by
    rw [List.prefix_iff_eq_take.mp hx, List.prefix_iff_eq_take.mp hy, hl]
  simpa only [FreeGroup.mk_toWord] using congrArg FreeGroup.mk hw

/-- If [x lies on the root path to g](hyp:hx), [y lies on that same path](hyp:hy),
[x is not the root](hyp:hx1), [y is not the root](hyp:hy1), and
[their parents coincide](hyp:hp), [x and y are equal](goal). -/
-- @node: treeParent_injective_on_path
lemma treeParent_injective_on_path (g x y : FG)
    (hx : x.toWord.IsPrefix g.toWord) (hy : y.toWord.IsPrefix g.toWord)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hp : treeParent x = treeParent y) : x = y := by
  apply treePathVertex_eq_of_length g x y hx hy
  have hl := congrArg (fun z : FG => z.toWord.length) hp
  rw [treeParent_toWord, treeParent_toWord, List.length_dropLast,
    List.length_dropLast] at hl
  have hxpos : 0 < x.toWord.length := List.length_pos_iff.mpr (by simpa using hx1)
  have hypos : 0 < y.toWord.length := List.length_pos_iff.mpr (by simpa using hy1)
  omega

/-- For [an endpoint g](hyp:g), [the backward path shift](goal) sends each basis vector
at a non-root vertex on the root path to g to the basis vector at its parent, and
sends all other basis vectors to zero. -/
-- @node: treePathBackwardShift
noncomputable def treePathBackwardShift (g : FG) : Op KSp :=
  ∑ y ∈ (treePathVertices g).erase 1, matUnit (treeParent y) y

-- @node: treePathBackwardShift_delta
/-- [The backward path shift ending at g sends the basis vector at y to the basis vector
at its parent if y is a non-root vertex on the root path to g, and to zero otherwise](goal). -/
lemma treePathBackwardShift_delta (g y : FG) :
    treePathBackwardShift g (delta y) =
      if y.toWord.IsPrefix g.toWord ∧ y ≠ 1 then delta (treeParent y) else 0 := by
  classical
  simp only [treePathBackwardShift, sum_apply, matUnit_delta]
  simp only [eq_comm (a := y)]
  rw [Finset.sum_ite_eq']
  simp [mem_treePathVertices, and_comm]

open scoped InnerProductSpace in
/-- [The adjoint of the matrix unit taking the basis vector at y to the basis vector
at x is the matrix unit taking the basis vector at x to the basis vector at y](goal). -/
-- @node: treeMatUnit_star
lemma treeMatUnit_star (x y : FG) : star (matUnit x y) = matUnit y x := by
  have hr (a b : FG) : matUnit a b = InnerProductSpace.rankOne ℂ (delta a) (delta b) := by
    ext v z
    change (v b • delta a) z = _
    simp [InnerProductSpace.rankOne_apply, delta, lp.inner_single_left]
  rw [hr, ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne, ← hr]

/-- For [an endpoint g](hyp:g), [the forward path shift](goal) is the adjoint of the
backward path shift: it moves a basis vector at a nonterminal path vertex to the
basis vector at its child toward g, and sends the remaining basis vectors to zero. -/
-- @node: treePathShift
noncomputable def treePathShift (g : FG) : Op KSp := star (treePathBackwardShift g)

-- @node: treePathShift_star_delta
/-- [The adjoint of the forward path shift ending at g sends the basis vector at y
to the basis vector at its parent if y is a non-root vertex on the root path to g,
and to zero otherwise](goal). -/
lemma treePathShift_star_delta (g y : FG) :
    star (treePathShift g) (delta y) =
      if y.toWord.IsPrefix g.toWord ∧ y ≠ 1 then delta (treeParent y) else 0 := by
  rw [treePathShift, star_star, treePathBackwardShift_delta]

/-- If [y lies on the root path to g](hyp:hy) and [y is not the root](hyp:hne),
[the forward path shift ending at g sends the basis vector at the parent of y to
the basis vector at y](goal). -/
-- @node: treePathShift_delta_parent
lemma treePathShift_delta_parent (g y : FG)
    (hy : y.toWord.IsPrefix g.toWord) (hne : y ≠ 1) :
    treePathShift g (delta (treeParent y)) = delta y := by
  classical
  simp only [treePathShift, treePathBackwardShift, star_sum, treeMatUnit_star,
    sum_apply, matUnit_delta]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z hz hzy
    have hz' := Finset.mem_erase.mp hz
    have hp : treeParent y ≠ treeParent z := by
      intro hp
      exact hzy (treeParent_injective_on_path g z y
        ((mem_treePathVertices g z).mp hz'.2) hy hz'.1 hne hp.symm)
    simp [hp]
  · intro h
    exact False.elim (h (Finset.mem_erase.mpr
      ⟨hne, (mem_treePathVertices g y).mpr hy⟩))

-- @node: treePathShift_delta_of_prefix
/-- If [y lies on the root path to g](hyp:hy) and [y differs from the endpoint g](hyp:hne),
[the forward path shift sends the basis vector at y to the basis vector at its next
neighbor toward g, obtained by translating y by the inverse of g, taking its parent,
and translating back by g](goal). -/
lemma treePathShift_delta_of_prefix (g y : FG)
    (hy : y.toWord.IsPrefix g.toWord) (hne : y ≠ g) :
    treePathShift g (delta y) = delta (g * treeParent (g⁻¹ * y)) := by
  obtain ⟨hp, hn, hpath⟩ := treeParent_next_of_prefix g y hy hne
  simpa only [hp] using treePathShift_delta_parent g _ hpath hn

-- @node: treePathShift_delta_endpoint
/-- [The forward path shift ending at g sends the basis vector at the endpoint g to zero](goal). -/
lemma treePathShift_delta_endpoint (g : FG) : treePathShift g (delta g) = 0 := by
  classical
  simp only [treePathShift, treePathBackwardShift, star_sum, treeMatUnit_star,
    sum_apply, matUnit_delta]
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨hy1, hy⟩ := Finset.mem_erase.mp hy
  have hlen := ((mem_treePathVertices g y).mp hy).length_le
  have hlt := treeParent_length_lt hy1
  have hne : g ≠ treeParent y := by
    intro he
    rw [← he] at hlt
    omega
  simp [hne]

-- @node: treePathShift_delta_of_not_prefix
/-- If [y lies off the root path to g](hyp:hy), [the forward path shift ending at g
sends the basis vector at y to zero](goal). -/
lemma treePathShift_delta_of_not_prefix (g y : FG)
    (hy : ¬ y.toWord.IsPrefix g.toWord) : treePathShift g (delta y) = 0 := by
  classical
  simp only [treePathShift, treePathBackwardShift, star_sum, treeMatUnit_star,
    sum_apply, matUnit_delta]
  apply Finset.sum_eq_zero
  intro z hz
  have hp := treeParent_prefix_of_prefix g z
    ((mem_treePathVertices g z).mp (Finset.mem_erase.mp hz).2)
  have hne : y ≠ treeParent z := by
    rintro rfl
    exact hy hp
  simp [hne]

/-- [The forward path shift ending at g composed with its adjoint equals the coordinate
projection onto the span of the basis vectors at the non-root vertices of the root
path to g](goal). -/
-- @node: treePathShift_mul_star
lemma treePathShift_mul_star (g : FG) :
    treePathShift g * star (treePathShift g) =
      treeCoordinateProjection {y | y.toWord.IsPrefix g.toWord ∧ y ≠ 1} := by
  apply treeOp_ext_delta
  intro y
  change treePathShift g (star (treePathShift g) (delta y)) = _
  rw [treePathShift_star_delta, treeCoordinateProjection_delta]
  by_cases hy : y.toWord.IsPrefix g.toWord ∧ y ≠ 1
  · simp only [Set.mem_ofPred_eq]
    rw [if_pos hy, if_pos hy]
    exact treePathShift_delta_parent g y hy.1 hy.2
  · simp [hy]

-- @node: treePathShift_norm_le
/-- [The operator norm of the forward path shift ending at g is at most one](goal). -/
lemma treePathShift_norm_le (g : FG) : ‖treePathShift g‖ ≤ 1 := by
  have hb := treeCoordinateProjection_norm_le
    {y | y.toWord.IsPrefix g.toWord ∧ y ≠ 1}
  rw [← treePathShift_mul_star, CStarRing.norm_self_mul_star] at hb
  nlinarith [norm_nonneg (treePathShift g)]

/-- If [t is strictly between zero and one](hyp:ht), [the path column operator ending at g
composed with the identity minus t times the adjoint forward path shift equals the
diagonal operator that scales non-root path coordinates by the square root of one
minus t squared and leaves all other coordinates unchanged](goal). -/
-- @node: treePathColumnOperator_recursion
lemma treePathColumnOperator_recursion (t : ℝ) (ht : DeformationRange t) (g : FG) :
    treePathColumnOperator t ht g * (1 - (t : ℂ) • star (treePathShift g)) =
      treePathDiagonal t ht g 1 := by
  apply treeOp_ext_delta
  intro y
  change treePathColumnOperator t ht g
    (delta y - (t : ℂ) • star (treePathShift g) (delta y)) = _
  rw [treePathShift_star_delta, treePathDiagonal_delta]
  by_cases hy : y.toWord.IsPrefix g.toWord ∧ y ≠ 1
  · rw [if_pos hy, if_pos hy]
    exact treePathColumnOperator_recursion_delta t ht g y hy.1 hy.2
  · rw [if_neg hy, if_neg hy, smul_zero, sub_zero]
    by_cases hp : y.toWord.IsPrefix g.toWord
    · have he : y = 1 := Classical.byContradiction (fun h => hy ⟨hp, h⟩)
      subst y
      rw [treePathColumnOperator_delta_of_prefix t ht g 1 hp, treeVector_one]
    · exact treePathColumnOperator_delta_of_not_prefix t ht g y hp

/-- If [t is strictly between zero and one](hyp:ht), [the tree perturbation at g equals the
path column operator composed with the diagonal that scales all path coordinates
except the endpoint by the square root of one minus t squared, minus t times the
forward path shift](goal). -/
-- @node: treePerturbation_eq_pathOperators
lemma treePerturbation_eq_pathOperators (t : ℝ) (ht : DeformationRange t) (g : FG) :
    treePerturbation t ht g =
      treePathColumnOperator t ht g * treePathDiagonal t ht g g -
        (t : ℂ) • treePathShift g := by
  apply treeOp_ext_delta
  intro y
  change treePerturbation t ht g (delta y) =
    treePathColumnOperator t ht g (treePathDiagonal t ht g g (delta y)) -
      (t : ℂ) • treePathShift g (delta y)
  rw [treePathDiagonal_delta]
  by_cases hy : y.toWord.IsPrefix g.toWord
  · by_cases hne : y ≠ g
    · rw [if_pos ⟨hy, hne⟩, map_smul,
        treePathColumnOperator_delta_of_prefix t ht g y hy,
        treePathShift_delta_of_prefix g y hy hne]
      exact treePerturbation_delta_of_prefix t ht g y hy hne
    · have he : y = g := Classical.not_not.mp hne
      subst y
      rw [if_neg (by simp), treePathShift_delta_endpoint, smul_zero, sub_zero,
        treePathColumnOperator_delta_of_prefix t ht g g hy,
        treePerturbation_delta_endpoint]
  · rw [if_neg (fun h => hy h.1), treePathShift_delta_of_not_prefix g y hy,
      smul_zero, sub_zero, treePathColumnOperator_delta_of_not_prefix t ht g y hy]
    exact treePerturbation_delta_of_not_prefix t ht g y hy

end Papers.OaiCloseSeparableCstar
