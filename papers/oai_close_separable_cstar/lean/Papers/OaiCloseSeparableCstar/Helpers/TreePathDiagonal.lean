module

public import Papers.OaiCloseSeparableCstar.Helpers.TreePerturbation

/-! # Coordinate projections and diagonals for the finite root path

The path projection isolates the support of `T - 1`. The diagonals extend
`R` and `R'` by the identity on the orthogonal complement of the path span.
-/

@[expose] public section

namespace Papers.OaiCloseSeparableCstar

/-- For [a set A of tree vertices](hyp:A), [the coordinate projection onto
A](goal) retains coordinates in A and sets all other coordinates to zero. -/
-- @node: treeCoordinateProjection
noncomputable def treeCoordinateProjection (A : Set FG) : Op KSp := by
  classical
  exact diagOp (fun x => if x ∈ A then (1 : ℂ →L[ℂ] ℂ) else 0) 1
    (fun x => by split_ifs <;> simp)

open Classical in
/-- [The coordinate at x of the projection of v onto A equals the coordinate
of v at x when x belongs to A, and equals zero otherwise](goal). -/
-- @node: treeCoordinateProjection_apply
lemma treeCoordinateProjection_apply (A : Set FG) (v : KSp) (x : FG) :
    treeCoordinateProjection A v x = if x ∈ A then v x else 0 := by
  classical
  change (if x ∈ A then (1 : ℂ →L[ℂ] ℂ) else 0) (v x) = _
  split_ifs <;> rfl

/-- [The coordinate projection onto any set A of vertices has operator norm
at most one](goal). -/
-- @node: treeCoordinateProjection_norm_le
lemma treeCoordinateProjection_norm_le (A : Set FG) :
    ‖treeCoordinateProjection A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [one_mul]
  apply lp.norm_mono (by norm_num)
  intro x
  rw [treeCoordinateProjection_apply]
  split_ifs <;> simp

open Classical in
/-- [The coordinate projection onto A sends the unit coordinate vector at y
to itself if y belongs to A, and to zero otherwise](goal). -/
-- @node: treeCoordinateProjection_delta
lemma treeCoordinateProjection_delta (A : Set FG) (y : FG) :
    treeCoordinateProjection A (delta y) = if y ∈ A then delta y else 0 := by
  classical
  ext x
  rw [treeCoordinateProjection_apply]
  by_cases hxy : x = y
  · subst x
    split_ifs <;> rfl
  · have hd : delta y x = 0 := by simp [delta, lp.single_apply, Ne.symm hxy]
    by_cases hy : y ∈ A <;> simp [hy, hd]

/-- [Applying the coordinate projection onto A twice gives the same operator
as applying it once](goal). -/
-- @node: treeCoordinateProjection_idempotent
lemma treeCoordinateProjection_idempotent (A : Set FG) :
    treeCoordinateProjection A * treeCoordinateProjection A = treeCoordinateProjection A := by
  ext v x
  change treeCoordinateProjection A (treeCoordinateProjection A v) x = _
  simp only [treeCoordinateProjection_apply]
  split_ifs <;> rfl

/-- If [two bounded operators A and B agree on the unit coordinate vector at
every vertex](hyp:h), [A and B are equal](goal). -/
-- @node: treeOp_ext_delta
lemma treeOp_ext_delta {A B : Op KSp} (h : ∀ x, A (delta x) = B (delta x)) :
    A = B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro x
  apply ContinuousLinearMap.ext
  intro z
  have hs : lp.single 2 x z = z • delta x := by
    simp [delta, ← lp.single_smul]
  change A (lp.single 2 x z) = B (lp.single 2 x z)
  rw [hs, map_smul, map_smul, h]

/-- For [a group element g](hyp:g), [the root-path projection](goal) retains
exactly the coordinates at vertices on the path from the identity to g. -/
-- @node: treePathProjection
noncomputable def treePathProjection (g : FG) : Op KSp :=
  treeCoordinateProjection {y | y.toWord.IsPrefix g.toWord}

/-- For [t strictly between zero and one](hyp:ht), [composing the tree
perturbation at g minus the identity with the root-path projection at g on the
right leaves the perturbation minus the identity unchanged](goal). -/
-- @node: treePerturbation_sub_one_mul_pathProjection
lemma treePerturbation_sub_one_mul_pathProjection (t : ℝ) (ht : DeformationRange t)
    (g : FG) :
    (treePerturbation t ht g - 1) * treePathProjection g = treePerturbation t ht g - 1 := by
  apply treeOp_ext_delta
  intro y
  change (treePerturbation t ht g - 1)
    (treeCoordinateProjection {y | y.toWord.IsPrefix g.toWord} (delta y)) = _
  rw [treeCoordinateProjection_delta]
  by_cases hy : y.toWord.IsPrefix g.toWord
  · simp [hy]
  · simp [hy, treePerturbation_delta_of_not_prefix t ht g y hy]

/-- [The root-path projection at g sends the unit coordinate vector at y to
itself if y lies on the root path to g, and to zero otherwise](goal). -/
-- @node: treePathProjection_delta
lemma treePathProjection_delta (g y : FG) :
    treePathProjection g (delta y) =
      if y.toWord.IsPrefix g.toWord then delta y else 0 := by
  rw [treePathProjection, treeCoordinateProjection_delta]
  by_cases hy : y.toWord.IsPrefix g.toWord <;> simp [hy]

/-- For [t strictly between zero and one](hyp:ht), if [y lies on the root path
to g](hyp:hy), [the root-path projection at g fixes the root-path vector at
y](goal). -/
-- @node: treePathProjection_treeVector
lemma treePathProjection_treeVector (t : ℝ) (ht : DeformationRange t)
    (g y : FG) (hy : y.toWord.IsPrefix g.toWord) :
    treePathProjection g (treeVector t ht y) = treeVector t ht y := by
  ext x
  rw [treePathProjection, treeCoordinateProjection_apply]
  by_cases hx : x.toWord.IsPrefix g.toWord
  · simp [hx]
  · have hxy : ¬ x.toWord.IsPrefix y.toWord := fun h => hx (h.trans hy)
    simp [hx, treeVector_apply_eq_zero_of_not_prefix t ht y x hxy]

/-- For [t strictly between zero and one](hyp:ht), [composing the tree
perturbation at g minus the identity with the root-path projection at g on the
left leaves the perturbation minus the identity unchanged](goal). -/
-- @node: treePathProjection_mul_treePerturbation_sub_one
lemma treePathProjection_mul_treePerturbation_sub_one (t : ℝ) (ht : DeformationRange t)
    (g : FG) :
    treePathProjection g * (treePerturbation t ht g - 1) = treePerturbation t ht g - 1 := by
  apply treeOp_ext_delta
  intro y
  change treePathProjection g (treePerturbation t ht g (delta y) - delta y) =
    treePerturbation t ht g (delta y) - delta y
  by_cases hy : y.toWord.IsPrefix g.toWord
  · rw [map_sub, treePathProjection_delta, if_pos hy]
    congr 1
    by_cases hye : y = g
    · subst y
      rw [treePerturbation_delta_endpoint,
        treePathProjection_treeVector t ht g g (by rfl)]
    · obtain ⟨_, _, hn⟩ := treeParent_next_of_prefix g y hy hye
      rw [treePerturbation_delta_of_prefix t ht g y hy hye, map_sub, map_smul,
        map_smul, treePathProjection_treeVector t ht g y hy,
        treePathProjection_delta, if_pos hn]
  · rw [treePerturbation_delta_of_not_prefix t ht g y hy, sub_self, map_zero]

/-- For [t strictly between zero and one](hyp:ht), [the nonnegative square root
of one minus t squared is at most one](goal). -/
-- @node: rValue_le_one
lemma rValue_le_one (t : ℝ) (ht : DeformationRange t) : rValue t ht ≤ 1 := by
  unfold rValue
  exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg t])

/-- For [a real parameter t](hyp:t) [strictly between zero and one](hyp:ht),
[a path endpoint g](hyp:g), and [an exceptional vertex a](hyp:a), [the path
diagonal operator](goal) multiplies coordinates on the root path to g other
than a by the square root of one minus t squared, and leaves all other
coordinates unchanged. -/
-- @node: treePathDiagonal
noncomputable def treePathDiagonal (t : ℝ) (ht : DeformationRange t) (g a : FG) :
    Op KSp :=
  1 + ((rValue t ht : ℂ) - 1) •
    treeCoordinateProjection {y | y.toWord.IsPrefix g.toWord ∧ y ≠ a}

/-- For [t strictly between zero and one](hyp:ht), [the coordinate at x of the
path diagonal applied to v is the coordinate of v at x multiplied by the
square root of one minus t squared when x lies on the root path to g and
differs from a, and is the original coordinate otherwise](goal). -/
-- @node: treePathDiagonal_apply
lemma treePathDiagonal_apply (t : ℝ) (ht : DeformationRange t) (g a x : FG) (v : KSp) :
    treePathDiagonal t ht g a v x =
      if x.toWord.IsPrefix g.toWord ∧ x ≠ a then (rValue t ht : ℂ) * v x else v x := by
  classical
  change v x + ((rValue t ht : ℂ) - 1) *
    treeCoordinateProjection {y | y.toWord.IsPrefix g.toWord ∧ y ≠ a} v x = _
  rw [treeCoordinateProjection_apply]
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> ring

/-- For [t strictly between zero and one](hyp:ht), [the path diagonal with
endpoint g and exceptional vertex a has operator norm at most one](goal). -/
-- @node: treePathDiagonal_norm_le
lemma treePathDiagonal_norm_le (t : ℝ) (ht : DeformationRange t) (g a : FG) :
    ‖treePathDiagonal t ht g a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [one_mul]
  apply lp.norm_mono (by norm_num)
  intro x
  rw [treePathDiagonal_apply]
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rValue_pos t ht)]
    exact mul_le_of_le_one_left (norm_nonneg _) (rValue_le_one t ht)
  · exact le_rfl

/-- For [t strictly between zero and one](hyp:ht), [the path diagonal with
endpoint g and exceptional vertex a differs from the identity by an operator
of norm at most one minus the square root of one minus t squared](goal). -/
-- @node: treePathDiagonal_sub_one_norm_le
lemma treePathDiagonal_sub_one_norm_le (t : ℝ) (ht : DeformationRange t) (g a : FG) :
    ‖treePathDiagonal t ht g a - 1‖ ≤ 1 - rValue t ht := by
  have hr : ‖(rValue t ht : ℂ) - 1‖ = 1 - rValue t ht := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (rValue_le_one t ht))]
    ring
  rw [treePathDiagonal, add_sub_cancel_left, norm_smul, hr]
  simpa using mul_le_mul_of_nonneg_left
    (treeCoordinateProjection_norm_le {y | y.toWord.IsPrefix g.toWord ∧ y ≠ a})
    (sub_nonneg.mpr (rValue_le_one t ht))

/-- For [t strictly between zero and one](hyp:ht), [the path diagonal with
endpoint g and exceptional vertex a multiplies the unit coordinate vector at y
by the square root of one minus t squared if y lies on the root path to g and
differs from a, and fixes that vector otherwise](goal). -/
-- @node: treePathDiagonal_delta
lemma treePathDiagonal_delta (t : ℝ) (ht : DeformationRange t) (g a y : FG) :
    treePathDiagonal t ht g a (delta y) =
      if y.toWord.IsPrefix g.toWord ∧ y ≠ a then
        (rValue t ht : ℂ) • delta y else delta y := by
  classical
  change delta y + ((rValue t ht : ℂ) - 1) •
    treeCoordinateProjection {y | y.toWord.IsPrefix g.toWord ∧ y ≠ a} (delta y) = _
  rw [treeCoordinateProjection_delta]
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> module

end Papers.OaiCloseSeparableCstar
