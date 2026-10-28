module

public import Papers.OaiCloseSeparableCstar.Helpers.TreePathDiagonal
public import Mathlib.Analysis.Normed.Ring.Units

/-! # Norm estimates for the finite root-path calculation

The Neumann series bounds the column operator `R (1 - t S*)⁻¹`. The resulting
estimate for `X R' - t S` is independent of the length of the root path.
-/

public section

namespace Papers.OaiCloseSeparableCstar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If [t is strictly between zero and one](hyp:ht) and [the operator norm of A
is at most one](hyp:hA), [the operator norm of t times A is at most t](goal). -/
-- @node: tree_scaled_contraction_norm
lemma tree_scaled_contraction_norm (t : ℝ) (ht : DeformationRange t)
    (A : Op H) (hA : ‖A‖ ≤ 1) : ‖(t : ℂ) • A‖ ≤ t := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
  simpa using mul_le_mul_of_nonneg_left hA ht.1.le

/-- If [t is strictly between zero and one](hyp:ht) and [the operator norm of A
is at most one](hyp:hA), [the inverse of the identity minus t times A has
operator norm at most one divided by one minus t](goal). -/
-- @node: tree_resolvent_norm
lemma tree_resolvent_norm (t : ℝ) (ht : DeformationRange t)
    (A : Op H) (hA : ‖A‖ ≤ 1) :
    ‖Ring.inverse (1 - (t : ℂ) • A)‖ ≤ (1 - t)⁻¹ := by
  have hle := tree_scaled_contraction_norm t ht A hA
  have hlt : ‖(t : ℂ) • A‖ < 1 := hle.trans_lt ht.2
  rw [← geom_series_eq_inverse _ hlt]
  calc
    ‖∑' n : ℕ, ((t : ℂ) • A) ^ n‖ ≤ (1 - ‖(t : ℂ) • A‖)⁻¹ :=
      (tsum_geometric_le_of_norm_lt_one _ hlt).trans (by
        have h1 : ‖(1 : Op H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        linarith)
    _ ≤ (1 - t)⁻¹ := by
      apply (inv_le_inv₀ (sub_pos.mpr hlt) (sub_pos.mpr ht.2)).2
      linarith

/-- If [t is strictly between zero and one](hyp:ht) and [the operator norm of A
is at most one](hyp:hA), [the inverse of the identity minus t times A differs
from the identity by an operator of norm at most t divided by one minus t](goal). -/
-- @node: tree_resolvent_sub_one_norm
lemma tree_resolvent_sub_one_norm (t : ℝ) (ht : DeformationRange t)
    (A : Op H) (hA : ‖A‖ ≤ 1) :
    ‖Ring.inverse (1 - (t : ℂ) • A) - 1‖ ≤ t / (1 - t) := by
  have hle := tree_scaled_contraction_norm t ht A hA
  have hlt : ‖(t : ℂ) • A‖ < 1 := hle.trans_lt ht.2
  have he : Ring.inverse (1 - (t : ℂ) • A) - 1 =
      ((t : ℂ) • A) * Ring.inverse (1 - (t : ℂ) • A) := by
    have h := NormedRing.inverse_one_sub_nth_order' 1 hlt
    simpa only [Finset.sum_range_one, pow_zero, pow_one, add_sub_cancel_left]
      using congrArg (fun B : Op H => B - 1) h
  rw [he, div_eq_mul_inv]
  exact (norm_mul_le _ _).trans (mul_le_mul hle (tree_resolvent_norm t ht A hA)
    (norm_nonneg _) ht.1.le)

/-- If [t is strictly between zero and one](hyp:ht), [A has operator norm at
most one](hyp:hA), and [X times the identity minus t times A equals R](hyp:hrec),
then [X equals R times the inverse of the identity minus t times A](goal). -/
-- @node: tree_columnOperator_factorization
lemma tree_columnOperator_factorization (t : ℝ) (ht : DeformationRange t)
    (X R A : Op H) (hA : ‖A‖ ≤ 1) (hrec : X * (1 - (t : ℂ) • A) = R) :
    X = R * Ring.inverse (1 - (t : ℂ) • A) := by
  have hlt : ‖(t : ℂ) • A‖ < 1 :=
    (tree_scaled_contraction_norm t ht A hA).trans_lt ht.2
  rw [← hrec, mul_assoc,
    Ring.mul_inverse_cancel _ (isUnit_one_sub_of_norm_lt_one hlt), mul_one]

/-- Suppose [t is strictly between zero and one](hyp:ht), [R has operator norm
at most one](hyp:hR), [A has operator norm at most one](hyp:hA), and [R differs
from the identity by an operator of norm at most one minus the square root of
one minus t squared](hyp:hRdiff). Then [R times the inverse of the identity
minus t times A differs from the identity in norm by at most one minus that
square root plus t divided by one minus t](goal). -/
-- @node: tree_columnOperator_sub_one_norm
lemma tree_columnOperator_sub_one_norm (t : ℝ) (ht : DeformationRange t)
    (R A : Op H) (hR : ‖R‖ ≤ 1) (hA : ‖A‖ ≤ 1)
    (hRdiff : ‖R - 1‖ ≤ 1 - rValue t ht) :
    ‖R * Ring.inverse (1 - (t : ℂ) • A) - 1‖ ≤
      1 - rValue t ht + t / (1 - t) := by
  have he : R * Ring.inverse (1 - (t : ℂ) • A) - 1 =
      (R - 1) + R * (Ring.inverse (1 - (t : ℂ) • A) - 1) := by
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖R - 1‖ + ‖R * (Ring.inverse (1 - (t : ℂ) • A) - 1)‖ := norm_add_le _ _
    _ ≤ (1 - rValue t ht) + 1 * (t / (1 - t)) := by
      apply add_le_add hRdiff
      exact (norm_mul_le _ _).trans (mul_le_mul hR
        (tree_resolvent_sub_one_norm t ht A hA) (norm_nonneg _) zero_le_one)
    _ = _ := by ring

/-- Suppose [t is strictly between zero and one](hyp:ht), [the norm of X minus
the identity is at most one minus the square root of one minus t squared plus
t divided by one minus t](hyp:hX), [R′ has norm at most one](hyp:hR'), [the norm
of R′ minus the identity is at most one minus that square root](hyp:hR'diff),
and [S has norm at most one](hyp:hS). Then [X times R′ minus t times S differs
from the identity in norm by at most twice one minus that square root, plus
t divided by one minus t, plus t](goal). -/
-- @node: tree_pathOperator_sub_one_norm
lemma tree_pathOperator_sub_one_norm (t : ℝ) (ht : DeformationRange t)
    (X R' S : Op H) (hX : ‖X - 1‖ ≤ 1 - rValue t ht + t / (1 - t))
    (hR' : ‖R'‖ ≤ 1) (hR'diff : ‖R' - 1‖ ≤ 1 - rValue t ht)
    (hS : ‖S‖ ≤ 1) :
    ‖X * R' - (t : ℂ) • S - 1‖ ≤ cBound t ht := by
  have he : X * R' - (t : ℂ) • S - 1 =
      ((X - 1) * R' + (R' - 1)) - (t : ℂ) • S := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(X - 1) * R' + (R' - 1)‖ + ‖(t : ℂ) • S‖ := norm_sub_le _ _
    _ ≤ (‖X - 1‖ * ‖R'‖ + ‖R' - 1‖) + t := by
      apply add_le_add _ (tree_scaled_contraction_norm t ht S hS)
      exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (le_refl _))
    _ ≤ ((1 - rValue t ht + t / (1 - t)) * 1 + (1 - rValue t ht)) + t := by
      apply add_le_add _ (le_refl _)
      apply add_le_add _ hR'diff
      exact mul_le_mul hX hR' (norm_nonneg _) (le_trans (norm_nonneg _) hX)
    _ = cBound t ht := by unfold cBound; ring

/-- Suppose [t is strictly between zero and one](hyp:ht), [S has norm at most
one](hyp:hS), [R has norm at most one](hyp:hR), [R′ has norm at most one](hyp:hR'),
[R differs from the identity in norm by at most one minus the square root of
one minus t squared](hyp:hRdiff), and [R′ satisfies the same bound](hyp:hR'diff).
If [X times the identity minus t times the adjoint of S equals R](hyp:hrec) and
[T equals X times R′ minus t times S](hyp:hT), then [the norm of T minus the
identity is at most twice one minus that square root, plus t divided by one
minus t, plus t](goal). -/
-- @node: tree_pathOperator_norm_of_recursion
lemma tree_pathOperator_norm_of_recursion (t : ℝ) (ht : DeformationRange t)
    (T X R R' S : Op H) (hS : ‖S‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hR' : ‖R'‖ ≤ 1)
    (hRdiff : ‖R - 1‖ ≤ 1 - rValue t ht) (hR'diff : ‖R' - 1‖ ≤ 1 - rValue t ht)
    (hrec : X * (1 - (t : ℂ) • star S) = R)
    (hT : T = X * R' - (t : ℂ) • S) :
    ‖T - 1‖ ≤ cBound t ht := by
  have hback : ‖star S‖ ≤ 1 := by simpa only [norm_star] using hS
  have hX : ‖X - 1‖ ≤ 1 - rValue t ht + t / (1 - t) := by
    rw [tree_columnOperator_factorization t ht X R (star S) hback hrec]
    exact tree_columnOperator_sub_one_norm t ht R (star S) hR hback hRdiff
  rw [hT]
  exact tree_pathOperator_sub_one_norm t ht X R' S hX hR' hR'diff hS

/-- For [t strictly between zero and one](hyp:ht), [the norm of the tree
perturbation at g minus the identity equals the norm of the difference between
the tree unitary and the left regular unitary at g](goal). -/
-- @node: treePerturbation_norm_eq
lemma treePerturbation_norm_eq (t : ℝ) (ht : DeformationRange t) (g : FG) :
    ‖treePerturbation t ht g - 1‖ =
      ‖(treeUnitaryRep t ht g : Op KSp) - (leftReg g : Op KSp)‖ := by
  have hcancel : (leftReg g : Op KSp) * (leftReg g⁻¹ : Op KSp) = 1 := by
    rw [← Submonoid.coe_mul, ← map_mul, mul_inv_cancel, map_one, Submonoid.coe_one]
  have he : ((treeUnitaryRep t ht g : Op KSp) - (leftReg g : Op KSp)) *
      (leftReg g⁻¹ : Op KSp) = treePerturbation t ht g - 1 := by
    rw [sub_mul, hcancel]
    rfl
  rw [← he, CStarRing.norm_mul_coe_unitary]

end Papers.OaiCloseSeparableCstar
