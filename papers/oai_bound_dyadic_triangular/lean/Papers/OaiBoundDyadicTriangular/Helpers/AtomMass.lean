module

public import Papers.OaiBoundDyadicTriangular.Helpers.AtomEnergy
public import Mathlib.Analysis.MeanInequalitiesPow

/-! # Probability normalization and the discrete edge-mass bound -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: atomCubeMass
/-- For [three input functions](hyp:F), [a parent scale and an atom scale](hyp:k,m),
[three interval indices](hyp:n), and [an edge of the triangle](hyp:v), the
[normalized cubic edge mass](goal) is the sum of the absolute cubes of the sampled
input values over all atom pairs, weighted by the product of their atom weights. -/
noncomputable def atomCubeMass (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) : ℝ :=
  ∑ i : Atom k m, ∑ j : Atom k m,
    (atomWeight k m * atomWeight k m) * |atomValue F k m n v i j| ^ 3

-- @node: atomWeight_pos
/-- [The normalized atom weight is strictly positive](goal) at any two integer scales. -/
lemma atomWeight_pos (k m : ℤ) : 0 < atomWeight k m := by
  unfold atomWeight
  positivity

-- @node: atomWeight_card
/-- If [the atom scale is no larger than the parent scale](hyp:hk),
[the number of atoms times their common normalized weight equals one](goal). -/
lemma atomWeight_card (k m : ℤ) (hk : TotalScale k m) :
    (Fintype.card (Atom k m) : ℝ) * atomWeight k m = 1 := by
  have he : ((k - m).toNat : ℤ) = k - m := Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hc : (Fintype.card (Atom k m) : ℝ) = (2 : ℝ) ^ (k - m) := by
    simp only [Atom, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    rw [← zpow_natCast, he]
  rw [hc, atomWeight, ← zpow_add₀ (by norm_num)]
  simp

-- @node: atomPairWeight_sum
/-- If [the atom scale is no larger than the parent scale](hyp:hk),
[the product weights sum to one over all pairs of atoms](goal). -/
lemma atomPairWeight_sum (k m : ℤ) (hk : TotalScale k m) :
    (∑ _i : Atom k m, ∑ _j : Atom k m, atomWeight k m * atomWeight k m) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = ((Fintype.card (Atom k m) : ℝ) * atomWeight k m) ^ 2 := by ring
    _ = 1 := by rw [atomWeight_card k m hk]; norm_num

-- @node: weightedEdge_trace_eq_atom_squares
/-- [The trace of the weighted edge matrix times its transpose equals the sum of
squared sampled input values, weighted by the product of the two atom weights](goal). -/
lemma weightedEdge_trace_eq_atom_squares (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) :
    (weightedEdge F k m n v * (weightedEdge F k m n v).transpose).trace =
      ∑ i : Atom k m, ∑ j : Atom k m,
        (atomWeight k m * atomWeight k m) * (atomValue F k m n v i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [weightedEdge]
  rw [show (Real.sqrt (atomWeight k m * atomWeight k m) * atomValue F k m n v i j) *
      (Real.sqrt (atomWeight k m * atomWeight k m) * atomValue F k m n v i j) =
      Real.sqrt (atomWeight k m * atomWeight k m) ^ 2 *
        atomValue F k m n v i j ^ 2 by ring,
    Real.sq_sqrt (mul_nonneg (atomWeight_pos k m).le (atomWeight_pos k m).le)]

-- @node: weightedEdge_mass_le_atom_cubes
/-- If [the atom scale is no larger than the parent scale](hyp:hk),
[the trace of the weighted edge matrix times its transpose, raised to the
three-halves power, is at most the normalized cubic edge mass](goal). -/
lemma weightedEdge_mass_le_atom_cubes (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) (hk : TotalScale k m) :
    ((weightedEdge F k m n v * (weightedEdge F k m n v).transpose).trace) ^
        (3 / 2 : ℝ) ≤
      atomCubeMass F k m n v := by
  have hw : (∑ a : Atom k m × Atom k m, atomWeight k m * atomWeight k m) = 1 := by
    simpa only [Fintype.sum_prod_type] using atomPairWeight_sum k m hk
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ : Atom k m × Atom k m => atomWeight k m * atomWeight k m)
    (fun a => atomValue F k m n v a.1 a.2 ^ 2)
    (by intro a _; positivity [atomWeight_pos k m]) hw
    (by intro a _; positivity) (p := (3 / 2 : ℝ)) (by norm_num)
  have hp (x : ℝ) : (x ^ 2) ^ (3 / 2 : ℝ) = |x| ^ 3 := by
    rw [← sq_abs x, ← Real.rpow_natCast_mul (abs_nonneg x)]
    norm_num
  simpa only [Fintype.sum_prod_type, hp, weightedEdge_trace_eq_atom_squares,
    atomCubeMass] using h

-- @node: atomCubeMass_nonneg
/-- [The normalized cubic edge mass is nonnegative](goal) for every input, pair of
scales, interval triple, and edge. -/
lemma atomCubeMass_nonneg (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (v : Fin 3) : 0 ≤ atomCubeMass F k m n v := by
  unfold atomCubeMass
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  positivity [atomWeight_pos k m]

-- @node: atomCubeMass_eq_zero_of_weightedEdge_eq_zero
/-- If [the weighted edge matrix is zero](hyp:h),
[its normalized cubic edge mass is zero](goal). -/
lemma atomCubeMass_eq_zero_of_weightedEdge_eq_zero (F : Fin 3 → ℝ × ℝ → ℝ)
    (k m : ℤ) (n : Fin 3 → ℕ) (v : Fin 3)
    (h : weightedEdge F k m n v = 0) : atomCubeMass F k m n v = 0 := by
  have hv (i j : Atom k m) : atomValue F k m n v i j = 0 := by
    have hij := congrFun (congrFun h i) j
    change Real.sqrt (atomWeight k m * atomWeight k m) * atomValue F k m n v i j = 0
      at hij
    exact (mul_eq_zero.mp hij).resolve_left
      (ne_of_gt (Real.sqrt_pos.2 (mul_pos (atomWeight_pos k m) (atomWeight_pos k m))))
  simp [atomCubeMass, hv]

end Papers.OaiBoundDyadicTriangular
