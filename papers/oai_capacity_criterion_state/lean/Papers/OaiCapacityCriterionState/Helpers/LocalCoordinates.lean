module

public import Papers.OaiCapacityCriterionState.Helpers.PosteriorLaws
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Coordinates for the conditional product of posterior laws -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

/-- For [a four-component vector p](hyp:p) and [a four-component vector q](hyp:q),
the [coordinate inner product](goal) is the sum of the products of their three posterior coordinates.
@realizes s(the inner product of the two coordinate vectors)
-/
-- @node: coordinateDot
def coordinateDot (p q : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 3, postCoords p i * postCoords q i

/-- For [a three-component vector x](hyp:x) and [a three-component vector y](hyp:y),
the [mixed coordinate vector](goal) pairs the two coordinates other than the output index:
[its first entry is x₁y₂ + x₂y₁](step:1), [its second is x₀y₂ + x₂y₀](step:2),
and [its third is x₀y₁ + x₁y₀](step:3).
@realizes R(the mixed vector with R_i = x_j y_k + x_k y_j for distinct indices)
-/
-- @node: mixedCoords
def mixedCoords (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 1 * y 2 + x 2 * y 1, x 0 * y 2 + x 2 * y 0, x 0 * y 1 + x 1 * y 0]

/-- For [a four-component vector p](hyp:p) and [a four-component vector q](hyp:q),
the [product coordinate numerator](goal) is the sum of their posterior coordinate vectors
and the mixed coordinate vector formed from them.
@realizes N(the normalized-product coordinate numerator x + y + R)
-/
-- @node: productNumerator
def productNumerator (p q : Fin 4 → ℝ) : Fin 3 → ℝ :=
  postCoords p + postCoords q + mixedCoords (postCoords p) (postCoords q)

-- @node: productNumerator_abs_le_four
/-- If [p is a probability vector on four states](hyp:hp) and
[q is a probability vector on four states](hyp:hq), then
[each of the three product coordinate numerators has absolute value at most four](goal). -/
lemma productNumerator_abs_le_four (p q : Fin 4 → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin 4)) (hq : q ∈ stdSimplex ℝ (Fin 4))
    (i : Fin 3) : |productNumerator p q i| ≤ 4 := by
  have hx (j : Fin 3) : |postCoords p j| ≤ 1 :=
    abs_le.mpr (postCoords_mem_Icc p hp j)
  have hy (j : Fin 3) : |postCoords q j| ≤ 1 :=
    abs_le.mpr (postCoords_mem_Icc q hq j)
  have hxy (j k : Fin 3) : |postCoords p j * postCoords q k| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (hx j) (hy k) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hR : |mixedCoords (postCoords p) (postCoords q) i| ≤ 2 := by
    fin_cases i <;> dsimp [mixedCoords] <;>
      exact (abs_add_le _ _).trans (by
        linarith [hxy 0 1, hxy 0 2, hxy 1 0, hxy 1 2, hxy 2 0, hxy 2 1])
  change |(postCoords p i + postCoords q i) +
    mixedCoords (postCoords p) (postCoords q) i| ≤ 4
  exact (abs_add_le _ _).trans (by
    linarith [abs_add_le (postCoords p i) (postCoords q i), hx i, hy i])

-- @node: productP_coordinates
/-- If [p is a probability vector on four states](hyp:hp),
[q is a probability vector on four states](hyp:hq), and
[their product normalizer is positive](hyp:hz), then
[each posterior coordinate of their normalized product equals its product coordinate
numerator divided by the product normalizer](goal). -/
lemma productP_coordinates (p q : Fin 4 → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin 4)) (hq : q ∈ stdSimplex ℝ (Fin 4))
    (hz : 0 < productZ (p, q)) (i : Fin 3) :
    postCoords (productP (p, q)) i = productNumerator p q i / productZ (p, q) := by
  have hn : productNumerator p q i =
      postCoords (fun j => 4 * p j * q j) i := by
    have hid : postCoords p i * (∑ j : Fin 4, q j) +
        postCoords q i * (∑ j : Fin 4, p j) +
        mixedCoords (postCoords p) (postCoords q) i =
        postCoords (fun j => 4 * p j * q j) i := by
      fin_cases i <;>
        simp [mixedCoords, postCoords, coordMatrix, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ] <;> ring
    simpa [hp.2, hq.2, productNumerator] using hid
  rw [hn]
  simp only [productP, if_pos hz]
  fin_cases i <;>
    simp [postCoords, coordMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

end OaiCapacityCriterionState
