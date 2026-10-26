module
public import Papers.OaiMetricMarkovCotype.Basic
public import Causalean.Mathlib.Analysis.WeightedCauchySchwarz

/-! # Flatness of cubic smoothing on weighted cubes -/

public section

namespace Papers.OaiMetricMarkovCotype

open scoped BigOperators

-- @node: cubicSmooth_increment_zero
/-- If [x lies between zero and one](hyp:hx) and [y lies between zero and
one](hyp:hy), then [the absolute change in the cubic smoothing function is at
most six times the absolute value of x times the absolute increment, plus three
times the squared increment](goal). -/
lemma cubicSmooth_increment_zero {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |cubicSmooth y - cubicSmooth x| ≤ 6 * |x| * |y - x| + 3 * |y - x| ^ 2 := by
  have hxx := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hyy := mul_nonneg hy.1 (sub_nonneg.mpr hy.2)
  have hxy := mul_nonneg hx.1 (sub_nonneg.mpr hy.2)
  have hyx := mul_nonneg hy.1 (sub_nonneg.mpr hx.2)
  have hf : 0 ≤ 3 * (x + y) - 2 * (x ^ 2 + x * y + y ^ 2) := by
    nlinarith
  have hfactor : cubicSmooth y - cubicSmooth x =
      (y - x) * (3 * (x + y) - 2 * (x ^ 2 + x * y + y ^ 2)) := by
    unfold cubicSmooth
    ring
  rw [hfactor, abs_mul, abs_of_nonneg hf, abs_of_nonneg hx.1]
  have hupper : 3 * (x + y) - 2 * (x ^ 2 + x * y + y ^ 2) ≤ 3 * (x + y) := by
    nlinarith [mul_nonneg hx.1 hy.1, sq_nonneg x, sq_nonneg y]
  have habs := le_abs_self (y - x)
  calc
    _ ≤ |y - x| * (3 * (x + y)) := mul_le_mul_of_nonneg_left hupper (abs_nonneg _)
    _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg (y - x)) (by linarith : 0 ≤ x + |y - x| - y)]

-- @node: cubicSmooth_increment_binary
/-- If [x lies between zero and one](hyp:hx), [y lies between zero and
one](hyp:hy), and [d is either zero or one](hyp:hd), then [the absolute change
in cubic smoothing from x to y is at most six times the distance from x to d
times the absolute increment, plus three times the squared increment](goal). -/
lemma cubicSmooth_increment_binary {x y d : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hd : d = 0 ∨ d = 1) :
    |cubicSmooth y - cubicSmooth x| ≤
      6 * |x - d| * |y - x| + 3 * |y - x| ^ 2 := by
  rcases hd with rfl | rfl
  · simpa using cubicSmooth_increment_zero hx hy
  · have h := cubicSmooth_increment_zero
      (x := 1 - x) (y := 1 - y) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hsym (r : ℝ) : cubicSmooth (1 - r) = 1 - cubicSmooth r := by
      unfold cubicSmooth
      ring
    rw [hsym, hsym] at h
    have h₁ : 1 - (cubicSmooth y) - (1 - cubicSmooth x) =
        -(cubicSmooth y - cubicSmooth x) := by ring
    have h₂ : 1 - y - (1 - x) = -(y - x) := by ring
    have h₃ : 1 - x = -(x - 1) := by ring
    rw [h₁, h₂, h₃, abs_neg, abs_neg, abs_neg] at h
    exact h

-- @node: weightedHNormSq_nonneg
/-- If [all weights are strictly positive](hyp:hw), then [the weighted sum of
squared coordinates of any real vector is nonnegative](goal). -/
lemma weightedHNormSq_nonneg {𝓑 : Type*} [Fintype 𝓑] (w a : 𝓑 → ℝ)
    (hw : PositiveWeights w) : 0 ≤ weightedHNormSq w a := by
  exact Finset.sum_nonneg fun B _ => mul_nonneg (le_of_lt (hw B)) (sq_nonneg _)

-- @node: weightedHNormSq_add
/-- [The weighted sum of squared coordinates of the sum of two vectors equals
the sum of their weighted squared norms plus twice their weighted inner
product](goal). -/
lemma weightedHNormSq_add {𝓑 : Type*} [Fintype 𝓑] (w a b : 𝓑 → ℝ) :
    weightedHNormSq w (a + b) =
      weightedHNormSq w a + 2 * weightedInner w a b + weightedHNormSq w b := by
  rw [wInner_real_eq_sum]
  simp only [weightedHNormSq, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B _
  ring

-- @node: weightedInner_sq_le
/-- If [all weights are strictly positive](hyp:hw), then [the square of the
weighted inner product of two real vectors is at most the product of their
weighted squared norms](goal). -/
lemma weightedInner_sq_le {𝓑 : Type*} [Fintype 𝓑] (w a b : 𝓑 → ℝ)
    (hw : PositiveWeights w) :
    weightedInner w a b ^ 2 ≤ weightedHNormSq w a * weightedHNormSq w b := by
  simpa [wInner_real_eq_sum, weightedHNormSq, mul_assoc] using
    Causalean.Mathlib.Analysis.weighted_inner_sq_le Finset.univ w a b
      (fun B _ => le_of_lt (hw B))

-- @node: cubicMap_increment_sq
/-- If [all weights are strictly positive](hyp:hw), [both argument vectors lie
in the unit cube](hyp:hu), and [the center vector has only zero or one
coordinates](hyp:he), then [the squared weighted ℓ¹ change in coordinatewise
cubic smoothing is at most 72 times the product of the weighted squared distance
to the center and the weighted squared increment, plus 18 times the square of
the weighted squared increment](goal). -/
lemma cubicMap_increment_sq {𝓑 : Type*} [Fintype 𝓑] (w u u' e : 𝓑 → ℝ)
    (hw : PositiveWeights w) (hu : CubeArguments u u') (he : BinaryVector e) :
    weightedL1Norm w (cubicMap u' - cubicMap u) ^ 2 ≤
      72 * weightedHNormSq w (u - e) * weightedHNormSq w (u' - u) +
        18 * weightedHNormSq w (u' - u) ^ 2 := by
  let K : ℝ := ∑ B, w B * (|u B - e B| * |u' B - u B|)
  let D := weightedHNormSq w (u' - u)
  let N := weightedL1Norm w (cubicMap u' - cubicMap u)
  have hK : 0 ≤ K := Finset.sum_nonneg fun B _ =>
    mul_nonneg (le_of_lt (hw B)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hD : 0 ≤ D := weightedHNormSq_nonneg w _ hw
  have hN : 0 ≤ N := Finset.sum_nonneg fun B _ =>
    mul_nonneg (le_of_lt (hw B)) (abs_nonneg _)
  have hinc : N ≤ 6 * K + 3 * D := by
    calc
      N ≤ ∑ B, w B * (6 * |u B - e B| * |u' B - u B| + 3 * |u' B - u B| ^ 2) := by
        apply Finset.sum_le_sum
        intro B _
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (hw B))
        exact cubicSmooth_increment_binary (hu.1 B (Set.mem_univ B))
          (hu.2 B (Set.mem_univ B)) (he B)
      _ = 6 * K + 3 * D := by
        dsimp [K, D, weightedHNormSq]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, sq_abs]
        apply Finset.sum_congr rfl
        intro B _
        ring
  have hcs : K ^ 2 ≤ weightedHNormSq w (u - e) * D := by
    simpa [K, D, weightedHNormSq, Pi.sub_apply, sq_abs] using
      Causalean.Mathlib.Analysis.weighted_inner_sq_le Finset.univ w
        (fun B => |u B - e B|) (fun B => |u' B - u B|)
        (fun B _ => le_of_lt (hw B))
  have hsquare : N ^ 2 ≤ (6 * K + 3 * D) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hinc) (by linarith : 0 ≤ 6 * K + 3 * D + N)]
  change N ^ 2 ≤ 72 * weightedHNormSq w (u - e) * D + 18 * D ^ 2
  nlinarith [sq_nonneg (6 * K - 3 * D)]

-- @node: flatRemainder_identity
/-- [The quartic potential remainder equals twice the product of the weighted
squared distance from the initial vector to the center and the weighted squared
increment, plus the square of the sum of twice their weighted inner product
and the weighted squared increment](goal). -/
lemma flatRemainder_identity {𝓑 : Type*} [Fintype 𝓑] (w u u' e : 𝓑 → ℝ) :
    flatRemainder w e u u' =
      2 * weightedHNormSq w (u - e) * weightedHNormSq w (u' - u) +
        (2 * weightedInner w (u - e) (u' - u) + weightedHNormSq w (u' - u)) ^ 2 := by
  have hsplit : u' - e = (u - e) + (u' - u) := by abel
  unfold flatRemainder quarticPotential
  rw [hsplit, weightedHNormSq_add]
  ring

-- @node: lem:flat
/-- With [a nonempty finite coordinate index set](hyp:h_finite), [strictly positive
weights](hyp:h_weights), [two argument vectors in the unit cube](hyp:h_arguments),
and [a center vector whose coordinates are zero or one](hyp:h_center), [the squared
weighted ℓ¹ change in coordinatewise cubic smoothing is at most 108 times the
quartic potential increase after subtracting its linear term, namely four times
the initial weighted squared distance to the center times the weighted inner
product of the initial displacement and the increment](goal). -/
lemma flat_cubic_bound {𝓑 : Type*} [Fintype 𝓑] (w u u' e : 𝓑 → ℝ)
    (h_finite : FiniteCutIndex 𝓑) (h_weights : PositiveWeights w)
    (h_arguments : CubeArguments u u') (h_center : BinaryVector e) :
    weightedL1Norm w (cubicMap u' - cubicMap u) ^ 2 ≤
      108 * (quarticPotential w e u' - quarticPotential w e u -
        4 * weightedHNormSq w (u - e) * weightedInner w (u - e) (u' - u)) := by
  have hinc := cubicMap_increment_sq w u u' e h_weights h_arguments h_center
  have hcs := weightedInner_sq_le w (u - e) (u' - u) h_weights
  have hid := flatRemainder_identity w u u' e
  have hprod : 0 ≤ weightedHNormSq w (u - e) * weightedHNormSq w (u' - u) :=
    mul_nonneg (weightedHNormSq_nonneg w _ h_weights) (weightedHNormSq_nonneg w _ h_weights)
  have hfirst : 2 * (weightedHNormSq w (u - e) * weightedHNormSq w (u' - u)) ≤
      flatRemainder w e u u' := by
    nlinarith [sq_nonneg (2 * weightedInner w (u - e) (u' - u) + weightedHNormSq w (u' - u))]
  have hsecond : weightedHNormSq w (u' - u) ^ 2 ≤ 4 * flatRemainder w e u u' := by
    nlinarith [sq_nonneg (2 * weightedInner w (u - e) (u' - u) + 2 * weightedHNormSq w (u' - u))]
  change _ ≤ 108 * flatRemainder w e u u'
  nlinarith

end Papers.OaiMetricMarkovCotype
