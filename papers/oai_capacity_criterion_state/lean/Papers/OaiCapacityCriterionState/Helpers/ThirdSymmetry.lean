module

public import Papers.OaiCapacityCriterionState.Helpers.QuadraticSymmetry

/-! # Symmetry averaging of the third-moment polynomial

The twelve even state permutations kill the mixed monomials that have degree
one in either posterior vector. The remaining terms have a quadratic envelope.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: coordQuad
/-- For [a real vector with three coordinates](hyp:x), its [quadratic statistic](goal)
is the sum of the squares of its coordinates. -/
def coordQuad (x : Fin 3 → ℝ) : ℝ := ∑ i, x i ^ 2

-- @node: coordThird
/-- For [a real vector with three coordinates](hyp:x), its [third-order statistic](goal)
is the product of its three coordinates. -/
def coordThird (x : Fin 3 → ℝ) : ℝ := x 0 * x 1 * x 2

-- @node: coordQuartic
/-- For [a real vector with three coordinates](hyp:x), its [quartic statistic](goal)
is the sum, over the three distinct pairs of coordinates, of the product of their squares. -/
def coordQuartic (x : Fin 3 → ℝ) : ℝ :=
  x 0 ^ 2 * x 1 ^ 2 + x 1 ^ 2 * x 2 ^ 2 + x 2 ^ 2 * x 0 ^ 2

-- @node: thirdIntegrand
/-- For [a first three-coordinate real vector](hyp:x) and [a second such vector](hyp:y),
the [third-moment integrand](goal) is the product of the three coordinate sums,
each augmented by its mixed-coordinate term, multiplied by one minus twice the
inner product of the two vectors. -/
def thirdIntegrand (x y : Fin 3 → ℝ) : ℝ :=
  (x 0 + y 0 + mixedCoords x y 0) *
  (x 1 + y 1 + mixedCoords x y 1) *
  (x 2 + y 2 + mixedCoords x y 2) * (1 - 2 * ∑ i, x i * y i)

-- @node: thirdCross
/-- For [a first three-coordinate real vector](hyp:x) and [a second such vector](hyp:y),
the [third-moment cross correction](goal) equals $-10T_xT_y-Q_xT_y-T_xQ_y
-2Q_x^2T_y-2T_xQ_y^2+(2/3)Q_xQ_y-(4/3)(U_xQ_y+Q_xU_y+U_xU_y)$,
where $Q$ is the sum of coordinate squares, $T$ is the product of the three
coordinates, and $U$ is the sum of pairwise products of squared coordinates. -/
noncomputable def thirdCross (x y : Fin 3 → ℝ) : ℝ :=
  -10 * coordThird x * coordThird y - coordQuad x * coordThird y -
  coordThird x * coordQuad y - 2 * coordQuad x ^ 2 * coordThird y -
  2 * coordThird x * coordQuad y ^ 2 + (2 / 3) * coordQuad x * coordQuad y -
  (4 / 3) * (coordQuartic x * coordQuad y + coordQuad x * coordQuartic y +
    coordQuartic x * coordQuartic y)

-- @node: postCoords_momentSymmetryPerm
/-- For [a real-valued vector on four states](hyp:q) and [an index among the twelve
even state permutations](hyp:k), [the posterior coordinates after that permutation
are the indexed member of the following list: each of the three cyclic coordinate
orders, with sign patterns all positive, last two negative, first and last negative,
and first two negative, in that order](goal). -/
lemma postCoords_momentSymmetryPerm (q : Fin 4 → ℝ) (k : Fin 12) :
    postCoords (q ∘ momentSymmetryPerm k) =
    ![![postCoords q 0, postCoords q 1, postCoords q 2],
      ![postCoords q 0, -postCoords q 1, -postCoords q 2],
      ![-postCoords q 0, postCoords q 1, -postCoords q 2],
      ![-postCoords q 0, -postCoords q 1, postCoords q 2],
      ![postCoords q 1, postCoords q 2, postCoords q 0],
      ![postCoords q 1, -postCoords q 2, -postCoords q 0],
      ![-postCoords q 1, postCoords q 2, -postCoords q 0],
      ![-postCoords q 1, -postCoords q 2, postCoords q 0],
      ![postCoords q 2, postCoords q 0, postCoords q 1],
      ![postCoords q 2, -postCoords q 0, -postCoords q 1],
      ![-postCoords q 2, postCoords q 0, -postCoords q 1],
      ![-postCoords q 2, -postCoords q 0, postCoords q 1]] k := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [momentSymmetryPerm, postCoords, coordMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

-- @node: third_symmetry_average
/-- For [a first real-valued vector on four states](hyp:p) and [a second such vector](hyp:q),
[summing the third-moment integrand over the twelve even permutations of the second
vector equals twelve times the sum of the two posterior-coordinate third-order
statistics and their third-moment cross correction](goal). -/
lemma third_symmetry_average (p q : Fin 4 → ℝ) :
    (∑ k : Fin 12, thirdIntegrand (postCoords p)
      (postCoords (q ∘ momentSymmetryPerm k))) =
    12 * (coordThird (postCoords p) + coordThird (postCoords q) +
      thirdCross (postCoords p) (postCoords q)) := by
  simp_rw [postCoords_momentSymmetryPerm]
  simp [thirdIntegrand, thirdCross, coordThird, coordQuad, coordQuartic,
    mixedCoords, Fin.sum_univ_succ]
  ring

-- @node: coordQuad_mem_Icc
/-- For [a three-coordinate real vector](hyp:x) [whose coordinates have absolute
value at most one](hyp:hx), [the sum of its squared coordinates lies between zero
and three, inclusive](goal). -/
lemma coordQuad_mem_Icc (x : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    coordQuad x ∈ Set.Icc 0 3 := by
  have hs (i : Fin 3) : x i ^ 2 ≤ 1 := by
    have hi := abs_le.mp (hx i)
    nlinarith
  refine ⟨Finset.sum_nonneg fun i _ => sq_nonneg _, ?_⟩
  calc
    _ ≤ ∑ _i : Fin 3, (1 : ℝ) := Finset.sum_le_sum fun i _ => hs i
    _ = 3 := by norm_num

-- @node: coordThird_abs_le_quad
/-- For [a three-coordinate real vector](hyp:x) [whose coordinates have absolute
value at most one](hyp:hx), [the absolute product of its three coordinates is at
most the sum of their squares](goal). -/
lemma coordThird_abs_le_quad (x : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |coordThird x| ≤ coordQuad x := by
  calc
    _ = |x 0| * |x 1| * |x 2| := by simp [coordThird, abs_mul]
    _ ≤ |x 0| * |x 1| := mul_le_of_le_one_right (by positivity) (hx 2)
    _ ≤ coordQuad x := by
      simp [coordQuad, Fin.sum_univ_succ]
      nlinarith [sq_nonneg (|x 0| - |x 1|), sq_abs (x 0), sq_abs (x 1),
        sq_nonneg (x 2)]

-- @node: coordQuartic_mem_Icc
/-- For [a three-coordinate real vector](hyp:x) [whose coordinates have absolute
value at most one](hyp:hx), [the sum of pairwise products of squared coordinates
lies between zero and the sum of coordinate squares, inclusive](goal). -/
lemma coordQuartic_mem_Icc (x : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    coordQuartic x ∈ Set.Icc 0 (coordQuad x) := by
  have hs (i : Fin 3) : x i ^ 2 ≤ 1 := by
    have hi := abs_le.mp (hx i)
    nlinarith
  have h01 := mul_le_mul_of_nonneg_left (hs 1) (sq_nonneg (x 0))
  have h12 := mul_le_mul_of_nonneg_left (hs 2) (sq_nonneg (x 1))
  have h20 := mul_le_mul_of_nonneg_left (hs 0) (sq_nonneg (x 2))
  constructor
  · unfold coordQuartic
    positivity
  · simpa [coordQuartic, coordQuad, Fin.sum_univ_succ, add_assoc] using
      add_le_add (add_le_add h01 h12) h20

-- @node: thirdCross_abs_le
/-- For [a first three-coordinate real vector](hyp:x) and [a second such vector](hyp:y),
if [every coordinate of the first has absolute value at most one](hyp:hx) and
[every coordinate of the second has absolute value at most one](hyp:hy),
[the absolute third-moment cross correction is at most thirty times the product
of their sums of squared coordinates](goal). -/
lemma thirdCross_abs_le (x y : Fin 3 → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) :
    |thirdCross x y| ≤ 30 * coordQuad x * coordQuad y := by
  have hA := coordQuad_mem_Icc x hx
  have hB := coordQuad_mem_Icc y hy
  have hT := coordThird_abs_le_quad x hx
  have hS := coordThird_abs_le_quad y hy
  have hU := coordQuartic_mem_Icc x hx
  have hV := coordQuartic_mem_Icc y hy
  have hTS : |coordThird x * coordThird y| ≤ coordQuad x * coordQuad y := by
    rw [abs_mul]
    exact mul_le_mul hT hS (abs_nonneg _) hA.1
  have hAS : |coordQuad x * coordThird y| ≤ coordQuad x * coordQuad y := by
    rw [abs_mul, abs_of_nonneg hA.1]
    exact mul_le_mul_of_nonneg_left hS hA.1
  have hTB : |coordThird x * coordQuad y| ≤ coordQuad x * coordQuad y := by
    rw [abs_mul, abs_of_nonneg hB.1]
    exact mul_le_mul_of_nonneg_right hT hB.1
  have hAAS : |coordQuad x ^ 2 * coordThird y| ≤
      3 * (coordQuad x * coordQuad y) := by
    calc
      _ = coordQuad x * |coordQuad x * coordThird y| := by
        simp only [abs_mul, abs_pow, abs_of_nonneg hA.1]; ring
      _ ≤ coordQuad x * (coordQuad x * coordQuad y) :=
        mul_le_mul_of_nonneg_left hAS hA.1
      _ ≤ 3 * (coordQuad x * coordQuad y) :=
        mul_le_mul_of_nonneg_right hA.2 (mul_nonneg hA.1 hB.1)
  have hTBB : |coordThird x * coordQuad y ^ 2| ≤
      3 * (coordQuad x * coordQuad y) := by
    calc
      _ = coordQuad y * |coordThird x * coordQuad y| := by
        simp only [abs_mul, abs_pow, abs_of_nonneg hB.1]; ring
      _ ≤ coordQuad y * (coordQuad x * coordQuad y) :=
        mul_le_mul_of_nonneg_left hTB hB.1
      _ ≤ 3 * (coordQuad x * coordQuad y) :=
        mul_le_mul_of_nonneg_right hB.2 (mul_nonneg hA.1 hB.1)
  have hUB := mul_le_mul_of_nonneg_right hU.2 hB.1
  have hAV := mul_le_mul_of_nonneg_left hV.2 hA.1
  have hUV := mul_le_mul hU.2 hV.2 hV.1 hA.1
  have hUB0 := mul_nonneg hU.1 hB.1
  have hAV0 := mul_nonneg hA.1 hV.1
  have hUV0 := mul_nonneg hU.1 hV.1
  have hab := mul_nonneg hA.1 hB.1
  unfold thirdCross
  apply abs_le.mpr
  constructor <;> nlinarith only [hab, hUB, hAV, hUV, hUB0, hAV0, hUV0,
    abs_le.mp hTS, abs_le.mp hAS, abs_le.mp hTB,
    abs_le.mp hAAS, abs_le.mp hTBB]

-- @node: third_integral_symmetry
/-- For [a posterior law](hyp:nu) [invariant under state permutations](hyp:hsym),
[a fixed real-valued vector on four states](hyp:p), and [one of the twelve even
state permutations](hyp:k), [the expected third-moment integrand is unchanged by
applying that permutation to the random vector's state labels](goal). -/
lemma third_integral_symmetry (nu : PosteriorLaw) (hsym : IsSymmetricLaw nu)
    (p : Fin 4 → ℝ) (k : Fin 12) :
    (∫ q, thirdIntegrand (postCoords p) (postCoords (q ∘ momentSymmetryPerm k))
      ∂(nu : Measure (Fin 4 → ℝ))) =
    ∫ q, thirdIntegrand (postCoords p) (postCoords q)
      ∂(nu : Measure (Fin 4 → ℝ)) := by
  have hm : Measurable (fun q : Fin 4 → ℝ => q ∘ momentSymmetryPerm k) := by fun_prop
  have hf : Measurable (fun q => thirdIntegrand (postCoords p) (postCoords q)) := by
    unfold thirdIntegrand mixedCoords postCoords Matrix.mulVec dotProduct
    fun_prop
  simpa only [Function.comp_def] using
    (integral_map hm.aemeasurable hf.aestronglyMeasurable).symm.trans
      (congrArg (fun m : Measure (Fin 4 → ℝ) =>
        ∫ q, thirdIntegrand (postCoords p) (postCoords q) ∂m)
        (hsym (momentSymmetryPerm k)))

-- @node: third_integral_average
/-- For [a posterior law](hyp:nu) [invariant under state permutations](hyp:hsym)
and [a fixed real-valued vector on four states](hyp:p), [the expected third-moment
integrand equals the expectation of the sum of the fixed and random vectors'
posterior-coordinate third-order statistics and their third-moment cross correction](goal). -/
lemma third_integral_average (nu : PosteriorLaw) (hsym : IsSymmetricLaw nu)
    (p : Fin 4 → ℝ) :
    (∫ q, thirdIntegrand (postCoords p) (postCoords q)
      ∂(nu : Measure (Fin 4 → ℝ))) =
    ∫ q, coordThird (postCoords p) + coordThird (postCoords q) +
      thirdCross (postCoords p) (postCoords q) ∂(nu : Measure (Fin 4 → ℝ)) := by
  have hi (k : Fin 12) : Integrable (fun q => thirdIntegrand (postCoords p)
      (postCoords (q ∘ momentSymmetryPerm k))) (nu : Measure (Fin 4 → ℝ)) := by
    apply posterior_continuous_integrable
    unfold thirdIntegrand mixedCoords postCoords Matrix.mulVec dotProduct
    fun_prop
  have he : (12 : ℝ) * (∫ q, thirdIntegrand (postCoords p) (postCoords q)
      ∂(nu : Measure (Fin 4 → ℝ))) =
      12 * (∫ q, coordThird (postCoords p) + coordThird (postCoords q) +
        thirdCross (postCoords p) (postCoords q) ∂(nu : Measure (Fin 4 → ℝ))) := by
    calc
      _ = ∫ q, (∑ k : Fin 12, thirdIntegrand (postCoords p)
          (postCoords (q ∘ momentSymmetryPerm k))) ∂(nu : Measure (Fin 4 → ℝ)) := by
        rw [integral_finsetSum Finset.univ (fun k _ => hi k)]
        simp [third_integral_symmetry nu hsym]
      _ = _ := by simp_rw [third_symmetry_average]; rw [integral_const_mul]
  linarith

-- @node: third_polynomial_integral_bound
/-- For [a first posterior law](hyp:mu) and [a second posterior law](hyp:nu)
[both invariant under state permutations](hyp:hsym), [the absolute difference
between the expected third-moment integrand under independent draws and the sum
of the two third moments is at most thirty times the product of the laws'
quadratic information measures](goal). -/
lemma third_polynomial_integral_bound (mu nu : PosteriorLaw)
    (hsym : LocalMomentsSymmetry mu nu) :
    |(∫ pq, thirdIntegrand (postCoords pq.1) (postCoords pq.2)
        ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))) -
      thirdMoment mu - thirdMoment nu| ≤ 30 * quadInfo mu * quadInfo nu := by
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  let : IsProbabilityMeasure (nu : Measure (Fin 4 → ℝ)) := nu.property.1
  have hi : Integrable (fun pq => thirdIntegrand (postCoords pq.1) (postCoords pq.2))
      ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
    apply posterior_prod_continuous_integrable
    unfold thirdIntegrand mixedCoords postCoords Matrix.mulVec dotProduct
    fun_prop
  have ht (rho : PosteriorLaw) : Integrable (fun p => coordThird (postCoords p))
      (rho : Measure (Fin 4 → ℝ)) := by
    apply posterior_continuous_integrable
    unfold coordThird postCoords Matrix.mulVec dotProduct
    fun_prop
  have hc : Integrable (fun pq => thirdCross (postCoords pq.1) (postCoords pq.2))
      ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
    apply posterior_prod_continuous_integrable
    unfold thirdCross coordQuad coordThird coordQuartic postCoords Matrix.mulVec dotProduct
    fun_prop
  have htx := (ht mu).comp_fst (ν := (nu : Measure (Fin 4 → ℝ)))
  have hty := (ht nu).comp_snd (μ := (mu : Measure (Fin 4 → ℝ)))
  have hid : (∫ pq, thirdIntegrand (postCoords pq.1) (postCoords pq.2)
      ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))) =
      thirdMoment mu + thirdMoment nu +
      ∫ pq, thirdCross (postCoords pq.1) (postCoords pq.2)
        ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
    rw [integral_prod _ hi]
    simp_rw [third_integral_average nu hsym.2]
    erw [← integral_prod _ ((htx.add hty).add hc),
      integral_add (htx.add hty) hc, integral_add htx hty,
      integral_fun_fst (fun p : Fin 4 → ℝ => coordThird (postCoords p)),
      integral_fun_snd (fun q : Fin 4 → ℝ => coordThird (postCoords q))]
    simp [thirdMoment, coordThird]
  rw [hid]
  ring_nf
  have hquad (rho : PosteriorLaw) : Integrable quadStat (rho : Measure (Fin 4 → ℝ)) := by
    apply posterior_continuous_integrable
    unfold quadStat postCoords Matrix.mulVec dotProduct
    fun_prop
  have hb := ((hquad mu).mul_prod (hquad nu)).const_mul 30
  calc
    _ ≤ ∫ pq, 30 * (quadStat pq.1 * quadStat pq.2)
        ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hb
      have hp := (Measure.quasiMeasurePreserving_fst
        (ν := (nu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr mu.property.2.1)
      have hq := (Measure.quasiMeasurePreserving_snd
        (μ := (mu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr nu.property.2.1)
      filter_upwards [hp, hq] with pq hp hq
      simpa only [Real.norm_eq_abs, coordQuad, quadStat, mul_assoc] using
        thirdCross_abs_le (postCoords pq.1) (postCoords pq.2)
          (fun i => abs_le.mpr (postCoords_mem_Icc pq.1 hp i))
          (fun i => abs_le.mpr (postCoords_mem_Icc pq.2 hq i))
    _ = _ := by rw [integral_const_mul, integral_prod_mul]; simp [quadInfo]; ring

end OaiCapacityCriterionState
