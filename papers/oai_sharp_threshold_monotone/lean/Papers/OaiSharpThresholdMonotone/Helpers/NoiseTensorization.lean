module
public import Papers.OaiSharpThresholdMonotone.Helpers.NoiseBasics
public import Causalean.Mathlib.Analysis.WeightedCauchySchwarz

/-! # The two-point fourth-moment inequality and product hypercontractivity -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

variable {J : Type*} [Fintype J] [DecidableEq J]

-- @node: oneCoordinate_fourthMoment_le
/-- If [the bias is strictly between zero and one](hyp:hp), [the fourth moment of
a plus the associated noise parameter times b times the standardized Bernoulli
character is at most the square of the sum of the squares of a and b](goal). -/
lemma oneCoordinate_fourthMoment_le (p : ℝ) (hp : BiasInterior p)
    (a : ℝ) -- @realizes a(arbitrary real scalar)
    (b : ℝ) : -- @realizes b(arbitrary real scalar)
    p * (a + noiseParameter p * b * ((1 - p) / biasScale p)) ^ 4 +
      (1 - p) * (a + noiseParameter p * b * ((0 - p) / biasScale p)) ^ 4 ≤
        (a ^ 2 + b ^ 2) ^ 2 := by
  have hσ : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  have hscale (z : ℝ) : noiseParameter p * b * (z / biasScale p) = b * z / 4 := by
    unfold noiseParameter
    field_simp
  rw [hscale, hscale]
  let q := p * (1 - p)
  have hq : 0 ≤ q := mul_nonneg hp.1.le (by linarith [hp.2])
  have hqle : q ≤ 1 / 4 := by dsimp [q]; nlinarith [sq_nonneg (p - 1 / 2)]
  have hw : |1 - 2 * p| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
  have hthird : |q * (1 - 2 * p)| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg hq]
    nlinarith [mul_le_mul_of_nonneg_left hw hq]
  have hcross : 2 * |a * b ^ 3| ≤ a ^ 2 * b ^ 2 + b ^ 4 := by
    have hab : |a * b ^ 3| ≤ (a ^ 2 * b ^ 2 + b ^ 4) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (a * b - b ^ 2), sq_nonneg (a * b + b ^ 2)]
    linarith
  have hcubic : q * (1 - 2 * p) * a * b ^ 3 ≤ (1 / 4) * |a * b ^ 3| := by
    calc
      _ = (q * (1 - 2 * p)) * (a * b ^ 3) := by ring
      _ ≤ |(q * (1 - 2 * p)) * (a * b ^ 3)| := le_abs_self _
      _ = |q * (1 - 2 * p)| * |a * b ^ 3| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hthird (abs_nonneg _)
  have hquartic : q * (1 - 3 * q) * b ^ 4 ≤ (1 / 4) * b ^ 4 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg q]
  have hquadratic : q * (a ^ 2 * b ^ 2) ≤ (1 / 4) * (a ^ 2 * b ^ 2) :=
    mul_le_mul_of_nonneg_right hqle (by positivity)
  have hexpand : p * (a + b * (1 - p) / 4) ^ 4 +
      (1 - p) * (a + b * (0 - p) / 4) ^ 4 =
      a ^ 4 + (3 / 8) * q * (a ^ 2 * b ^ 2) +
        (1 / 16) * (q * (1 - 2 * p) * a * b ^ 3) +
        (1 / 256) * (q * (1 - 3 * q) * b ^ 4) := by
    dsimp [q]
    ring
  rw [hexpand]
  nlinarith [sq_nonneg (a * b), sq_nonneg (b ^ 2)]


/-- [The noise-transformed value of g at x equals the expectation of g at a random
configuration y times the product, over coordinates, of one plus the noise parameter
times the standardized coordinate characters at x and y](goal). -/
-- @node: noiseOperator_eq_kernel
lemma noiseOperator_eq_kernel (p ρ : ℝ) (g : (J → Bool) → ℝ) (x : J → Bool) :
    noiseOperator p ρ g x = (biasedLaw J p).E
      (fun y => g y * ∏ j : J, (1 + ρ * coordChar p j x * coordChar p j y)) := by
  simp_rw [Finset.prod_one_add, Finset.powerset_univ, Finset.mul_sum,
    FiniteDesign.E_sum]
  unfold noiseOperator fourierCoeffR
  apply Finset.sum_congr rfl
  intro A _
  simp only [Finset.prod_mul_distrib, Finset.prod_const]
  change ρ ^ A.card * (biasedLaw J p).E (fun y => g y * fourierChar p A y) *
    fourierChar p A x = (biasedLaw J p).E
      (fun y => g y * (ρ ^ A.card * fourierChar p A x * fourierChar p A y))
  simp_rw [show ∀ y, g y * (ρ ^ A.card * fourierChar p A x * fourierChar p A y) =
    (ρ ^ A.card * fourierChar p A x) * (g y * fourierChar p A y) by intro y; ring]
  rw [FiniteDesign.E_const_mul]
  ring

-- @node: noiseOperator_coordinate_split
/-- If [the bias is strictly between zero and one](hyp:hp), [the noise-transformed
value of g equals the noise transform of its coordinate mean on the remaining
coordinates plus the noise parameter times the noise transform of its coordinate
Fourier coefficient times the standardized character of the removed coordinate](goal). -/
lemma noiseOperator_coordinate_split (p ρ : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) (i : J) (x : J → Bool) :
    let A := noiseOperator p ρ (coordinateMean p g i) -- @realizes A(transformed coefficient a)
    let B := noiseOperator p ρ (coordinateFourier p g i) -- @realizes B(transformed coefficient b)
    noiseOperator p ρ g x = A (fun j => x j.val) + ρ * B (fun j => x j.val) *
      coordChar p i x := by
  classical
  dsimp only
  rw [noiseOperator_eq_kernel, biasedLaw_E_coordinate_split p hp _ i]
  have hs : biasScale p ≠ 0 := (biasScale_pos_le_half p hp).1.ne'
  have hs2 := biasScale_sq p hp
  have hrest (t : Bool) (y : {j : J // j ≠ i} → Bool) :
      (fun j : {j : J // j ≠ i} => insertCoordinate i y t j.val) = y := by
    funext j
    simp [insertCoordinate, j.property]
  have hprod (t : Bool) (y : {j : J // j ≠ i} → Bool) :
      (∏ j : J, (1 + ρ * coordChar p j x * coordChar p j (insertCoordinate i y t))) =
      (1 + ρ * coordChar p i x * (((if t then 1 else 0) - p) / biasScale p)) *
        ∏ j : {j : J // j ≠ i},
          (1 + ρ * coordChar p j (fun j => x j.val) * coordChar p j y) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp [coordChar, insertCoordinate,
      show ∀ j : {j : J // j ≠ i}, (j : J) ≠ i from fun j => j.property]
  simp_rw [coordinate_decomposition p hp g i, hrest, hprod]
  have hcoord (t : Bool) (y : {j : J // j ≠ i} → Bool) :
      coordChar p i (insertCoordinate i y t) = ((if t then 1 else 0) - p) / biasScale p := by
    simp [coordChar, insertCoordinate]
  simp_rw [hcoord]
  rw [noiseOperator_eq_kernel, noiseOperator_eq_kernel, ← FiniteDesign.E_const_mul,
    ← FiniteDesign.E_mul_const, ← FiniteDesign.E_add]
  apply FiniteDesign.E_congr
  intro y
  simp only [↓reduceIte, Bool.false_eq_true]
  field_simp
  linear_combination -(∏ j : {j : J // j ≠ i},
    (1 + ρ * coordChar p j (fun j => x j.val) * coordChar p j y)) *
      coordinateFourier p g i y * ρ * coordChar p i x * hs2

-- @node: coordinate_fourthMoment_le
/-- For [real-valued functions a and b of the coordinates other than i](hyp:a,b),
if [the bias is strictly between zero and one](hyp:hp), [the fourth moment of
a plus the associated noise parameter times b times the standardized character of
coordinate i is at most the expectation, over the remaining coordinates, of the
square of the sum of the squares of a and b](goal). -/
lemma coordinate_fourthMoment_le (p : ℝ) (hp : BiasInterior p) (i : J)
    (a b : ({j : J // j ≠ i} → Bool) → ℝ) :
    (biasedLaw J p).E (fun x =>
      (a (fun j => x j.val) + noiseParameter p * b (fun j => x j.val) *
        coordChar p i x) ^ 4) ≤
      (biasedLaw {j : J // j ≠ i} p).E (fun y => (a y ^ 2 + b y ^ 2) ^ 2) := by
  rw [biasedLaw_E_coordinate_split p hp _ i]
  unfold FiniteDesign.E
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ ((biasedLaw {j : J // j ≠ i} p).p_nonneg y)
  simpa [coordChar, insertCoordinate,
    show ∀ j : {j : J // j ≠ i}, (j : J) ≠ i from fun j => j.property]
    using oneCoordinate_fourthMoment_le p hp (a y) (b y)

-- @node: noiseOperator_fourthMoment_le
/-- If [the bias is strictly between zero and one](hyp:hp), [the fourth moment of
g after applying noise with the associated noise parameter is at most the square
of the second moment of g](goal). -/
lemma noiseOperator_fourthMoment_le (p : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) :
    (biasedLaw J p).E (fun x => noiseOperator p (noiseParameter p) g x ^ 4) ≤
      ((biasedLaw J p).E (fun x => g x ^ 2)) ^ 2 := by
  classical
  induction hn : Fintype.card J using Nat.strong_induction_on generalizing J with
  | h n ih =>
    by_cases he : IsEmpty J
    · let := he
      have hg : g = fun _ => g (fun j => isEmptyElim j) := by
        funext x
        congr 1
        funext j
        exact isEmptyElim j
      rw [hg]
      simp [noiseOperator_eq_kernel, ← pow_mul]
    · obtain ⟨i⟩ := not_isEmpty_iff.mp he
      let a := coordinateMean p g i
      let b := coordinateFourier p g i
      have hnorm := coordinate_secondMoment p hp g i
      rw [FiniteDesign.E_add] at hnorm
      have hlt : Fintype.card {j : J // j ≠ i} < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := i) (by simp)
      have ha := ih _ hlt a rfl
      have hb := ih _ hlt b rfl
      let D := biasedLaw {j : J // j ≠ i} p
      let u := noiseOperator p (noiseParameter p) a
      let v := noiseOperator p (noiseParameter p) b
      have hA : 0 ≤ D.E (fun y => a y ^ 2) := D.E_nonneg (fun y => sq_nonneg _)
      have hB : 0 ≤ D.E (fun y => b y ^ 2) := D.E_nonneg (fun y => sq_nonneg _)
      have hu : Real.sqrt (D.E (fun y => u y ^ 4)) ≤ D.E (fun y => a y ^ 2) := by
        calc
          _ ≤ Real.sqrt ((D.E (fun y => a y ^ 2)) ^ 2) := Real.sqrt_le_sqrt ha
          _ = _ := Real.sqrt_sq hA
      have hv : Real.sqrt (D.E (fun y => v y ^ 4)) ≤ D.E (fun y => b y ^ 2) := by
        calc
          _ ≤ Real.sqrt ((D.E (fun y => b y ^ 2)) ^ 2) := Real.sqrt_le_sqrt hb
          _ = _ := Real.sqrt_sq hB
      have hcross : D.E (fun y => u y ^ 2 * v y ^ 2) ≤
          D.E (fun y => a y ^ 2) * D.E (fun y => b y ^ 2) := by
        have hc := Causalean.Mathlib.Analysis.abs_weighted_inner_le Finset.univ
          D.p (fun y => u y ^ 2) (fun y => v y ^ 2) (fun y _ => D.p_nonneg y)
        have hc' : |D.E (fun y => u y ^ 2 * v y ^ 2)| ≤
            Real.sqrt (D.E (fun y => u y ^ 4)) * Real.sqrt (D.E (fun y => v y ^ 4)) := by
          simpa only [FiniteDesign.E, ← pow_mul, Nat.reduceMul] using hc
        exact (le_abs_self _).trans
          (hc'.trans (mul_le_mul hu hv (Real.sqrt_nonneg _) hA))
      calc
        _ ≤ D.E (fun y => (u y ^ 2 + v y ^ 2) ^ 2) := by
          simpa only [noiseOperator_coordinate_split p (noiseParameter p) hp g i]
            using coordinate_fourthMoment_le p hp i u v
        _ = D.E (fun y => u y ^ 4) + 2 * D.E (fun y => u y ^ 2 * v y ^ 2) +
            D.E (fun y => v y ^ 4) := by
          simp_rw [show ∀ y, (u y ^ 2 + v y ^ 2) ^ 2 =
            u y ^ 4 + 2 * (u y ^ 2 * v y ^ 2) + v y ^ 4 by intro y; ring,
            FiniteDesign.E_add, FiniteDesign.E_const_mul]
        _ ≤ _ := by rw [hnorm]; nlinarith [ha, hb, hcross]

-- @node: noiseOperator_norm_four_le_two
/-- If [the bias is strictly between zero and one](hyp:hp), [the fourth norm of g
after applying noise with the associated noise parameter is at most the second
norm of g](goal). -/
lemma noiseOperator_norm_four_le_two (p : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) :
    cubeNorm p 4 (noiseOperator p (noiseParameter p) g) ≤ cubeNorm p 2 g := by
  have htwo := (biasedLaw J p).E_nonneg (fun x => sq_nonneg (g x))
  unfold cubeNorm
  simp only [show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl, Real.rpow_natCast,
    (by decide : Even 4).pow_abs, Real.rpow_two, sq_abs]
  calc
    _ ≤ (((biasedLaw J p).E (fun x => g x ^ 2)) ^ 2) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow ((biasedLaw J p).E_nonneg (fun x => by positivity))
        (noiseOperator_fourthMoment_le p hp g) (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul htwo]
      congr 1
      norm_num

end Papers.OaiSharpThresholdMonotone
