module
public import Papers.OaiSharpThresholdMonotone.Helpers.Fourier
public import Mathlib.LinearAlgebra.Span.Defs

/-! # Finite Fourier noise and orthogonal degree projections -/

@[expose] public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- For [bias p](hyp:p) and [real degree bound d](hyp:d), the [low-degree space](goal)
is the real linear span of Fourier characters indexed by coordinate sets of size at most d. -/
noncomputable def lowDegreeSpace (p d : ℝ) : Submodule ℝ ((J → Bool) → ℝ) :=
  Submodule.span ℝ {u | ∃ S : Finset J, (S.card : ℝ) ≤ d ∧ u = fourierChar p S}

/-- For [bias p](hyp:p), [a real function g on Boolean configurations](hyp:g),
[a coordinate i](hyp:i), and [an assignment y of all remaining coordinates](hyp:y),
the [coordinate mean](goal) averages g over the two values of i with weights p and one minus p. -/
noncomputable def coordinateMean (p : ℝ) (g : (J → Bool) → ℝ) (i : J)
    (y : {j : J // j ≠ i} → Bool) : ℝ :=
  p * g (insertCoordinate i y true) + (1 - p) * g (insertCoordinate i y false)
  -- @realizes a(real coefficient function on the remaining coordinates)

/-- For [bias p](hyp:p), [a real function g on Boolean configurations](hyp:g),
[a coordinate i](hyp:i), and [an assignment y of all remaining coordinates](hyp:y),
the [coordinate Fourier coefficient](goal) is the value of g with i set to true minus
its value with i set to false, multiplied by the bias scale. -/
noncomputable def coordinateFourier (p : ℝ) (g : (J → Bool) → ℝ) (i : J)
    (y : {j : J // j ≠ i} → Bool) : ℝ :=
  biasScale p * coordDiffRemaining g i y
  -- @realizes b(real coefficient function on the remaining coordinates)

-- @node: cubeNorm_nonneg
/-- If [the norm exponent is at least one](hyp:hq), [the biased cube norm of any
real function is nonnegative](goal). -/
lemma cubeNorm_nonneg (p q : ℝ) (hq : 1 ≤ q) -- @realizes q(norm exponent at least one)
    (g : (J → Bool) → ℝ) :
    0 ≤ cubeNorm p q g := by
  exact Real.rpow_nonneg ((biasedLaw J p).E_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)) _

-- @node: noiseParameter_bounds
/-- If [the bias is strictly between zero and one](hyp:hp), [the associated noise
parameter is positive and at most one eighth](goal). -/
lemma noiseParameter_bounds (p : ℝ) (hp : BiasInterior p) :
    0 < noiseParameter p ∧ noiseParameter p ≤ 1 / 8 := by
  obtain ⟨hpos, hle⟩ := biasScale_pos_le_half p hp
  dsimp [noiseParameter]
  constructor <;> linarith
    -- @realizes \rho(positive noise parameter at most one eighth)

-- @node: noiseOperator_linear
/-- [The noise operator preserves addition of real functions and multiplication
by a real scalar](goal). -/
lemma noiseOperator_linear (p ρ : ℝ) (g h : (J → Bool) → ℝ) (c : ℝ) :
    noiseOperator p ρ (g + h) = noiseOperator p ρ g + noiseOperator p ρ h ∧
    noiseOperator p ρ (c • g) = c • noiseOperator p ρ g := by
  constructor
  · funext x
    simp only [noiseOperator, fourierCoeffR, Pi.add_apply, add_mul, FiniteDesign.E_add,
      mul_add, Finset.sum_add_distrib]
  · funext x
    simp only [noiseOperator, fourierCoeffR, Pi.smul_apply, smul_eq_mul, mul_assoc,
      FiniteDesign.E_const_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring

-- @node: noiseOperator_fourierChar
/-- If [the bias is strictly between zero and one](hyp:hp), [applying the noise
operator to a Fourier character multiplies that character by the noise parameter
raised to the number of coordinates indexing it](goal). -/
lemma noiseOperator_fourierChar (p ρ : ℝ) (hp : BiasInterior p) (S : Finset J) :
    noiseOperator p ρ (fourierChar p S) = fun x => ρ ^ S.card * fourierChar p S x := by
  funext x
  simp only [noiseOperator, fourierCoeffR, fourierChar_orthonormal p hp]
  simp

-- @node: fourierCoeffR_lowProjection
/-- If [the bias is strictly between zero and one](hyp:hp), [the Fourier coefficient
of the low-degree projection equals the original coefficient when its coordinate
set has size at most the degree bound, and is zero otherwise](goal). -/
lemma fourierCoeffR_lowProjection (p d : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) (S : Finset J) :
    fourierCoeffR p (lowProjection p d g) S =
      if (S.card : ℝ) ≤ d then fourierCoeffR p g S else 0 := by
  classical
  unfold fourierCoeffR lowProjection
  simp_rw [Finset.sum_mul, FiniteDesign.E_sum, mul_assoc, FiniteDesign.E_const_mul,
    fourierChar_orthonormal p hp]
  simp [fourierCoeffR]

-- @node: lowProjection_orthogonal
/-- If [the bias is strictly between zero and one](hyp:hp) and [the degree bound
is nonnegative](hyp:hd), [the low-degree projection belongs to the low-degree space,
and its residual has zero expected product with every function in that space](goal). -/
lemma lowProjection_orthogonal (p d : ℝ) (hp : BiasInterior p) (hd : 0 ≤ d)
    (g : (J → Bool) → ℝ) :
    lowProjection p d g ∈ lowDegreeSpace p d ∧
    ∀ u ∈ lowDegreeSpace p d,
      (biasedLaw J p).E (fun x => (g x - lowProjection p d g x) * u x) = 0 := by
  classical
  constructor
  · have heq : lowProjection p d g =
        ∑ S ∈ Finset.univ.filter (fun S : Finset J => (S.card : ℝ) ≤ d),
          fourierCoeffR p g S • fourierChar p S := by
        funext x
        simp [lowProjection, Finset.sum_apply]
    rw [heq]
    apply Submodule.sum_mem
    intro S hS
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨S, (Finset.mem_filter.mp hS).2, rfl⟩
  · intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨S, hS, rfl⟩ := hu
        simp only [sub_mul, FiniteDesign.E_sub]
        change fourierCoeffR p g S - fourierCoeffR p (lowProjection p d g) S = 0
        rw [fourierCoeffR_lowProjection p d hp g S, if_pos hS, sub_self]
    | zero => simp
    | add u v hu hv ihu ihv =>
        simpa only [Pi.add_apply, mul_add, FiniteDesign.E_add, ihu, ihv, add_zero]
    | smul c u hu ihu =>
        simp only [Pi.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm (g _ - lowProjection p d g _), FiniteDesign.E_const_mul,
          ihu, mul_zero]

-- @node: lowProjection_idempotent
/-- If [the bias is strictly between zero and one](hyp:hp) and [the degree bound
is nonnegative](hyp:hd), [applying the low-degree projection twice gives the same
function as applying it once](goal). -/
lemma lowProjection_idempotent (p d : ℝ) (hp : BiasInterior p) (hd : 0 ≤ d)
    (g : (J → Bool) → ℝ) :
    lowProjection p d (lowProjection p d g) = lowProjection p d g := by
  classical
  funext x
  change (∑ S ∈ Finset.univ.filter (fun S : Finset J => (S.card : ℝ) ≤ d),
    fourierCoeffR p (lowProjection p d g) S * fourierChar p S x) = _
  apply Finset.sum_congr rfl
  intro S hS
  rw [fourierCoeffR_lowProjection p d hp g S, if_pos (Finset.mem_filter.mp hS).2]

omit [Fintype J] in
-- @node: coordinate_decomposition
/-- If [the bias is strictly between zero and one](hyp:hp), [the value of any real
function at a configuration equals its coordinate mean plus its coordinate Fourier
coefficient times the standardized character of that coordinate](goal). -/
lemma coordinate_decomposition (p : ℝ) (hp : BiasInterior p) (g : (J → Bool) → ℝ)
    (i : J) (x : J → Bool) :
    g x = coordinateMean p g i (fun j => x j.val) +
      coordinateFourier p g i (fun j => x j.val) * coordChar p i x := by
  have hσ : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  have hins : insertCoordinate i (fun j => x j.val) (x i) = x := by
    funext j
    by_cases hj : j = i
    · subst j; simp [insertCoordinate]
    · simp [insertCoordinate, hj]
  unfold coordinateMean coordinateFourier coordDiffRemaining coordChar
  cases hxi : x i <;> simp only [hxi, Bool.false_eq_true, ite_false, ite_true] at * <;>
    field_simp <;> nlinarith [congrArg g hins]

-- @node: coordinate_secondMoment
/-- If [the bias is strictly between zero and one](hyp:hp), [the second moment of
a real function equals the expectation over the remaining coordinates of the sum
of the squared coordinate mean and squared coordinate Fourier coefficient](goal). -/
lemma coordinate_secondMoment (p : ℝ) (hp : BiasInterior p) (g : (J → Bool) → ℝ) (i : J) :
    (biasedLaw J p).E (fun x => g x ^ 2) =
      (biasedLaw {j : J // j ≠ i} p).E
        (fun y => coordinateMean p g i y ^ 2 + coordinateFourier p g i y ^ 2) := by
  rw [biasedLaw_E_coordinate_split p hp _ i]
  apply FiniteDesign.E_congr
  intro y
  dsimp [coordinateMean, coordinateFourier, coordDiffRemaining]
  rw [mul_pow, biasScale_sq p hp]
  ring

end Papers.OaiSharpThresholdMonotone
