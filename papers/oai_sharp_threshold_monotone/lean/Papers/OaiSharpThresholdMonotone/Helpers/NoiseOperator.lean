module
public import Papers.OaiSharpThresholdMonotone.Helpers.NoiseTensorization
public import Mathlib.Analysis.MeanInequalities

/-! # Duality and the low-degree projection norm -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

variable {J : Type*} [Fintype J] [DecidableEq J]

-- @node: cubeNorm_two_eq_sqrt
/-- [The biased cube norm with exponent two is the square root of the function's
second moment](goal). -/
lemma cubeNorm_two_eq_sqrt (p : ℝ) (g : (J → Bool) → ℝ) :
    cubeNorm p 2 g = Real.sqrt ((biasedLaw J p).E (fun x => g x ^ 2)) := by
  simp only [cubeNorm, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]

-- @node: cubeNorm_two_sq
/-- [The square of the biased cube norm with exponent two equals the function's
second moment](goal). -/
lemma cubeNorm_two_sq (p : ℝ) (g : (J → Bool) → ℝ) :
    cubeNorm p 2 g ^ 2 = (biasedLaw J p).E (fun x => g x ^ 2) := by
  rw [cubeNorm_two_eq_sqrt]
  exact Real.sq_sqrt ((biasedLaw J p).E_nonneg (fun x => sq_nonneg _))

-- @node: cubeNorm_two_const_mul
/-- [Multiplying a real function by a constant multiplies its biased cube norm
with exponent two by the absolute value of that constant](goal). -/
lemma cubeNorm_two_const_mul (p c : ℝ) (g : (J → Bool) → ℝ) :
    cubeNorm p 2 (fun x => c * g x) = |c| * cubeNorm p 2 g := by
  simp_rw [cubeNorm_two_eq_sqrt, mul_pow]
  rw [FiniteDesign.E_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

-- @node: fourierCoeffR_noiseOperator
/-- If [the bias is strictly between zero and one](hyp:hp), [the Fourier coefficient
of the noise-transformed function on a coordinate set equals its original coefficient
times the noise parameter raised to the size of that set](goal). -/
lemma fourierCoeffR_noiseOperator (p ρ : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) (A : Finset J) :
    fourierCoeffR p (noiseOperator p ρ g) A = ρ ^ A.card * fourierCoeffR p g A := by
  unfold fourierCoeffR noiseOperator
  simp_rw [Finset.sum_mul, FiniteDesign.E_sum, mul_assoc,
    FiniteDesign.E_const_mul, fourierChar_orthonormal p hp]
  simp [fourierCoeffR]

-- @node: lowDegree_norm_four_le
/-- If [the bias is strictly between zero and one](hyp:hp), [the degree bound is
nonnegative](hyp:hd), and [u equals its own low-degree projection](hyp:hu),
[the fourth norm of u is at most its second norm times the associated noise parameter
raised to the negative degree bound](goal). -/
lemma lowDegree_norm_four_le (p d : ℝ) (hp : BiasInterior p) (hd : 0 ≤ d)
    (u : (J → Bool) → ℝ) -- @realizes u(real function in the projection argument)
    (hu : u = lowProjection p d u) : -- @realizes u(bounded-degree projection fixed point)
    cubeNorm p 4 u ≤ noiseParameter p ^ (-d) * cubeNorm p 2 u := by
  let ρ := noiseParameter p
  have hρ : 0 < ρ := (noiseParameter_bounds p hp).1
  have hρle : ρ ≤ 1 := le_trans (noiseParameter_bounds p hp).2 (by norm_num)
  let v := noiseOperator p ρ⁻¹ u
  have hinv : noiseOperator p ρ v = u := by
    funext x
    unfold noiseOperator
    simp_rw [show ∀ A, fourierCoeffR p v A = ρ⁻¹ ^ A.card * fourierCoeffR p u A
      from fun A => fourierCoeffR_noiseOperator p ρ⁻¹ hp u A]
    simp only [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ.ne', one_pow, one_mul]
    exact (congrFun (fourier_expansion p hp u) x).symm
  have hnorm : cubeNorm p 2 v ≤ ρ ^ (-d) * cubeNorm p 2 u := by
    have hs : (biasedLaw J p).E (fun x => v x ^ 2) ≤
        (ρ ^ (-d)) ^ 2 * (biasedLaw J p).E (fun x => u x ^ 2) := by
      rw [secondMoment_eq_sum_fourierCoeffR_sq p hp,
        secondMoment_eq_sum_fourierCoeffR_sq p hp, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro A _
      rw [show fourierCoeffR p v A = ρ⁻¹ ^ A.card * fourierCoeffR p u A
        from fourierCoeffR_noiseOperator p ρ⁻¹ hp u A, mul_pow]
      by_cases hAd : (A.card : ℝ) ≤ d
      · have hb : ρ⁻¹ ^ A.card ≤ ρ ^ (-d) := by
          rw [← Real.rpow_natCast, ← Real.rpow_neg_eq_inv_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge hρ hρle (neg_le_neg hAd)
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (pow_nonneg (inv_nonneg.mpr hρ.le) _) hb 2) (sq_nonneg _)
      · have hz : fourierCoeffR p u A = 0 := by
          have he := congrArg (fun v => fourierCoeffR p v A) hu
          rw [fourierCoeffR_lowProjection p d hp, if_neg hAd] at he
          exact he
        rw [hz]
        simp
    have hn : 0 ≤ ρ ^ (-d) * cubeNorm p 2 u :=
      mul_nonneg (Real.rpow_nonneg hρ.le _) (cubeNorm_nonneg p 2 (by norm_num) u)
    have hv : cubeNorm p 2 v ^ 2 = (biasedLaw J p).E (fun x => v x ^ 2) :=
      cubeNorm_two_sq p v
    have hu2 : cubeNorm p 2 u ^ 2 = (biasedLaw J p).E (fun x => u x ^ 2) :=
      cubeNorm_two_sq p u
    rw [← hv, ← hu2] at hs
    nlinarith [cubeNorm_nonneg p 2 (by norm_num) v]
  calc
    cubeNorm p 4 u = cubeNorm p 4 (noiseOperator p ρ v) := congrArg _ hinv.symm
    _ ≤ cubeNorm p 2 v := noiseOperator_norm_four_le_two p hp v
    _ ≤ _ := hnorm

-- @node: cube_holder
/-- If [q and r are conjugate Hölder exponents](hyp:hqr), [the absolute expected
product of two real functions is at most the product of their biased cube norms
with exponents q and r, respectively](goal). -/
lemma cube_holder (p q r : ℝ) (hqr : q.HolderConjugate r)
    (g u : (J → Bool) → ℝ) :
    |(biasedLaw J p).E (fun x => g x * u x)| ≤ cubeNorm p q g * cubeNorm p r u := by
  classical
  let D := biasedLaw J p
  let G := fun x => D.p x ^ (1 / q) * |g x|
  let U := fun x => D.p x ^ (1 / r) * |u x|
  have hG (x) : 0 ≤ G x := mul_nonneg (Real.rpow_nonneg (D.p_nonneg x) _) (abs_nonneg _)
  have hU (x) : 0 ≤ U x := mul_nonneg (Real.rpow_nonneg (D.p_nonneg x) _) (abs_nonneg _)
  have hprod (x) : G x * U x = D.p x * |g x * u x| := by
    dsimp [G, U]
    rw [abs_mul]
    calc
      _ = (D.p x ^ (1 / q) * D.p x ^ (1 / r)) * (|g x| * |u x|) := by ring
      _ = D.p x * (|g x| * |u x|) := by
        rw [← Real.rpow_add' (D.p_nonneg x)
          (by simpa only [one_div, hqr.inv_add_inv_eq_one] using (one_ne_zero : (1 : ℝ) ≠ 0)),
          one_div, one_div, hqr.inv_add_inv_eq_one, Real.rpow_one]
  have hpowG (x) : G x ^ q = D.p x * |g x| ^ q := by
    dsimp [G]
    rw [Real.mul_rpow (Real.rpow_nonneg (D.p_nonneg x) _) (abs_nonneg _),
      ← Real.rpow_mul (D.p_nonneg x)]
    simp [hqr.ne_zero]
  have hpowU (x) : U x ^ r = D.p x * |u x| ^ r := by
    dsimp [U]
    rw [Real.mul_rpow (Real.rpow_nonneg (D.p_nonneg x) _) (abs_nonneg _),
      ← Real.rpow_mul (D.p_nonneg x)]
    simp [hqr.symm.ne_zero]
  calc
    |D.E (fun x => g x * u x)| ≤ ∑ x, |D.p x * (g x * u x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, G x * U x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hprod, abs_mul, abs_of_nonneg (D.p_nonneg x)]
    _ ≤ (∑ x, G x ^ q) ^ (1 / q) * (∑ x, U x ^ r) ^ (1 / r) :=
      Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hqr (fun x _ => hG x) (fun x _ => hU x)
    _ = cubeNorm p q g * cubeNorm p r u := by
      simp_rw [hpowG, hpowU]
      rfl

-- @node: cube_holder_fourThirds_four
/-- [The absolute expected product of two real functions is at most the product
of the first function's biased cube norm with exponent four thirds and the second
function's norm with exponent four](goal). -/
lemma cube_holder_fourThirds_four (p : ℝ) (g u : (J → Bool) → ℝ) :
    |(biasedLaw J p).E (fun x => g x * u x)| ≤ cubeNorm p (4 / 3) g * cubeNorm p 4 u := by
  exact cube_holder p (4 / 3) 4 (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) g u

-- @node: lowProjection_const_mul
/-- [The low-degree projection of a constant times a real function equals that
constant times the function's low-degree projection](goal). -/
lemma lowProjection_const_mul (p d c : ℝ) (g : (J → Bool) → ℝ) :
    lowProjection p d (fun x => c * g x) = fun x => c * lowProjection p d g x := by
  classical
  funext x
  simp only [lowProjection, fourierCoeffR, mul_assoc, FiniteDesign.E_const_mul,
    Finset.mul_sum]

-- @node: lowProjection_inner_eq
/-- If [the bias is strictly between zero and one](hyp:hp), [the degree bound is
nonnegative](hyp:hd), and [u equals its own low-degree projection](hyp:hu),
[the expected product of v and u equals the expected product of the low-degree
projection of v and u](goal). -/
lemma lowProjection_inner_eq (p d : ℝ) (hp : BiasInterior p) (hd : 0 ≤ d)
    (v u : (J → Bool) → ℝ) (hu : u = lowProjection p d u) :
    (biasedLaw J p).E (fun x => v x * u x) =
      (biasedLaw J p).E (fun x => lowProjection p d v x * u x) := by
  have hmem : u ∈ lowDegreeSpace p d := by
    rw [hu]
    exact (lowProjection_orthogonal p d hp hd u).1
  have ho := (lowProjection_orthogonal p d hp hd v).2 u hmem
  simp_rw [sub_mul] at ho
  rw [FiniteDesign.E_sub] at ho
  exact sub_eq_zero.mp ho

-- @node: lowProjection_norm_dual
/-- If [the bias is strictly between zero and one](hyp:hp), [the degree bound is
nonnegative](hyp:hd), and [c is nonnegative](hyp:hc), [the second norm of the
low-degree projection of v is at most c if and only if the absolute expected product of v
with every low-degree function of second norm one is at most c](goal). -/
lemma lowProjection_norm_dual (p d : ℝ) (hp : BiasInterior p) (hd : 0 ≤ d)
    (v : (J → Bool) → ℝ) (c : ℝ) (hc : 0 ≤ c) : -- @realizes v(arbitrary projected real function)
    cubeNorm p 2 (lowProjection p d v) ≤ c ↔
      ∀ u : (J → Bool) → ℝ, u = lowProjection p d u →
        cubeNorm p 2 u = 1 → -- @realizes u(unit norm test function)
        |(biasedLaw J p).E (fun x => v x * u x)| ≤ c := by
  constructor
  · intro h u hu hn
    rw [lowProjection_inner_eq p d hp hd v u hu]
    calc
      _ ≤ cubeNorm p 2 (lowProjection p d v) * cubeNorm p 2 u :=
        cube_holder p 2 2
          (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) _ _
      _ ≤ c := by rwa [hn, mul_one]
  · intro h
    let n := cubeNorm p 2 (lowProjection p d v)
    have hn : 0 ≤ n := cubeNorm_nonneg p 2 (by norm_num) _
    by_cases hz : n = 0
    · change n ≤ c
      rwa [hz]
    have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hz)
    let u := fun x => n⁻¹ * lowProjection p d v x
    have hu : u = lowProjection p d u := by
      dsimp [u]
      rw [lowProjection_const_mul, lowProjection_idempotent p d hp hd]
    have huunit : cubeNorm p 2 u = 1 := by
      rw [cubeNorm_two_const_mul, abs_of_pos (inv_pos.mpr hnpos)]
      exact inv_mul_cancel₀ hz
    have hh := h u hu huunit
    rw [lowProjection_inner_eq p d hp hd v u hu] at hh
    have he : (biasedLaw J p).E (fun x => lowProjection p d v x * u x) = n := by
      calc
        _ = n⁻¹ * (biasedLaw J p).E (fun x => lowProjection p d v x ^ 2) := by
          rw [← FiniteDesign.E_const_mul]
          apply FiniteDesign.E_congr
          intro x
          dsimp [u]
          ring
        _ = n⁻¹ * n ^ 2 := by rw [← cubeNorm_two_sq]
        _ = n := by field_simp
    rwa [he, abs_of_nonneg hn] at hh

-- @node: lowProjection_norm_le
/-- If [the bias is strictly between zero and one](hyp:hp) and [the degree bound
is nonnegative](hyp:hd), [the second norm of the low-degree projection of g is at
most the four-thirds norm of g times the associated noise parameter raised to the
negative degree bound](goal). -/
lemma lowProjection_norm_le (p d : ℝ) (hp : BiasInterior p) (hd : 0 ≤ d)
    (g : (J → Bool) → ℝ) :
    cubeNorm p 2 (lowProjection p d g) ≤
      noiseParameter p ^ (-d) * cubeNorm p (4 / 3) g := by
  have hc : 0 ≤ noiseParameter p ^ (-d) * cubeNorm p (4 / 3) g :=
    mul_nonneg (Real.rpow_nonneg (noiseParameter_bounds p hp).1.le _)
      (Real.rpow_nonneg ((biasedLaw J p).E_nonneg
        (fun x => Real.rpow_nonneg (abs_nonneg _) _)) _)
  apply (lowProjection_norm_dual p d hp hd g _ hc).mpr
  intro u hu hn
  calc
    _ ≤ cubeNorm p (4 / 3) g * cubeNorm p 4 u := cube_holder_fourThirds_four p g u
    _ ≤ cubeNorm p (4 / 3) g * (noiseParameter p ^ (-d) * cubeNorm p 2 u) :=
      mul_le_mul_of_nonneg_left (lowDegree_norm_four_le p d hp hd u hu)
        (Real.rpow_nonneg ((biasedLaw J p).E_nonneg
          (fun x => Real.rpow_nonneg (abs_nonneg _) _)) _)
    _ = _ := by rw [hn, mul_one, mul_comm]

end Papers.OaiSharpThresholdMonotone
