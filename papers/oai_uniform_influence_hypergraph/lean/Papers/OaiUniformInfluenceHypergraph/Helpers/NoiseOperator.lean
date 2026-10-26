module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.NoiseTensorization

/-! # Low-degree projection bounds from the noise estimate -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

variable {J : Type*} [Fintype J] [DecidableEq J]

-- @node: fourierCoeffR_noiseOperator
/-- If [the Bernoulli bias p is strictly between zero and one](hyp:hp),
[applying the noise operator with multiplier ρ to g multiplies its Fourier coefficient
on any coordinate set A by ρ raised to the number of coordinates in A](goal). -/
lemma fourierCoeffR_noiseOperator (p ρ : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) (A : Finset J) :
    fourierCoeffR p (noiseOperator p ρ g) A = ρ ^ A.card * fourierCoeffR p g A := by
  unfold noiseOperator
  rw [fourierCoeffR_spectral_sum p hp]
  simp

-- @node: lowDegreeSpace_coeff_eq_zero
/-- If [the Bernoulli bias p is strictly between zero and one](hyp:hp),
[u belongs to the span of Fourier terms of degree at most k](hyp:hu), and
[the coordinate set A has more than k elements](hyp:hA), then
[the Fourier coefficient of u on A is zero](goal). -/
lemma lowDegreeSpace_coeff_eq_zero (p k : ℝ) (hp : BiasInterior p)
    (u : (J → Bool) → ℝ) (hu : u ∈ lowDegreeSpace p k)
    (A : Finset J) (hA : k < (A.card : ℝ)) : fourierCoeffR p u A = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨B, hB, rfl⟩ := hu
      have hne : B ≠ A := by intro he; subst B; linarith
      simp [fourierCoeffR, fourierChar_orthonormal p hp, hne]
  | zero => simp [fourierCoeffR]
  | add u v hu hv ihu ihv =>
      simp only [fourierCoeffR, Pi.add_apply, add_mul, FiniteDesign.E_add] at *
      rw [ihu, ihv, add_zero]
  | smul c u hu ihu =>
      simp only [fourierCoeffR, Pi.smul_apply, smul_eq_mul, mul_assoc,
        FiniteDesign.E_const_mul] at *
      rw [ihu, mul_zero]

-- @node: lowDegree_norm_four_le
/-- If [the Bernoulli bias p is strictly between zero and one](hyp:hp),
[the degree cutoff k is nonnegative](hyp:hk), and
[u belongs to the span of Fourier terms of degree at most k](hyp:hu), then
[the L⁴ norm of u is at most its L² norm multiplied by the noise parameter
raised to the power −k](goal), with both norms taken under the p-biased product law. -/
lemma lowDegree_norm_four_le (p k : ℝ) (hp : BiasInterior p) (hk : 0 ≤ k)
    (u : (J → Bool) → ℝ) -- @realizes u(real function on J)
    (hu : u ∈ lowDegreeSpace p k) : -- @realizes u(low-degree span membership)
    cubeNormFour p u ≤ noiseParameter p ^ (-k) * cubeNormTwo p u := by
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
    exact (fourier_expansion p hp u x).symm
  have hnorm : cubeNormTwo p v ≤ ρ ^ (-k) * cubeNormTwo p u := by
    have hs : (biasedLaw J p).E (fun x => v x ^ 2) ≤
        (ρ ^ (-k)) ^ 2 * (biasedLaw J p).E (fun x => u x ^ 2) := by
      rw [secondMoment_eq_sum_fourierCoeffR_sq p hp,
        secondMoment_eq_sum_fourierCoeffR_sq p hp, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro A _
      rw [show fourierCoeffR p v A = ρ⁻¹ ^ A.card * fourierCoeffR p u A
        from fourierCoeffR_noiseOperator p ρ⁻¹ hp u A, mul_pow]
      by_cases hAk : (A.card : ℝ) ≤ k
      · have hb : ρ⁻¹ ^ A.card ≤ ρ ^ (-k) := by
          rw [← Real.rpow_natCast, ← Real.rpow_neg_eq_inv_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge hρ hρle (neg_le_neg hAk)
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (pow_nonneg (inv_nonneg.mpr hρ.le) _) hb 2) (sq_nonneg _)
      · rw [lowDegreeSpace_coeff_eq_zero p k hp u hu A (lt_of_not_ge hAk)]
        simp
    have hn : 0 ≤ ρ ^ (-k) * cubeNormTwo p u :=
      mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.sqrt_nonneg _)
    have hv : cubeNormTwo p v ^ 2 = (biasedLaw J p).E (fun x => v x ^ 2) :=
      Real.sq_sqrt ((biasedLaw J p).E_nonneg (fun x => sq_nonneg _))
    have hu2 : cubeNormTwo p u ^ 2 = (biasedLaw J p).E (fun x => u x ^ 2) :=
      Real.sq_sqrt ((biasedLaw J p).E_nonneg (fun x => sq_nonneg _))
    rw [← hv, ← hu2] at hs
    nlinarith [Real.sqrt_nonneg ((biasedLaw J p).E (fun x => v x ^ 2))]
  calc
    cubeNormFour p u = cubeNormFour p (noiseOperator p ρ v) := congrArg _ hinv.symm
    _ ≤ cubeNormTwo p v := noiseOperator_norm_four_le_two p hp v
    _ ≤ _ := hnorm

-- @node: cubeNormTwo_nonneg
/-- [The L² norm of any real function g under the p-biased product law is nonnegative](goal). -/
lemma cubeNormTwo_nonneg (p : ℝ) (g : (J → Bool) → ℝ) :
    0 ≤ cubeNormTwo p g := Real.sqrt_nonneg _

-- @node: cubeNormTwo_sq
/-- [The square of the L² norm of g under the p-biased product law equals
the expectation of g squared under that law](goal). -/
lemma cubeNormTwo_sq (p : ℝ) (g : (J → Bool) → ℝ) :
    cubeNormTwo p g ^ 2 = (biasedLaw J p).E (fun x => g x ^ 2) :=
  Real.sq_sqrt ((biasedLaw J p).E_nonneg (fun x => sq_nonneg _))

-- @node: cubeNormTwo_const_mul
/-- [Multiplying a real function g by a real constant c multiplies its L² norm
under the p-biased product law by the absolute value of c](goal). -/
lemma cubeNormTwo_const_mul (p c : ℝ) (g : (J → Bool) → ℝ) :
    cubeNormTwo p (fun x => c * g x) = |c| * cubeNormTwo p g := by
  unfold cubeNormTwo
  simp_rw [mul_pow]
  rw [FiniteDesign.E_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

-- @node: cube_inner_le
/-- [The absolute expectation of the product of g and u under the p-biased product
law is at most the product of their L² norms under that law](goal). -/
lemma cube_inner_le (p : ℝ) (g u : (J → Bool) → ℝ) :
    |(biasedLaw J p).E (fun x => g x * u x)| ≤ cubeNormTwo p g * cubeNormTwo p u := by
  exact Causalean.Mathlib.Analysis.abs_weighted_inner_le Finset.univ
    (biasedLaw J p).p g u (fun x _ => (biasedLaw J p).p_nonneg x)

-- @node: lowProjection_inner_eq
/-- If [the Bernoulli bias p is strictly between zero and one](hyp:hp),
[the degree cutoff k is nonnegative](hyp:hk), and
[u belongs to the span of Fourier terms of degree at most k](hyp:hu), then
[the expectation of g times u equals the expectation of the degree-at-most-k
projection of g times u](goal), under the p-biased product law. -/
lemma lowProjection_inner_eq (p k : ℝ) (hp : BiasInterior p) (hk : 0 ≤ k)
    (g u : (J → Bool) → ℝ) (hu : u ∈ lowDegreeSpace p k) :
    (biasedLaw J p).E (fun x => g x * u x) =
      (biasedLaw J p).E (fun x => lowProjection p k g x * u x) := by
  have ho := (lowProjection_orthogonal p k hp hk g).2 u hu
  simp_rw [sub_mul] at ho
  rw [FiniteDesign.E_sub] at ho
  exact sub_eq_zero.mp ho

-- @node: lowProjection_norm_dual
/-- If [the Bernoulli bias p is strictly between zero and one](hyp:hp),
[the degree cutoff k is nonnegative](hyp:hk), and [c is nonnegative](hyp:hc), then
[the L² norm of the degree-at-most-k projection of g is at most c if and only if
the absolute expectation of g times u is at most c for every u in the
degree-at-most-k Fourier span with L² norm one](goal), under the p-biased product law. -/
lemma lowProjection_norm_dual (p k : ℝ) (hp : BiasInterior p) (hk : 0 ≤ k)
    (g : (J → Bool) → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    cubeNormTwo p (lowProjection p k g) ≤ c ↔
      ∀ u ∈ lowDegreeSpace p k, cubeNormTwo p u = 1 → -- @realizes u(unit L2 vector in the span)
        |(biasedLaw J p).E (fun x => g x * u x)| ≤ c := by
  have hP := (lowProjection_orthogonal p k hp hk g).1
  constructor
  · intro h u hu hn
    rw [lowProjection_inner_eq p k hp hk g u hu]
    calc
      _ ≤ cubeNormTwo p (lowProjection p k g) * cubeNormTwo p u := cube_inner_le p _ _
      _ ≤ c := by rwa [hn, mul_one]
  · intro h
    let n := cubeNormTwo p (lowProjection p k g)
    have hn : 0 ≤ n := cubeNormTwo_nonneg p _
    by_cases hz : n = 0
    · change n ≤ c
      rwa [hz]
    have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hz)
    let u := fun x => n⁻¹ * lowProjection p k g x
    have hu : u ∈ lowDegreeSpace p k := (lowDegreeSpace p k).smul_mem n⁻¹ hP
    have huunit : cubeNormTwo p u = 1 := by
      rw [cubeNormTwo_const_mul, abs_of_pos (inv_pos.mpr hnpos)]
      exact inv_mul_cancel₀ hz
    have hh := h u hu huunit
    rw [lowProjection_inner_eq p k hp hk g u hu] at hh
    have he : (biasedLaw J p).E (fun x => lowProjection p k g x * u x) = n := by
      calc
        _ = n⁻¹ * (biasedLaw J p).E (fun x => lowProjection p k g x ^ 2) := by
          rw [← FiniteDesign.E_const_mul]
          apply FiniteDesign.E_congr
          intro x
          dsimp [u]
          ring
        _ = n⁻¹ * n ^ 2 := by rw [← cubeNormTwo_sq]
        _ = n := by field_simp
    rwa [he, abs_of_nonneg hn] at hh

-- @node: cube_holder_fourThirds_four
/-- [The absolute expectation of the product of g and u under the p-biased product
law is at most the L⁴ᐟ³ norm of g times the L⁴ norm of u under that law](goal). -/
lemma cube_holder_fourThirds_four (p : ℝ) (g u : (J → Bool) → ℝ) :
    |(biasedLaw J p).E (fun x => g x * u x)| ≤
      cubeNormFourThirds p g * cubeNormFour p u := by
  let w := (biasedLaw J p).p
  have hw (x) : 0 ≤ w x := (biasedLaw J p).p_nonneg x
  have hconj : (4 / 3 : ℝ).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hconj
    (f := fun x => w x ^ (3 / 4 : ℝ) * |g x|)
    (g := fun x => w x ^ (1 / 4 : ℝ) * |u x|)
    (fun x _ => mul_nonneg (Real.rpow_nonneg (hw x) _) (abs_nonneg _))
    (fun x _ => mul_nonneg (Real.rpow_nonneg (hw x) _) (abs_nonneg _))
  have hf (x) : (w x ^ (3 / 4 : ℝ) * |g x|) ^ (4 / 3 : ℝ) =
      w x * |g x| ^ (4 / 3 : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw x) _) (abs_nonneg _),
      ← Real.rpow_mul (hw x)]
    norm_num
  have hu (x) : (w x ^ (1 / 4 : ℝ) * |u x|) ^ (4 : ℝ) = w x * u x ^ 4 := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw x) _) (abs_nonneg _),
      ← Real.rpow_mul (hw x)]
    norm_num only [show (1 / 4 * 4 : ℝ) = 1 by norm_num, Real.rpow_one]
    rw [show |u x| ^ (4 : ℝ) = |u x| ^ (4 : ℕ) from Real.rpow_natCast _ 4]
    rw [show |u x| ^ (4 : ℕ) = u x ^ (4 : ℕ) by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
  have hm (x) : (w x ^ (3 / 4 : ℝ) * |g x|) *
      (w x ^ (1 / 4 : ℝ) * |u x|) = w x * |g x * u x| := by
    rw [abs_mul]
    calc
      _ = (w x ^ (3 / 4 : ℝ) * w x ^ (1 / 4 : ℝ)) * (|g x| * |u x|) := by ring
      _ = _ := by rw [← Real.rpow_add' (hw x) (by norm_num : (3 / 4 : ℝ) + 1 / 4 ≠ 0)]; norm_num
  simp_rw [hf, hu, hm] at h
  norm_num only [show (1 / (4 / 3) : ℝ) = 3 / 4 by norm_num] at h
  refine le_trans ?_ h
  change |∑ x, w x * (g x * u x)| ≤ ∑ x, w x * |g x * u x|
  calc
    _ ≤ ∑ x, |w x * (g x * u x)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp_rw [abs_mul, abs_of_nonneg (hw _)]

-- @node: lowProjection_norm_le
/-- If [the Bernoulli bias p is strictly between zero and one](hyp:hp) and
[the degree cutoff k is nonnegative](hyp:hk), then
[the L² norm of the degree-at-most-k projection of g is at most the L⁴ᐟ³ norm
of g multiplied by the noise parameter raised to the power −k](goal),
with both norms taken under the p-biased product law. -/
lemma lowProjection_norm_le (p k : ℝ) (hp : BiasInterior p) (hk : 0 ≤ k)
    (g : (J → Bool) → ℝ) :
    cubeNormTwo p (lowProjection p k g) ≤
      noiseParameter p ^ (-k) * cubeNormFourThirds p g := by
  have hc : 0 ≤ noiseParameter p ^ (-k) * cubeNormFourThirds p g :=
    mul_nonneg (Real.rpow_nonneg (noiseParameter_bounds p hp).1.le _)
      (Real.rpow_nonneg ((biasedLaw J p).E_nonneg
        (fun x => Real.rpow_nonneg (abs_nonneg _) _)) _)
  apply (lowProjection_norm_dual p k hp hk g _ hc).mpr
  intro u hu hn
  calc
    _ ≤ cubeNormFourThirds p g * cubeNormFour p u := cube_holder_fourThirds_four p g u
    _ ≤ cubeNormFourThirds p g * (noiseParameter p ^ (-k) * cubeNormTwo p u) :=
      mul_le_mul_of_nonneg_left (lowDegree_norm_four_le p k hp hk u hu)
        (Real.rpow_nonneg ((biasedLaw J p).E_nonneg
          (fun x => Real.rpow_nonneg (abs_nonneg _) _)) _)
    _ = _ := by rw [hn, mul_one, mul_comm]

end Papers.OaiUniformInfluenceHypergraph
