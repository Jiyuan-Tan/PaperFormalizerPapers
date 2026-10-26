module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.Fourier
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Analysis.MeanInequalities
public import Causalean.Mathlib.Analysis.WeightedCauchySchwarz

/-! # Noise, tensorization, and projection on the biased cube

All operators are constructed by their finite Fourier sums. Linearity,
tensorization, and norm estimates are conclusions to prove locally.
-/

@[expose] public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- For [bias p](hyp:p), the [noise parameter](goal) is one quarter of the
square root of p times one minus p. -/
noncomputable def noiseParameter (p : ℝ) : ℝ := biasScale p / 4 -- @realizes \rho(sigma/4)

/-- On a [finite coordinate set J](hyp:J), for [bias p](hyp:p),
[noise multiplier ρ](hyp:ρ), a [real-valued function g on the Boolean cube](hyp:g),
and a [configuration x](hyp:x), the [noise operator evaluated at x](goal) is the
sum of the Fourier terms of g, with each term of degree d multiplied by ρ to the power d. -/
noncomputable def noiseOperator (p ρ : ℝ) (g : (J → Bool) → ℝ) (x : J → Bool) : ℝ :=
  -- @realizes T(multiplier rho^card A)
  ∑ A : Finset J, ρ ^ A.card * fourierCoeffR p g A * fourierChar p A x

/-- On a [finite coordinate set J](hyp:J), for [bias p](hyp:p), a [degree cutoff k](hyp:k),
a [real-valued function g on the Boolean cube](hyp:g), and a [configuration x](hyp:x),
the [low-degree projection evaluated at x](goal) is the sum of the Fourier terms of g
whose degrees do not exceed k. -/
noncomputable def lowProjection (p k : ℝ) (g : (J → Bool) → ℝ) (x : J → Bool) : ℝ :=
  ∑ A ∈ Finset.univ.filter (fun A : Finset J => (A.card : ℝ) ≤ k),
    fourierCoeffR p g A * fourierChar p A x -- @realizes P_{\le k}(Fourier orthogonal projection)

/-- On a [finite coordinate set J](hyp:J), for [bias p](hyp:p) and a
[real-valued function g on the Boolean cube](hyp:g), the [L² norm of g](goal)
is the square root of its expected square under the product Bernoulli law with bias p. -/
noncomputable def cubeNormTwo (p : ℝ) (g : (J → Bool) → ℝ) : ℝ :=
  Real.sqrt ((biasedLaw J p).E (fun x => g x ^ 2))

/-- On a [finite coordinate set J](hyp:J), for [bias p](hyp:p) and a
[real-valued function g on the Boolean cube](hyp:g), the [L⁴ norm of g](goal)
is the fourth root of its expected fourth power under the product Bernoulli law with bias p. -/
noncomputable def cubeNormFour (p : ℝ) (g : (J → Bool) → ℝ) : ℝ :=
  ((biasedLaw J p).E (fun x => g x ^ 4)) ^ (1 / 4 : ℝ)

/-- On a [finite coordinate set J](hyp:J), for [bias p](hyp:p) and a
[real-valued function g on the Boolean cube](hyp:g), the [L⁴ᐟ³ norm of g](goal)
is the expected four-thirds power of its absolute value, raised to the three-quarters
power, under the product Bernoulli law with bias p. -/
noncomputable def cubeNormFourThirds (p : ℝ) (g : (J → Bool) → ℝ) : ℝ :=
  ((biasedLaw J p).E (fun x => |g x| ^ (4 / 3 : ℝ))) ^ (3 / 4 : ℝ)

/-- On a [finite coordinate set J](hyp:J), for [bias p](hyp:p) and a
[degree cutoff k](hyp:k), the [low-degree space](goal) is the real linear span
of the biased Fourier characters indexed by coordinate subsets of size at most k. -/
noncomputable def lowDegreeSpace (p k : ℝ) : Submodule ℝ ((J → Bool) → ℝ) :=
  Submodule.span ℝ {u | ∃ A : Finset J, (A.card : ℝ) ≤ k ∧ u = fourierChar p A}

-- @node: noiseParameter_bounds
/-- If [the bias p lies strictly between zero and one](hyp:hp), then
[its noise parameter is positive and at most one eighth](goal). -/
lemma noiseParameter_bounds (p : ℝ) (hp : BiasInterior p) :
    0 < noiseParameter p ∧ noiseParameter p ≤ 1 / 8 := by
  obtain ⟨hpos, hle⟩ := biasScale_pos_le_half p hp
  unfold noiseParameter
  constructor
  · exact div_pos hpos (by norm_num)
  · linarith

-- @node: noiseOperator_linear
/-- For real-valued functions g and [h on the Boolean cube](hyp:h),
[the noise operator with bias p and multiplier ρ preserves their sum and
commutes with multiplication of g by any real scalar c](goal). -/
lemma noiseOperator_linear (p ρ : ℝ) (g h : (J → Bool) → ℝ) (c : ℝ) :
    noiseOperator p ρ (g + h) = noiseOperator p ρ g + noiseOperator p ρ h ∧
    noiseOperator p ρ (c • g) = c • noiseOperator p ρ g := by
  constructor
  · funext x
    simp only [noiseOperator, fourierCoeffR, Pi.add_apply, add_mul,
      FiniteDesign.E_add, mul_add, Finset.sum_add_distrib]
  · funext x
    simp only [noiseOperator, fourierCoeffR, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc c, FiniteDesign.E_const_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    ring

-- @node: noiseOperator_fourierChar
/-- If [the bias p lies strictly between zero and one](hyp:hp), then
[applying the noise operator with multiplier ρ to the Fourier character indexed
by A multiplies that character by ρ to the power of the size of A](goal). -/
lemma noiseOperator_fourierChar (p ρ : ℝ) (hp : BiasInterior p) (A : Finset J) :
    noiseOperator p ρ (fourierChar p A) = fun x => ρ ^ A.card * fourierChar p A x := by
  funext x
  simp only [noiseOperator, fourierCoeffR, fourierChar_orthonormal p hp]
  simp

-- @node: fourierCoeffR_spectral_sum
/-- If [the bias p lies strictly between zero and one](hyp:hp), then
[the Fourier coefficient at A of a finite sum of Fourier characters indexed by s
with weights a equals a at A when A belongs to s, and zero otherwise](goal). -/
lemma fourierCoeffR_spectral_sum (p : ℝ) (hp : BiasInterior p)
    (s : Finset (Finset J)) (a : Finset J → ℝ) (A : Finset J) :
    fourierCoeffR p (fun x => ∑ B ∈ s, a B * fourierChar p B x) A =
      if A ∈ s then a A else 0 := by
  unfold fourierCoeffR
  simp_rw [Finset.sum_mul, FiniteDesign.E_sum, mul_assoc,
    FiniteDesign.E_const_mul, fourierChar_orthonormal p hp]
  simp [eq_comm]

-- @node: fourierCoeffR_lowProjection
/-- If [the bias p lies strictly between zero and one](hyp:hp), then
[the Fourier coefficient at A of the degree-k projection of g equals the
coefficient of g when the size of A is at most k, and zero otherwise](goal). -/
lemma fourierCoeffR_lowProjection (p k : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) (A : Finset J) :
    fourierCoeffR p (lowProjection p k g) A =
      if (A.card : ℝ) ≤ k then fourierCoeffR p g A else 0 := by
  unfold lowProjection
  rw [fourierCoeffR_spectral_sum p hp]
  simp

-- @node: lowProjection_orthogonal
/-- If [the bias p lies strictly between zero and one](hyp:hp) and
[the degree cutoff k is nonnegative](hyp:hk), then [the degree-k projection of g
belongs to the low-degree space, and the expected product of its residual with
every function in that space is zero under the biased product law](goal). -/
lemma lowProjection_orthogonal (p k : ℝ) (hp : BiasInterior p) (hk : 0 ≤ k)
    (g : (J → Bool) → ℝ) :
    lowProjection p k g ∈ lowDegreeSpace p k ∧
    ∀ u ∈ lowDegreeSpace p k,
      (biasedLaw J p).E (fun x => (g x - lowProjection p k g x) * u x) = 0 := by
  constructor
  · change (fun x => ∑ A ∈ Finset.univ.filter
        (fun A : Finset J => (A.card : ℝ) ≤ k),
        fourierCoeffR p g A * fourierChar p A x) ∈ lowDegreeSpace p k
    have heq : (fun x => ∑ A ∈ Finset.univ.filter
        (fun A : Finset J => (A.card : ℝ) ≤ k),
        fourierCoeffR p g A * fourierChar p A x) =
        ∑ A ∈ Finset.univ.filter (fun A : Finset J => (A.card : ℝ) ≤ k),
          fourierCoeffR p g A • fourierChar p A := by
      ext x
      simp
    rw [heq]
    apply Submodule.sum_mem
    intro A hA
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨A, (Finset.mem_filter.mp hA).2, rfl⟩
  · intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨A, hA, rfl⟩ := hu
        simp_rw [sub_mul]
        rw [FiniteDesign.E_sub]
        change fourierCoeffR p g A - fourierCoeffR p (lowProjection p k g) A = 0
        rw [fourierCoeffR_lowProjection p k hp, if_pos hA, sub_self]
    | zero => simp
    | add u v hu hv ihu ihv =>
        simp only [Pi.add_apply, mul_add, FiniteDesign.E_add, ihu, ihv, add_zero]
    | smul c u hu ihu =>
        simp only [Pi.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm _ c, FiniteDesign.E_const_mul, ihu, mul_zero]


-- @node: lowProjection_norm_sq
/-- If [the bias p lies strictly between zero and one](hyp:hp) and
[the cutoff k is nonnegative](hyp:hk), then [the squared L² norm of the
degree-k projection of g equals the sum of its squared Fourier coefficients
over coordinate subsets of size at most k](goal). -/
lemma lowProjection_norm_sq (p k : ℝ) (hp : BiasInterior p) (hk : 0 ≤ k)
    (g : (J → Bool) → ℝ) :
    cubeNormTwo p (lowProjection p k g) ^ 2 =
      ∑ A ∈ Finset.univ.filter (fun A : Finset J => (A.card : ℝ) ≤ k),
        fourierCoeffR p g A ^ 2 := by
  unfold cubeNormTwo
  rw [Real.sq_sqrt ((biasedLaw J p).E_nonneg (fun x => sq_nonneg _)),
    secondMoment_eq_sum_fourierCoeffR_sq p hp]
  simp_rw [fourierCoeffR_lowProjection p k hp]
  simp [Finset.sum_filter]


-- @realizes a(real scalar in the one-coordinate calculation)
-- @realizes b(real scalar in the one-coordinate calculation)
-- @node: oneCoordinate_fourthMoment_le
/-- If [the bias p lies strictly between zero and one](hyp:hp), then
[the expected fourth power of a plus b times the noise parameter times a
normalized Bernoulli coordinate is at most the square of a² + b²](goal). -/
lemma oneCoordinate_fourthMoment_le (p : ℝ) (hp : BiasInterior p) (a b : ℝ) :
    (biasedLaw Unit p).E
      (fun x => (a + noiseParameter p * b * coordChar p () x) ^ 4) ≤ (a ^ 2 + b ^ 2) ^ 2 := by
  have hs : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  have hcancel (x : Unit → Bool) :
      noiseParameter p * b * coordChar p () x =
        b * ((if x () then 1 else 0) - p) / 4 := by
    unfold noiseParameter coordChar
    field_simp
    <;> ring
  simp_rw [hcancel]
  rw [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
    bernoulliDesign_E_eval _ _ _ ()
      (fun t => (a + b * ((if t then 1 else 0) - p) / 4) ^ 4), coinDesign_E]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hv : 0 ≤ p * (1 - p) := mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)
  have hvle : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hcubic : (1 - 2 * p) * a * b ^ 3 ≤ (a ^ 2 * b ^ 2 + b ^ 4) / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.2.le) (sq_nonneg (a * b - b ^ 2)),
      mul_nonneg hp.1.le (sq_nonneg (a * b + b ^ 2))]
  have hexp : p * (a + b * (1 - p) / 4) ^ 4 +
      (1 - p) * (a + b * (0 - p) / 4) ^ 4 =
      a ^ 4 + 3 / 8 * (p * (1 - p)) * (a ^ 2 * b ^ 2) +
      (p * (1 - p)) / 16 * ((1 - 2 * p) * a * b ^ 3) +
      (p * (1 - p)) * (1 - 3 * (p * (1 - p))) / 256 * b ^ 4 := by ring
  rw [hexp]
  have hcross := mul_le_mul_of_nonneg_left hcubic (div_nonneg hv (by norm_num : (0:ℝ) ≤ 16))
  have hfour : (p * (1 - p)) * (1 - 3 * (p * (1 - p))) / 256 * b ^ 4 ≤
      1 / 256 * (p * (1 - p)) * b ^ 4 := by
    nlinarith [mul_nonneg hv (sq_nonneg (b ^ 2)),
      mul_nonneg (sq_nonneg (p * (1 - p))) (sq_nonneg (b ^ 2))]
  have htwo := mul_le_mul_of_nonneg_right hvle (mul_nonneg (sq_nonneg a) (sq_nonneg b))
  have hfour' := mul_le_mul_of_nonneg_right hvle (sq_nonneg (b ^ 2))
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a * b), sq_nonneg (b ^ 2)]

-- @node: biasedLaw_E_split_coordinate
/-- If [the bias p lies strictly between zero and one](hyp:hp), then
[the expectation of g equals the expectation over all coordinates other than i
of p times g with coordinate i set to true plus one minus p times g with
coordinate i set to false](goal). -/
lemma biasedLaw_E_split_coordinate (p : ℝ) (hp : BiasInterior p) (i : J)
    (g : (J → Bool) → ℝ) :
    (biasedLaw J p).E g =
      (biasedLaw {j : J // j ≠ i} p).E (fun y =>
        p * g ((Equiv.piSplitAt i (fun _ : J => Bool)).symm (true, y)) +
        (1 - p) * g ((Equiv.piSplitAt i (fun _ : J => Bool)).symm (false, y))) := by
  classical
  rw [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
    biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩]
  simp only [FiniteDesign.E, bernoulliDesign, prodDesign_p]
  have hprod (x : J → Bool) :
      (∏ j : J, (coinDesign p hp.1.le hp.2.le).p (x j)) =
        (coinDesign p hp.1.le hp.2.le).p (x i) *
          ∏ j : {j : J // j ≠ i}, (coinDesign p hp.1.le hp.2.le).p (x j.val) :=
    Fintype.prod_eq_mul_prod_subtype_ne _ i
  simp_rw [hprod, mul_assoc]
  rw [← (Equiv.piSplitAt i (fun _ : J => Bool)).symm.sum_comp]
  have hne (j : {j : J // j ≠ i}) : (j : J) ≠ i := j.property
  simp only [Fintype.sum_prod_type, Equiv.piSplitAt_symm_apply,
    hne, ↓reduceDIte, Subtype.coe_eta]
  simp only [Fintype.sum_bool, coinDesign, Bool.cond_true, Bool.cond_false]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

-- @node: coordinate_decomposition
/-- If [the bias p lies strictly between zero and one](hyp:hp), then
[there are two real-valued functions a and b of the coordinates other than i
such that g is a plus b times the normalized i-th coordinate, and the squared
L² norm of g is the sum of the squared L² norms of a and b](goal). -/
lemma coordinate_decomposition (p : ℝ) (hp : BiasInterior p) (i : J) (g : (J → Bool) → ℝ) :
    -- @realizes a(coefficient function on the other coordinates)
    -- @realizes b(coefficient function on the other coordinates)
    ∃ a b : ({j : J // j ≠ i} → Bool) → ℝ,
      (∀ x, g x = a (fun j => x j.val) + b (fun j => x j.val) * coordChar p i x) ∧
      cubeNormTwo p g ^ 2 = cubeNormTwo p a ^ 2 + cubeNormTwo p b ^ 2 := by
  classical
  let e := Equiv.piSplitAt i (fun _ : J => Bool)
  let g₁ := fun y => g (e.symm (true, y))
  let g₀ := fun y => g (e.symm (false, y))
  let a := fun y => p * g₁ y + (1 - p) * g₀ y
  let b := fun y => biasScale p * (g₁ y - g₀ y)
  have hs : biasScale p ≠ 0 := (biasScale_pos_le_half p hp).1.ne'
  have hs2 : biasScale p ^ 2 = p * (1 - p) :=
    Real.sq_sqrt (mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le))
  refine ⟨a, b, ?_, ?_⟩
  · intro x
    have hx : e.symm (x i, fun j => x j.val) = x := e.symm_apply_apply x
    unfold a b g₁ g₀ coordChar
    cases hxi : x i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hx₀ : e.symm (false, fun j => x j.val) = x := by simpa [hxi] using hx
      rw [hx₀]
      field_simp
      <;> ring
    · simp only [↓reduceIte]
      have hx₁ : e.symm (true, fun j => x j.val) = x := by simpa [hxi] using hx
      rw [hx₁]
      field_simp
      <;> ring
  · unfold cubeNormTwo
    rw [Real.sq_sqrt ((biasedLaw J p).E_nonneg (fun x => sq_nonneg _)),
      Real.sq_sqrt ((biasedLaw {j : J // j ≠ i} p).E_nonneg (fun x => sq_nonneg _)),
      Real.sq_sqrt ((biasedLaw {j : J // j ≠ i} p).E_nonneg (fun x => sq_nonneg _))]
    rw [biasedLaw_E_split_coordinate p hp i, ← FiniteDesign.E_add]
    apply FiniteDesign.E_congr
    intro y
    change p * g₁ y ^ 2 + (1 - p) * g₀ y ^ 2 = a y ^ 2 + b y ^ 2
    dsimp [a, b]
    rw [mul_pow, hs2]
    ring

end Papers.OaiUniformInfluenceHypergraph
