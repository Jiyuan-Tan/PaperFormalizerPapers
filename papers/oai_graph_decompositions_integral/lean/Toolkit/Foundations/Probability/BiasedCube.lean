module
public import Causalean.Experimentation.DesignBased.Designs.Bernoulli
public import Causalean.Experimentation.DesignBased.Designs.BernoulliMoments
public import Causalean.Experimentation.DesignBased.Designs.Coin
public import Causalean.Experimentation.DesignBased.ProductReindex
public import Causalean.Stat.FiniteDesign.DesignCore
public import Causalean.Stat.FiniteDesign.Product
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder

/-! # Independent biased bits and coordinate influences

Coordinate influence is the probability that forcing one bit to true rather than false
changes a Boolean function. The probability uses Causalean's finite Bernoulli product
design, so both endpoints are included and no measurability assumptions are needed.
For a total real parameter the bias is clamped to the closed unit interval; within that
interval the definition is exactly the independent Bernoulli pivotal probability.

A symmetry of a Boolean function preserves the influences of the coordinates it permutes.
The underlying change of variables is already available as
`FiniteDesign.prodDesign_Pr_reindex`; no separate cube-permutation infrastructure is needed.

Reference: O'Donnell, *Analysis of Boolean Functions* (2014), §§2.1–2.2,
for symmetry and pivotality. This module uses the pivotal-probability convention
for biased inputs, without a variance normalization factor.
-/

@[expose] public section

open Causalean.Experimentation.DesignBased

namespace Toolkit.Foundations.Probability

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The [influence](goal) of [a coordinate](hyp:i) on [a Boolean function](hyp:h)
over [a finite coordinate set](hyp:J) is the probability that forcing this bit to
true rather than false changes the function, when all coordinates are independent
Bernoulli draws with [the common bias clamped to the closed unit interval](hyp:p). -/
noncomputable def influence (p : ℝ) (h : (J → Bool) → Bool) (i : J) : ℝ :=
  (bernoulliDesign (fun _ : J => max 0 (min p 1))
    (fun _ => le_max_left _ _)
    (fun _ => max_le zero_le_one (min_le_right _ _))).Pr
      (fun x => h (Function.update x i true) ≠ h (Function.update x i false))

/-- For [a Boolean function](hyp:h), [a coordinate](hyp:i) and [a common bias](hyp:p)
that is [nonnegative](hyp:hp0) and [at most one](hyp:hp1), [the influence of the
coordinate equals the probability, under independent Bernoulli draws with that bias, that
switching the coordinate from false to true changes the function](goal). -/
theorem influence_eq_bernoulliDesign_Pr (p : ℝ) (h : (J → Bool) → Bool) (i : J)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    influence p h i =
      (bernoulliDesign (fun _ : J => p) (fun _ => hp0) (fun _ => hp1)).Pr
        (fun x => h (Function.update x i true) ≠ h (Function.update x i false)) := by
  simp only [influence, min_eq_left hp1, max_eq_right hp0]

/-- Symmetries of a Boolean function preserve coordinate influences: for
[a Boolean function](hyp:h) of independent bits with [any real bias parameter](hyp:p),
[a permutation of the coordinates](hyp:σ) such that [composing every input with the
permutation leaves the function unchanged](hyp:hh), and [any coordinate](hyp:i),
[the influence of that coordinate equals the influence of its image under the
permutation](goal).

The bias is clamped outside the unit interval, so the equality holds for every real
parameter and specializes directly to definitions using that convention.
-/
theorem influence_eq_influence_apply_of_comp_perm_eq
    (p : ℝ) (h : (J → Bool) → Bool) (σ : Equiv.Perm J)
    (hh : ∀ x : J → Bool, h (fun j => x (σ j)) = h x) (i : J) :
    influence p h i = influence p h (σ i) := by
  classical
  unfold influence bernoulliDesign
  have hreindex := FiniteDesign.prodDesign_Pr_reindex σ
    (fun _ : J => coinDesign (max 0 (min p 1))
      (le_max_left _ _) (max_le zero_le_one (min_le_right _ _)))
    (fun x => h (Function.update x i true) ≠ h (Function.update x i false))
  refine hreindex.symm.trans ?_
  apply FiniteDesign.Pr_congr
  intro x
  have hupdate (b : Bool) :
      h (Function.update (fun j => x (σ j)) i b) =
        h (Function.update x (σ i) b) := by
    have heq := Function.update_comp_equiv x σ (σ i) b
    simp only [Equiv.symm_apply_apply] at heq
    change h (Function.update (x ∘ σ) i b) = _
    rw [← heq]
    exact hh (Function.update x (σ i) b)
  rw [hupdate true, hupdate false]

/-! ## Fourier analysis on the biased cube

The cube law below is the same clamped independent Bernoulli design used by `influence`.
Characters take zero-or-one inputs, centered at the bias and divided by the square root of
its Bernoulli variance; coefficients are defined for arbitrary real statistics, so the
expansion, orthonormality and Parseval identities also apply to coordinate differences.
For a Boolean function, the spectral energy on subsets containing a coordinate is
`p(1-p)` times that coordinate's influence; summing over coordinates weights each squared
coefficient by its subset size, and the variance is the energy on nonempty subsets.
The unnormalized centered-monomial theory is Causalean's.

Reference: O'Donnell, *Analysis of Boolean Functions* (2014), §8.4. The reference uses a
sign encoding; here both inputs and Boolean output indicators use the zero-or-one encoding,
and influence is the pivotal probability, so the multiplier is `p(1-p)` with no factor four.
-/

/-- On [a finite set of coordinates](hyp:J), the [Bernoulli cube law](goal)
draws independent bits with [common success probability clamped to the closed
unit interval](hyp:p). -/
noncomputable def bernoulliCube (J : Type*) [Fintype J] [DecidableEq J]
    (p : ℝ) : FiniteDesign (J → Bool) :=
  bernoulliDesign (fun _ => max 0 (min p 1))
    (fun _ => le_max_left _ _)
    (fun _ => max_le zero_le_one (min_le_right _ _))

/-- For [a success probability](hyp:p) that is [nonnegative](hyp:hp0)
and [at most one](hyp:hp1), [the clamped cube law equals the independent
Bernoulli design with that probability](goal). -/
theorem bernoulliCube_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliCube J p =
      bernoulliDesign (fun _ : J => p) (fun _ => hp0) (fun _ => hp1) := by
  simp only [bernoulliCube, min_eq_left hp1, max_eq_right hp0]

/-- For [a bias](hyp:p), [a finite coordinate subset](hyp:S), and
[an assignment of bits](hyp:x) on [the coordinate set](hyp:J), the
[normalized cube character](goal) is the product over that subset of each
zero-or-one bit minus the bias, divided by the square root of the Bernoulli variance. -/
noncomputable def cubeCharacter (p : ℝ) (S : Finset J) (x : J → Bool) : ℝ :=
  ∏ j ∈ S, (((if x j then 1 else 0) - p) / Real.sqrt (p * (1 - p)))

/-- For [a bias](hyp:p), [a real statistic of the bits](hyp:f) on
[a finite coordinate set](hyp:J), and [a coordinate subset](hyp:S), the
[cube Fourier coefficient](goal) is the expectation of the statistic times
the normalized character under the independent Bernoulli cube law. -/
noncomputable def cubeFourierCoeff (p : ℝ) (f : (J → Bool) → ℝ)
    (S : Finset J) : ℝ :=
  (bernoulliCube J p).E (fun x => f x * cubeCharacter p S x)

/-- For [a real statistic of bits](hyp:f), [a coordinate](hyp:i), and
[an assignment](hyp:x) on [a finite coordinate set](hyp:J), the
[coordinate difference](goal) is the statistic with that bit forced true
minus the statistic with that bit forced false. -/
def coordinateDifference (f : (J → Bool) → ℝ) (i : J) (x : J → Bool) : ℝ :=
  f (Function.update x i true) - f (Function.update x i false)

/-- If [the bias](hyp:p) is [strictly positive](hyp:hp0) and
[strictly less than one](hyp:hp1), [the square root of its Bernoulli variance
is strictly positive](goal). -/
theorem sqrt_bernoulliVariance_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < Real.sqrt (p * (1 - p)) :=
  Real.sqrt_pos_of_pos (mul_pos hp0 (sub_pos.mpr hp1))

/-- If [the bias](hyp:p) is [nonnegative](hyp:hp0) and
[at most one](hyp:hp1), [squaring the square root of its Bernoulli variance
recovers p times one minus p](goal). -/
theorem sq_sqrt_bernoulliVariance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) :=
  Real.sq_sqrt (mul_nonneg hp0 (sub_nonneg.mpr hp1))

omit [Fintype J] [DecidableEq J] in
/-- For [a bias](hyp:p), [a coordinate subset](hyp:S), and
[an assignment](hyp:x), [the normalized character equals the
centered monomial of the subset divided by the normalization scale raised to the
subset size](goal). -/
theorem cubeCharacter_eq_centeredMonomial_div (p : ℝ) (S : Finset J)
    (x : J → Bool) :
    cubeCharacter p S x = centeredMonomial (fun _ : J => p) S x /
      Real.sqrt (p * (1 - p)) ^ S.card := by
  simp only [cubeCharacter, centeredMonomial, treatInd, Finset.prod_div_distrib,
    Finset.prod_const]

omit [Fintype J] [DecidableEq J] in
/-- For [a bias](hyp:p) and [an assignment](hyp:x), [the character of
the empty coordinate subset is one](goal). -/
@[simp] theorem cubeCharacter_empty (p : ℝ) (x : J → Bool) :
    cubeCharacter p (∅ : Finset J) x = 1 := by
  simp [cubeCharacter]

/-- For [a bias](hyp:p) and [a real statistic](hyp:f), [the Fourier
coefficient of the empty coordinate subset is the statistic's expectation](goal). -/
@[simp] theorem cubeFourierCoeff_empty (p : ℝ) (f : (J → Bool) → ℝ) :
    cubeFourierCoeff p f ∅ = (bernoulliCube J p).E f := by
  simp [cubeFourierCoeff]

/-- For [a bias](hyp:p) that is [strictly positive and less than one](hyp:hp0,hp1)
and [two coordinate subsets](hyp:S,T), [the expected product of their normalized
characters is one when the subsets agree and zero otherwise](goal). -/
theorem cubeCharacter_orthonormal (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (S T : Finset J) :
    (bernoulliCube J p).E (fun x => cubeCharacter p S x * cubeCharacter p T x) =
      if S = T then 1 else 0 := by
  -- Rewrite characters using cubeCharacter_eq_centeredMonomial_div, pull the
  -- constant denominator out of E, and use bernoulliDesign_E_centeredMonomial_mul.
  -- The diagonal denominator is nonzero by sqrt_bernoulliVariance_pos, and
  -- sq_sqrt_bernoulliVariance identifies the diagonal numerator with its square.
  have hr : Real.sqrt (p * (1 - p)) ≠ 0 :=
    (sqrt_bernoulliVariance_pos p hp0 hp1).ne'
  simp_rw [cubeCharacter_eq_centeredMonomial_div, div_mul_div_comm,
    div_eq_mul_inv]
  rw [FiniteDesign.E_mul_const, bernoulliCube_eq p hp0.le hp1.le,
    bernoulliDesign_E_centeredMonomial_mul]
  by_cases h : S = T
  · subst T
    simp only [ite_true, Finset.prod_const]
    have hscale : (p * (1 - p)) ^ S.card =
        Real.sqrt (p * (1 - p)) ^ S.card * Real.sqrt (p * (1 - p)) ^ S.card := by
      rw [← mul_pow, ← pow_two, sq_sqrt_bernoulliVariance p hp0.le hp1.le]
    rw [hscale]
    exact mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hr))
  · simp [h]

/-- For [a bias](hyp:p) that is [strictly positive and less than one](hyp:hp0,hp1),
[a real statistic](hyp:f), and [any assignment](hyp:x), [the statistic equals
the sum of its Fourier coefficients times the corresponding characters](goal). -/
theorem cube_fourier_expansion (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : (J → Bool) → ℝ) (x : J → Bool) :
    f x = ∑ S : Finset J, cubeFourierCoeff p f S * cubeCharacter p S x := by
  -- Obtain exists_centeredMonomial_expansion at the constant probability p.
  -- Replace each coefficient a S by a S * sqrt(p*(1-p))^S.card to obtain
  -- a normalized expansion. Pair with each character using orthonormality
  -- to identify those coefficients with cubeFourierCoeff. The powerset of
  -- univ in the existing expansion is all of Finset J (simp).
  obtain ⟨a, ha⟩ := exists_centeredMonomial_expansion (fun _ : J => p) f
  have hr : Real.sqrt (p * (1 - p)) ≠ 0 :=
    (sqrt_bernoulliVariance_pos p hp0 hp1).ne'
  let b : Finset J → ℝ := fun S => a S * Real.sqrt (p * (1 - p)) ^ S.card
  have hb (z : J → Bool) : f z = ∑ S : Finset J, b S * cubeCharacter p S z := by
    rw [ha z]
    simp only [Finset.powerset_univ]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [cubeCharacter_eq_centeredMonomial_div]
    dsimp [b]
    field_simp
  have hcoef (T : Finset J) : cubeFourierCoeff p f T = b T := by
    unfold cubeFourierCoeff
    rw [show (fun z => f z * cubeCharacter p T z) =
        (fun z => ∑ S : Finset J, b S *
          (cubeCharacter p S z * cubeCharacter p T z)) by
      funext z
      rw [hb z, Finset.sum_mul]
      exact Finset.sum_congr rfl fun S _ => by ring]
    rw [FiniteDesign.E_sum]
    simp_rw [FiniteDesign.E_const_mul, cubeCharacter_orthonormal p hp0 hp1]
    simp
  simpa only [hcoef] using hb x

/-- For [a bias](hyp:p) that is [strictly positive and less than one](hyp:hp0,hp1)
and [a real statistic](hyp:f), [its second moment equals the sum of all squared
Fourier coefficients](goal). -/
theorem cube_secondMoment_eq_sum_sq (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : (J → Bool) → ℝ) :
    (bernoulliCube J p).E (fun x => f x ^ 2) =
      ∑ S : Finset J, cubeFourierCoeff p f S ^ 2 := by
  -- Use bernoulliDesign_E_sq_of_expansion on cube_fourier_expansion after
  -- replacing characters by centered monomials divided by their scale.
  have hr : Real.sqrt (p * (1 - p)) ≠ 0 :=
    (sqrt_bernoulliVariance_pos p hp0 hp1).ne'
  have ha (z : J → Bool) : f z =
      ∑ S ∈ (Finset.univ : Finset J).powerset,
        (cubeFourierCoeff p f S / Real.sqrt (p * (1 - p)) ^ S.card) *
          centeredMonomial (fun _ : J => p) S z := by
    rw [cube_fourier_expansion p hp0 hp1 f z]
    simp only [Finset.powerset_univ]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [cubeCharacter_eq_centeredMonomial_div]
    ring
  rw [bernoulliCube_eq p hp0.le hp1.le,
    bernoulliDesign_E_sq_of_expansion _ _ _ f _ ha]
  simp only [Finset.powerset_univ, Finset.prod_const]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hscale : (p * (1 - p)) ^ S.card =
      (Real.sqrt (p * (1 - p)) ^ S.card) ^ 2 := by
    calc
      _ = (Real.sqrt (p * (1 - p)) ^ 2) ^ S.card :=
        congrArg (fun r : ℝ => r ^ S.card)
          (sq_sqrt_bernoulliVariance p hp0.le hp1.le).symm
      _ = _ := pow_right_comm _ _ _
  rw [hscale, div_pow]
  exact div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hr))

/-- For [a bias](hyp:p) that is [strictly positive and less than one](hyp:hp0,hp1)
and [a real statistic](hyp:f), [its variance equals the sum of squared Fourier
coefficients over nonempty coordinate subsets](goal). -/
theorem cube_variance_eq_sum_sq_nonempty (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : (J → Bool) → ℝ) :
    (bernoulliCube J p).Var f =
      ∑ S ∈ (Finset.univ : Finset (Finset J)).filter (fun S => S ≠ ∅),
        cubeFourierCoeff p f S ^ 2 := by
  -- FiniteDesign.Var_eq and Parseval reduce the claim to removing the empty
  -- coefficient, which cubeFourierCoeff_empty identifies with the mean.
  rw [FiniteDesign.Var_eq, cube_secondMoment_eq_sum_sq p hp0 hp1]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset J)) (fun S => S = ∅)
    (fun S => cubeFourierCoeff p f S ^ 2)
  simp only [Finset.filter_eq', Finset.mem_univ, if_true,
    Finset.sum_singleton, cubeFourierCoeff_empty] at hsplit
  linarith

omit [Fintype J] in
/-- For [a bias](hyp:p), [a coordinate subset](hyp:S), [a coordinate](hyp:i),
and [an assignment](hyp:x), [the coordinate difference of the subset character
is zero if the coordinate is absent, and otherwise equals the character with
that coordinate removed divided by the Bernoulli standard deviation](goal). -/
theorem coordinateDifference_cubeCharacter (p : ℝ) (S : Finset J) (i : J)
    (x : J → Bool) :
    coordinateDifference (cubeCharacter p S) i x =
      if i ∈ S then cubeCharacter p (S.erase i) x / Real.sqrt (p * (1 - p))
      else 0 := by
  have update_eq (T : Finset J) (hi : i ∉ T) (b : Bool) :
      cubeCharacter p T (Function.update x i b) = cubeCharacter p T x := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by
      intro h
      exact hi (h ▸ hj)
    simp only [Function.update_of_ne hji]
  by_cases hi : i ∈ S
  · have factor (b : Bool) :
        cubeCharacter p S (Function.update x i b) =
          (((if b then 1 else 0) - p) / Real.sqrt (p * (1 - p))) *
            cubeCharacter p (S.erase i) x := by
      unfold cubeCharacter
      rw [← Finset.mul_prod_erase S _ hi]
      change _ * cubeCharacter p (S.erase i) (Function.update x i b) = _
      rw [update_eq _ (by simp) b]
      simp only [Function.update_self]
      rfl
    rw [if_pos hi]
    unfold coordinateDifference
    rw [factor true, factor false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  · rw [if_neg hi]
    unfold coordinateDifference
    rw [update_eq S hi true, update_eq S hi false, sub_self]

omit [Fintype J] in
/-- For [a Boolean function](hyp:f), [a coordinate](hyp:i), and
[an assignment](hyp:x), [the squared difference of its zero-or-one values
equals one exactly when forcing the coordinate changes the output, and zero
otherwise](goal). -/
theorem coordinateDifference_bool_sq (f : (J → Bool) → Bool) (i : J)
    (x : J → Bool) :
    coordinateDifference (fun y => if f y then (1 : ℝ) else 0) i x ^ 2 =
      if f (Function.update x i true) ≠ f (Function.update x i false) then 1 else 0 := by
  cases ht : f (Function.update x i true) <;>
    cases hf : f (Function.update x i false) <;>
    simp [coordinateDifference, ht, hf]

/-- For [any real bias](hyp:p), [a Boolean function](hyp:f), and
[a coordinate](hyp:i), [the second moment of its zero-or-one coordinate
difference equals the pivotal influence of that coordinate](goal). -/
theorem cube_secondMoment_difference_bool (p : ℝ) (f : (J → Bool) → Bool) (i : J) :
    (bernoulliCube J p).E
        (fun x => coordinateDifference (fun y => if f y then (1 : ℝ) else 0) i x ^ 2) =
      influence p f i := by
  change (bernoulliCube J p).E _ = (bernoulliCube J p).Pr _
  unfold FiniteDesign.Pr FiniteDesign.ind
  exact FiniteDesign.E_congr _ (coordinateDifference_bool_sq f i)

/-- For [real weights on subsets of a finite coordinate set](hyp:a), [the sum
of each subset's weight times its cardinality equals the sum, over coordinates,
of the weights of subsets containing that coordinate](goal). -/
theorem sum_card_mul_eq_sum_mem (a : Finset J → ℝ) :
    (∑ S : Finset J, (S.card : ℝ) * a S) =
      ∑ i : J, ∑ S ∈ (Finset.univ : Finset (Finset J)).filter (fun S => i ∈ S), a S := by
  calc
    (∑ S : Finset J, (S.card : ℝ) * a S) =
        ∑ S : Finset J, ∑ i : J, if i ∈ S then a S else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      simp
    _ = ∑ i : J, ∑ S : Finset J, if i ∈ S then a S else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [Finset.sum_filter]

/-- For [a bias](hyp:p) that is [strictly positive and less than one](hyp:hp0,hp1),
[a real statistic](hyp:f), [a coordinate](hyp:i), and [a coordinate subset](hyp:S),
[the Fourier coefficient of the coordinate difference is zero on subsets
containing that coordinate and otherwise is the coefficient of the original
statistic on the subset with that coordinate inserted, divided by the
Bernoulli standard deviation](goal). -/
theorem cubeFourierCoeff_coordinateDifference (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : (J → Bool) → ℝ) (i : J) (S : Finset J) :
    cubeFourierCoeff p (coordinateDifference f i) S =
      if i ∈ S then 0 else
        cubeFourierCoeff p f (insert i S) / Real.sqrt (p * (1 - p)) := by
  -- Apply coordinateDifference to cube_fourier_expansion pointwise; distribute
  -- through the finite sum and use coordinateDifference_cubeCharacter.
  -- Pair with the S character and apply cubeCharacter_orthonormal. A summand
  -- indexed by T survives exactly when i ∈ T and T.erase i = S; if i ∉ S its
  -- unique index is insert i S, so Finset.sum_eq_single avoids reindexing.
  classical
  have hd (x : J → Bool) : coordinateDifference f i x =
      ∑ T : Finset J, if i ∈ T then
        (cubeFourierCoeff p f T / Real.sqrt (p * (1 - p))) *
          cubeCharacter p (T.erase i) x else 0 := by
    unfold coordinateDifference
    rw [cube_fourier_expansion p hp0 hp1 f (Function.update x i true),
      cube_fourier_expansion p hp0 hp1 f (Function.update x i false),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← mul_sub]
    change cubeFourierCoeff p f T * coordinateDifference (cubeCharacter p T) i x = _
    rw [coordinateDifference_cubeCharacter]
    split_ifs <;> ring
  unfold cubeFourierCoeff
  rw [show (fun x => coordinateDifference f i x * cubeCharacter p S x) =
      (fun x => ∑ T : Finset J, if i ∈ T then
        (cubeFourierCoeff p f T / Real.sqrt (p * (1 - p))) *
          (cubeCharacter p (T.erase i) x * cubeCharacter p S x) else 0) by
    funext x
    rw [hd x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs <;> ring]
  rw [FiniteDesign.E_sum]
  trans ∑ T : Finset J, if i ∈ T then
    (cubeFourierCoeff p f T / Real.sqrt (p * (1 - p))) *
      (if T.erase i = S then 1 else 0) else 0
  · apply Finset.sum_congr rfl
    intro T _
    by_cases hit : i ∈ T
    · simp only [if_pos hit, FiniteDesign.E_const_mul,
        cubeCharacter_orthonormal p hp0 hp1]
    · simp [hit]
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    apply Finset.sum_eq_zero
    intro T _
    have hne : T.erase i ≠ S := by
      intro h
      have hm : i ∈ T.erase i := h.symm ▸ hi
      simp at hm
    simp [hne]
  · rw [if_neg hi]
    rw [Finset.sum_eq_single (insert i S)]
    · simp [Finset.erase_insert hi, cubeFourierCoeff]
    · intro T _ hT
      by_cases hit : i ∈ T
      · have hne : T.erase i ≠ S := by
          intro h
          apply hT
          rw [← h, Finset.insert_erase hit]
        simp [hit, hne]
      · simp [hit]
    · simp

/-- For [a bias](hyp:p) that is [strictly positive and less than one](hyp:hp0,hp1),
[a real statistic](hyp:f), and [a coordinate](hyp:i), [the sum of squared Fourier
coefficients over subsets containing that coordinate equals p times one minus p
times the second moment of its coordinate difference](goal). -/
theorem sum_sq_cubeFourierCoeff_of_mem_eq_mul_secondMoment_difference
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : (J → Bool) → ℝ) (i : J) :
    (∑ S ∈ (Finset.univ : Finset (Finset J)).filter (fun S => i ∈ S),
      cubeFourierCoeff p f S ^ 2) =
      p * (1 - p) * (bernoulliCube J p).E (fun x => coordinateDifference f i x ^ 2) := by
  -- Apply Parseval to the coordinate difference, substitute
  -- cubeFourierCoeff_coordinateDifference, and reindex by insert i / erase i.
  classical
  have hr : Real.sqrt (p * (1 - p)) ≠ 0 :=
    (sqrt_bernoulliVariance_pos p hp0 hp1).ne'
  rw [cube_secondMoment_eq_sum_sq p hp0 hp1, Finset.mul_sum]
  symm
  calc
    (∑ S : Finset J, p * (1 - p) *
        cubeFourierCoeff p (coordinateDifference f i) S ^ 2) =
        ∑ S ∈ (Finset.univ : Finset (Finset J)).filter (fun S => i ∉ S),
          cubeFourierCoeff p f (insert i S) ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      rw [cubeFourierCoeff_coordinateDifference p hp0 hp1]
      by_cases hi : i ∈ S
      · simp [hi]
      · simp only [hi, if_false, not_false_eq_true, if_true]
        rw [div_pow]
        field_simp
        rw [sq_sqrt_bernoulliVariance p hp0.le hp1.le]
        ring
    _ = ∑ S ∈ (Finset.univ : Finset (Finset J)).filter (fun S => i ∈ S),
          cubeFourierCoeff p f S ^ 2 := by
      refine Finset.sum_bij (fun S _ => insert i S) ?_ ?_ ?_ ?_
      · intro S _
        simp
      · intro S hS T hT h
        have hS' : i ∉ S := (Finset.mem_filter.mp hS).2
        have hT' : i ∉ T := (Finset.mem_filter.mp hT).2
        simpa [Finset.erase_insert hS', Finset.erase_insert hT'] using
          congrArg (fun U : Finset J => U.erase i) h
      · intro T hT
        refine ⟨T.erase i, by simp, ?_⟩
        exact Finset.insert_erase (Finset.mem_filter.mp hT).2
      · intro S _
        rfl

/-- **Fourier formula for influence on the biased cube.** For
[a Boolean function on a finite cube](hyp:f), [a bias](hyp:p) that is
[strictly positive and less than one](hyp:hp0,hp1), and [any coordinate](hyp:i),
[the sum of squared Fourier coefficients over subsets containing that coordinate
equals p times one minus p times the probability that forcing the coordinate
from zero to one changes the function](goal).

The coefficient uses the zero-or-one output indicator, and influence uses the
pivotal-probability convention. Thus the multiplier is the square of the
Bernoulli standard deviation, with no extra factor of four.
-/
theorem sum_sq_fourierCoeff_of_mem_eq_mul_influence
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : (J → Bool) → Bool) (i : J) :
    (∑ S ∈ (Finset.univ : Finset (Finset J)).filter (fun S => i ∈ S),
      cubeFourierCoeff p (fun x => if f x then (1 : ℝ) else 0) S ^ 2) =
      p * (1 - p) * influence p f i := by
  rw [sum_sq_cubeFourierCoeff_of_mem_eq_mul_secondMoment_difference p hp0 hp1,
    cube_secondMoment_difference_bool]

/-- For [a Boolean function](hyp:f) and [a bias](hyp:p) that is
[strictly positive and less than one](hyp:hp0,hp1), [the sum of each squared
Fourier coefficient times its subset size equals p times one minus p times
the sum of pivotal coordinate influences](goal). -/
theorem sum_card_mul_sq_fourierCoeff_eq_mul_sum_influence
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : (J → Bool) → Bool) :
    (∑ S : Finset J, (S.card : ℝ) *
      cubeFourierCoeff p (fun x => if f x then (1 : ℝ) else 0) S ^ 2) =
      p * (1 - p) * ∑ i : J, influence p f i := by
  rw [sum_card_mul_eq_sum_mem]
  simp_rw [sum_sq_fourierCoeff_of_mem_eq_mul_influence p hp0 hp1]
  rw [Finset.mul_sum]

/-- High-degree Fourier weight is bounded by total influence: for
[a Boolean function](hyp:f) on [a finite cube](hyp:J), [a bias](hyp:p) that is
[strictly between zero and one](hyp:hp0,hp1), and [a degree cutoff](hyp:L)
that is [strictly positive](hyp:hL), [the sum of squared biased Fourier
coefficients of the function's zero-or-one indicator over subsets larger than
the cutoff is at most p times one minus p divided by the cutoff, multiplied
by the sum of pivotal coordinate influences](goal).

This is O'Donnell, *Analysis of Boolean Functions* (2014), Proposition 3.2, in
the biased normalization of §8.4. The cutoff may be any positive real number.
The proof bounds the cutoff times each tail coefficient's square by its
degree-weighted square, adds the nonnegative terms outside the tail, and applies
the total-influence identity.
-/
theorem sum_card_gt_sq_cubeFourierCoeff_le_mul_sum_influence
    (p L : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hL : 0 < L)
    (f : (J → Bool) → Bool) :
    (∑ S ∈ (Finset.univ : Finset (Finset J)).filter (fun S => L < (S.card : ℝ)),
      cubeFourierCoeff p (fun x => if f x then (1 : ℝ) else 0) S ^ 2) ≤
      (p * (1 - p) / L) * ∑ i : J, influence p f i := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hL, mul_comm _ L, Finset.mul_sum]
  calc
    (∑ S ∈ (Finset.univ : Finset (Finset J)).filter (fun S => L < (S.card : ℝ)),
        L * cubeFourierCoeff p (fun x => if f x then (1 : ℝ) else 0) S ^ 2) ≤
        ∑ S ∈ (Finset.univ : Finset (Finset J)).filter (fun S => L < (S.card : ℝ)),
          (S.card : ℝ) *
            cubeFourierCoeff p (fun x => if f x then (1 : ℝ) else 0) S ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hS).2.le (sq_nonneg _)
    _ ≤ ∑ S : Finset J, (S.card : ℝ) *
          cubeFourierCoeff p (fun x => if f x then (1 : ℝ) else 0) S ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro S _ _
      exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    _ = p * (1 - p) * ∑ i : J, influence p f i :=
      sum_card_mul_sq_fourierCoeff_eq_mul_sum_influence p hp0 hp1 f




end Toolkit.Foundations.Probability
