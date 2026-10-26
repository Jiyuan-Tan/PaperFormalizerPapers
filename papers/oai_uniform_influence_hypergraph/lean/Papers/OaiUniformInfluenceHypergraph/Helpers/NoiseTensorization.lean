module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.NoiseBasics

/-! # Product induction for the fourth-moment noise estimate -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

variable {J : Type*} [Fintype J] [DecidableEq J]

-- @node: noiseOperator_eq_kernel
/-- [The noise operator with multiplier ρ applied to g at configuration x equals
the expectation over y of g at y times the product, over all coordinates, of one
plus ρ times the standardized coordinate at x times the standardized coordinate
at y](goal), where expectation uses the p-biased product law. -/
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
/-- Suppose [the Bernoulli bias p is strictly between zero and one](hyp:hp),
[a is a real function of all coordinates except i](hyp:a),
[b is another real function of those remaining coordinates](hyp:b), and
[g equals a plus b times the standardized coordinate i at every configuration](hyp:hg).
Then [the noise operator with multiplier ρ applied to g at x equals the same
operator applied to a on the remaining coordinates, plus ρ times that operator
applied to b on the remaining coordinates times the standardized coordinate i at x](goal). -/
lemma noiseOperator_coordinate_split (p ρ : ℝ) (hp : BiasInterior p) (i : J)
    (g : (J → Bool) → ℝ) (a b : ({j : J // j ≠ i} → Bool) → ℝ)
    (hg : ∀ x, g x = a (fun j => x j.val) + b (fun j => x j.val) * coordChar p i x)
    (x : J → Bool) :
    noiseOperator p ρ g x =
      noiseOperator p ρ a (fun j => x j.val) +
        ρ * noiseOperator p ρ b (fun j => x j.val) * coordChar p i x := by
  classical
  rw [noiseOperator_eq_kernel, biasedLaw_E_split_coordinate p hp i]
  have hs : biasScale p ≠ 0 := (biasScale_pos_le_half p hp).1.ne'
  have hs2 : biasScale p ^ 2 = p * (1 - p) :=
    Real.sq_sqrt (mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le))
  let e := Equiv.piSplitAt i (fun _ : J => Bool)
  have hrest (t : Bool) (y : {j : J // j ≠ i} → Bool) :
      (fun j : {j : J // j ≠ i} => (e.symm (t, y)) j.val) = y := by
    funext j
    simp [e, Equiv.piSplitAt_symm_apply, j.property]
  have hprod (t : Bool) (y : {j : J // j ≠ i} → Bool) :
      (∏ j : J, (1 + ρ * coordChar p j x * coordChar p j (e.symm (t, y)))) =
      (1 + ρ * coordChar p i x * (((if t then 1 else 0) - p) / biasScale p)) *
        ∏ j : {j : J // j ≠ i},
          (1 + ρ * coordChar p j (fun j => x j.val) * coordChar p j y) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp [coordChar, e, Equiv.piSplitAt_symm_apply,
      show ∀ j : {j : J // j ≠ i}, (j : J) ≠ i from fun j => j.property]
  change (biasedLaw {j : J // j ≠ i} p).E (fun y =>
    p * (g (e.symm (true, y)) * _) +
      (1-p) * (g (e.symm (false, y)) * _)) = _
  dsimp only [e] at hprod
  simp_rw [hg, hrest, hprod]
  have hcoord (t : Bool) (y : {j : J // j ≠ i} → Bool) :
      coordChar p i (e.symm (t, y)) = ((if t then 1 else 0) - p) / biasScale p := by
    simp [coordChar, e, Equiv.piSplitAt_symm_apply]
  simp_rw [hcoord]
  rw [noiseOperator_eq_kernel, noiseOperator_eq_kernel, ← FiniteDesign.E_const_mul,
    ← FiniteDesign.E_mul_const, ← FiniteDesign.E_add]
  apply FiniteDesign.E_congr
  intro y
  simp only [↓reduceIte, Bool.false_eq_true]
  field_simp
  linear_combination -(∏ j : {j : J // j ≠ i},
    (1 + ρ * coordChar p j (fun j => x j.val) * coordChar p j y)) *
      b y * ρ * coordChar p i x * hs2

-- @node: coordinate_fourthMoment_le
/-- Suppose [the Bernoulli bias p is strictly between zero and one](hyp:hp),
[a is a real function of all coordinates except i](hyp:a), and
[b is another real function of those remaining coordinates](hyp:b).
Then [the fourth moment of a plus the noise parameter times b times the standardized
coordinate i is at most the expectation of the square of the sum of a squared and
b squared over the remaining coordinates](goal), using the respective p-biased product laws. -/
lemma coordinate_fourthMoment_le (p : ℝ) (hp : BiasInterior p) (i : J)
    (a b : ({j : J // j ≠ i} → Bool) → ℝ) :
    (biasedLaw J p).E (fun x =>
      (a (fun j => x j.val) + noiseParameter p * b (fun j => x j.val) *
        coordChar p i x) ^ 4) ≤
      (biasedLaw {j : J // j ≠ i} p).E (fun y => (a y ^ 2 + b y ^ 2) ^ 2) := by
  have hone (c d : ℝ) :
      p * (c + noiseParameter p * d * ((1 - p) / biasScale p)) ^ 4 +
        (1 - p) * (c + noiseParameter p * d * ((0 - p) / biasScale p)) ^ 4 ≤
          (c ^ 2 + d ^ 2) ^ 2 := by
    have h := oneCoordinate_fourthMoment_le p hp c d
    simp only [coordChar] at h
    rw [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
      bernoulliDesign_E_eval _ _ _ ()
        (fun t => (c + noiseParameter p * d * (((if t then 1 else 0) - p) /
          biasScale p)) ^ 4), coinDesign_E] at h
    simpa using h
  rw [biasedLaw_E_split_coordinate p hp i]
  unfold FiniteDesign.E
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ ((biasedLaw {j : J // j ≠ i} p).p_nonneg y)
  simpa [coordChar, Equiv.piSplitAt_symm_apply,
    show ∀ j : {j : J // j ≠ i}, (j : J) ≠ i from fun j => j.property] using hone (a y) (b y)

-- @node: noiseOperator_fourthMoment_le
/-- If [the Bernoulli bias p is strictly between zero and one](hyp:hp), then
[the fourth moment of g after applying the noise operator at the noise parameter
is at most the square of the second moment of g](goal), under the p-biased product law. -/
lemma noiseOperator_fourthMoment_le (p : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) :
    (biasedLaw J p).E (fun x => noiseOperator p (noiseParameter p) g x ^ 4) ≤
      ((biasedLaw J p).E (fun x => g x ^ 2)) ^ 2 := by
  classical
  induction hn : Fintype.card J using Nat.strong_induction_on generalizing J with
  | h n ih =>
    by_cases he : IsEmpty J
    · letI := he
      have hg : g = fun _ => g (fun j => isEmptyElim j) := by
        funext x
        congr 1
        funext j
        exact isEmptyElim j
      rw [hg]
      simp [noiseOperator_eq_kernel, ← pow_mul]
    · obtain ⟨i⟩ := not_isEmpty_iff.mp he
      obtain ⟨a, b, hg, hnorm⟩ := coordinate_decomposition p hp i g
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
      unfold cubeNormTwo at hnorm
      rw [Real.sq_sqrt ((biasedLaw J p).E_nonneg (fun x => sq_nonneg _)),
        Real.sq_sqrt hA, Real.sq_sqrt hB] at hnorm
      calc
        _ ≤ D.E (fun y => (u y ^ 2 + v y ^ 2) ^ 2) := by
          simpa only [noiseOperator_coordinate_split p (noiseParameter p) hp i g a b hg]
            using coordinate_fourthMoment_le p hp i u v
        _ = D.E (fun y => u y ^ 4) + 2 * D.E (fun y => u y ^ 2 * v y ^ 2) +
            D.E (fun y => v y ^ 4) := by
          simp_rw [show ∀ y, (u y ^ 2 + v y ^ 2) ^ 2 =
            u y ^ 4 + 2 * (u y ^ 2 * v y ^ 2) + v y ^ 4 by intro y; ring,
            FiniteDesign.E_add, FiniteDesign.E_const_mul]
        _ ≤ _ := by rw [hnorm]; nlinarith [ha, hb, hcross]

-- @node: noiseOperator_norm_four_le_two
/-- If [the Bernoulli bias p is strictly between zero and one](hyp:hp), then
[the L⁴ norm of g after applying the noise operator at the noise parameter is at
most the L² norm of g](goal), with both norms taken under the p-biased product law. -/
lemma noiseOperator_norm_four_le_two (p : ℝ) (hp : BiasInterior p) (g : (J → Bool) → ℝ) :
    cubeNormFour p (noiseOperator p (noiseParameter p) g) ≤ cubeNormTwo p g := by
  have htwo := (biasedLaw J p).E_nonneg (fun x => sq_nonneg (g x))
  unfold cubeNormFour cubeNormTwo
  calc
    _ ≤ (((biasedLaw J p).E (fun x => g x ^ 2)) ^ 2) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow ((biasedLaw J p).E_nonneg (fun x => by positivity))
        (noiseOperator_fourthMoment_le p hp g) (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul htwo]
      norm_num
      exact (Real.sqrt_eq_rpow _).symm

end Papers.OaiUniformInfluenceHypergraph
