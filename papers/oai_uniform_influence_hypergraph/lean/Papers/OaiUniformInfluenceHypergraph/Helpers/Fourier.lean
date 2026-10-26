module
public import Papers.OaiUniformInfluenceHypergraph.Basic

/-! # Normalization bridges and Fourier identities

These obligations use Causalean's `centeredMonomial`, its orthogonality,
`exists_centeredMonomial_expansion`, and `bernoulliDesign_E_sq_of_expansion`.
The two identities in the paper's Parseval node are explicit lemmas here.
-/

@[expose] public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

variable {J : Type*} [Fintype J] [DecidableEq J]

-- @node: biasedLaw_eq_bernoulliDesign
/-- If [the bias lies between zero and one, including the endpoints](hyp:hp), then
[the biased configuration law equals the independent Bernoulli design with that
same success probability at every coordinate](goal). -/
lemma biasedLaw_eq_bernoulliDesign (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    biasedLaw J p = bernoulliDesign (fun _ : J => p) (fun _ => hp.1) (fun _ => hp.2) := by
  have hc : max 0 (min p 1) = p := by
    rw [min_eq_left hp.2, max_eq_right hp.1]
  unfold biasedLaw
  simp only [hc]

-- @node: biasScale_pos_le_half
/-- If [the bias is strictly between zero and one](hyp:hp), then [the square root
of the Bernoulli variance is positive and at most one half](goal). -/
lemma biasScale_pos_le_half (p : ℝ) (hp : BiasInterior p) :
    0 < biasScale p ∧ biasScale p ≤ 1 / 2 := by
  have hpos : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  constructor
  · exact Real.sqrt_pos.mpr hpos
  · have hs := Real.sq_sqrt hpos.le
    have hn := Real.sqrt_nonneg (p * (1 - p))
    unfold biasScale
    nlinarith [sq_nonneg (p - 1 / 2)]

-- @node: captureExponent_bounds
/-- If [the edge size r is at least three](hyp:hr), then [the capture exponent
r/(r − 1) is greater than one and at most three halves](goal). -/
lemma captureExponent_bounds (r : ℕ) (hr : MainUniformity r) :
    1 < captureExponent r ∧ captureExponent r ≤ 3 / 2 := by
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hd : 0 < (r : ℝ) - 1 := by linarith
  unfold captureExponent
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith
  · apply (div_le_iff₀ hd).mpr
    linarith

-- @node: supportCutoff_pos
/-- If [the edge size r is at least three](hyp:hr) and [the capture cutoff k is
positive](hyp:hk), then [the support cutoff (k/r) raised to the capture exponent
is positive](goal). -/
lemma supportCutoff_pos (r : ℕ) (hr : MainUniformity r) (k : ℝ)
    (hk : CapturePositiveCutoff k) : 0 < supportCutoff r k := by
  have hr' : (0 : ℝ) < r := by
    have : 3 ≤ r := hr
    exact_mod_cast (show 0 < r by omega)
  exact Real.rpow_pos_of_pos (div_pos hk hr') _

-- @node: lowCutoff_pos
/-- If [the bias is strictly between zero and one](hyp:hp) and [m is at least
two](hyp:hm), then [the low-degree cutoff, the square root of the Bernoulli
variance times the natural logarithm of m divided by 64, is positive](goal). -/
lemma lowCutoff_pos (p m : ℝ) (hp : BiasInterior p) (hm : LowDegreeParam m) :
    0 < lowCutoff p m := by
  exact div_pos (mul_pos (biasScale_pos_le_half p hp).1
    (Real.log_pos (by have : 2 ≤ m := hm; linarith))) (by norm_num)

omit [Fintype J] [DecidableEq J] in
-- @node: fourierChar_eq_centeredMonomial_div
/-- [The Fourier basis function for a coordinate set A at a configuration x equals
the product of its centered coordinates divided by the bias scale raised to the
number of coordinates in A](goal). -/
lemma fourierChar_eq_centeredMonomial_div (p : ℝ) (A : Finset J) (x : J → Bool) :
    fourierChar p A x = centeredMonomial (fun _ : J => p) A x / biasScale p ^ A.card := by
  simp only [fourierChar, coordChar, centeredMonomial, Finset.prod_div_distrib,
    Finset.prod_const]
  rfl

/-- If [the bias is strictly between zero and one](hyp:hp) and [the real-valued
function g is, at every configuration, the sum of centered coordinate monomials
with coefficients a](hyp:ha), then [its Fourier coefficient at A equals a's
coefficient at A times the bias scale raised to the size of A](goal). -/
-- @node: fourierCoeffR_of_centeredMonomial_expansion
lemma fourierCoeffR_of_centeredMonomial_expansion (p : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) (a : Finset J → ℝ)
    (ha : ∀ x, g x = ∑ A ∈ (Finset.univ : Finset J).powerset,
      a A * centeredMonomial (fun _ : J => p) A x) (A : Finset J) :
    fourierCoeffR p g A = a A * biasScale p ^ A.card := by
  have hs : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  have hs2 : p * (1 - p) = biasScale p ^ 2 :=
    (Real.sq_sqrt (mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le))).symm
  have hpair : (biasedLaw J p).E
      (fun x => g x * centeredMonomial (fun _ : J => p) A x) =
      a A * (p * (1 - p)) ^ A.card := by
    calc
      _ = (biasedLaw J p).E (fun x => ∑ B ∈ (Finset.univ : Finset J).powerset,
          a B * (centeredMonomial (fun _ : J => p) B x *
            centeredMonomial (fun _ : J => p) A x)) := by
        apply FiniteDesign.E_congr
        intro x
        rw [ha x, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro B _
        ring
      _ = _ := by
        rw [FiniteDesign.E_sum, biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩]
        simp_rw [FiniteDesign.E_const_mul, bernoulliDesign_E_centeredMonomial_mul]
        simp
  unfold fourierCoeffR
  simp_rw [fourierChar_eq_centeredMonomial_div, ← mul_div_assoc, div_eq_mul_inv]
  rw [FiniteDesign.E_mul_const, hpair, hs2]
  rw [← pow_mul, Nat.mul_comm 2 A.card, pow_mul]
  field_simp

-- @node: fourierChar_orthonormal
/-- If [the bias is strictly between zero and one](hyp:hp), then [the expected
product of two Fourier basis functions is one when their coordinate sets agree
and zero otherwise](goal). -/
lemma fourierChar_orthonormal (p : ℝ) (hp : BiasInterior p) (A B : Finset J) :
    (biasedLaw J p).E (fun x => fourierChar p A x * fourierChar p B x) =
      if A = B then 1 else 0 := by
  have hs : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  have hs2 : p * (1 - p) = biasScale p ^ 2 :=
    (Real.sq_sqrt (mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le))).symm
  simp_rw [fourierChar_eq_centeredMonomial_div, div_mul_div_comm, div_eq_mul_inv]
  rw [FiniteDesign.E_mul_const, biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
    bernoulliDesign_E_centeredMonomial_mul]
  by_cases hAB : A = B
  · subst B
    simp only [if_pos rfl, Finset.prod_const, hs2]
    rw [← pow_mul, Nat.mul_comm 2 A.card, pow_mul]
    simp [← pow_two, pow_ne_zero _ hs]
  · simp [hAB]

-- @node: fourier_expansion
/-- If [the bias is strictly between zero and one](hyp:hp), then [a real-valued
function at any configuration equals the sum over all coordinate subsets of its
Fourier coefficient times the corresponding basis function at that configuration](goal). -/
lemma fourier_expansion (p : ℝ) (hp : BiasInterior p) (g : (J → Bool) → ℝ) (x : J → Bool) :
    g x = ∑ A : Finset J, fourierCoeffR p g A * fourierChar p A x := by
  obtain ⟨a, ha⟩ := exists_centeredMonomial_expansion (fun _ : J => p) g
  have hs : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  rw [ha x]
  simp_rw [fourierCoeffR_of_centeredMonomial_expansion p hp g a ha,
    fourierChar_eq_centeredMonomial_div]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro A _
  field_simp

-- @node: secondMoment_eq_sum_fourierCoeffR_sq
/-- If [the bias is strictly between zero and one](hyp:hp), then [the second
moment of a real-valued function under the independent biased law equals the sum
of its squared Fourier coefficients over all coordinate subsets](goal). -/
lemma secondMoment_eq_sum_fourierCoeffR_sq (p : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) :
    (biasedLaw J p).E (fun x => g x ^ 2) = ∑ A : Finset J, fourierCoeffR p g A ^ 2 := by
  obtain ⟨a, ha⟩ := exists_centeredMonomial_expansion (fun _ : J => p) g
  rw [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
    bernoulliDesign_E_sq_of_expansion _ _ _ g a ha]
  simp_rw [fourierCoeffR_of_centeredMonomial_expansion p hp g a ha, mul_pow]
  have hs2 : biasScale p ^ 2 = p * (1 - p) :=
    Real.sq_sqrt (mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le))
  simp only [Finset.powerset_univ, Finset.prod_const]
  apply Finset.sum_congr rfl
  intro A _
  rw [← pow_mul, Nat.mul_comm A.card 2, pow_mul, hs2]

/-- On [the coordinate set J](hyp:J), [the completed configuration](goal) assigns
[the selected coordinate i](hyp:i) [the Boolean value b](hyp:b) and uses
[the configuration x on all coordinates other than i](hyp:x) elsewhere. -/
def otherConfig (i : J) (x : {j : J // j ≠ i} → Bool) (b : Bool) : J → Bool :=
  fun j => if hj : j = i then b else x ⟨j, hj⟩

/-- On [the coordinate set J](hyp:J), [the section difference](goal) of
[a Boolean function h](hyp:h) at [coordinate i](hyp:i), with [the other coordinates
fixed at x](hyp:x), is its zero-one value when i is true minus its zero-one value
when i is false. -/
def sectionDiff (h : (J → Bool) → Bool) (i : J)
    (x : {j : J // j ≠ i} → Bool) : ℝ :=
  boolValue h (otherConfig i x true) - boolValue h (otherConfig i x false)

omit [Fintype J] in
-- @node: coordDiff_eq_sectionDiff
/-- For [a Boolean function h](hyp:h), [its difference obtained by setting
coordinate i to true and to false at a full configuration equals its section
difference with the other coordinates fixed at that configuration](goal). -/
lemma coordDiff_eq_sectionDiff (h : (J → Bool) → Bool) (i : J) (x : J → Bool) :
    coordDiff h i x = sectionDiff h i (fun j => x j.val) := by
  have hc (b : Bool) : replaceCoord x i b = otherConfig i (fun j => x j.val) b := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [replaceCoord, otherConfig]
    · simp [replaceCoord, otherConfig, hj]
  simp only [coordDiff, sectionDiff, hc]

omit [Fintype J] in
-- @node: coordDiff_values
/-- For [a Boolean function h](hyp:h), [the difference between its zero-one values
when coordinate i is true and when it is false is always −1, zero, or one](goal). -/
lemma coordDiff_values (h : (J → Bool) → Bool) (i : J) (x : J → Bool) :
    coordDiff h i x = -1 ∨ coordDiff h i x = 0 ∨ coordDiff h i x = 1 := by
  unfold coordDiff boolValue
  cases h (replaceCoord x i true) <;> cases h (replaceCoord x i false) <;> norm_num

omit [Fintype J] in
-- @node: fourierChar_replaceCoord_of_not_mem
/-- If [coordinate i is absent from A](hyp:hi), then [replacing its Boolean value
in any configuration leaves the Fourier basis function indexed by A unchanged](goal). -/
lemma fourierChar_replaceCoord_of_not_mem (p : ℝ) (A : Finset J) (i : J)
    (hi : i ∉ A) (x : J → Bool) (b : Bool) :
    fourierChar p A (replaceCoord x i b) = fourierChar p A x := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [coordChar, replaceCoord, Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]

omit [Fintype J] in
-- @node: fourierChar_coordinate_difference
/-- [The difference between a Fourier basis function with coordinate i set to
true and set to false is zero if i is absent from its index set; otherwise it is
the basis function indexed by that set with i removed, divided by the bias scale](goal). -/
lemma fourierChar_coordinate_difference (p : ℝ) (A : Finset J) (i : J)
    (x : J → Bool) :
    fourierChar p A (replaceCoord x i true) -
      fourierChar p A (replaceCoord x i false) =
      if i ∈ A then fourierChar p (A.erase i) x / biasScale p else 0 := by
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    have he : i ∉ A.erase i := by simp
    have hA : A = insert i (A.erase i) := (Finset.insert_erase hi).symm
    conv_lhs => rw [hA]
    simp only [fourierChar, Finset.prod_insert he]
    change coordChar p i (replaceCoord x i true) *
        fourierChar p (A.erase i) (replaceCoord x i true) -
      coordChar p i (replaceCoord x i false) *
        fourierChar p (A.erase i) (replaceCoord x i false) =
        fourierChar p (A.erase i) x / biasScale p
    rw [fourierChar_replaceCoord_of_not_mem p _ i he,
      fourierChar_replaceCoord_of_not_mem p _ i he]
    simp only [coordChar, replaceCoord, Function.update_self, Bool.true_eq, ↓reduceIte,
      Bool.false_eq_true]
    ring
  · rw [if_neg hi, fourierChar_replaceCoord_of_not_mem p A i hi,
      fourierChar_replaceCoord_of_not_mem p A i hi, sub_self]

-- @node: coordDiff_fourier_expansion
/-- If [the bias is strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [its coordinate-i difference equals the sum over coordinate
sets containing i of its Fourier coefficient divided by the bias scale, times
the basis function with i removed, evaluated at the given configuration](goal). -/
lemma coordDiff_fourier_expansion (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) (i : J) (x : J → Bool) :
    coordDiff h i x = ∑ A : Finset J, if i ∈ A then
      fourierCoeff p h A / biasScale p * fourierChar p (A.erase i) x else 0 := by
  unfold coordDiff
  rw [fourier_expansion p hp (boolValue h) (replaceCoord x i true),
    fourier_expansion p hp (boolValue h) (replaceCoord x i false),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [← mul_sub, fourierChar_coordinate_difference]
  split_ifs <;> simp [fourierCoeff] <;> ring

-- @node: fourierCoeffR_coordDiff
/-- If [the bias is strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the Fourier coefficient at A of its coordinate-i difference
is zero when A contains i, and otherwise equals h's coefficient at A with i
adjoined divided by the bias scale](goal). -/
lemma fourierCoeffR_coordDiff (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) (i : J) (A : Finset J) :
    fourierCoeffR p (coordDiff h i) A =
      if i ∈ A then 0 else fourierCoeff p h (insert i A) / biasScale p := by
  unfold fourierCoeffR
  simp_rw [coordDiff_fourier_expansion p hp h i, Finset.sum_mul]
  rw [FiniteDesign.E_sum]
  have hterm (B : Finset J) :
      (biasedLaw J p).E (fun x =>
        (if i ∈ B then fourierCoeff p h B / biasScale p *
          fourierChar p (B.erase i) x else 0) * fourierChar p A x) =
        if i ∈ B then fourierCoeff p h B / biasScale p *
          (if B.erase i = A then 1 else 0) else 0 := by
    by_cases hi : i ∈ B
    · simp only [if_pos hi, mul_assoc]
      rw [FiniteDesign.E_const_mul, fourierChar_orthonormal p hp]
    · simp [hi]
  simp_rw [hterm]
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    apply Finset.sum_eq_zero
    intro B _
    have hne : B.erase i ≠ A := by
      intro he
      have hn : i ∉ B.erase i := by simp
      rw [he] at hn
      exact hn hi
    simp [hne]
  · rw [if_neg hi, Finset.sum_eq_single (insert i A)]
    · simp [hi]
    · intro B _ hB
      by_cases hiB : i ∈ B
      · have hne : B.erase i ≠ A := by
          intro he
          apply hB
          rw [← he, Finset.insert_erase hiB]
        simp [hiB, hne]
      · simp [hiB]
    · simp

-- @node: fourierCoeff_insert_eq_biasScale_mul_difference
/-- If [the bias is strictly between zero and one](hyp:hp) and [coordinate i is
absent from A](hyp:hi), then for [a Boolean function h](hyp:h), [its Fourier
coefficient at A with i adjoined equals the bias scale times the Fourier
coefficient at A of its coordinate-i difference](goal). -/
lemma fourierCoeff_insert_eq_biasScale_mul_difference (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) (i : J) (A : Finset J) (hi : i ∉ A) :
    fourierCoeff p h (insert i A) = biasScale p * fourierCoeffR p (coordDiff h i) A := by
  rw [fourierCoeffR_coordDiff p hp h i A, if_neg hi]
  have hs : biasScale p ≠ 0 := (biasScale_pos_le_half p hp).1.ne'
  field_simp

-- @node: difference_secondMoment_eq_influence
/-- If [the bias is strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the expected square of its coordinate-i difference equals
the probability that changing coordinate i changes its output](goal). -/
lemma difference_secondMoment_eq_influence (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) (i : J) :
    (biasedLaw J p).E (fun x => coordDiff h i x ^ 2) = coordInfluence p h i := by
  unfold coordInfluence FiniteDesign.Pr
  apply FiniteDesign.E_congr
  intro x
  unfold coordDiff boolValue FiniteDesign.ind
  cases ht : h (replaceCoord x i true) <;>
    cases hf : h (replaceCoord x i false) <;> norm_num [ht, hf]

-- @node: sum_fourierCoeff_sq_containing
/-- If [the bias is strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the sum of squared Fourier coefficients over sets containing
coordinate i equals the Bernoulli variance times the influence of i](goal). -/
lemma sum_fourierCoeff_sq_containing (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) (i : J) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset J => i ∈ S), fourierCoeff p h S ^ 2 =
      biasScale p ^ 2 * coordInfluence p h i := by
  rw [← difference_secondMoment_eq_influence p hp h i,
    secondMoment_eq_sum_fourierCoeffR_sq p hp, Finset.mul_sum]
  calc
    _ = ∑ A ∈ Finset.univ.filter (fun A : Finset J => i ∉ A),
        biasScale p ^ 2 * fourierCoeffR p (coordDiff h i) A ^ 2 := by
      apply Finset.sum_bij (fun S _ => S.erase i)
      · intro S hS
        simp
      · intro S hS T hT he
        have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
        have hiT : i ∈ T := (Finset.mem_filter.mp hT).2
        calc
          S = insert i (S.erase i) := (Finset.insert_erase hiS).symm
          _ = insert i (T.erase i) := congrArg (insert i) he
          _ = T := Finset.insert_erase hiT
      · intro A hA
        have hiA : i ∉ A := (Finset.mem_filter.mp hA).2
        exact ⟨insert i A, by simp, by simp [hiA]⟩
      · intro S hS
        have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
        have he := fourierCoeff_insert_eq_biasScale_mul_difference p hp h i
          (S.erase i) (by simp)
        rw [Finset.insert_erase hiS] at he
        rw [he, mul_pow]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro A _
      by_cases hiA : i ∈ A
      · simp [hiA, fourierCoeffR_coordDiff p hp h i A]
      · simp [hiA]

/-- If [the bias is strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the sum of squared Fourier coefficients weighted by the size
of their coordinate sets equals the Bernoulli variance times total coordinate
influence](goal). -/
-- @node: weightedSpectralMass_eq
lemma weightedSpectralMass_eq (p : ℝ) (hp : BiasInterior p) (h : (J → Bool) → Bool) :
    weightedSpectralMass p h = biasScale p ^ 2 * totalCoordInfluence p h := by
  have hcount (S : Finset J) : (S.card : ℝ) * fourierCoeff p h S ^ 2 =
      ∑ i : J, if i ∈ S then fourierCoeff p h S ^ 2 else 0 := by
    simp
  unfold weightedSpectralMass
  simp_rw [hcount]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter, sum_fourierCoeff_sq_containing p hp h]
  exact (Finset.mul_sum _ _ _).symm

/-- If [the bias is strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the variance of its zero-one value under the biased law
equals the sum of squared Fourier coefficients over nonempty coordinate sets](goal). -/
-- @node: variance_eq_sum_fourierCoeff_sq
lemma variance_eq_sum_fourierCoeff_sq (p : ℝ) (hp : BiasInterior p) (h : (J → Bool) → Bool) :
    (biasedLaw J p).Var (boolValue h) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset J => S ≠ ∅), fourierCoeff p h S ^ 2 := by
  have he : fourierCoeff p h ∅ = (biasedLaw J p).E (boolValue h) := by
    simp [fourierCoeff, fourierCoeffR, fourierChar]
  rw [FiniteDesign.Var_eq, secondMoment_eq_sum_fourierCoeffR_sq p hp, ← he]
  change (∑ S : Finset J, fourierCoeff p h S ^ 2) - fourierCoeff p h ∅ ^ 2 = _
  have hf : Finset.univ.filter (fun S : Finset J => S ≠ ∅) =
      (Finset.univ : Finset (Finset J)).erase ∅ := by
    ext S
    simp [ne_comm]
  rw [hf, Finset.sum_erase_eq_sub (Finset.mem_univ ∅)]

/-- For [a Boolean function h](hyp:h), [whenever the bias is strictly between zero
and one, its size-weighted squared Fourier mass equals the Bernoulli variance
times total influence, and its output variance equals its squared Fourier mass
over nonempty coordinate sets](goal). -/
-- keep: Proof witness for the public FourierIdentities proposition (def:parseval, eq:parseval); downstream proofs use its two component lemmas directly.
lemma fourierIdentities_holds (p : ℝ) (h : (J → Bool) → Bool) : FourierIdentities p h := by
  intro hp
  exact ⟨weightedSpectralMass_eq p hp h, variance_eq_sum_fourierCoeff_sq p hp h⟩

-- @node: coordInfluence_nonneg_le_one
/-- For [a Boolean function h](hyp:h), [the probability that coordinate i is
pivotal lies between zero and one, including the endpoints](goal). -/
lemma coordInfluence_nonneg_le_one (p : ℝ) (h : (J → Bool) → Bool) (i : J) :
    0 ≤ coordInfluence p h i ∧ coordInfluence p h i ≤ 1 := by
  exact ⟨(biasedLaw J p).Pr_nonneg _, (biasedLaw J p).Pr_le_one _⟩

-- @node: totalCoordInfluence_nonneg_le_card
/-- For [a Boolean function h](hyp:h), [total coordinate influence is nonnegative
and at most the number of coordinates](goal). -/
lemma totalCoordInfluence_nonneg_le_card (p : ℝ) (h : (J → Bool) → Bool) :
    0 ≤ totalCoordInfluence p h ∧ totalCoordInfluence p h ≤ Fintype.card J := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (coordInfluence_nonneg_le_one p h i).1)
  · calc
      totalCoordInfluence p h ≤ ∑ _i : J, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (coordInfluence_nonneg_le_one p h i).2)
      _ = Fintype.card J := by simp

-- @node: boolean_variance_le_quarter
/-- For [a Boolean function h](hyp:h), [the variance of its zero-one value under
the biased configuration law is at most one quarter](goal). -/
lemma boolean_variance_le_quarter (p : ℝ) (h : (J → Bool) → Bool) :
    (biasedLaw J p).Var (boolValue h) ≤ 1 / 4 := by
  have hsq : (fun x => boolValue h x ^ 2) = boolValue h := by
    funext x
    cases h x <;> norm_num [boolValue]
  rw [FiniteDesign.Var_eq, hsq]
  nlinarith [sq_nonneg ((biasedLaw J p).E (boolValue h) - 1 / 2)]

-- @node: variance_le_biasScale_sq_mul_influence
/-- If [the bias is strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the variance of its zero-one value is at most the Bernoulli
variance times its total coordinate influence](goal). -/
lemma variance_le_biasScale_sq_mul_influence (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) :
    (biasedLaw J p).Var (boolValue h) ≤ biasScale p ^ 2 * totalCoordInfluence p h := by
  rw [variance_eq_sum_fourierCoeff_sq p hp h, ← weightedSpectralMass_eq p hp h]
  unfold weightedSpectralMass
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = ∅
  · simp [hS]
  · rw [if_pos hS]
    have hc : (1 : ℝ) ≤ S.card := by
      exact_mod_cast (Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hS))
    exact le_mul_of_one_le_left (sq_nonneg _) hc

end Papers.OaiUniformInfluenceHypergraph
