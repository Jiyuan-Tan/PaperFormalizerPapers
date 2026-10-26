module
public import Papers.OaiSharpThresholdMonotone.Basic

/-! # Fourier expansion, Parseval, and the influence identities

These are paper-owned identities, derived from the finite Bernoulli centered-monomial
API. In particular no expansion, orthogonality, or Dirichlet identity is an input.
-/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

variable {J : Type*} [Fintype J] [DecidableEq J]

-- @node: biasedLaw_eq_bernoulliDesign
/-- If [the bias p lies between zero and one, inclusive](hyp:hp), [the biased cube law
equals the product Bernoulli design with success probability p at every coordinate](goal). -/
lemma biasedLaw_eq_bernoulliDesign (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    biasedLaw J p = bernoulliDesign (fun _ : J => p) (fun _ => hp.1) (fun _ => hp.2) := by
  simp only [biasedLaw, min_eq_left hp.2, max_eq_right hp.1]

-- @node: biasScale_pos_le_half
/-- If [the bias p lies strictly between zero and one](hyp:hp), [the square root of
the Bernoulli variance is positive and at most one half](goal). -/
lemma biasScale_pos_le_half (p : ℝ) (hp : BiasInterior p) :
    0 < biasScale p ∧ biasScale p ≤ 1 / 2 := by
  have hv : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  constructor
  · exact Real.sqrt_pos.mpr hv
  · change Real.sqrt (p * (1 - p)) ≤ 1 / 2
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [sq_nonneg (p - 1 / 2)]
    -- @realizes \sigma(positive bias scale at most one half)

-- @node: biasScale_sq
/-- If [the bias p lies strictly between zero and one](hyp:hp), [the squared bias
scale equals the Bernoulli variance p times one minus p](goal). -/
lemma biasScale_sq (p : ℝ) (hp : BiasInterior p) :
    biasScale p ^ 2 = p * (1 - p) := by
  exact Real.sq_sqrt (le_of_lt (mul_pos hp.1 (sub_pos.mpr hp.2)))

omit [Fintype J] [DecidableEq J] in
-- @node: fourierChar_empty
/-- [The Fourier character indexed by the empty set equals one at every configuration,
for any bias](goal). -/
lemma fourierChar_empty (p : ℝ) (x : J → Bool) : fourierChar p ∅ x = 1 := by
  simp [fourierChar]

omit [Fintype J] [DecidableEq J] in
/-- [The Fourier character for a coordinate set S at configuration x equals the product
of the centered coordinates in S, divided by the bias scale raised to the size of S](goal). -/
-- @node: fourierChar_eq_centeredMonomial
lemma fourierChar_eq_centeredMonomial (p : ℝ) (S : Finset J) (x : J → Bool) :
    fourierChar p S x = centeredMonomial (fun _ => p) S x / biasScale p ^ S.card := by
  simp [fourierChar, coordChar, centeredMonomial, treatInd, Finset.prod_div_distrib]

-- @node: fourierChar_orthonormal
/-- If [the bias p lies strictly between zero and one](hyp:hp), [the expected product
of the Fourier characters indexed by S and T is one when S equals T and zero otherwise](goal). -/
lemma fourierChar_orthonormal (p : ℝ) (hp : BiasInterior p) (S T : Finset J) :
    (biasedLaw J p).E (fun x => fourierChar p S x * fourierChar p T x) =
      if S = T then 1 else 0 := by
  have hσ : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  simp_rw [fourierChar_eq_centeredMonomial]
  simp_rw [div_mul_div_comm, div_eq_mul_inv]
  rw [FiniteDesign.E_mul_const,
    biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
    bernoulliDesign_E_centeredMonomial_mul]
  by_cases hST : S = T
  · subst T
    simp only [if_pos rfl, Finset.prod_const]
    rw [← biasScale_sq p hp]
    simp only [ite_true, sq, mul_pow]
    field_simp
  · simp [hST]


/-- If [the bias p lies strictly between zero and one](hyp:hp), [every real function
on the Boolean cube equals its expansion in the biased Fourier characters](goal).

This is the first displayed identity of `eq:parseval`. -/
-- @node: fourier_expansion
lemma fourier_expansion (p : ℝ) (hp : BiasInterior p) (g : (J → Bool) → ℝ) :
    g = fourierExpansion p g := by
  obtain ⟨a, ha⟩ := exists_centeredMonomial_expansion (fun _ : J => p) g
  let b : Finset J → ℝ := fun S => a S * biasScale p ^ S.card
  have hσ : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  have hg (x : J → Bool) : g x = ∑ S : Finset J, b S * fourierChar p S x := by
    rw [ha x]
    simp only [Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro S _
    rw [fourierChar_eq_centeredMonomial]
    dsimp [b]
    field_simp
  have hb (T : Finset J) : fourierCoeffR p g T = b T := by
    unfold fourierCoeffR
    simp_rw [hg, Finset.sum_mul, FiniteDesign.E_sum]
    simp_rw [mul_assoc, FiniteDesign.E_const_mul, fourierChar_orthonormal p hp]
    simp
  funext x
  simpa only [fourierExpansion, hb] using hg x

/-- If [the bias p lies strictly between zero and one](hyp:hp), [the second moment
of a real function under the biased cube law equals the sum of its squared Fourier coefficients](goal).

This is the second displayed identity of `eq:parseval`. -/
-- @node: secondMoment_eq_sum_fourierCoeffR_sq
lemma secondMoment_eq_sum_fourierCoeffR_sq (p : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) :
    (biasedLaw J p).E (fun x => g x ^ 2) = ∑ S : Finset J, fourierCoeffR p g S ^ 2 := by
  have hg (x : J → Bool) : g x =
      ∑ S : Finset J, fourierCoeffR p g S * fourierChar p S x :=
    congrFun (fourier_expansion p hp g) x
  calc
    (biasedLaw J p).E (fun x => g x ^ 2) =
        (biasedLaw J p).E (fun x =>
          ∑ S : Finset J, ∑ T : Finset J,
            (fourierCoeffR p g S * fourierCoeffR p g T) *
              (fourierChar p S x * fourierChar p T x)) := by
      apply FiniteDesign.E_congr
      intro x
      rw [hg x, sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      ring
    _ = _ := by
      simp_rw [FiniteDesign.E_sum, FiniteDesign.E_const_mul,
        fourierChar_orthonormal p hp]
      simp [sq]

/-- If [the bias p lies strictly between zero and one](hyp:hp), [the variance of a real
function under the biased cube law equals the sum of its squared Fourier coefficients
over nonempty coordinate sets](goal).

This is the third displayed identity of `eq:parseval`. -/
-- @node: variance_eq_sum_fourierCoeffR_sq
lemma variance_eq_sum_fourierCoeffR_sq (p : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) :
    (biasedLaw J p).Var g =
      ∑ S ∈ Finset.univ.filter (fun S : Finset J => S ≠ ∅), fourierCoeffR p g S ^ 2 := by
  have hzero : fourierCoeffR p g ∅ = (biasedLaw J p).E g := by
    simp [fourierCoeffR, fourierChar_empty]
  have hsum : (∑ S : Finset J, fourierCoeffR p g S ^ 2) =
      fourierCoeffR p g ∅ ^ 2 +
        ∑ S ∈ Finset.univ.filter (fun S : Finset J => S ≠ ∅), fourierCoeffR p g S ^ 2 := by
    have hfilter : Finset.univ.filter (fun S : Finset J => S ≠ ∅) =
        Finset.univ.erase (∅ : Finset J) := by
      ext S
      simp
    rw [hfilter]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset J))).symm
  rw [FiniteDesign.Var_eq, secondMoment_eq_sum_fourierCoeffR_sq p hp g, hsum, hzero]
  ring

/-- [For any real function on the Boolean cube, every bias strictly between zero and one
gives Fourier reconstruction, a second moment equal to the sum of all squared Fourier
coefficients, and a variance equal to the sum over nonempty coordinate sets](goal).

These are the three identities in the canonical `eq:parseval` interface. -/
-- keep: Certifies the paper's three eq:parseval identities together through the canonical fourierIdentities interface; a delivered equation, even though downstream proofs use its individual components.
lemma fourierIdentities_hold (p : ℝ) (g : (J → Bool) → ℝ) :
    fourierIdentities p g := by
  intro hp
  exact ⟨fourier_expansion p hp g, secondMoment_eq_sum_fourierCoeffR_sq p hp g,
    variance_eq_sum_fourierCoeffR_sq p hp g⟩

-- @node: variance_eq_sum_fourierCoeff_sq
/-- If [the bias p lies strictly between zero and one](hyp:hp), [a Boolean function h](hyp:h)
has [variance equal to the sum of its squared Fourier coefficients over nonempty
coordinate sets, when its outputs are coded as zero and one](goal). -/
lemma variance_eq_sum_fourierCoeff_sq (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) :
    (biasedLaw J p).Var (boolValue h) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset J => S ≠ ∅), fourierCoeff p h S ^ 2 := by
  exact variance_eq_sum_fourierCoeffR_sq p hp (boolValue h)

omit [Fintype J] in
-- @node: coordDiff_eq_remaining
/-- [The change in a real function when coordinate i is switched from false to true
at configuration x equals the same difference computed using only the coordinates other than i](goal). -/
lemma coordDiff_eq_remaining (g : (J → Bool) → ℝ) (i : J) (x : J → Bool) :
    coordDiffR g i x = coordDiffRemaining g i (fun j => x j.val) := by
  have heq (b : Bool) : coordinateReplace i x b =
      insertCoordinate i (fun j => x j.val) b := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [coordinateReplace, Causalean.Mathlib.Probability.PoissonAddOnePoincare.coordinateReplace,
        insertCoordinate]
    · simp [coordinateReplace, Causalean.Mathlib.Probability.PoissonAddOnePoincare.coordinateReplace,
        insertCoordinate, hj]
  simp only [coordDiffR, coordDiffRemaining, heq]

omit [Fintype J] in
-- @node: coordDiff_values
/-- For [a Boolean function h](hyp:h), [switching coordinate i from false to true
changes its zero-one value by minus one, zero, or one](goal). -/
lemma coordDiff_values (h : (J → Bool) → Bool) (i : J) (x : J → Bool) :
    coordDiff h i x = -1 ∨ coordDiff h i x = 0 ∨ coordDiff h i x = 1 := by
  unfold coordDiff coordDiffR boolValue
  cases h (coordinateReplace i x true) <;>
    cases h (coordinateReplace i x false) <;> norm_num

-- @node: coordInfluence_nonneg_le_one
/-- For [a Boolean function h](hyp:h), [the influence of any coordinate under the
biased cube law lies between zero and one, inclusive](goal). -/
lemma coordInfluence_nonneg_le_one (p : ℝ) (h : (J → Bool) → Bool) (i : J) :
    0 ≤ coordInfluence p h i ∧ coordInfluence p h i ≤ 1 := by
  exact ⟨(biasedLaw J p).Pr_nonneg _, (biasedLaw J p).Pr_le_one _⟩

-- @node: totalCoordInfluence_nonneg
/-- For [a Boolean function h](hyp:h), [the sum of its coordinate influences under
the biased cube law is nonnegative](goal). -/
lemma totalCoordInfluence_nonneg (p : ℝ) (h : (J → Bool) → Bool) :
    0 ≤ totalCoordInfluence p h := by
  exact Finset.sum_nonneg (fun i _ => (coordInfluence_nonneg_le_one p h i).1)

-- @node: difference_secondMoment_eq_influence
/-- For [a Boolean function h](hyp:h), [the expected squared change in its zero-one
value when coordinate i is switched from false to true equals that coordinate's influence](goal). -/
lemma difference_secondMoment_eq_influence (p : ℝ) (h : (J → Bool) → Bool) (i : J) :
    (biasedLaw J p).E (fun x => coordDiff h i x ^ 2) = coordInfluence p h i := by
  unfold coordInfluence FiniteDesign.Pr
  apply FiniteDesign.E_congr
  intro x
  rcases coordDiff_values h i x with hx | hx | hx <;>
    simp [FiniteDesign.ind, show coordDiffR (boolValue h) i x = coordDiff h i x from rfl, hx]

/-- If [the bias p lies strictly between zero and one](hyp:hp), [the expectation of
a real function equals the expectation over all coordinates other than i of its value
with i set to true weighted by p plus its value with i set to false weighted by one minus p](goal). -/
-- @node: biasedLaw_E_coordinate_split
lemma biasedLaw_E_coordinate_split (p : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) (i : J) :
    (biasedLaw J p).E g =
      (biasedLaw {j : J // j ≠ i} p).E (fun y =>
        p * g (insertCoordinate i y true) + (1 - p) * g (insertCoordinate i y false)) := by
  classical
  let e : (Bool × ({j : J // j ≠ i} → Bool)) ≃ (J → Bool) :=
    { toFun := fun z => insertCoordinate i z.2 z.1
      invFun := fun x => (x i, fun j => x j.val)
      left_inv := by
        intro z
        apply Prod.ext
        · simp [insertCoordinate]
        · funext j
          simp [insertCoordinate, j.property]
      right_inv := by
        intro x
        funext j
        by_cases hj : j = i
        · subst j; simp [insertCoordinate]
        · simp [insertCoordinate, hj] }
  have hw (z : Bool × ({j : J // j ≠ i} → Bool)) :
      (biasedLaw J p).p (e z) =
        (if z.1 then p else 1 - p) * (biasedLaw {j : J // j ≠ i} p).p z.2 := by
    simp only [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
      bernoulliDesign, prodDesign_p]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hi (j : {j : J // j ≠ i}) : (j : J) ≠ i := j.property
    cases hz : z.1 <;> simp [e, insertCoordinate, coinDesign, hi, hz]
  unfold FiniteDesign.E
  rw [← e.sum_comp]
  simp_rw [hw]
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Fintype.sum_bool]
  dsimp [e]
  ring

-- @node: difference_fourierCoeff
/-- For [a set A of coordinates other than i](hyp:A), if
[the bias p lies strictly between zero and one](hyp:hp), [the Fourier coefficient
at A of the difference obtained by switching coordinate i
from false to true equals the original function's coefficient at A together with i,
divided by the bias scale](goal). -/
lemma difference_fourierCoeff (p : ℝ) (hp : BiasInterior p) (g : (J → Bool) → ℝ)
    (i : J) (A : Finset {j : J // j ≠ i}) : -- @realizes A(index on remaining coordinates)
    fourierCoeffR p (coordDiffRemaining g i) A =
      fourierCoeffR p g (insert i (A.image Subtype.val)) / biasScale p := by
  have hσ : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  have hi : i ∉ A.image Subtype.val := by
    simp only [Finset.mem_image]
    rintro ⟨j, _, hj⟩
    exact j.property hj
  have hchar (y : {j : J // j ≠ i} → Bool) (b : Bool) :
      fourierChar p (insert i (A.image Subtype.val)) (insertCoordinate i y b) =
        ((if b then 1 else 0) - p) / biasScale p * fourierChar p A y := by
    rw [fourierChar, Finset.prod_insert hi, Finset.prod_image Subtype.val_injective.injOn]
    change coordChar p i (insertCoordinate i y b) *
      (∏ j ∈ A, coordChar p j.val (insertCoordinate i y b)) = _
    congr 1
    · simp [coordChar, insertCoordinate]
    · apply Finset.prod_congr rfl
      intro j _
      simp [coordChar, insertCoordinate, j.property]
  unfold fourierCoeffR
  rw [biasedLaw_E_coordinate_split p hp _ i]
  simp_rw [hchar]
  simp only [div_eq_mul_inv, ← FiniteDesign.E_mul_const]
  apply FiniteDesign.E_congr
  intro y
  simp only [coordDiffRemaining, Bool.false_eq_true, if_false, if_true]
  field_simp
  rw [biasScale_sq p hp]
  ring

/-- If [the bias p lies strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the sum of squared Fourier coefficients over sets containing i
equals the squared bias scale times the influence of coordinate i](goal).

This is the coordinate identity displayed in `eq:dirichlet`. -/
-- @node: coordSpectralMass_eq
lemma coordSpectralMass_eq (p : ℝ) (hp : BiasInterior p) (h : (J → Bool) → Bool) (i : J) :
    coordSpectralMass p h i = biasScale p ^ 2 * coordInfluence p h i := by
  classical
  have hσ : biasScale p ≠ 0 := ne_of_gt (biasScale_pos_le_half p hp).1
  have hI : (biasedLaw {j : J // j ≠ i} p).E
      (fun y => coordDiffRemaining (boolValue h) i y ^ 2) = coordInfluence p h i := by
    rw [← difference_secondMoment_eq_influence p h i,
      biasedLaw_E_coordinate_split p hp _ i]
    apply FiniteDesign.E_congr
    intro y
    have hr (b : Bool) :
        (fun j : {j : J // j ≠ i} => insertCoordinate i y b j.val) = y := by
      funext j
      simp [insertCoordinate, j.property]
    simp only [coordDiff, coordDiff_eq_remaining, hr]
    ring
  have hsum : (∑ A : Finset {j : J // j ≠ i},
      fourierCoeff p h (insert i (A.image Subtype.val)) ^ 2) = coordSpectralMass p h i := by
    unfold coordSpectralMass
    apply Finset.sum_bij (fun A _ => insert i (A.image Subtype.val))
    · intro A _
      simp
    · intro A _ B _ hAB
      apply Finset.ext
      intro j
      have hm := congrArg (fun S : Finset J => j.val ∈ S) hAB
      simpa [j.property, Subtype.val_injective] using hm
    · intro S hS
      refine ⟨S.subtype (fun j => j ≠ i), Finset.mem_univ _, ?_⟩
      have hiS := (Finset.mem_filter.mp hS).2
      ext j
      by_cases hj : j = i
      · subst j; simp [hiS]
      · simp [hj, Finset.mem_subtype]
    · intro A _
      rfl
  rw [← hsum, ← hI, secondMoment_eq_sum_fourierCoeffR_sq p hp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [difference_fourierCoeff p hp]
  change _ = biasScale p ^ 2 * (fourierCoeff p h _ / biasScale p) ^ 2
  field_simp

/-- If [the bias p lies strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the sum of squared Fourier coefficients weighted by the sizes of
their coordinate sets equals the squared bias scale times total coordinate influence](goal).

This is the total identity displayed in `eq:dirichlet`. -/
-- @node: weightedSpectralMass_eq
lemma weightedSpectralMass_eq (p : ℝ) (hp : BiasInterior p) (h : (J → Bool) → Bool) :
    weightedSpectralMass p h = biasScale p ^ 2 * totalCoordInfluence p h := by
  classical
  calc
    weightedSpectralMass p h =
        ∑ S : Finset J, ∑ i : J, if i ∈ S then fourierCoeff p h S ^ 2 else 0 := by
      simp [weightedSpectralMass]
    _ = ∑ i : J, ∑ S : Finset J,
        if i ∈ S then fourierCoeff p h S ^ 2 else 0 := Finset.sum_comm
    _ = ∑ i : J, coordSpectralMass p h i := by
      simp only [coordSpectralMass, Finset.sum_filter]
    _ = biasScale p ^ 2 * totalCoordInfluence p h := by
      simp_rw [coordSpectralMass_eq p hp]
      exact (Finset.mul_sum _ _ _).symm

/-- For [a Boolean function h](hyp:h), [every bias strictly between zero and one gives
both influence identities: the Fourier mass on sets containing each coordinate equals
the squared bias scale times its influence, and the Fourier mass weighted by set size
equals the squared bias scale times total influence](goal).

These are both identities in the canonical `eq:dirichlet` interface. -/
-- keep: Certifies both paper eq:dirichlet identities through the canonical fourierInfluenceIdentities interface; a delivered equation, even though downstream proofs use its individual components.
lemma fourierInfluenceIdentities_hold (p : ℝ) (h : (J → Bool) → Bool) :
    fourierInfluenceIdentities p h := by
  intro hp
  exact ⟨fun i => coordSpectralMass_eq p hp h i, weightedSpectralMass_eq p hp h⟩

-- @node: variance_le_biasScale_sq_mul_influence
/-- If [the bias p lies strictly between zero and one](hyp:hp), [a Boolean function h](hyp:h)
has [variance, with outputs coded as zero and one, at most the squared bias scale
times its total coordinate influence](goal). -/
lemma variance_le_biasScale_sq_mul_influence (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) :
    (biasedLaw J p).Var (boolValue h) ≤ biasScale p ^ 2 * totalCoordInfluence p h := by
  classical
  rw [variance_eq_sum_fourierCoeff_sq p hp, ← weightedSpectralMass_eq p hp]
  unfold weightedSpectralMass
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = ∅
  · simp [hS]
  · rw [if_pos hS]
    have hc : (1 : ℝ) ≤ S.card := by
      exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    exact le_mul_of_one_le_left (sq_nonneg _) hc

-- @node: edgeInfluence_eq_coordInfluence
/-- [The influence of an edge e on a Boolean graph function f equals its influence
when e is viewed as a coordinate of the Boolean cube](goal). -/
lemma edgeInfluence_eq_coordInfluence {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (e : GraphEdge n) : edgeInfluence p f e = coordInfluence p f e := by
  unfold edgeInfluence coordInfluence
  apply FiniteDesign.Pr_congr
  intro x
  unfold coordDiffR boolValue
  cases f (coordinateReplace e x true) <;>
    cases f (coordinateReplace e x false) <;> norm_num

-- @node: graphTotalInfluence_eq_totalCoordInfluence
/-- [The total edge influence of a Boolean graph function f equals its total coordinate
influence when graphs are viewed as Boolean configurations indexed by edges](goal). -/
lemma graphTotalInfluence_eq_totalCoordInfluence {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool) : graphTotalInfluence p f = totalCoordInfluence p f := by
  unfold graphTotalInfluence totalCoordInfluence
  exact Finset.sum_congr rfl (fun e _ => edgeInfluence_eq_coordInfluence p f e)

end Papers.OaiSharpThresholdMonotone
