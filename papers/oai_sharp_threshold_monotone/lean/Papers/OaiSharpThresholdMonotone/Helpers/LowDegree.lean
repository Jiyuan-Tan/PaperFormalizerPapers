module
public import Papers.OaiSharpThresholdMonotone.Helpers.NoiseOperator

/-! # Low-degree mass under small coordinate influences

The real cutoff is compared directly to integer cardinalities; no rounding occurs.
-/

public section

open scoped BigOperators

namespace Papers.OaiSharpThresholdMonotone

variable {J : Type*} [Fintype J] [DecidableEq J]

-- @node: coordDiff_norm_fourThirds_sq
/-- If [the bias p lies strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the squared L⁴ᐟ³ norm of its difference in coordinate i equals
the influence of i raised to the power three halves](goal). -/
lemma coordDiff_norm_fourThirds_sq (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) (i : J) :
    cubeNorm p (4 / 3) (coordDiff h i) ^ 2 = coordInfluence p h i ^ (3 / 2 : ℝ) := by
  have hmoment : (biasedLaw J p).E (fun x => |coordDiff h i x| ^ (4 / 3 : ℝ)) =
      coordInfluence p h i := by
    unfold coordInfluence Causalean.Experimentation.DesignBased.FiniteDesign.Pr
    apply Causalean.Experimentation.DesignBased.FiniteDesign.E_congr
    intro x
    rcases coordDiff_values h i x with hx | hx | hx <;>
      simp [Causalean.Experimentation.DesignBased.FiniteDesign.ind,
        show coordDiffR (boolValue h) i x = coordDiff h i x from rfl, hx]
  unfold cubeNorm
  rw [hmoment, ← Real.rpow_natCast, ← Real.rpow_mul (coordInfluence_nonneg_le_one p h i).1]
  norm_num

-- @node: scalar_log_bound
/-- If [s is positive and at most one half](hyp:hs), [s times the natural logarithm
of four divided by s is at most two](goal). -/
lemma scalar_log_bound (s : ℝ) (hs : 0 < s ∧ s ≤ 1 / 2) :
    s * Real.log (4 / s) ≤ 2 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    have heq : Real.log 4 = 2 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
    linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hs.1)
  have heq : Real.log (4 / s) = Real.log 4 + Real.log s⁻¹ := by
    rw [div_eq_mul_inv, Real.log_mul (by norm_num) (inv_ne_zero (ne_of_gt hs.1))]
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_left hlog hs.1.le
  have hcancel : s * s⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hs.1)
  have hmul4 := mul_le_mul_of_nonneg_left hlog4 hs.1.le
  nlinarith
    -- @realizes s(positive scalar at most one half)

-- @node: noiseParameter_neg_two_mul_cutoff_le
/-- If [the bias p lies strictly between zero and one](hyp:hp) and [m is at least
two](hyp:hm), [the noise parameter raised to minus twice the low-degree cutoff
is at most m raised to the power one sixteenth](goal). -/
lemma noiseParameter_neg_two_mul_cutoff_le (p m : ℝ) (hp : BiasInterior p)
    (hm : LowDegreeParam m) :
    noiseParameter p ^ (-2 * lowCutoff p m) ≤ m ^ (1 / 16 : ℝ) := by
  have hσ := biasScale_pos_le_half p hp
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by dsimp [LowDegreeParam] at hm; linarith)
  have hscalar := scalar_log_bound (biasScale p) hσ
  have hlogρ : Real.log (noiseParameter p) = -Real.log (4 / biasScale p) := by
    unfold noiseParameter
    rw [Real.log_div (ne_of_gt hσ.1) (by norm_num),
      Real.log_div (by norm_num) (ne_of_gt hσ.1)]
    ring
  rw [Real.rpow_def_of_pos (noiseParameter_bounds p hp).1,
    Real.rpow_def_of_pos hmpos, hlogρ]
  apply Real.exp_le_exp.mpr
  unfold lowCutoff
  nlinarith [mul_nonneg hlogm (sub_nonneg.mpr hscalar)]

-- @node: lowProjection_norm_sq
/-- If [the bias p lies strictly between zero and one](hyp:hp), [the squared L² norm
of the projection of a real function onto degrees at most d equals the sum of its
squared Fourier coefficients over coordinate sets of size at most d](goal). -/
lemma lowProjection_norm_sq (p d : ℝ) (hp : BiasInterior p)
    (g : (J → Bool) → ℝ) :
    cubeNorm p 2 (lowProjection p d g) ^ 2 =
      ∑ A ∈ Finset.univ.filter (fun A : Finset J => (A.card : ℝ) ≤ d),
        fourierCoeffR p g A ^ 2 := by
  rw [cubeNorm_two_sq, secondMoment_eq_sum_fourierCoeffR_sq p hp]
  simp only [fourierCoeffR_lowProjection p d hp, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  split_ifs <;> simp

-- @node: sectionDiff_norm_fourThirds_sq
/-- If [the bias p lies strictly between zero and one](hyp:hp), then for [a Boolean
function h](hyp:h), [the squared L⁴ᐟ³ norm over the remaining coordinates of the
difference obtained by switching coordinate i from false to true equals the influence
of i raised to the power three halves](goal). -/
lemma sectionDiff_norm_fourThirds_sq (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) (i : J) :
    cubeNorm p (4 / 3) (coordDiffRemaining (boolValue h) i) ^ 2 =
      coordInfluence p h i ^ (3 / 2 : ℝ) := by
  have he : (biasedLaw J p).E (fun x => |coordDiff h i x| ^ (4 / 3 : ℝ)) =
      (biasedLaw {j : J // j ≠ i} p).E
        (fun y => |coordDiffRemaining (boolValue h) i y| ^ (4 / 3 : ℝ)) := by
    rw [biasedLaw_E_coordinate_split p hp _ i]
    apply Causalean.Experimentation.DesignBased.FiniteDesign.E_congr
    intro y
    have hr (b : Bool) :
        (fun j : {j : J // j ≠ i} => insertCoordinate i y b j.val) = y := by
      funext j
      simp [insertCoordinate, j.property]
    simp only [coordDiff, coordDiff_eq_remaining, hr]
    ring
  rw [← coordDiff_norm_fourThirds_sq p hp h i]
  unfold cubeNorm
  rw [he]

-- @node: lowDegree_mass_le_derivative_mass
/-- If [the bias p lies strictly between zero and one](hyp:hp) and [the degree bound
k is nonnegative](hyp:hk), then for [a Boolean function h](hyp:h), [the sum of squared
Fourier coefficients over nonempty coordinate sets of size at most k is at most the
squared bias scale times the noise parameter raised to minus twice k times the sum
of coordinate influences raised to the power three halves](goal). -/
lemma lowDegree_mass_le_derivative_mass (p k : ℝ) (hp : BiasInterior p) (hk : 0 ≤ k)
    (h : (J → Bool) → Bool) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset J => 1 ≤ S.card ∧ (S.card : ℝ) ≤ k),
      fourierCoeff p h S ^ 2) ≤
      biasScale p ^ 2 * noiseParameter p ^ (-2 * k) *
        ∑ i : J, coordInfluence p h i ^ (3 / 2 : ℝ) := by
  classical
  let C := Finset.univ.filter (fun S : Finset J => 1 ≤ S.card ∧ (S.card : ℝ) ≤ k)
  have hcount : (∑ S ∈ C, fourierCoeff p h S ^ 2) ≤
      ∑ i : J, ∑ S ∈ C.filter (fun S => i ∈ S), fourierCoeff p h S ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro S hS
    have hc : (1 : ℝ) ≤ S.card := by
      exact_mod_cast (Finset.mem_filter.mp hS).2.1
    simpa using mul_le_mul_of_nonneg_right hc (sq_nonneg (fourierCoeff p h S))
  have hi (i : J) :
      (∑ S ∈ C.filter (fun S => i ∈ S), fourierCoeff p h S ^ 2) ≤
        biasScale p ^ 2 * cubeNorm p 2
          (lowProjection p k (coordDiffRemaining (boolValue h) i)) ^ 2 := by
    rw [lowProjection_norm_sq p k hp, Finset.mul_sum]
    let D := Finset.univ.filter (fun A : Finset {j : J // j ≠ i} =>
      (insert i (A.image Subtype.val)).card ≥ 1 ∧
      ((insert i (A.image Subtype.val)).card : ℝ) ≤ k)
    have he : (∑ S ∈ C.filter (fun S => i ∈ S), fourierCoeff p h S ^ 2) =
        ∑ A ∈ D, biasScale p ^ 2 *
          fourierCoeffR p (coordDiffRemaining (boolValue h) i) A ^ 2 := by
      symm
      apply Finset.sum_bij (fun A _ => insert i (A.image Subtype.val))
      · intro A hA
        simpa [C, D] using hA
      · intro A _ B _ hAB
        apply Finset.ext
        intro j
        have hm := congrArg (fun S : Finset J => j.val ∈ S) hAB
        simpa [j.property, Subtype.val_injective] using hm
      · intro S hS
        have hiS := (Finset.mem_filter.mp hS).2
        have heq : insert i ((S.subtype (fun j => j ≠ i)).image Subtype.val) = S := by
          ext j
          by_cases hj : j = i
          · subst j; simp [hiS]
          · simp [hj, Finset.mem_subtype]
        refine ⟨S.subtype (fun j => j ≠ i), ?_, heq⟩
        simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and, heq] using
          (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
      · intro A _
        rw [difference_fourierCoeff p hp]
        change _ * (fourierCoeff p h _ / biasScale p) ^ 2 = _
        field_simp [(biasScale_pos_le_half p hp).1.ne']
    rw [he]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro A hA
      have hAk := (Finset.mem_filter.mp hA).2.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, le_trans ?_ hAk⟩
      exact_mod_cast le_trans (Finset.card_image_iff.mpr Subtype.val_injective.injOn).ge
        (Finset.card_le_card (Finset.subset_insert i (A.image Subtype.val)))
    · intro A _ _
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hn (i : J) : cubeNorm p 2
      (lowProjection p k (coordDiffRemaining (boolValue h) i)) ^ 2 ≤
      noiseParameter p ^ (-2 * k) * coordInfluence p h i ^ (3 / 2 : ℝ) := by
    have hb := lowProjection_norm_le p k hp hk (coordDiffRemaining (boolValue h) i)
    have hb2 := pow_le_pow_left₀ (cubeNorm_nonneg p 2 (by norm_num) _) hb 2
    rw [mul_pow, sectionDiff_norm_fourThirds_sq p hp h i] at hb2
    have he : (noiseParameter p ^ (-k)) ^ 2 = noiseParameter p ^ (-2 * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (noiseParameter_bounds p hp).1.le]
      congr 1
      ring
    rwa [he] at hb2
  calc
    _ ≤ ∑ i : J, ∑ S ∈ C.filter (fun S => i ∈ S), fourierCoeff p h S ^ 2 := hcount
    _ ≤ ∑ i : J, biasScale p ^ 2 * cubeNorm p 2
        (lowProjection p k (coordDiffRemaining (boolValue h) i)) ^ 2 :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ ≤ ∑ i : J, biasScale p ^ 2 *
        (noiseParameter p ^ (-2 * k) * coordInfluence p h i ^ (3 / 2 : ℝ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hn i) (sq_nonneg _))
    _ = _ := by simp_rw [← mul_assoc]; rw [Finset.mul_sum]

-- @node: lem:low-degree
/-- For [a Boolean function h](hyp:h) on [a finite coordinate set](hyp:hJ), suppose
[the bias p lies strictly between zero and one](hyp:hp), [m is at least two](hyp:hm),
[each coordinate influence is at most total influence divided by m](hyp:hsmall), and
[k equals the bias scale times the natural logarithm of m divided by 64](hyp:hk).
Then [the sum of squared Fourier coefficients over nonempty coordinate sets of size
at most k is at most m raised to minus one quarter times total coordinate influence](goal). -/
lemma sum_lowDegree_fourierCoeff_sq_le (p m k : ℝ) (h : (J → Bool) → Bool)
    (hJ : FiniteCoordinateSet J) (hp : BiasInterior p) (hm : LowDegreeParam m)
    (hsmall : SmallIndividualInfluences p h m) (hk : LowDegreeCutoff p m k) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset J => 1 ≤ S.card ∧ (S.card : ℝ) ≤ k),
      fourierCoeff p h S ^ 2 ≤ m ^ (-(1 / 4 : ℝ)) * totalCoordInfluence p h := by
  classical
  change k = lowCutoff p m at hk
  subst k
  have hm2 : 2 ≤ m := hm
  have hmpos : 0 < m := by linarith
  have hmone : 1 ≤ m := by linarith
  have hIpos : 0 ≤ totalCoordInfluence p h :=
    Finset.sum_nonneg (fun i _ => (coordInfluence_nonneg_le_one p h i).1)
  have hvar : (∑ S ∈ Finset.univ.filter
      (fun S : Finset J => 1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p m),
        fourierCoeff p h S ^ 2) ≤ (biasedLaw J p).E (fun x => boolValue h x ^ 2) := by
    rw [secondMoment_eq_sum_fourierCoeffR_sq p hp (boolValue h)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro S hS
      exact Finset.mem_univ _
    · intro S _ _
      exact sq_nonneg _
  have hcancel : m ^ (-(1 / 4 : ℝ)) * m ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hmpos]
    norm_num
  by_cases htotal : totalCoordInfluence p h ≤ m ^ (1 / 4 : ℝ)
  · have hcoord (i : J) : coordInfluence p h i ≤ m ^ (-3 / 4 : ℝ) := by
      calc
        _ ≤ totalCoordInfluence p h / m := hsmall i
        _ ≤ m ^ (1 / 4 : ℝ) / m := div_le_div_of_nonneg_right htotal hmpos.le
        _ = _ := by
          convert (Real.rpow_sub hmpos (1 / 4 : ℝ) 1).symm using 1 <;> norm_num
    have hroot (i : J) : coordInfluence p h i ^ (1 / 2 : ℝ) ≤ m ^ (-3 / 8 : ℝ) := by
      have hh := Real.rpow_le_rpow (coordInfluence_nonneg_le_one p h i).1
        (hcoord i) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [← Real.rpow_mul hmpos.le] at hh
      norm_num at hh ⊢
      exact hh
    have hsum : (∑ i : J, coordInfluence p h i ^ (3 / 2 : ℝ)) ≤
        m ^ (-3 / 8 : ℝ) * totalCoordInfluence p h := by
      rw [totalCoordInfluence, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      calc
        _ = coordInfluence p h i ^ (1 / 2 : ℝ) * coordInfluence p h i := by
          convert (Real.rpow_add' (coordInfluence_nonneg_le_one p h i).1
            (by norm_num : (1 / 2 : ℝ) + 1 ≠ 0)) using 1 <;> norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right (hroot i)
          (coordInfluence_nonneg_le_one p h i).1
    have hk : 0 ≤ lowCutoff p m := div_nonneg
      (mul_nonneg (biasScale_pos_le_half p hp).1.le (Real.log_nonneg hmone)) (by norm_num)
    have hs : biasScale p ^ 2 ≤ 1 := by
      obtain ⟨hs, hsle⟩ := biasScale_pos_le_half p hp
      nlinarith
    have hrho := noiseParameter_neg_two_mul_cutoff_le p m hp hm
    have hpowers : m ^ (1 / 16 : ℝ) * m ^ (-3 / 8 : ℝ) ≤ m ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hmpos]
      apply Real.rpow_le_rpow_of_exponent_le hmone
      norm_num
    calc
      _ ≤ biasScale p ^ 2 * noiseParameter p ^ (-2 * lowCutoff p m) *
          ∑ i : J, coordInfluence p h i ^ (3 / 2 : ℝ) :=
        lowDegree_mass_le_derivative_mass p _ hp hk h
      _ ≤ biasScale p ^ 2 * m ^ (1 / 16 : ℝ) *
          (m ^ (-3 / 8 : ℝ) * totalCoordInfluence p h) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hrho (sq_nonneg _)
        · exact hsum
        · exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg
            (coordInfluence_nonneg_le_one p h i).1 _)
        · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hmpos.le _)
      _ = biasScale p ^ 2 * (m ^ (1 / 16 : ℝ) * m ^ (-3 / 8 : ℝ)) *
          totalCoordInfluence p h := by ring
      _ ≤ 1 * m ^ (-(1 / 4 : ℝ)) * totalCoordInfluence p h := by
        apply mul_le_mul_of_nonneg_right _ hIpos
        exact mul_le_mul hs hpowers (mul_nonneg (Real.rpow_nonneg hmpos.le _)
          (Real.rpow_nonneg hmpos.le _)) (by norm_num)
      _ = _ := by rw [one_mul]
  · have hlarge : 1 ≤ m ^ (-(1 / 4 : ℝ)) * totalCoordInfluence p h := by
      calc
        1 = m ^ (-(1 / 4 : ℝ)) * m ^ (1 / 4 : ℝ) := hcancel.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge htotal))
          (Real.rpow_nonneg hmpos.le _)
    have hmoment : (biasedLaw J p).E (fun x => boolValue h x ^ 2) ≤ 1 := by
      calc
        _ ≤ (biasedLaw J p).E (fun _ => 1) := by
          unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
          apply Finset.sum_le_sum
          intro x _
          apply mul_le_mul_of_nonneg_left _ ((biasedLaw J p).p_nonneg x)
          unfold boolValue
          cases hx : h x <;> simp [hx]
        _ = 1 := by simp
    exact hvar.trans (hmoment.trans hlarge)

end Papers.OaiSharpThresholdMonotone
