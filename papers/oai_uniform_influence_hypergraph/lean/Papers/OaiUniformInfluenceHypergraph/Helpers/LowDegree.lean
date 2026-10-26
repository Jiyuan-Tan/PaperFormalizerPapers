module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.NoiseOperator

/-! # Low-degree Fourier mass for small individual influences -/

public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

variable {J : Type*} [Fintype J] [DecidableEq J]

-- @node: biasedLaw_E_other_coordinates
/-- For [a real-valued function g of the Boolean coordinates other than i](hyp:g),
if [the bias p lies strictly between zero and one](hyp:hp), then
[the expectation of g on the full Boolean cube equals its expectation under
the biased product law on those remaining coordinates](goal). -/
lemma biasedLaw_E_other_coordinates (p : ℝ) (hp : BiasInterior p) (i : J)
    (g : ({j : J // j ≠ i} → Bool) → ℝ) :
    (biasedLaw J p).E (fun x => g (fun j => x j.val)) =
      (biasedLaw {j : J // j ≠ i} p).E g := by
  classical
  rw [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
    biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩]
  simp only [Causalean.Experimentation.DesignBased.FiniteDesign.E, bernoulliDesign,
    Causalean.Experimentation.DesignBased.prodDesign_p]
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
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, FiniteDesign.p_sum, one_mul]

-- @node: sectionDiff_norm_fourThirds_sq
/-- For [a Boolean-valued function h](hyp:h), if [the bias p lies strictly
between zero and one](hyp:hp), then [the squared L⁴ᐟ³ norm on the remaining
coordinates of the difference between h with coordinate i set to true and h
with it set to false equals the i-th coordinate influence raised to the
three-halves power](goal). -/
lemma sectionDiff_norm_fourThirds_sq (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) (i : J) :
    cubeNormFourThirds p (sectionDiff h i) ^ 2 = coordInfluence p h i ^ (3 / 2 : ℝ) := by
  have hmoment : (biasedLaw {j : J // j ≠ i} p).E
      (fun x => |sectionDiff h i x| ^ (4 / 3 : ℝ)) = coordInfluence p h i := by
    rw [← biasedLaw_E_other_coordinates p hp i,
      ← difference_secondMoment_eq_influence p hp h i]
    apply FiniteDesign.E_congr
    intro x
    rw [← coordDiff_eq_sectionDiff]
    rcases coordDiff_values h i x with hv | hv | hv <;> rw [hv] <;> norm_num
  unfold cubeNormFourThirds
  rw [hmoment, ← Real.rpow_natCast,
    ← Real.rpow_mul (coordInfluence_nonneg_le_one p h i).1]
  norm_num

-- @node: noiseParameter_neg_two_mul_cutoff_le
/-- If [the bias p lies strictly between zero and one](hyp:hp) and
[the real parameter m is at least two](hyp:hm), then [the noise parameter
raised to minus twice the low-degree cutoff σ log m / 64 is at most the
sixteenth root of m, where σ is the square root of p times one minus p](goal). -/
lemma noiseParameter_neg_two_mul_cutoff_le (p m : ℝ) (hp : BiasInterior p)
    (hm : LowDegreeParam m) :
    noiseParameter p ^ (-2 * lowCutoff p m) ≤ m ^ (1 / 16 : ℝ) := by
  obtain ⟨hs, hsle⟩ := biasScale_pos_le_half p hp
  have hmpos : 0 < m := by have : 2 ≤ m := hm; linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by
    have : 2 ≤ m := hm
    linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlogdiv := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hs)
  have hlogbound : biasScale p * Real.log (4 / biasScale p) ≤ 2 := by
    have heq : (4 : ℝ) / biasScale p = 2 * (2 / biasScale p) := by ring
    rw [heq, Real.log_mul (by norm_num) (ne_of_gt (div_pos (by norm_num) hs))]
    have hb := mul_le_mul_of_nonneg_left hlogdiv hs.le
    have hc := mul_le_mul_of_nonneg_left hlog2 hs.le
    have hcancel : biasScale p * (2 / biasScale p) = 2 := by field_simp
    nlinarith
  have hlogrho : Real.log (noiseParameter p) = -Real.log (4 / biasScale p) := by
    unfold noiseParameter
    rw [Real.log_div hs.ne' (by norm_num), Real.log_div (by norm_num) hs.ne']
    ring
  rw [Real.rpow_def_of_pos (noiseParameter_bounds p hp).1,
    Real.rpow_def_of_pos hmpos]
  apply Real.exp_le_exp.mpr
  rw [hlogrho]
  unfold lowCutoff
  have hb := mul_le_mul_of_nonneg_right hlogbound hlogm
  nlinarith

-- @node: coordDiff_norm_fourThirds_sq
/-- For [a Boolean-valued function h](hyp:h), if [the bias p lies strictly
between zero and one](hyp:hp), then [the squared L⁴ᐟ³ norm on the full cube
of the difference between h with coordinate i set to true and h with it set
to false equals the i-th coordinate influence raised to the three-halves power](goal). -/
lemma coordDiff_norm_fourThirds_sq (p : ℝ) (hp : BiasInterior p)
    (h : (J → Bool) → Bool) (i : J) :
    cubeNormFourThirds p (coordDiff h i) ^ 2 = coordInfluence p h i ^ (3 / 2 : ℝ) := by
  have he : (biasedLaw J p).E (fun x => |coordDiff h i x| ^ (4 / 3 : ℝ)) =
      coordInfluence p h i := by
    rw [← difference_secondMoment_eq_influence p hp h i]
    apply FiniteDesign.E_congr
    intro x
    rcases coordDiff_values h i x with hv | hv | hv <;> rw [hv] <;> norm_num
  unfold cubeNormFourThirds
  rw [he, ← Real.rpow_natCast, ← Real.rpow_mul (coordInfluence_nonneg_le_one p h i).1]
  norm_num

-- @node: lowDegree_mass_le_derivative_mass
/-- For [a Boolean-valued function h](hyp:h), if [the bias p lies strictly
between zero and one](hyp:hp) and [the cutoff k is nonnegative](hyp:hk), then
[the sum of squared Fourier coefficients at degrees from one through k is
at most p times one minus p, multiplied by the noise parameter to the power
−2k and by the sum of the three-halves powers of the coordinate influences](goal). -/
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
    have hc : (1 : ℝ) ≤ S.card := by exact_mod_cast (Finset.mem_filter.mp hS).2.1
    simpa using mul_le_mul_of_nonneg_right hc (sq_nonneg (fourierCoeff p h S))
  have hi (i : J) :
      (∑ S ∈ C.filter (fun S => i ∈ S), fourierCoeff p h S ^ 2) ≤
        biasScale p ^ 2 * cubeNormTwo p (lowProjection p k (coordDiff h i)) ^ 2 := by
    rw [lowProjection_norm_sq p k hp hk, Finset.mul_sum]
    let D := (C.filter (fun S => i ∈ S)).image (fun S => S.erase i)
    have he : (∑ S ∈ C.filter (fun S => i ∈ S), fourierCoeff p h S ^ 2) =
        ∑ A ∈ D, biasScale p ^ 2 * fourierCoeffR p (coordDiff h i) A ^ 2 := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro S hS
        have hiS := (Finset.mem_filter.mp hS).2
        have hh := fourierCoeff_insert_eq_biasScale_mul_difference p hp h i
          (S.erase i) (by simp)
        rw [Finset.insert_erase hiS] at hh
        rw [hh, mul_pow]
      · intro S hS T hT he
        have hiS := (Finset.mem_filter.mp hS).2
        have hiT := (Finset.mem_filter.mp hT).2
        change S.erase i = T.erase i at he
        rw [← Finset.insert_erase hiS, ← Finset.insert_erase hiT, he]
    rw [he]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro A hA
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hA
      have hSk := (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, le_trans (by exact_mod_cast Finset.card_erase_le) hSk⟩
    · intro A _ _
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hn (i : J) : cubeNormTwo p (lowProjection p k (coordDiff h i)) ^ 2 ≤
      noiseParameter p ^ (-2 * k) * coordInfluence p h i ^ (3 / 2 : ℝ) := by
    have hb := lowProjection_norm_le p k hp hk (coordDiff h i)
    have hb2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
    rw [mul_pow, coordDiff_norm_fourThirds_sq p hp h i] at hb2
    have he : (noiseParameter p ^ (-k)) ^ 2 = noiseParameter p ^ (-2 * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (noiseParameter_bounds p hp).1.le]
      congr 1
      ring
    rwa [he] at hb2
  calc
    _ ≤ ∑ i : J, ∑ S ∈ C.filter (fun S => i ∈ S), fourierCoeff p h S ^ 2 := hcount
    _ ≤ ∑ i : J, biasScale p ^ 2 * cubeNormTwo p (lowProjection p k (coordDiff h i)) ^ 2 :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ ≤ ∑ i : J, biasScale p ^ 2 *
        (noiseParameter p ^ (-2 * k) * coordInfluence p h i ^ (3 / 2 : ℝ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hn i) (sq_nonneg _))
    _ = _ := by simp_rw [← mul_assoc]; rw [Finset.mul_sum]


-- @node: lem:low
/-- For [a Boolean-valued function h](hyp:h), suppose [the bias p lies strictly
between zero and one](hyp:hp), [the real parameter m is at least two](hyp:hm),
and [each coordinate influence is at most the total coordinate influence
divided by m](hyp:hI). Then [the sum of squared Fourier coefficients at
degrees from one through σ log m / 64 is at most m^(−1/4) times the total
coordinate influence, where σ is the square root of p times one minus p](goal). -/
lemma sum_lowDegree_fourierCoeff_sq_le (p m : ℝ) (h : (J → Bool) → Bool)
    (hp : BiasInterior p) (hm : LowDegreeParam m) (hI : SmallIndividualInfluences p h m) :
    (∑ S ∈ Finset.univ.filter
      (fun S : Finset J => 1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p m), fourierCoeff p h S ^ 2) ≤
      m ^ (-(1 : ℝ) / 4) * totalCoordInfluence p h := by
  classical
  have hm2 : 2 ≤ m := hm
  have hmpos : 0 < m := by linarith
  have hmone : 1 ≤ m := by linarith
  have hIpos : 0 ≤ totalCoordInfluence p h :=
    Finset.sum_nonneg (fun i _ => (coordInfluence_nonneg_le_one p h i).1)
  have hvar : (∑ S ∈ Finset.univ.filter
      (fun S : Finset J => 1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p m),
        fourierCoeff p h S ^ 2) ≤ (biasedLaw J p).Var (boolValue h) := by
    rw [variance_eq_sum_fourierCoeff_sq p hp h]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro S hS
      have hcard := (Finset.mem_filter.mp hS).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        intro he
        simp [he] at hcard⟩
    · intro S _ _
      exact sq_nonneg _
  have hcancel : m ^ (-(1 : ℝ) / 4) * m ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hmpos]
    norm_num
  by_cases hsmall : totalCoordInfluence p h ≤ m ^ (1 / 4 : ℝ)
  · have hcoord (i : J) : coordInfluence p h i ≤ m ^ (-3 / 4 : ℝ) := by
      calc
        _ ≤ totalCoordInfluence p h / m := hI i
        _ ≤ m ^ (1 / 4 : ℝ) / m := div_le_div_of_nonneg_right hsmall hmpos.le
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
    have hpowers : m ^ (1 / 16 : ℝ) * m ^ (-3 / 8 : ℝ) ≤ m ^ (-(1 : ℝ) / 4) := by
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
      _ ≤ 1 * m ^ (-(1 : ℝ) / 4) * totalCoordInfluence p h := by
        apply mul_le_mul_of_nonneg_right _ hIpos
        exact mul_le_mul hs hpowers (mul_nonneg (Real.rpow_nonneg hmpos.le _)
          (Real.rpow_nonneg hmpos.le _)) (by norm_num)
      _ = _ := by rw [one_mul]
  · have hlarge : 1 ≤ m ^ (-(1 : ℝ) / 4) * totalCoordInfluence p h := by
      calc
        1 = m ^ (-(1 : ℝ) / 4) * m ^ (1 / 4 : ℝ) := hcancel.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hsmall))
          (Real.rpow_nonneg hmpos.le _)
    exact le_trans hvar (le_trans (boolean_variance_le_quarter p h)
      (le_trans (by norm_num : (1 / 4 : ℝ) ≤ 1) hlarge))


end Papers.OaiUniformInfluenceHypergraph
