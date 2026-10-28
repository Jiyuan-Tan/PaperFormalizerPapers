module

public import Papers.OaiExactSemidefiniteLift.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Finite Fourier coefficients through degree seven

The fifteen-point sampling formula is used only for degree-seven trigonometric
polynomials, so frequencies from minus seven to seven remain distinct.
-/

@[expose] public section

noncomputable section

namespace Papers.OaiExactSemidefiniteLift

open scoped BigOperators

/-- For [an index k from zero to fourteen](hyp:k) and [a real angle θ](hyp:θ),
[the indexed trigonometric basis value](goal) is [one when k is zero](step:1),
[cosine of ((k + 1)/2)θ when k is odd](step:2), or
[sine of (k/2)θ when k is positive and even](step:3). -/
def trigBasis7 (k : Fin 15) (θ : ℝ) : ℝ :=
  if k.val = 0 then 1
  else if k.val % 2 = 1 then Real.cos (((k.val + 1) / 2 : ℕ) * θ)
  else Real.sin (((k.val + 1) / 2 : ℕ) * θ)

/-- For [a sample index n from zero to fourteen](hyp:n), [the sample angle](goal)
is 2πn/15, giving fifteen equally spaced angles around the circle. -/
def sampleAngle (n : Fin 15) : ℝ := 2 * Real.pi * (n.val : ℝ) / 15


-- @node: trigBasis7_spans
/-- For [a real-valued function f of a real angle](hyp:f),
[f is a trigonometric polynomial of degree at most seven if and only if it is a
real linear combination of the constant function and the cosine and sine functions
at frequencies one through seven](goal). -/
lemma trigBasis7_spans (f : ℝ → ℝ) :
    IsTrigPolyLE 7 f ↔ ∃ c : Fin 15 → ℝ, ∀ θ, f θ = ∑ k, c k * trigBasis7 k θ := by
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨![a 0, a 1, b 1, a 2, b 2, a 3, b 3, a 4, b 4,
      a 5, b 5, a 6, b 6, a 7, b 7], ?_⟩
    intro θ
    rw [h θ]
    simp [Finset.sum_range_succ, Fin.sum_univ_succ, trigBasis7]
    ring
  · rintro ⟨c, h⟩
    refine ⟨fun k => if k = 0 then c 0 else if k = 1 then c 1 else
      if k = 2 then c 3 else if k = 3 then c 5 else if k = 4 then c 7 else
      if k = 5 then c 9 else if k = 6 then c 11 else c 13,
      fun k => if k = 1 then c 2 else if k = 2 then c 4 else
      if k = 3 then c 6 else if k = 4 then c 8 else if k = 5 then c 10 else
      if k = 6 then c 12 else c 14, ?_⟩
    intro θ
    rw [h θ]
    simp [Finset.sum_range_succ, Fin.sum_univ_succ, trigBasis7]
    ring

-- @node: sample_frequency_not_periodic
/-- For [an integer frequency m](hyp:m) that is [nonzero](hyp:hm),
[greater than −15](hyp:hlo), and [less than 15](hyp:hhi), and for
[any integer k](hyp:k), [the phase increment 2πm/15 is not equal to 2πk](goal). -/
lemma sample_frequency_not_periodic (m : ℤ) (hm : m ≠ 0)
    (hlo : -15 < m) (hhi : m < 15) (k : ℤ) :
    (m : ℝ) * (2 * Real.pi / 15) ≠ k * (2 * Real.pi) := by
  intro h
  have he : (m : ℝ) = 15 * (k : ℝ) := by
    nlinarith [Real.pi_pos]
  have hei : m = 15 * k := by exact_mod_cast he
  omega

-- @node: sample_cos_sum
/-- For [an integer frequency m](hyp:m) that is [greater than −15](hyp:hlo) and
[less than 15](hyp:hhi), [the sum of cos(mθ) over the fifteen equally spaced
sample angles is fifteen if m is zero and zero otherwise](goal). -/
lemma sample_cos_sum (m : ℤ) (hlo : -15 < m) (hhi : m < 15) :
    (∑ n : Fin 15, Real.cos ((m : ℝ) * sampleAngle n)) =
      if m = 0 then 15 else 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [if_neg hm]
    have h := Real.sum_cos 15 (sample_frequency_not_periodic m hm hlo hhi) 0
    have hs : Real.sin ((15 : ℝ) * ((m : ℝ) * (2 * Real.pi / 15)) / 2) = 0 := by
      convert Real.sin_int_mul_pi m using 1
      congr 1
      ring
    norm_num only [Nat.cast_ofNat] at h
    rw [hs] at h
    rw [← Fin.sum_univ_eq_sum_range] at h
    simpa [sampleAngle, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using h

-- @node: sample_sin_sum
/-- For [an integer frequency m](hyp:m) that is [greater than −15](hyp:hlo) and
[less than 15](hyp:hhi), [the sum of sin(mθ) over the fifteen equally spaced
sample angles is zero](goal). -/
lemma sample_sin_sum (m : ℤ) (hlo : -15 < m) (hhi : m < 15) :
    (∑ n : Fin 15, Real.sin ((m : ℝ) * sampleAngle n)) = 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · have h := Real.sum_sin 15 (sample_frequency_not_periodic m hm hlo hhi) 0
    have hs : Real.sin ((15 : ℝ) * ((m : ℝ) * (2 * Real.pi / 15)) / 2) = 0 := by
      convert Real.sin_int_mul_pi m using 1
      congr 1
      ring
    norm_num only [Nat.cast_ofNat] at h
    rw [hs] at h
    rw [← Fin.sum_univ_eq_sum_range] at h
    simpa [sampleAngle, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using h

-- @node: sample_cos_cos_sum
/-- For [natural-number frequencies a and b](hyp:a,b), with
[a at least one](hyp:ha), [a at most seven](hyp:ha'),
[b at least one](hyp:hb), and [b at most seven](hyp:hb'),
[the sum of cos(aθ)cos(bθ) over the fifteen equally spaced sample angles is
15/2 when a and b coincide and zero otherwise](goal). -/
lemma sample_cos_cos_sum (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 7)
    (hb : 1 ≤ b) (hb' : b ≤ 7) :
    (∑ n : Fin 15, Real.cos ((a : ℝ) * sampleAngle n) *
      Real.cos ((b : ℝ) * sampleAngle n)) = if a = b then 15 / 2 else 0 := by
  calc
    _ = ((∑ n : Fin 15, Real.cos (((a : ℤ) - b : ℤ) * sampleAngle n)) +
        ∑ n : Fin 15, Real.cos (((a : ℤ) + b : ℤ) * sampleAngle n)) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n _
      simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast, add_mul, sub_mul,
        Real.cos_add, Real.cos_sub]
      ring
    _ = _ := by
      rw [sample_cos_sum _ (by omega) (by omega),
        sample_cos_sum _ (by omega) (by omega)]
      have hpos : (a : ℤ) + b ≠ 0 := by omega
      by_cases hab : a = b <;> simp [hpos, sub_eq_zero, hab, show b ≠ 0 by omega]

-- @node: sample_sin_sin_sum
/-- For [natural-number frequencies a and b](hyp:a,b), with
[a at least one](hyp:ha), [a at most seven](hyp:ha'),
[b at least one](hyp:hb), and [b at most seven](hyp:hb'),
[the sum of sin(aθ)sin(bθ) over the fifteen equally spaced sample angles is
15/2 when a and b coincide and zero otherwise](goal). -/
lemma sample_sin_sin_sum (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 7)
    (hb : 1 ≤ b) (hb' : b ≤ 7) :
    (∑ n : Fin 15, Real.sin ((a : ℝ) * sampleAngle n) *
      Real.sin ((b : ℝ) * sampleAngle n)) = if a = b then 15 / 2 else 0 := by
  calc
    _ = ((∑ n : Fin 15, Real.cos (((a : ℤ) - b : ℤ) * sampleAngle n)) -
        ∑ n : Fin 15, Real.cos (((a : ℤ) + b : ℤ) * sampleAngle n)) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n _
      simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast, add_mul, sub_mul,
        Real.cos_add, Real.cos_sub]
      ring
    _ = _ := by
      rw [sample_cos_sum _ (by omega) (by omega),
        sample_cos_sum _ (by omega) (by omega)]
      have hpos : (a : ℤ) + b ≠ 0 := by omega
      by_cases hab : a = b <;> simp [hpos, sub_eq_zero, hab, show b ≠ 0 by omega]

-- @node: sample_cos_sin_sum
/-- For [natural-number frequencies a and b](hyp:a,b), with
[a at least one](hyp:ha), [a at most seven](hyp:ha'),
[b at least one](hyp:hb), and [b at most seven](hyp:hb'),
[the sum of cos(aθ)sin(bθ) over the fifteen equally spaced sample angles is zero](goal). -/
lemma sample_cos_sin_sum (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 7)
    (hb : 1 ≤ b) (hb' : b ≤ 7) :
    (∑ n : Fin 15, Real.cos ((a : ℝ) * sampleAngle n) *
      Real.sin ((b : ℝ) * sampleAngle n)) = 0 := by
  calc
    _ = ((∑ n : Fin 15, Real.sin (((a : ℤ) + b : ℤ) * sampleAngle n)) -
        ∑ n : Fin 15, Real.sin (((a : ℤ) - b : ℤ) * sampleAngle n)) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n _
      simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast, add_mul, sub_mul,
        Real.sin_add, Real.sin_sub]
      ring
    _ = _ := by
      rw [sample_sin_sum _ (by omega) (by omega),
        sample_sin_sum _ (by omega) (by omega)]
      norm_num

-- @node: sample_sin_cos_sum
/-- For [natural-number frequencies a and b](hyp:a,b), with
[a at least one](hyp:ha), [a at most seven](hyp:ha'),
[b at least one](hyp:hb), and [b at most seven](hyp:hb'),
[the sum of sin(aθ)cos(bθ) over the fifteen equally spaced sample angles is zero](goal). -/
lemma sample_sin_cos_sum (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 7)
    (hb : 1 ≤ b) (hb' : b ≤ 7) :
    (∑ n : Fin 15, Real.sin ((a : ℝ) * sampleAngle n) *
      Real.cos ((b : ℝ) * sampleAngle n)) = 0 := by
  simpa only [mul_comm] using sample_cos_sin_sum b a hb hb' ha ha'

-- @node: sample_cos_nat_sum
/-- For [a natural-number frequency a](hyp:a) that is [at least one](hyp:ha) and
[at most seven](hyp:ha'), [the sum of cos(aθ) over the fifteen equally spaced
sample angles is zero](goal). -/
lemma sample_cos_nat_sum (a : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 7) :
    (∑ n : Fin 15, Real.cos ((a : ℝ) * sampleAngle n)) = 0 := by
  simpa [show a ≠ 0 by omega] using
    sample_cos_sum a (by omega) (by omega)

-- @node: sample_sin_nat_sum
/-- For [a natural-number frequency a](hyp:a) that is [at least one](hyp:ha) and
[at most seven](hyp:ha'), [the sum of sin(aθ) over the fifteen equally spaced
sample angles is zero](goal). -/
lemma sample_sin_nat_sum (a : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 7) :
    (∑ n : Fin 15, Real.sin ((a : ℝ) * sampleAngle n)) = 0 := by
  simpa using sample_sin_sum a (by omega) (by omega)

-- @node: trigBasis7_sample_sum
/-- For [a basis index k from zero to fourteen](hyp:k), [the sum of the kth
trigonometric basis function over the fifteen equally spaced sample angles is
fifteen for the constant function and zero for every sine or cosine function](goal). -/
lemma trigBasis7_sample_sum (k : Fin 15) :
    (∑ n : Fin 15, trigBasis7 k (sampleAngle n)) =
      if k.val = 0 then 15 else 0 := by
  by_cases hk : k.val = 0
  · simp [trigBasis7, hk]
  · have ha : 1 ≤ (k.val + 1) / 2 := by omega
    have hb : (k.val + 1) / 2 ≤ 7 := by omega
    simp only [trigBasis7, if_neg hk]
    split
    · exact sample_cos_nat_sum _ ha hb
    · exact sample_sin_nat_sum _ ha hb

-- @node: discrete_trig_orthogonality
/-- For [two trigonometric basis indices k and l from zero to fourteen](hyp:k,l),
[the sum of the products of their basis values over the fifteen equally spaced
sample angles, multiplied by 1/15 if k is zero and by 2/15 otherwise, equals one
when the indices coincide and zero otherwise](goal). -/
lemma discrete_trig_orthogonality (k l : Fin 15) :
    (if k.val = 0 then (1 / 15 : ℝ) else 2 / 15) *
      (∑ n : Fin 15, trigBasis7 l (sampleAngle n) * trigBasis7 k (sampleAngle n)) =
        if k = l then 1 else 0 := by
  have hz (θ : ℝ) : trigBasis7 0 θ = 1 := rfl
  by_cases hk : k.val = 0
  · have hk' : k = 0 := Fin.ext hk
    subst k
    simp only [hz, mul_one, Fin.val_zero, ite_true, trigBasis7_sample_sum]
    by_cases hl : l.val = 0
    · have hl' : l = 0 := Fin.ext hl
      simp [hl']
    · have hl' : (0 : Fin 15) ≠ l := by intro h; subst l; contradiction
      simp [hl, hl']
  · by_cases hl : l.val = 0
    · have hl' : l = 0 := Fin.ext hl
      subst l
      have hk' : k ≠ 0 := by intro h; subst k; contradiction
      simp [hz, hk, hk', trigBasis7_sample_sum]
    · have hka : 1 ≤ (k.val + 1) / 2 := by omega
      have hkb : (k.val + 1) / 2 ≤ 7 := by omega
      have hla : 1 ≤ (l.val + 1) / 2 := by omega
      have hlb : (l.val + 1) / 2 ≤ 7 := by omega
      by_cases hko : k.val % 2 = 1 <;> by_cases hlo : l.val % 2 = 1
      · have he : (l.val + 1) / 2 = (k.val + 1) / 2 ↔ k = l := by
          constructor
          · intro h; apply Fin.ext; omega
          · intro h; subst l; rfl
        simp only [trigBasis7, if_neg hk, if_neg hl, if_pos hko, if_pos hlo]
        rw [sample_cos_cos_sum _ _ hla hlb hka hkb]
        by_cases h : k = l <;> simp [he, h]
      · have he : k ≠ l := by intro h; subst l; contradiction
        simp only [trigBasis7, if_neg hk, if_neg hl, if_pos hko, if_neg hlo]
        rw [sample_sin_cos_sum _ _ hla hlb hka hkb]
        simp [he]
      · have he : k ≠ l := by intro h; subst l; contradiction
        simp only [trigBasis7, if_neg hk, if_neg hl, if_neg hko, if_pos hlo]
        rw [sample_cos_sin_sum _ _ hla hlb hka hkb]
        simp [he]
      · have he : (l.val + 1) / 2 = (k.val + 1) / 2 ↔ k = l := by
          constructor
          · intro h; apply Fin.ext; omega
          · intro h; subst l; rfl
        simp only [trigBasis7, if_neg hk, if_neg hl, if_neg hko, if_neg hlo]
        rw [sample_sin_sin_sum _ _ hla hlb hka hkb]
        by_cases h : k = l <;> simp [he, h]

-- @node: trigBasis7_coefficient_recovery
/-- For [fifteen real coefficients c](hyp:c) and [a basis index k from zero to
fourteen](hyp:k), [the kth coefficient is recovered by summing the product of
the corresponding trigonometric polynomial and the kth basis function over the
fifteen equally spaced sample angles, then multiplying by 1/15 for the constant
term or 2/15 for a sine or cosine term](goal). -/
lemma trigBasis7_coefficient_recovery (c : Fin 15 → ℝ) (k : Fin 15) :
    (if k.val = 0 then (1 / 15 : ℝ) else 2 / 15) *
      (∑ n : Fin 15, (∑ l : Fin 15, c l * trigBasis7 l (sampleAngle n)) *
        trigBasis7 k (sampleAngle n)) = c k := by
  calc
    _ = ∑ l : Fin 15, c l *
        ((if k.val = 0 then (1 / 15 : ℝ) else 2 / 15) *
          ∑ n : Fin 15, trigBasis7 l (sampleAngle n) *
            trigBasis7 k (sampleAngle n)) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = c k := by
      simp_rw [discrete_trig_orthogonality]
      simp

-- @node: trigBasis7_independent
/-- [The constant function and the cosine and sine functions at frequencies one
through seven are linearly independent over the real numbers: a real linear
combination that vanishes at every angle has all coefficients zero](goal). -/
lemma trigBasis7_independent : LinearIndependent ℝ trigBasis7 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hz (θ : ℝ) : (∑ l : Fin 15, c l * trigBasis7 l θ) = 0 := by
    simpa using congrFun hc θ
  have h := trigBasis7_coefficient_recovery c k
  simpa [hz] using h.symm

end Papers.OaiExactSemidefiniteLift
