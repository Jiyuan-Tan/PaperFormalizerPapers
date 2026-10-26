module
public import Papers.OaiMetricMarkovCotype.TMain
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Complex scalars via interleaving real and imaginary coordinates -/

@[expose] public section

noncomputable section
namespace Papers.OaiMetricMarkovCotype

/-- For [an absolutely summable complex sequence x](hyp:x) and [a zero-based
coordinate index k](hyp:k), [the interleaved real coordinate](goal) is the real
part of entry k divided by two, rounded down, when k is even, and the imaginary
part of that entry when k is odd. -/
-- @node: realificationCoordinate
def realificationCoordinate (x : ComplexEllOne) (k : ℕ) : ℝ :=
  if k % 2 = 0 then (x (k / 2)).re else (x (k / 2)).im

-- @node: realification_memℓp
/-- [Interleaving the real and imaginary parts of an absolutely summable
complex sequence gives an absolutely summable real sequence](goal). -/
lemma realification_memℓp (x : ComplexEllOne) : Memℓp (realificationCoordinate x) 1 := by
  have hx : Summable (fun k => ‖x k‖) := by
    simpa using (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)
  have hr : Summable (fun k => ‖(x k).re‖) :=
    hx.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => Complex.abs_re_le_norm (x k))
  have hi : Summable (fun k => ‖(x k).im‖) :=
    hx.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => Complex.abs_im_le_norm (x k))
  apply memℓp_gen
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.even_add_odd
  · simpa [realificationCoordinate, Nat.mul_div_right] using hr
  · simpa [realificationCoordinate, Nat.add_div, Nat.mul_div_right] using hi

/-- For [an absolutely summable complex sequence x](hyp:x), [its realification](goal)
is the absolutely summable real sequence with real parts in the even positions
and imaginary parts in the odd positions, indexing from zero.
@realizes J(realification with even real parts and odd imaginary parts) -/
-- @node: realification
def realification (x : ComplexEllOne) : RealEllOne :=
  ⟨realificationCoordinate x, realification_memℓp x⟩

-- @node: complexificationCoordinate
/-- For [an absolutely summable real sequence x](hyp:x) and [a zero-based
index k](hyp:k), [the k-th complexified coordinate](goal) has real part equal
to entry 2k of x and imaginary part equal to entry 2k + 1. -/
def complexificationCoordinate (x : RealEllOne) (k : ℕ) : ℂ :=
  ⟨x (2 * k), x (2 * k + 1)⟩

-- @node: complexification_memℓp
/-- [Pairing successive entries of an absolutely summable real sequence as
real and imaginary parts gives an absolutely summable complex sequence](goal). -/
lemma complexification_memℓp (x : RealEllOne) : Memℓp (complexificationCoordinate x) 1 := by
  have hx : Summable (fun k => ‖x k‖) := by
    simpa using (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)
  have he := hx.comp_injective (show Function.Injective (fun k : ℕ => 2 * k) by
    intro a b h; dsimp at h; omega)
  have ho := hx.comp_injective (show Function.Injective (fun k : ℕ => 2 * k + 1) by
    intro a b h; dsimp at h; omega)
  apply memℓp_gen
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact (he.add ho).of_nonneg_of_le (fun _ => norm_nonneg _) (fun k =>
    Complex.norm_le_abs_re_add_abs_im (complexificationCoordinate x k))

-- @node: complexification
/-- For [an absolutely summable real sequence x](hyp:x), [its complexification](goal)
is the absolutely summable complex sequence formed by pairing entries 2k and
2k + 1 as the real and imaginary parts of entry k, indexing from zero. -/
def complexification (x : RealEllOne) : ComplexEllOne :=
  ⟨complexificationCoordinate x, complexification_memℓp x⟩

-- @node: realification_real_linear
/-- For any real scalar and two absolutely summable complex sequences,
[realifying the scalar multiple of the first sequence plus the second equals
the same scalar multiple of the first realification plus the second
realification](goal). -/
lemma realification_real_linear (r : ℝ) (x y : ComplexEllOne) :
    realification (r • x + y) = r • realification x + realification y := by
  apply Subtype.ext
  funext k
  change realificationCoordinate (r • x + y) k =
    r * realificationCoordinate x k + realificationCoordinate y k
  unfold realificationCoordinate
  split_ifs
  · change (r • x (k / 2) + y (k / 2)).re = _
    simp
  · change (r • x (k / 2) + y (k / 2)).im = _
    simp

-- @node: complex_abs_parts_le
/-- For any complex number, [the sum of the absolute values of its real and
imaginary parts is at most the square root of two times its modulus](goal). -/
lemma complex_abs_parts_le (z : ℂ) : |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := by
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply] at hn
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have ha := sq_nonneg (|z.re| - |z.im|)
  have hr := sq_abs z.re
  have hi := sq_abs z.im
  have hp : 0 ≤ Real.sqrt 2 * ‖z‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (sq_le_sq₀ (by positivity) hp).mp
  rw [mul_pow, hs]
  nlinarith only [hn, ha, hr, hi]

-- @node: realification_norm_eq
/-- For any absolutely summable complex sequence, [the ℓ₁ norm of its
realification equals the sum, over all entries, of the absolute values of
the real and imaginary parts](goal). -/
lemma realification_norm_eq (x : ComplexEllOne) :
    ‖realification x‖ = ∑' k, (|(x k).re| + |(x k).im|) := by
  have hx : Summable (fun k => ‖x k‖) := by
    simpa using (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)
  have hr : Summable (fun k => |(x k).re|) :=
    hx.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => Complex.abs_re_le_norm (x k))
  have hi : Summable (fun k => |(x k).im|) :=
    hx.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => Complex.abs_im_le_norm (x k))
  have he : Summable (fun k => ‖realification x (2 * k)‖) := by
    simpa [realification, realificationCoordinate] using hr
  have ho : Summable (fun k => ‖realification x (2 * k + 1)‖) := by
    simpa [realification, realificationCoordinate, Nat.add_div] using hi
  have hn : ‖realification x‖ = ∑' k, ‖realification x k‖ := by
    simpa using lp.norm_eq_tsum_rpow
      (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal) (realification x)
  have hsplit := tsum_even_add_odd (f := fun k => ‖realification x k‖) he ho
  have hparts : (∑' k, |(x k).re|) + (∑' k, |(x k).im|) =
      ∑' k, ‖realification x k‖ := by
    simpa [realification, realificationCoordinate, Nat.add_div] using hsplit
  exact hn.trans (hparts.symm.trans (hr.tsum_add hi).symm)

-- @node: realification_norm_bounds
/-- For any absolutely summable complex sequence, [the ℓ₁ norm of its
realification lies between its original ℓ₁ norm and the square root of two
times that norm](goal). -/
lemma realification_norm_bounds (x : ComplexEllOne) :
    ‖x‖ ≤ ‖realification x‖ ∧ ‖realification x‖ ≤ Real.sqrt 2 * ‖x‖ := by
  have hx : Summable (fun k => ‖x k‖) := by
    simpa using (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)
  have hr : Summable (fun k => |(x k).re|) :=
    hx.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => Complex.abs_re_le_norm (x k))
  have hi : Summable (fun k => |(x k).im|) :=
    hx.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => Complex.abs_im_le_norm (x k))
  have hn : ‖x‖ = ∑' k, ‖x k‖ := by
    simpa using lp.norm_eq_tsum_rpow
      (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal) x
  rw [realification_norm_eq, hn]
  constructor
  · exact hx.tsum_le_tsum (fun k => Complex.norm_le_abs_re_add_abs_im (x k)) (hr.add hi)
  · calc
      (∑' k, (|(x k).re| + |(x k).im|)) ≤ ∑' k, Real.sqrt 2 * ‖x k‖ :=
        (hr.add hi).tsum_le_tsum (fun k => complex_abs_parts_le (x k)) (hx.mul_left _)
      _ = Real.sqrt 2 * ∑' k, ‖x k‖ := tsum_mul_left

-- @node: complexification_realification
/-- [Complexifying the realification of an absolutely summable complex
sequence recovers the original sequence](goal). -/
lemma complexification_realification (x : ComplexEllOne) :
    complexification (realification x) = x := by
  apply Subtype.ext
  funext k
  apply Complex.ext <;>
    simp [complexification, complexificationCoordinate, realification,
      realificationCoordinate, Nat.add_div, Nat.mul_div_right]

-- @node: realification_complexification
/-- [Realifying the complexification of an absolutely summable real sequence
recovers the original sequence](goal). -/
lemma realification_complexification (x : RealEllOne) :
    realification (complexification x) = x := by
  apply Subtype.ext
  funext k
  change realificationCoordinate (complexification x) k = x k
  unfold realificationCoordinate
  split_ifs with h
  · have hk : 2 * (k / 2) = k := by omega
    simpa [complexification, complexificationCoordinate, hk]
  · have hk : 2 * (k / 2) + 1 = k := by omega
    simpa [complexification, complexificationCoordinate, hk]

-- @node: realification_bijective
/-- [Realification is a one-to-one correspondence between absolutely summable
complex sequences and absolutely summable real sequences](goal). -/
lemma realification_bijective : Function.Bijective realification :=
  ⟨Function.LeftInverse.injective complexification_realification,
    Function.RightInverse.surjective realification_complexification⟩

-- @node: realification_sub
/-- For two absolutely summable complex sequences, [realifying their difference
equals the difference of their realifications](goal). -/
lemma realification_sub (x y : ComplexEllOne) :
    realification (x - y) = realification x - realification y := by
  simpa [sub_eq_add_neg, add_comm] using realification_real_linear (-1) y x

-- @node: realification_dist_sq_bounds
/-- For any two absolutely summable complex sequences, [the squared ℓ₁ distance
between their realifications lies between their original squared ℓ₁ distance
and twice that distance](goal). -/
lemma realification_dist_sq_bounds (x y : ComplexEllOne) :
    dist x y ^ 2 ≤ dist (realification x) (realification y) ^ 2 ∧
    dist (realification x) (realification y) ^ 2 ≤ 2 * dist x y ^ 2 := by
  have h := realification_norm_bounds (x - y)
  rw [realification_sub] at h
  simp only [dist_eq_norm]
  constructor
  · exact pow_le_pow_left₀ (norm_nonneg _) h.1 2
  · calc
      ‖realification x - realification y‖ ^ 2 ≤ (Real.sqrt 2 * ‖x - y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h.2 2
      _ = 2 * ‖x - y‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]

-- @node: hasMetricMarkovCotypeTwo_complex_of_real
/-- If [real ℓ₁ has metric Markov cotype two with constant C](hyp:hC), then
[complex ℓ₁ has metric Markov cotype two with constant the square root of two
times C](goal). -/
lemma hasMetricMarkovCotypeTwo_complex_of_real (C : ℝ)
    (hC : HasMetricMarkovCotypeTwo RealEllOne C) :
    HasMetricMarkovCotypeTwo ComplexEllOne (Real.sqrt 2 * C) := by
  classical
  constructor
  intro n t hn ht π A hπ hA hrev x
  obtain ⟨y, hy⟩ := hC.cotype_condition n t hn ht π A hπ hA hrev
    (fun i => realification (x i))
  refine ⟨fun i => complexification (y i), ?_⟩
  have hπ0 : ∀ i, 0 ≤ π i := hπ.1
  have hpull (a b : RealEllOne) :
      dist (complexification a) (complexification b) ^ 2 ≤ dist a b ^ 2 := by
    simpa only [realification_complexification] using
      (realification_dist_sq_bounds (complexification a) (complexification b)).1
  have hfirst : (∑ i, π i * dist (x i) (complexification (y i)) ^ 2) ≤
      ∑ i, π i * dist (realification (x i)) (y i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hπ0 i)
    simpa only [realification_complexification] using
      (realification_dist_sq_bounds (x i) (complexification (y i))).1
  have hsecond : (∑ i, ∑ j, π i * A i j *
      dist (complexification (y i)) (complexification (y j)) ^ 2) ≤
      ∑ i, ∑ j, π i * A i j * dist (y i) (y j) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hpull _ _) (mul_nonneg (hπ0 i) (hA.nonneg i j))
  have havg (i j : Fin n) :
      0 ≤ (((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, A ^ s) i j) := by
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun s _ => Matrix.pow_apply_nonneg hA.nonneg s i j
  have hright :
      (∑ i, ∑ j, π i * (((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, A ^ s) i j) *
        dist (realification (x i)) (realification (x j)) ^ 2) ≤
      2 * ∑ i, ∑ j, π i * (((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, A ^ s) i j) *
        dist (x i) (x j) ^ 2 := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_left (realification_dist_sq_bounds (x i) (x j)).2
      (mul_nonneg (hπ0 i) (havg i j))
    nlinarith only [h]
  calc
    _ ≤ (∑ i, π i * dist (realification (x i)) (y i) ^ 2) +
        (t : ℝ) * ∑ i, ∑ j, π i * A i j * dist (y i) (y j) ^ 2 :=
      add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ ≤ _ := hy
    _ ≤ C ^ 2 * (2 * ∑ i, ∑ j, π i *
        (((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, A ^ s) i j) * dist (x i) (x j) ^ 2) :=
      mul_le_mul_of_nonneg_left hright (sq_nonneg C)
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring

-- @node: thm:complex
/-- [The metric Markov cotype two constant of complex ℓ₁ is at most twelve
times the square root of forty-two](goal). -/
theorem metricMarkovCotypeConstant_complexEllOne_le :
    metricMarkovCotypeConstant ComplexEllOne ≤ ENNReal.ofReal (12 * Real.sqrt 42) := by
  have hC := hasMetricMarkovCotypeTwo_complex_of_real (12 * Real.sqrt 21)
    hasMetricMarkovCotypeTwo_realEllOne
  have heq : Real.sqrt 2 * (12 * Real.sqrt 21) = 12 * Real.sqrt 42 := by
    rw [show (42 : ℝ) = 2 * 21 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [heq] at hC
  exact iInf_le_of_le (12 * Real.sqrt 42)
    (iInf_le_of_le (by positivity) (iInf_le_of_le hC le_rfl))

end Papers.OaiMetricMarkovCotype
