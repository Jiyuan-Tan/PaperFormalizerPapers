module

public import Mathlib.MeasureTheory.Integral.Pi
public import Papers.HawkesD75660b.Helpers.Duration
public import Papers.HawkesD75660b.T1

/-! The fixed-size reciprocal means and the Borel duration series. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Papers.HawkesD75660b

-- @node: expMeasure_density_first_moment
/-- If [the rate r is positive](hyp:hr), [multiplying the exponential density at x by x gives the gamma density with shape two and rate r, divided by r](goal). -/
lemma expMeasure_density_first_moment {r : ℝ} (hr : 0 < r) (x : ℝ) :
    x * (gammaPDF 1 r x).toReal = r⁻¹ * (gammaPDF 2 r x).toReal := by
  rw [gammaPDF, gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr x),
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg (by norm_num) hr x)]
  unfold gammaPDFReal
  split_ifs with hx
  · simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero,
      mul_one, Real.rpow_two]
    norm_num [Real.Gamma_add_one, Real.Gamma_one]
    field_simp
  · simp

-- @node: expMeasure_first_moment
/-- If [the rate r is positive](hyp:hr), [the exponential distribution with rate r has an integrable value and mean 1/r](goal). -/
lemma expMeasure_first_moment {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) ∧
      (∫ x : ℝ, x ∂expMeasure r) = 1 / r := by
  have hm (a : ℝ) : Measurable (gammaPDF a r) := by
    unfold gammaPDF
    fun_prop
  have ht (a : ℝ) : ∀ᵐ x ∂volume, gammaPDF a r x < ⊤ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  have hi : Integrable (fun x => (gammaPDF 2 r x).toReal) :=
    integrable_toReal_of_lintegral_ne_top (hm 2).aemeasurable
      (by rw [lintegral_gammaPDF_eq_one (by norm_num) hr]; exact ENNReal.one_ne_top)
  have he : (∫ x, (gammaPDF 2 r x).toReal) = 1 := by
    rw [integral_toReal (hm 2).aemeasurable (ht 2),
      lintegral_gammaPDF_eq_one (by norm_num) hr, ENNReal.toReal_one]
  constructor
  · change Integrable (fun x : ℝ => x) (volume.withDensity (gammaPDF 1 r))
    rw [integrable_withDensity_iff (hm 1) (ht 1)]
    simpa only [expMeasure_density_first_moment hr] using hi.const_mul r⁻¹
  · change (∫ x : ℝ, x ∂volume.withDensity (gammaPDF 1 r)) = _
    rw [integral_withDensity_eq_integral_toReal_smul (hm 1) (ht 1)]
    simp_rw [smul_eq_mul, mul_comm ((gammaPDF 1 r _).toReal),
      expMeasure_density_first_moment hr]
    rw [integral_const_mul, he, mul_one, one_div]

-- @node: countGapMeasure_coordinate_moment
/-- If [κ is a valid preference count vector](hyp:hκ), [gap a is integrable under the conditional gap distribution and has mean equal to the reciprocal of its gap rate](goal). -/
lemma countGapMeasure_coordinate_moment {n : ℕ} {κ : CountVector n}
    (hκ : PreferenceCounts κ) (a : Fin n) :
    Integrable (fun z : GapVector n => (z a : ℝ)) (countGapMeasure κ) ∧
      (∫ z : GapVector n, (z a : ℝ) ∂countGapMeasure κ) = 1 / gapRate κ a := by
  have hp (b : Fin n) : IsProbabilityMeasure (expMeasure (gapRate κ b)) :=
    isProbabilityMeasure_expMeasure (gapRate_pos hκ b)
  have hcoord := expMeasure_first_moment (gapRate_pos hκ a)
  have hmap := countGapMeasure_joint_law hκ
  have hm : Measurable (fun z : GapVector n => fun b => (z b : ℝ)) := by fun_prop
  constructor
  · have hi := integrable_comp_eval (μ := fun b => expMeasure (gapRate κ b)) hcoord.1
    rw [← hmap] at hi
    exact hi.comp_aemeasurable hm.aemeasurable
  · calc
      (∫ z : GapVector n, (z a : ℝ) ∂countGapMeasure κ) =
          ∫ z : Fin n → ℝ, z a ∂(countGapMeasure κ).map
            (fun z b => (z b : ℝ)) :=
        (integral_map (f := fun z : Fin n → ℝ => z a) hm.aemeasurable
          (measurable_pi_apply a).aestronglyMeasurable).symm
      _ = 1 / gapRate κ a := by
        rw [hmap, integral_eval]
        exact hcoord.2

-- @node: preferenceCountMass_nonneg
/-- [The preference count mass assigned to any count vector κ of length n is nonnegative](goal). -/
lemma preferenceCountMass_nonneg (n : ℕ) (κ : CountVector n) :
    0 ≤ preferenceCountMass n κ := by
  unfold preferenceCountMass
  split_ifs <;> positivity

-- @node: preferenceCountMeasure_integral
/-- [The integral of f under the preference count distribution of length n equals the finite sum of f at each vector with entries from zero through n, weighted by that vector's preference count mass](goal). -/
lemma preferenceCountMeasure_integral (n : ℕ) (f : CountVector n → ℝ) :
    (∫ κ, f κ ∂preferenceCountMeasure n) =
      ∑ k : Fin n → Fin (n + 1),
        preferenceCountMass n (fun a => (k a).val) * f (fun a => (k a).val) := by
  classical
  unfold preferenceCountMeasure
  rw [integral_finsetSum_measure]
  · simp_rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (preferenceCountMass_nonneg n _)]
  · intro k hk
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

-- @node: preferenceCountMeasure_integrable
/-- [Every real-valued function on count vectors of length n is integrable under the preference count distribution](goal). -/
lemma preferenceCountMeasure_integrable (n : ℕ) (f : CountVector n → ℝ) :
    Integrable f (preferenceCountMeasure n) := by
  classical
  unfold preferenceCountMeasure
  exact integrable_finsetSum_measure.mpr (fun k _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)

-- @node: duration_reciprocal_mean_bounds
/-- If [m is smaller than the count vector length n](hyp:hm), [the expected reciprocal of the cumulative count through position m + 1 minus m lies between zero and one under the preference count distribution](goal). -/
lemma duration_reciprocal_mean_bounds {n m : ℕ} (hm : m < n) :
    0 ≤ (∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n) ∧
      (∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n) ≤ 1 := by
  have hp := preferenceCountMeasure_supported n
  have hb : ∀ᵐ κ ∂preferenceCountMeasure n,
      0 ≤ 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∧
        1 / ((prefixCount κ (m + 1) : ℝ) - m) ≤ 1 := by
    filter_upwards [hp] with κ hκ
    have hprefix := hκ.prefix (m + 1) (by omega) (by omega)
    have hprefix' : (m : ℝ) + 1 ≤ (prefixCount κ (m + 1) : ℝ) := by
      exact_mod_cast hprefix
    have hd : 1 ≤ (prefixCount κ (m + 1) : ℝ) - m := by linarith
    exact ⟨by positivity, by simpa using one_div_le_one_div_of_le (by norm_num) hd⟩
  have := preferenceCountMeasure_probability n
  constructor
  · exact integral_nonneg_of_ae (hb.mono fun κ hκ => hκ.1)
  · calc
      _ ≤ ∫ _ : CountVector n, (1 : ℝ) ∂preferenceCountMeasure n :=
        integral_mono_ae (preferenceCountMeasure_integrable n _) (integrable_const _)
          (hb.mono fun κ hκ => hκ.2)
      _ = 1 := by simp

-- @node: countGapMeasure_sum_moment
/-- If [κ is a valid preference count vector](hyp:hκ), [the sum of the gaps is integrable under its conditional gap distribution, with mean equal to the sum of the reciprocal gap rates](goal). -/
lemma countGapMeasure_sum_moment {n : ℕ} {κ : CountVector n}
    (hκ : PreferenceCounts κ) :
    Integrable (fun z : GapVector n => ((∑ a, z a : ℝ≥0) : ℝ)) (countGapMeasure κ) ∧
      (∫ z : GapVector n, ((∑ a, z a : ℝ≥0) : ℝ) ∂countGapMeasure κ) =
        ∑ a, 1 / gapRate κ a := by
  simp only [NNReal.coe_sum]
  constructor
  · exact integrable_finsetSum _ (fun a _ => (countGapMeasure_coordinate_moment hκ a).1)
  · rw [integral_finsetSum _ (fun a _ => (countGapMeasure_coordinate_moment hκ a).1)]
    exact Finset.sum_congr rfl (fun a _ => (countGapMeasure_coordinate_moment hκ a).2)

-- @node: durationComponent_integrable
/-- [The sum of the n gaps is integrable under the duration component distribution of size n](goal). -/
lemma durationComponent_integrable (n : ℕ) :
    Integrable (fun q : CountVector n × GapVector n => ((∑ a, q.2 a : ℝ≥0) : ℝ))
      (durationComponentMeasure n) := by
  classical
  unfold durationComponentMeasure
  apply integrable_finsetSum_measure.mpr
  intro k hk
  by_cases hκ : PreferenceCounts (fun a => (k a).val)
  · apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    exact (countGapMeasure_sum_moment hκ).1
  · simp [preferenceCountMass, hκ]

-- @node: durationComponent_mean
/-- [The mean total gap under the duration component distribution of size n is the sum, over stages m from zero through n − 1, of the expected reciprocal of the cumulative preference count through m + 1 minus m](goal). -/
lemma durationComponent_mean (n : ℕ) :
    (∫ q, ((∑ a, q.2 a : ℝ≥0) : ℝ) ∂durationComponentMeasure n) =
      ∑ m ∈ Finset.range n,
        ∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n := by
  classical
  have hi := durationComponent_integrable n
  unfold durationComponentMeasure at hi ⊢
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hi)]
  simp_rw [integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal (preferenceCountMass_nonneg n _)]
  have hterm (k : Fin n → Fin (n + 1)) :
      preferenceCountMass n (fun a => (k a).val) *
        (∫ q : CountVector n × GapVector n, ((∑ a, q.2 a : ℝ≥0) : ℝ)
          ∂(countGapMeasure (fun a => (k a).val)).map
            (fun z => (fun a => (k a).val, z))) =
      preferenceCountMass n (fun a => (k a).val) *
        ∑ a : Fin n, 1 / gapRate (fun a => (k a).val) a := by
    by_cases hκ : PreferenceCounts (fun a => (k a).val)
    · congr 1
      rw [integral_map (by fun_prop) (by fun_prop)]
      exact (countGapMeasure_sum_moment hκ).2
    · simp [preferenceCountMass, hκ]
  simp_rw [hterm, preferenceCountMeasure_integral]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hrate (a : Fin n) : gapRate (fun a => (k a).val) a =
      (prefixCount (fun a => (k a).val) (a.val + 1) : ℝ) - a.val := by
    unfold gapRate
    ring
  simp_rw [Finset.mul_sum, hrate]
  exact Fin.sum_univ_eq_sum_range (fun m : ℕ =>
    preferenceCountMass n (fun a => (k a).val) *
      (1 / ((prefixCount (fun a => (k a).val) (m + 1) : ℝ) - m))) n

-- @node: canonical_reciprocal_mean_solution
/-- If [m is smaller than n](hyp:hm), [the expected reciprocal of the cumulative preference count through m + 1 minus m equals (n + 1)/(n − m), less 1/(n − m) times the sum over i from zero through m of the binomial coefficient choosing i from n, multiplied by ((i + 1)/(n + 1)) to power i − 1 and ((n − i)/(n + 1)) to power n − i](goal). -/
lemma canonical_reciprocal_mean_solution {n m : ℕ} (hm : m < n) :
    (∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n) =
      (n + 1 : ℝ) / ((n : ℝ) - m) -
        (1 / ((n : ℝ) - m)) * ∑ i ∈ Finset.range (m + 1),
          (Nat.choose n i : ℝ) * (((i + 1 : ℝ) / (n + 1 : ℝ)) ^ ((i : ℤ) - 1)) *
            (((n : ℝ) - i) / (n + 1 : ℝ)) ^ (n - i) := by
  have := preferenceCountMeasure_probability n
  have hnat : Set.range (Int.ofNat : ℕ → ℤ) = Set.Ici 0 := by
    ext z
    constructor
    · rintro ⟨k, rfl⟩
      exact Int.natCast_nonneg k
    · intro hz
      exact ⟨z.toNat, Int.toNat_of_nonneg hz⟩
  exact meanRecurrenceSolution (preferenceCountMeasure n) id m
    ⟨by omega, hm⟩ HasLaw.id hnat ⟨by omega, hm⟩ hnat

-- @node: reciprocal_tail_harmonic
/-- [The sum of 1/(n − m) over integers m from i through n − 1 equals the harmonic number of n − i, with both sides zero when i exceeds n](goal). -/
lemma reciprocal_tail_harmonic (n i : ℕ) :
    (∑ m ∈ Finset.Ico i n, 1 / ((n : ℝ) - m)) = harmonicNumber (n - i) := by
  rw [Finset.sum_Ico_eq_sum_range]
  calc
    _ = ∑ k ∈ Finset.range (n - i),
        (1 / (((n - i - 1 - k) + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have heq : n - i - 1 - k + 1 = n - (i + k) := by omega
      rw [heq, Nat.cast_sub (by omega : i + k ≤ n)]
    _ = ∑ k ∈ Finset.range (n - i), 1 / ((k + 1 : ℕ) : ℝ) :=
      Finset.sum_range_reflect (fun k => 1 / ((k + 1 : ℕ) : ℝ)) (n - i)
    _ = harmonicNumber (n - i) := by
      simp [harmonicNumber, harmonic]

-- @node: duration_fixed_size_harmonic
/-- [The sum of the n expected reciprocal cumulative count surpluses equals (n + 1) times the nth harmonic number, less the sum over i from zero through n − 1 of the harmonic number of n − i weighted by the binomial coefficient choosing i from n, ((i + 1)/(n + 1)) to power i − 1, and ((n − i)/(n + 1)) to power n − i](goal). -/
lemma duration_fixed_size_harmonic (n : ℕ) :
    (∑ m ∈ Finset.range n,
      ∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n) =
      (n + 1 : ℝ) * harmonicNumber n -
        ∑ i ∈ Finset.range n,
          ((Nat.choose n i : ℝ) * (((i + 1 : ℝ) / (n + 1 : ℝ)) ^ ((i : ℤ) - 1)) *
            (((n : ℝ) - i) / (n + 1 : ℝ)) ^ (n - i)) * harmonicNumber (n - i) := by
  let A : ℕ → ℝ := fun i =>
    (Nat.choose n i : ℝ) * (((i + 1 : ℝ) / (n + 1 : ℝ)) ^ ((i : ℤ) - 1)) *
      (((n : ℝ) - i) / (n + 1 : ℝ)) ^ (n - i)
  have hsol : (∑ m ∈ Finset.range n,
      ∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n) =
      (n + 1 : ℝ) * (∑ m ∈ Finset.range n, 1 / ((n : ℝ) - m)) -
        ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range (m + 1),
          A i * (1 / ((n : ℝ) - m)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [canonical_reciprocal_mean_solution (Finset.mem_range.mp hm)]
    simp only [← Finset.sum_mul, div_eq_mul_inv, one_mul, A]
    ring
  rw [hsol]
  have hlead : (∑ m ∈ Finset.range n, 1 / ((n : ℝ) - m)) = harmonicNumber n := by
    simpa using reciprocal_tail_harmonic n 0
  rw [hlead]
  congr 1
  calc
    _ = ∑ i ∈ Finset.range n, ∑ m ∈ Finset.Ico i n,
        A i * (1 / ((n : ℝ) - m)) := by
      simpa only [Nat.Ico_zero_eq_range] using
        (Finset.sum_Ico_Ico_comm 0 n (fun i m => A i * (1 / ((n : ℝ) - m)))).symm
    _ = ∑ i ∈ Finset.range n, A i * harmonicNumber (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum, reciprocal_tail_harmonic]

-- @node: borelMass_succ_zpow
/-- For [a nonnegative branching parameter ρ](hyp:ρ), [the Borel mass at n + 1 equals exp(−ρ(n + 1)) times ρ to power n times (n + 1) to integer power n − 1, divided by n factorial](goal). -/
lemma borelMass_succ_zpow (ρ : ℝ≥0) (n : ℕ) :
    borelMass ρ (n + 1) = Real.exp (-(ρ : ℝ) * (n + 1)) * (ρ : ℝ) ^ n *
      (n + 1 : ℝ) ^ ((n : ℤ) - 1) / Nat.factorial n := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hp : (n + 1 : ℝ) ^ n =
      (n + 1 : ℝ) * (n + 1 : ℝ) ^ ((n : ℤ) - 1) := by
    rw [← zpow_one_add₀ hn]
    rw [show (1 : ℤ) + ((n : ℤ) - 1) = (n : ℤ) by ring, zpow_natCast]
  simp only [borelMass, Nat.succ_ne_zero, if_false,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_pow, Nat.factorial_succ,
    Nat.cast_mul]
  rw [hp]
  field_simp

-- @node: borel_meanCorrection_factor
/-- For [a nonnegative branching parameter ρ](hyp:ρ), if [i is smaller than n](hyp:hi), [the Borel mass at n + 1 times the correction weight given by the binomial coefficient choosing i from n, ((i + 1)/(n + 1)) to power i − 1, and ((n − i)/(n + 1)) to power n − i equals ρ times the Borel masses at i + 1 and n − i times n − i](goal). -/
lemma borel_meanCorrection_factor (ρ : ℝ≥0) {n i : ℕ} (hi : i < n) :
    borelMass ρ (n + 1) *
      ((Nat.choose n i : ℝ) * (((i + 1 : ℝ) / (n + 1 : ℝ)) ^ ((i : ℤ) - 1)) *
        (((n : ℝ) - i) / (n + 1 : ℝ)) ^ (n - i)) =
      (ρ : ℝ) * borelMass ρ (i + 1) * borelMass ρ (n - i) * (n - i : ℕ) := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hnfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hifac : (Nat.factorial i : ℝ) ≠ 0 := by positivity
  have hkfac : (Nat.factorial (n - i) : ℝ) ≠ 0 := by positivity
  have hk : n - i ≠ 0 := by omega
  have he : Real.exp (-(ρ : ℝ) * (n + 1)) =
      Real.exp (-(ρ : ℝ) * (i + 1)) * Real.exp (-(ρ : ℝ) * (n - i : ℕ)) := by
    rw [← Real.exp_add, Nat.cast_sub hi.le]
    congr 1
    ring
  have hr : (ρ : ℝ) ^ n = (ρ : ℝ) * (ρ : ℝ) ^ i * (ρ : ℝ) ^ (n - i - 1) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have hz : ((n - i : ℕ) : ℝ) ^ (n - i - 1) =
      ((n : ℝ) - i) ^ ((n : ℤ) - i - 1) := by
    rw [← zpow_natCast, Nat.cast_sub hi.le]
    congr 1
    omega
  rw [meanCorrection_normalize hi, borelMass_succ_zpow, borelMass_succ_zpow,
    Nat.cast_choose ℝ hi.le]
  simp only [borelMass, hk, if_false, mul_pow]
  rw [he, hr, hz, Nat.cast_sub hi.le]
  field_simp

-- @node: duration_series_summable
/-- If [the nonnegative branching parameter ρ is subcritical](hyp:ρ,hρ), [the series over n of the Borel mass at n + 1 multiplied by the sum of the n expected reciprocal cumulative preference count surpluses is summable](goal). -/
lemma duration_series_summable (ρ : ℝ≥0) (hρ : subcritical ρ) :
    Summable (fun n => borelMass ρ (n + 1) *
      ∑ m ∈ Finset.range n,
        ∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n) := by
  have hnonneg (n : ℕ) : 0 ≤ ∑ m ∈ Finset.range n,
      ∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n := by
    exact Finset.sum_nonneg (fun m hm =>
      (duration_reciprocal_mean_bounds (Finset.mem_range.mp hm)).1)
  have hbound (n : ℕ) : (∑ m ∈ Finset.range n,
      ∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n) ≤ n := by
    calc
      _ ≤ ∑ _m ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun m hm =>
          (duration_reciprocal_mean_bounds (Finset.mem_range.mp hm)).2)
      _ = n := by simp
  have hs : Summable (fun n => borelMass ρ (n + 1) * ((n + 1 : ℕ) : ℝ)^2) :=
    (summable_nat_add_iff 1).mpr (borel_second_moment_summable ρ hρ)
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (borelMass_nonneg ρ _) (hnonneg n))
    (fun n => ?_) hs
  apply mul_le_mul_of_nonneg_left _ (borelMass_nonneg ρ _)
  calc
    _ ≤ (n : ℝ) := hbound n
    _ ≤ ((n + 1 : ℕ) : ℝ)^2 := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]

-- @node: combinatorialDuration_integrable
/-- If [the nonnegative branching parameter ρ is subcritical](hyp:ρ,hρ), [the combinatorial duration is integrable under the combinatorial distribution with parameter ρ](goal). -/
lemma combinatorialDuration_integrable (ρ : ℝ≥0) (hρ : subcritical ρ) :
    Integrable (fun q => (combinatorialDuration q : ℝ)) (combinatorialMeasure ρ) := by
  unfold combinatorialMeasure
  apply integrable_sum_measure
  · intro n
    apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    exact durationComponent_integrable n
  · have heq (n : ℕ) :
        (∫ q : DurationSample, ‖(combinatorialDuration q : ℝ)‖
          ∂(ENNReal.ofReal (borelMass ρ (n + 1)) •
            (durationComponentMeasure n).map (fun q => Sigma.mk n q))) =
        borelMass ρ (n + 1) * ∑ m ∈ Finset.range n,
          ∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m)
            ∂preferenceCountMeasure n := by
      rw [integral_smul_measure, integral_map (by fun_prop) (by fun_prop)]
      simp only [Real.norm_eq_abs, NNReal.abs_eq, smul_eq_mul,
        ENNReal.toReal_ofReal (borelMass_nonneg ρ _), combinatorialDuration]
      rw [durationComponent_mean]
    simpa only [heq] using duration_series_summable ρ hρ

-- @node: combinatorialDuration_mean_series
/-- If [the nonnegative branching parameter ρ is subcritical](hyp:ρ,hρ), [the mean combinatorial duration equals the series over n of the Borel mass at n + 1 times the sum, over stages m from zero through n − 1, of the expected reciprocal of the cumulative preference count through m + 1 minus m](goal). -/
lemma combinatorialDuration_mean_series (ρ : ℝ≥0) (hρ : subcritical ρ) :
    (∫ q, (combinatorialDuration q : ℝ) ∂combinatorialMeasure ρ) =
      ∑' n, borelMass ρ (n + 1) * ∑ m ∈ Finset.range n,
        ∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m)
          ∂preferenceCountMeasure n := by
  have hi := combinatorialDuration_integrable ρ hρ
  unfold combinatorialMeasure at hi ⊢
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro n
  rw [integral_smul_measure, integral_map (by fun_prop) (by fun_prop)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (borelMass_nonneg ρ _),
    combinatorialDuration]
  rw [durationComponent_mean]

-- @node: combinatorialDuration_mean_zero
/-- [The mean combinatorial duration is zero when the branching parameter is zero](goal). -/
lemma combinatorialDuration_mean_zero :
    (∫ q, (combinatorialDuration q : ℝ) ∂combinatorialMeasure 0) = 0 := by
  rw [combinatorialDuration_mean_series 0 (by norm_num [subcritical])]
  calc
    _ = ∑' _n : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro n
      cases n <;> simp [borelMass]
    _ = 0 := by simp

-- @node: borel_harmonic_moment_series
/-- For [a nonnegative branching parameter ρ](hyp:ρ), [the integral of size times its harmonic number under the Borel measure equals the series of these products weighted by their Borel masses](goal). -/
lemma borel_harmonic_moment_series (ρ : ℝ≥0) :
    (∫ j : ℕ, (j : ℝ) * harmonicNumber j ∂borelMeasure ρ) =
      ∑' j, borelMass ρ j * (j : ℝ) * harmonicNumber j := by
  unfold borelMeasure
  rw [integral_sum_dirac (fun j => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (borelMass_nonneg ρ _), smul_eq_mul, mul_assoc]

-- @node: borel_centered_harmonic_series
/-- If [the nonnegative branching parameter ρ is subcritical](hyp:ρ,hρ), [(1 − ρ) times the Borel expectation of size times its harmonic number, less one, equals the series of Borel masses weighted by (1 − ρ) times size times its harmonic number, less one](goal). -/
lemma borel_centered_harmonic_series (ρ : ℝ≥0) (hρ : subcritical ρ) :
    (1 - (ρ : ℝ)) * (∫ j : ℕ, (j : ℝ) * harmonicNumber j ∂borelMeasure ρ) - 1 =
      ∑' j, borelMass ρ j * ((1 - (ρ : ℝ)) * (j : ℝ) * harmonicNumber j - 1) := by
  rw [borel_harmonic_moment_series]
  have hs := (borel_harmonic_moment_summable ρ hρ).mul_left (1 - (ρ : ℝ))
  calc
    _ = (∑' j, (1 - (ρ : ℝ)) *
        (borelMass ρ j * (j : ℝ) * harmonicNumber j)) - ∑' j, borelMass ρ j := by
      rw [tsum_mul_left, borelMass_sum ρ hρ]
    _ = ∑' j, ((1 - (ρ : ℝ)) *
        (borelMass ρ j * (j : ℝ) * harmonicNumber j) - borelMass ρ j) :=
      (hs.tsum_sub (borelMass_summable ρ hρ)).symm
    _ = _ := by
      apply tsum_congr
      intro j
      ring

-- @node: borel_harmonic_convolution
/-- If [the nonnegative branching parameter ρ is subcritical](hyp:ρ,hρ), [the convolution series, summing over n and i from zero through n − 1 the Borel mass at i + 1 times the Borel mass at n − i times n − i times its harmonic number, is summable and equals the Borel size-weighted harmonic moment series](goal). -/
lemma borel_harmonic_convolution (ρ : ℝ≥0) (hρ : subcritical ρ) :
    Summable (fun n => ∑ i ∈ Finset.range n, borelMass ρ (i + 1) *
      (borelMass ρ (n - i) * (n - i : ℕ) * harmonicNumber (n - i))) ∧
    (∑' n, ∑ i ∈ Finset.range n, borelMass ρ (i + 1) *
      (borelMass ρ (n - i) * (n - i : ℕ) * harmonicNumber (n - i))) =
      ∑' j, borelMass ρ j * (j : ℝ) * harmonicNumber j := by
  have hf : Summable (fun i => borelMass ρ (i + 1)) :=
    (summable_nat_add_iff 1).mpr (borelMass_summable ρ hρ)
  have hg := borel_harmonic_moment_summable ρ hρ
  have heq (n : ℕ) :
      (∑ i ∈ Finset.range (n + 1), borelMass ρ (i + 1) *
        (borelMass ρ (n - i) * (n - i : ℕ) * harmonicNumber (n - i))) =
      ∑ i ∈ Finset.range n, borelMass ρ (i + 1) *
        (borelMass ρ (n - i) * (n - i : ℕ) * harmonicNumber (n - i)) := by
    rw [Finset.sum_range_succ]
    simp
  have hmass : (∑' i, borelMass ρ (i + 1)) = 1 := by
    have h := (borelMass_summable ρ hρ).tsum_eq_zero_add
    rw [borelMass_sum ρ hρ] at h
    simpa only [show borelMass ρ 0 = 0 by simp [borelMass], zero_add] using h.symm
  constructor
  · have hs := (summable_norm_sum_mul_range_of_summable_norm hf.norm hg.norm).of_norm
    simpa only [heq] using hs
  · rw [← show (∑' n, ∑ i ∈ Finset.range (n + 1), borelMass ρ (i + 1) *
        (borelMass ρ (n - i) * (n - i : ℕ) * harmonicNumber (n - i))) =
        ∑' n, ∑ i ∈ Finset.range n, borelMass ρ (i + 1) *
        (borelMass ρ (n - i) * (n - i : ℕ) * harmonicNumber (n - i)) from
      tsum_congr heq]
    rw [← tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf.norm hg.norm,
      hmass, one_mul]

-- @node: borel_harmonic_shift_term
/-- For [a nonnegative branching parameter ρ](hyp:ρ), [the Borel mass at n + 1 times n + 1 times the nth harmonic number equals the same mass times n + 1 times the next harmonic number, less that mass](goal). -/
lemma borel_harmonic_shift_term (ρ : ℝ≥0) (n : ℕ) :
    borelMass ρ (n + 1) * (n + 1 : ℝ) * harmonicNumber n =
      borelMass ρ (n + 1) * (n + 1 : ℝ) * harmonicNumber (n + 1) -
        borelMass ρ (n + 1) := by
  have hharm : harmonicNumber (n + 1) = harmonicNumber n + (n + 1 : ℝ)⁻¹ := by
    simp [harmonicNumber, harmonic_succ]
  rw [hharm]
  field_simp
  ring

-- @node: duration_series_identity
/-- If [the nonnegative branching parameter ρ is subcritical](hyp:ρ,hρ), [the mean combinatorial duration equals (1 − ρ) times the Borel expectation of size times its harmonic number, less one](goal). -/
lemma duration_series_identity (ρ : ℝ≥0) (hρ : subcritical ρ) :
    (∫ q, (combinatorialDuration q : ℝ) ∂combinatorialMeasure ρ) =
      (1 - (ρ : ℝ)) * (∫ j : ℕ, (j : ℝ) * harmonicNumber j ∂borelMeasure ρ) - 1 := by
  let M : ℝ := ∑' j, borelMass ρ j * (j : ℝ) * harmonicNumber j
  let C : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, borelMass ρ (i + 1) *
    (borelMass ρ (n - i) * (n - i : ℕ) * harmonicNumber (n - i))
  have hconv := borel_harmonic_convolution ρ hρ
  change Summable C ∧ (∑' n, C n) = M at hconv
  have hsB : Summable (fun n => borelMass ρ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (borelMass_summable ρ hρ)
  have hsM : Summable (fun n =>
      borelMass ρ (n + 1) * (n + 1 : ℝ) * harmonicNumber (n + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (borel_harmonic_moment_summable ρ hρ)
  have hsumB : (∑' n, borelMass ρ (n + 1)) = 1 := by
    have h := (borelMass_summable ρ hρ).tsum_eq_zero_add
    rw [borelMass_sum ρ hρ] at h
    simpa only [show borelMass ρ 0 = 0 by simp [borelMass], zero_add] using h.symm
  have hsumM : (∑' n, borelMass ρ (n + 1) * (n + 1 : ℝ) *
      harmonicNumber (n + 1)) = M := by
    have h := (borel_harmonic_moment_summable ρ hρ).tsum_eq_zero_add
    simpa [M] using h.symm
  -- The fixed-size correction becomes the Cauchy product of the shifted
  -- Borel law and its size-weighted harmonic moment.
  have hterm (n : ℕ) : borelMass ρ (n + 1) *
      (∑ m ∈ Finset.range n,
        ∫ κ, 1 / ((prefixCount κ (m + 1) : ℝ) - m) ∂preferenceCountMeasure n) =
      (borelMass ρ (n + 1) * (n + 1 : ℝ) * harmonicNumber (n + 1) -
        borelMass ρ (n + 1)) - (ρ : ℝ) * C n := by
    rw [duration_fixed_size_harmonic, mul_sub, ← mul_assoc,
      borel_harmonic_shift_term]
    congr 1
    rw [Finset.mul_sum]
    dsimp [C]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, borel_meanCorrection_factor ρ (Finset.mem_range.mp hi)]
    ring
  rw [combinatorialDuration_mean_series ρ hρ]
  simp_rw [hterm]
  rw [(hsM.sub hsB).tsum_sub (hconv.1.mul_left (ρ : ℝ)), hsM.tsum_sub hsB,
    tsum_mul_left, hconv.2, hsumB, hsumM, borel_harmonic_moment_series]
  dsimp [M]
  ring

end Papers.HawkesD75660b
