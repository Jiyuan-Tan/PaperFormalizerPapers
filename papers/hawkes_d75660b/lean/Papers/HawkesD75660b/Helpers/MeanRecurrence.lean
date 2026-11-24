module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Sum
public import Papers.HawkesD75660b.Helpers.ConditionalCounts
public import Papers.HawkesD75660b.Helpers.TightPrefixes

/-! The reciprocal-mean recurrence on the full count law. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

-- @node: canonicalCount_integrable
/-- [Every real-valued function of a count vector of length n is integrable under the canonical preference count distribution](goal). -/
lemma canonicalCount_integrable (n : ℕ) (f : CountVector n → ℝ) :
    Integrable f (preferenceCountMeasure n) := by
  unfold preferenceCountMeasure
  exact integrable_finsetSum_measure.mpr (fun k _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)

-- @node: canonicalCount_integral_eq_sum_cond
/-- [The expectation of any real-valued function of the canonical count vector equals the sum, over the values of a finite observable, of each value's probability times the function's conditional expectation given that value](goal). -/
lemma canonicalCount_integral_eq_sum_cond {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι] (n : ℕ)
    (X : CountVector n → ι) (f : CountVector n → ℝ) :
    (∫ q, f q ∂preferenceCountMeasure n) =
      ∑ x, (preferenceCountMeasure n).real (X ⁻¹' {x}) *
        ∫ q, f q ∂ProbabilityTheory.cond (preferenceCountMeasure n) (X ⁻¹' {x}) := by
  have := preferenceCountMeasure_probability n
  conv_lhs => rw [← sum_meas_smul_cond_fiber (measurable_of_countable X)
    (preferenceCountMeasure n)]
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, smul_eq_mul, Measure.real]
  · intro x hx
    by_cases hz : preferenceCountMeasure n (X ⁻¹' {x}) = 0
    · simp [hz]
    · apply Integrable.smul_measure _ (measure_ne_top _ _)
      exact (canonicalCount_integrable n f).restrict.smul_measure (ENNReal.inv_ne_top.mpr hz)

-- @node: reciprocalTransition_binomial_sum
/-- If [a is strictly positive](hyp:ha), [the sum over v from zero through r of the binomial coefficient choosing v from r times a to the integer power r − v − 1, divided by (a + 1) to the integer power r − 1, equals 1 + 1/a](goal).

Integer exponents include the case r = 0. -/
lemma reciprocalTransition_binomial_sum (r : ℕ) (a : ℝ) (ha : 0 < a) :
    (∑ v ∈ Finset.range (r + 1),
      (Nat.choose r v : ℝ) * a ^ ((r : ℤ) - v - 1)) /
        (a + 1) ^ ((r : ℤ) - 1) = 1 + 1 / a := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : a + 1 ≠ 0 := by positivity
  have hterm (v : ℕ) (hv : v ∈ Finset.range (r + 1)) :
      (Nat.choose r v : ℝ) * a ^ ((r : ℤ) - v - 1) =
        a⁻¹ * (1 ^ v * a ^ (r - v) * (Nat.choose r v : ℝ)) := by
    have hvr : v ≤ r := by
      have := Finset.mem_range.mp hv
      omega
    have he : (r : ℤ) - v - 1 = ((r - v : ℕ) : ℤ) + (-1) := by
      rw [Nat.cast_sub hvr]
      ring
    rw [he, zpow_add₀ ha0, zpow_natCast, zpow_neg_one]
    simp only [one_pow, one_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow,
    zpow_sub₀ hb0, zpow_natCast, zpow_one]
  have hpow : (a + 1) ^ r ≠ 0 := pow_ne_zero _ hb0
  rw [add_comm (1 : ℝ) a]
  field_simp

-- @node: conditionalCountMass_reciprocal_sum
/-- If [the prefix length m is below n](hyp:hm), [the cumulative count s is at least m](hyp:hms), and [s is at most n](hyp:hsn),
[the sum over increments v from zero through n − s of the conditional count mass divided by s + v − m equals (1 + 1/(n − m))/(s − m + 1), minus a correction of ((n − m)/(n − m + 1)) to the integer power n − s − 1 when s = m, and zero correction otherwise](goal). -/
lemma conditionalCountMass_reciprocal_sum {n m s : ℕ}
    (hm : m < n) (hms : m ≤ s) (hsn : s ≤ n) :
    (∑ v ∈ Finset.range (n - s + 1),
      conditionalCountMass n m s v / ((s : ℝ) + v - m)) =
        (1 + 1 / ((n : ℝ) - m)) / ((s : ℝ) - m + 1) -
          if s = m then
            ((n : ℝ) - m) ^ ((n : ℤ) - s - 1) /
              ((n : ℝ) - m + 1) ^ ((n : ℤ) - s - 1)
          else 0 := by
  classical
  let a : ℝ := (n : ℝ) - m
  let d : ℝ := (s : ℝ) - m + 1
  let f : ℕ → ℝ := fun v =>
    (Nat.choose (n - s) v : ℝ) * a ^ ((n : ℤ) - s - v - 1) /
      (a + 1) ^ ((n : ℤ) - s - 1) / d
  have ha : 0 < a := by
    have : (m : ℝ) < n := by exact_mod_cast hm
    dsimp [a]
    linarith
  have hd : 0 < d := by
    have : (m : ℝ) ≤ s := by exact_mod_cast hms
    dsimp [d]
    linarith
  have hterm (v : ℕ) :
      conditionalCountMass n m s v / ((s : ℝ) + v - m) =
        f v - if s = m ∧ v = 0 then f 0 else 0 := by
    by_cases hz : s = m ∧ v = 0
    · obtain ⟨rfl, rfl⟩ := hz
      simp [conditionalCountMass, f, a, d]
    · have hne : (s : ℝ) + v - m ≠ 0 := by
        have hms' : (m : ℝ) ≤ s := by exact_mod_cast hms
        have hv' : 0 ≤ (v : ℝ) := Nat.cast_nonneg v
        intro heq
        have hsm : (s : ℝ) = m := by linarith
        have hv0 : (v : ℝ) = 0 := by linarith
        exact hz ⟨by exact_mod_cast hsm, by exact_mod_cast hv0⟩
      rw [if_neg hz, sub_zero]
      unfold conditionalCountMass f
      push_cast
      dsimp [a, d]
      simp only [sub_add_eq_sub_sub]
      field_simp
  have hsum : ∑ v ∈ Finset.range (n - s + 1), f v =
      (1 + 1 / a) / d := by
    simp only [f, ← Finset.sum_div]
    have he : (n : ℤ) - s = ((n - s : ℕ) : ℤ) := by
      rw [Nat.cast_sub hsn]
    simp only [he]
    rw [reciprocalTransition_binomial_sum (n - s) a ha]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, hsum]
  have hcorr : (∑ v ∈ Finset.range (n - s + 1),
      if s = m ∧ v = 0 then f 0 else 0) =
      if s = m then
        a ^ ((n : ℤ) - s - 1) / (a + 1) ^ ((n : ℤ) - s - 1)
      else 0 := by
    by_cases hsm : s = m
    · subst s
      simp [f, d]
    · simp [hsm]
  rw [hcorr]

-- @node: auxiliaryCountLaw_sum_support
/-- If [m is below n](hyp:hm), [s is at least m](hyp:hms), and [s is at most n](hyp:hsn),
[the sum of the two auxiliary counts is at most n − s almost surely under their joint law](goal). -/
lemma auxiliaryCountLaw_sum_support {n m s : ℕ} (hm : m < n)
    (hms : m ≤ s) (hsn : s ≤ n) :
    ∀ᵐ v ∂(auxiliaryCountLaw n m s).map (fun q => q.1 + q.2), v ≤ n - s := by
  have := auxiliaryCountLaw_probability hm hms hsn
  apply ae_iff_of_countable.mpr
  intro v hv
  by_contra hlarge
  apply hv
  apply (measureReal_eq_zero_iff).mp
  rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton v)]
  change (auxiliaryCountLaw n m s).real {q | q.1 + q.2 = v} = 0
  rw [auxiliaryCountLaw_sum_mass hm hms hsn]
  simp [conditionalCountMass, Nat.choose_eq_zero_of_lt (by omega : n - s < v)]

-- @node: auxiliaryCountLaw_reciprocal_integral
/-- If [m is below n](hyp:hm), [s is at least m](hyp:hms), and [s is at most n](hyp:hsn),
[the expectation of 1/(s + v − m), when v is the sum of the two auxiliary counts, equals the sum from v = 0 through n − s of the conditional count mass divided by s + v − m](goal). -/
lemma auxiliaryCountLaw_reciprocal_integral {n m s : ℕ} (hm : m < n)
    (hms : m ≤ s) (hsn : s ≤ n) :
    (∫ v : ℕ, 1 / ((s : ℝ) + v - m)
      ∂(auxiliaryCountLaw n m s).map (fun q => q.1 + q.2)) =
      ∑ v ∈ Finset.range (n - s + 1),
        conditionalCountMass n m s v / ((s : ℝ) + v - m) := by
  have := auxiliaryCountLaw_probability hm hms hsn
  let μ := (auxiliaryCountLaw n m s).map (fun q => q.1 + q.2)
  have hs : ∀ᵐ v ∂μ, v ∈ (Finset.range (n - s + 1) : Set ℕ) := by
    filter_upwards [auxiliaryCountLaw_sum_support hm hms hsn] with v hv
    simpa using Nat.lt_succ_of_le hv
  calc
    _ = ∫ v in (Finset.range (n - s + 1) : Set ℕ),
        1 / ((s : ℝ) + v - m) ∂μ := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [hs] with v hv
      exact fun hn => (hn hv).elim
    _ = _ := by
      rw [setIntegral_finset _ IntegrableOn.finset]
      apply Finset.sum_congr rfl
      intro v hv
      dsimp only [μ]
      rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton v)]
      change (auxiliaryCountLaw n m s).real {q | q.1 + q.2 = v} *
        (1 / ((s : ℝ) + v - m)) = _
      rw [auxiliaryCountLaw_sum_mass hm hms hsn]
      ring

-- @node: canonical_reciprocalTransition_average
/-- If [m is below n](hyp:hm), [the canonical expectation of the conditional transition sum of 1/(s + v − m), with s the cumulative count through m, equals (1 + 1/(n − m)) times the expectation of 1/(s − m + 1), minus the probability that s = m times ((n − m)/(n − m + 1)) to the integer power n − m − 1](goal). -/
lemma canonical_reciprocalTransition_average {n m : ℕ} (hm : m < n) :
    (∫ k : CountVector n,
      (∑ v ∈ Finset.range (n - prefixCount k m + 1),
        conditionalCountMass n m (prefixCount k m) v /
          ((prefixCount k m : ℝ) + v - m)) ∂preferenceCountMeasure n) =
      (1 + 1 / ((n : ℝ) - m)) *
        (∫ k : CountVector n, 1 / ((prefixCount k m : ℝ) - m + 1)
          ∂preferenceCountMeasure n) -
      (preferenceCountMeasure n).real {k | prefixCount k m = m} *
        (((n : ℝ) - m) ^ ((n : ℤ) - m - 1) /
          ((n : ℝ) - m + 1) ^ ((n : ℤ) - m - 1)) := by
  classical
  have hi (f : CountVector n → ℝ) : Integrable f (preferenceCountMeasure n) := by
    unfold preferenceCountMeasure
    exact integrable_finsetSum_measure.mpr (fun k _ =>
      (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)
  let c : ℝ := ((n : ℝ) - m) ^ ((n : ℤ) - m - 1) /
    ((n : ℝ) - m + 1) ^ ((n : ℤ) - m - 1)
  have heq : (fun k : CountVector n =>
      ∑ v ∈ Finset.range (n - prefixCount k m + 1),
        conditionalCountMass n m (prefixCount k m) v /
          ((prefixCount k m : ℝ) + v - m)) =ᵐ[preferenceCountMeasure n]
      (fun k => (1 + 1 / ((n : ℝ) - m)) *
        (1 / ((prefixCount k m : ℝ) - m + 1)) -
          ({k : CountVector n | prefixCount k m = m}).indicator (fun _ => c) k) := by
    filter_upwards [preferenceCountMeasure_supported n] with k hk
    have hlo : m ≤ prefixCount k m := by
      by_cases hz : m = 0
      · subst m; simp [prefixCount]
      · exact hk.prefix m (by omega) (by omega)
    have hhi : prefixCount k m ≤ n := by
      calc
        _ ≤ ∑ a, k a := by
          unfold prefixCount
          exact Finset.sum_le_sum (fun a _ => by split_ifs <;> omega)
        _ = n := hk.total
    rw [conditionalCountMass_reciprocal_sum hm hlo hhi]
    by_cases he : prefixCount k m = m
    · simp [he, c, div_eq_mul_inv]
    · simp [he, div_eq_mul_inv]
  rw [integral_congr_ae heq, integral_sub (hi _) (hi _), integral_const_mul,
    integral_indicator_const c (by exact (Set.to_countable _).measurableSet)]
  simp only [smul_eq_mul, c]

-- @env: S2
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (κ : Ω → CountVector n)

-- @node: reciprocalPrefix_integrable
/-- If [the random count vector has the canonical preference count distribution under P](hyp:hlaw) and [m is below n](hyp:hm),
[the reciprocal of the cumulative count through m + 1 minus m is integrable under P](goal). -/
lemma reciprocalPrefix_integrable (hlaw : meanRecurrenceLaw P κ)
    (m : ℕ) (hm : m < n) :
    Integrable (fun ω => 1 / ((prefixCount (κ ω) (m + 1) : ℝ) - m)) P := by
  classical
  let f : CountVector n → ℝ := fun k => 1 / ((prefixCount k (m + 1) : ℝ) - m)
  have hf : AEStronglyMeasurable f (preferenceCountMeasure n) := by
    fun_prop
  have hfin : Integrable f (preferenceCountMeasure n) := by
    unfold preferenceCountMeasure
    apply integrable_finsetSum_measure.mpr
    intro k hk
    apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    exact integrable_dirac (by simp)
  have hmap : Integrable f (P.map κ) := by
    rw [show P.map κ = preferenceCountMeasure n from hlaw.map_eq]
    exact hfin
  exact (integrable_map_measure (hlaw.map_eq.symm ▸ hf) hlaw.aemeasurable).mp hmap

-- @node: conditionalPrefix_reciprocal_integral
/-- Suppose [the random count vector has the canonical preference count distribution under P](hyp:hlaw),
[the natural count domain is identified with the nonnegative integers](hyp:hdomain), and
[the zero count convention also identifies natural counts with the nonnegative integers](hyp:hzero).
If [m is at least one](hyp:hmpos), [m is below n](hyp:hm), and [the event that the first m coordinates equal those of k has positive probability](hyp:hk),
[the conditional expectation of the reciprocal of the cumulative count through m + 1 minus m equals the finite transition sum of the conditional count mass divided by s + v − m, where s is the cumulative count of k through m and v ranges from zero through n − s](goal). -/
lemma conditionalPrefix_reciprocal_integral (hlaw : meanRecurrenceLaw P κ)
    (hdomain : naturalCountDomainConvention) (hzero : zeroCountConvention)
    {m : ℕ} (hmpos : 1 ≤ m) (hm : m < n) (k : CountVector n)
    (hk : 0 < P (countPrefixEvent κ m k)) :
    (∫ ω, 1 / ((prefixCount (κ ω) (m + 1) : ℝ) - m)
      ∂ProbabilityTheory.cond P (countPrefixEvent κ m k)) =
      ∑ v ∈ Finset.range (n - prefixCount k m + 1),
        conditionalCountMass n m (prefixCount k m) v /
          ((prefixCount k m : ℝ) + v - m) := by
  have hprefix : P (countPrefixEvent κ m k) =
      preferenceCountMeasure n (countPrefixEvent id m k) :=
    hlaw.measure_eq (p := fun q => ∀ a : Fin n, a.val < m → q a = k a)
      (Set.to_countable _).measurableSet
  have hb := canonicalPrefix_feasible hm k (hprefix ▸ hk)
  have hid := ((conditionalPreferenceCountLaw P κ (show 0 < n by omega)
    hlaw hdomain hzero).1 m hmpos hm k hk).2.1
  have he : ∀ᵐ ω ∂ProbabilityTheory.cond P (countPrefixEvent κ m k),
      prefixCount (κ ω) m = prefixCount k m := by
    filter_upwards [ae_cond_mem₀ (μ := P)
      (s := countPrefixEvent κ m k)
      (hlaw.aemeasurable.nullMeasurableSet_preimage
        (s := countPrefixEvent id m k) (Set.to_countable _).measurableSet)] with ω hω
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with ham
    · exact hω a ham
    · rfl
  calc
    _ = ∫ ω, 1 / ((prefixCount k m : ℝ) + κ ω ⟨m, hm⟩ - m)
        ∂ProbabilityTheory.cond P (countPrefixEvent κ m k) := by
      apply integral_congr_ae
      filter_upwards [he] with ω hω
      rw [prefixCount_succ (κ ω) ⟨m, hm⟩, Nat.cast_add, hω]
    _ = ∫ q : ℕ × ℕ, 1 / ((prefixCount k m : ℝ) + (q.1 + q.2 : ℕ) - m)
        ∂auxiliaryCountLaw n m (prefixCount k m) :=
      (hid.comp (by fun_prop : Measurable (fun v : ℕ =>
        1 / ((prefixCount k m : ℝ) + v - m)))).integral_eq
    _ = _ := by
      rw [← integral_map (φ := fun q : ℕ × ℕ => q.1 + q.2)
        (f := fun v : ℕ => 1 / ((prefixCount k m : ℝ) + v - m))
        (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]
      exact auxiliaryCountLaw_reciprocal_integral hm hb.1 hb.2

-- @node: canonical_reciprocalTransition_positive
/-- If [m is at least one](hyp:hmpos), [m is below n](hyp:hm),
[the natural count domain is identified with the nonnegative integers](hyp:hdomain), and
[the zero count convention also identifies natural counts with the nonnegative integers](hyp:hzero),
[the canonical expectation of the reciprocal of the cumulative count through m + 1 minus m equals the canonical expectation of the transition sum of the conditional count mass divided by s + v − m, where s is the cumulative count through m and v ranges from zero through n − s](goal). -/
lemma canonical_reciprocalTransition_positive {n m : ℕ} (hmpos : 1 ≤ m)
    (hm : m < n) (hdomain : naturalCountDomainConvention) (hzero : zeroCountConvention) :
    (∫ q : CountVector n, 1 / ((prefixCount q (m + 1) : ℝ) - m)
      ∂preferenceCountMeasure n) =
      ∫ q : CountVector n,
        (∑ v ∈ Finset.range (n - prefixCount q m + 1),
          conditionalCountMass n m (prefixCount q m) v /
            ((prefixCount q m : ℝ) + v - m)) ∂preferenceCountMeasure n := by
  classical
  have := preferenceCountMeasure_probability n
  let X : CountVector n → (Fin m → Fin (n + 1)) := fun q a =>
    ⟨min (q ⟨a.val, by omega⟩) n, by omega⟩
  rw [canonicalCount_integral_eq_sum_cond n X,
    canonicalCount_integral_eq_sum_cond n X]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hz : preferenceCountMeasure n (X ⁻¹' {x}) = 0
  · simp [Measure.real, hz]
  · let k : CountVector n := fun a => if ha : a.val < m then (x ⟨a.val, ha⟩).val else 0
    have hfiber : X ⁻¹' {x} =ᵐ[preferenceCountMeasure n] countPrefixEvent id m k := by
      filter_upwards [preferenceCountMeasure_supported n] with q hq
      change (X q = x) = (∀ a : Fin n, a.val < m → q a = k a)
      apply propext
      constructor
      · intro he a ha
        have he' := congrArg (fun z => (z ⟨a.val, ha⟩).val) he
        have hb := preferenceCounts_coordinate_bound hq a
        simpa [X, k, ha, min_eq_left hb] using he'
      · intro he
        funext a
        apply Fin.ext
        have hh := he ⟨a.val, by omega⟩ a.isLt
        have hb := preferenceCounts_coordinate_bound hq ⟨a.val, by omega⟩
        simpa [X, k, a.isLt, min_eq_left hb] using hh
    have hcond : ProbabilityTheory.cond (preferenceCountMeasure n) (X ⁻¹' {x}) =
        ProbabilityTheory.cond (preferenceCountMeasure n) (countPrefixEvent id m k) := by
      rw [ProbabilityTheory.cond, ProbabilityTheory.cond, measure_congr hfiber,
        Measure.restrict_congr_set hfiber]
    have hk : 0 < preferenceCountMeasure n (countPrefixEvent id m k) := by
      rw [← measure_congr hfiber]
      exact pos_iff_ne_zero.mpr hz
    congr 1
    rw [hcond]
    have hmean := conditionalPrefix_reciprocal_integral (preferenceCountMeasure n) id
      HasLaw.id hdomain hzero hmpos hm k hk
    simp only [id_eq] at hmean
    rw [hmean]
    have := cond_isProbabilityMeasure (ne_of_gt hk)
    have he : ∀ᵐ q ∂ProbabilityTheory.cond (preferenceCountMeasure n)
        (countPrefixEvent id m k), prefixCount q m = prefixCount k m := by
      filter_upwards [ae_cond_mem ((Set.to_countable (countPrefixEvent id m k)).measurableSet)]
        with q hq
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs with ham
      · exact hq a ham
      · rfl
    calc
      _ = ∫ _q : CountVector n,
          (∑ v ∈ Finset.range (n - prefixCount k m + 1),
            conditionalCountMass n m (prefixCount k m) v /
              ((prefixCount k m : ℝ) + v - m))
          ∂ProbabilityTheory.cond (preferenceCountMeasure n) (countPrefixEvent id m k) := by
        simp
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [he] with q hq
        rw [hq]

-- @node: auxiliaryCountLaw_zero
/-- If [n is positive](hyp:hn), [the auxiliary joint count law at the empty prefix is the distribution of the pair consisting of a binomial count with n − 1 trials and success probability 1/(n + 1), followed by the constant one](goal). -/
lemma auxiliaryCountLaw_zero {n : ℕ} (hn : 0 < n) :
    auxiliaryCountLaw n 0 0 =
      (ProbabilityTheory.binomial (n - 1) (reciprocalProbability n)).map
        (fun v => (v, 1)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hp : bernoulliParameter n 0 0 = 1 := by
    simp [bernoulliParameter, hn']
  simp only [auxiliaryCountLaw, hp, bernoulliNat, ENNReal.ofReal_one,
    one_smul, sub_self, ENNReal.ofReal_zero, zero_smul, add_zero]
  rw [Measure.dirac_bind (measurable_of_countable _)]
  simp

-- @node: canonical_reciprocalTransition_zero
/-- If [n is positive](hyp:hn), [the natural count domain is identified with the nonnegative integers](hyp:hdomain), and
[the zero count convention also identifies natural counts with the nonnegative integers](hyp:hzero),
[the canonical expectation of the reciprocal of the first cumulative count equals the canonical expectation of the empty-prefix transition sum, which sums the conditional count mass divided by s + v over v from zero through n − s, with s the empty cumulative count](goal). -/
lemma canonical_reciprocalTransition_zero {n : ℕ} (hn : 0 < n)
    (hdomain : naturalCountDomainConvention) (hzero : zeroCountConvention) :
    (∫ q : CountVector n, 1 / (prefixCount q 1 : ℝ) ∂preferenceCountMeasure n) =
      ∫ q : CountVector n,
        (∑ v ∈ Finset.range (n - prefixCount q 0 + 1),
          conditionalCountMass n 0 (prefixCount q 0) v /
            ((prefixCount q 0 : ℝ) + v)) ∂preferenceCountMeasure n := by
  have := preferenceCountMeasure_probability n
  have hinit := (conditionalPreferenceCountLaw (preferenceCountMeasure n) id hn
    HasLaw.id hdomain hzero).2
  have hi := hinit.integral_comp (f := fun v : ℕ => 1 / ((v : ℝ) + 1))
    (measurable_of_countable _).aestronglyMeasurable
  have he : (∫ q : CountVector n, 1 / (prefixCount q 1 : ℝ)
      ∂preferenceCountMeasure n) =
      ∫ v : ℕ, 1 / ((v : ℝ) + 1)
        ∂ProbabilityTheory.binomial (n - 1) (reciprocalProbability n) := by
    rw [← hi]
    apply integral_congr_ae
    filter_upwards [preferenceCountMeasure_supported n] with q hq
    have hs := prefixCount_succ q ⟨0, hn⟩
    have hp := hq.prefix 1 (by omega) (by omega)
    change prefixCount q 1 = prefixCount q 0 + q ⟨0, hn⟩ at hs
    rw [show prefixCount q 0 = 0 by simp [prefixCount], zero_add] at hs
    have hqpos : 1 ≤ q ⟨0, hn⟩ := by omega
    have hcast : ((q ⟨0, hn⟩ - 1 : ℕ) : ℝ) + 1 = q ⟨0, hn⟩ := by
      exact_mod_cast Nat.sub_add_cancel hqpos
    simp only [Function.comp_def, id_eq, hcast, hs]
  have haux : (∫ v : ℕ, 1 / (v : ℝ)
      ∂(auxiliaryCountLaw n 0 0).map (fun q => q.1 + q.2)) =
      ∫ v : ℕ, 1 / ((v : ℝ) + 1)
        ∂ProbabilityTheory.binomial (n - 1) (reciprocalProbability n) := by
    rw [auxiliaryCountLaw_zero hn, Measure.map_map (by fun_prop) (by fun_prop),
      integral_map (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]
    simp
  have hs := auxiliaryCountLaw_reciprocal_integral (n := n) (m := 0) (s := 0)
    hn (by omega) (by omega)
  simp only [Nat.cast_zero, zero_add, sub_zero] at hs
  rw [he, ← haux, hs]
  simp [prefixCount]

-- @node: lem:meanrecur1
/-- Suppose [n is positive](hyp:hindex), [the random count vector has the canonical preference count distribution under P](hyp:hlaw),
[the natural count domain is identified with the nonnegative integers](hyp:hdomain), and
[the zero count convention also identifies natural counts with the nonnegative integers](hyp:hzero).
[For every nonnegative integer m below n, the expected reciprocal of the cumulative count through m + 1 minus m equals (1 + 1/(n − m)) times the expected reciprocal of the cumulative count through m minus m + 1, minus the binomial coefficient choosing m from n times (m + 1) to the integer power m − 1, divided by (n + 1) to the integer power n − 1, times (n − m) to the integer power n − m − 1](goal). -/
lemma meanRecurrence
    (hindex : meanRecurrenceIndex n) (hlaw : meanRecurrenceLaw P κ)
    (hdomain : naturalCountDomainConvention) (hzero : zeroCountConvention) :
    ∀ m : ℕ, m < n →
      (∫ ω, 1 / ((prefixCount (κ ω) (m + 1) : ℝ) - m) ∂P) =
      (1 + 1 / ((n : ℝ) - m)) *
        (∫ ω, 1 / ((prefixCount (κ ω) m : ℝ) - m + 1) ∂P) -
      (Nat.choose n m : ℝ) *
        ((m + 1 : ℝ) ^ ((m : ℤ) - 1) / (n + 1 : ℝ) ^ ((n : ℤ) - 1)) *
        ((n : ℝ) - m) ^ ((n : ℤ) - m - 1) := by
  -- Assemble transition averaging with the two-component tight-prefix count.
  suffices hboundary : ∀ m : ℕ, m < n →
      (preferenceCountMeasure n).real {k | prefixCount k m = m} =
        (Nat.choose n m : ℝ) *
          ((m + 1 : ℝ) ^ ((m : ℤ) - 1) / (n + 1 : ℝ) ^ ((n : ℤ) - 1)) *
          ((n : ℝ) - m + 1) ^ ((n : ℤ) - m - 1) by
    intro m hm
    have hnext := hlaw.integral_comp (f := fun k : CountVector n =>
      1 / ((prefixCount k (m + 1) : ℝ) - m)) ((measurable_of_countable _).aestronglyMeasurable)
    have hprev := hlaw.integral_comp (f := fun k : CountVector n =>
      1 / ((prefixCount k m : ℝ) - m + 1)) ((measurable_of_countable _).aestronglyMeasurable)
    change (∫ ω, 1 / ((prefixCount (κ ω) (m + 1) : ℝ) - m) ∂P) = _ at hnext
    change (∫ ω, 1 / ((prefixCount (κ ω) m : ℝ) - m + 1) ∂P) = _ at hprev
    have htransition :
        (∫ k : CountVector n, 1 / ((prefixCount k (m + 1) : ℝ) - m)
          ∂preferenceCountMeasure n) =
        ∫ k : CountVector n,
          (∑ v ∈ Finset.range (n - prefixCount k m + 1),
            conditionalCountMass n m (prefixCount k m) v /
              ((prefixCount k m : ℝ) + v - m)) ∂preferenceCountMeasure n := by
      by_cases hmzero : m = 0
      · subst m
        simpa only [Nat.zero_add, Nat.cast_zero, sub_zero] using
          canonical_reciprocalTransition_zero (show 0 < n from hindex) hdomain hzero
      · exact canonical_reciprocalTransition_positive (by omega) hm hdomain hzero
    rw [hnext, hprev, htransition,
      canonical_reciprocalTransition_average hm, hboundary m hm]
    have ha : (0 : ℝ) < (n : ℝ) - m + 1 := by
      have : (m : ℝ) < n := by exact_mod_cast hm
      linarith
    have hp : ((n : ℝ) - m + 1) ^ ((n : ℤ) - m - 1) ≠ 0 :=
      zpow_ne_zero _ (ne_of_gt ha)
    field_simp
  intro m hm
  exact canonicalTightPrefix_mass_zpow hm

end Papers.HawkesD75660b
