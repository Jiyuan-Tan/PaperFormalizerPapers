module
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalPushforwardSampling
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! # Polynomial tails for the complete observational sampling bound

The binomial small-count terms decay exponentially at every positive-mass
label. A single eventual cutoff suffices for the finitely many labels. The
conditional joint-latent concentration estimate remains a separate obligation.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- If [the exponential decay rate a is positive](hyp:ha), then [the exponential of minus a times n is eventually at most n to the power minus p, for any natural-number power p](goal). -/
-- @node: observational_exp_eventually_le_inverse_power
lemma observational_exp_eventually_le_inverse_power {a : ℝ} (ha : 0 < a) (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-a * n) ≤ (n : ℝ) ^ (-(p : ℤ)) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop ha (-(p : ℝ))).bound zero_lt_one
  have hn := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [hn, eventually_ge_atTop (1 : ℕ)] with n hn hpos
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), one_mul,
    Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast, zpow_neg, zpow_natCast, abs_inv, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hn

/-- If [the number of categories k is positive](hyp:hk) and [the sample size n exceeds one](hyp:hn),
then [the frequency-tail expression at tolerance k times the square root of twice log n divided by n equals twice k times n to the power minus four](goal). -/
-- @node: observational_frequency_log_tail_eq
lemma observational_frequency_log_tail_eq {k n : ℕ} (hk : 0 < k) (hn : 1 < n) :
    2 * (k : ℝ) * Real.exp (-2 * n *
      (((k : ℝ) * Real.sqrt (2 * Real.log n / n)) / k)^2) =
        2 * k * (n : ℝ)^(-(4 : ℤ)) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [mul_div_cancel_left₀ _ hkR.ne', Real.sq_sqrt (by positivity)]
  have he : -2 * (n : ℝ) * (2 * Real.log n / n) = -(4 * Real.log n) := by
    field_simp
    ring
  rw [he, Real.exp_neg, show (4 : ℝ) * Real.log n = (4 : ℕ) * Real.log n by norm_num,
    Real.exp_nat_mul, Real.exp_log hnR, zpow_neg, zpow_ofNat]

/-- If [the number of categories k is positive](hyp:hk), then [eventually, simultaneously for every category with positive weight, twice k times the exponential of minus twice n times the square of that weight divided by twice k is at most twice k times n to the power minus four](goal). -/
-- @node: observational_small_count_polynomial_tail
lemma observational_small_count_polynomial_tail {k : ℕ} (hk : 0 < k)
    (p : Fin k → ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ a, 0 < p a →
      2 * (k : ℝ) * Real.exp (-2 * n * ((p a / 2) / k)^2) ≤
        2 * k * (n : ℝ)^(-(4 : ℤ)) := by
  apply eventually_all.mpr
  intro a
  by_cases hp : 0 < p a
  · have hrate : 0 < 2 * ((p a / 2) / (k : ℝ))^2 := by positivity
    filter_upwards [observational_exp_eventually_le_inverse_power hrate 4] with n hn
    intro _
    have he : -(2 * ((p a / 2) / (k : ℝ))^2) * n =
        -2 * n * ((p a / 2) / k)^2 := by ring
    rw [he] at hn
    exact mul_le_mul_of_nonneg_left hn (by positivity)
  · exact Eventually.of_forall (fun _ h => False.elim (hp h))

/-- If [the number of categories k is positive](hyp:hk) and [every category-specific coefficient B is nonnegative](hyp:hB),
then [eventually the frequency-tail expression at logarithmic tolerance plus the small-count and B-weighted inverse-fourth-power terms for all positive-weight categories is at most n to the power minus four times the sum of twice k, twice k squared, and all the B coefficients](goal). -/
-- @node: observational_stratified_polynomial_tail_sum
lemma observational_stratified_polynomial_tail_sum {k : ℕ} (hk : 0 < k)
    (p B : Fin k → ℝ) (hB : ∀ a, 0 ≤ B a) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (2 * k * Real.exp (-2 * n *
        (((k : ℝ) * Real.sqrt (2 * Real.log n / n)) / k)^2)) +
      (∑ a, if 0 < p a then
        ENNReal.ofReal (2 * k * Real.exp (-2 * n * ((p a / 2) / k)^2)) +
          ENNReal.ofReal (B a * (n : ℝ)^(-(4 : ℤ))) else 0) ≤
      ENNReal.ofReal ((2 * k + (k : ℝ) * (2 * k) + ∑ a, B a) *
        (n : ℝ)^(-(4 : ℤ))) := by
  classical
  filter_upwards [observational_small_count_polynomial_tail hk p,
    eventually_gt_atTop (1 : ℕ)] with n hn hn1
  rw [observational_frequency_log_tail_eq hk hn1]
  have hsum : (∑ a, if 0 < p a then
      ENNReal.ofReal (2 * k * Real.exp (-2 * n * ((p a / 2) / k)^2)) +
        ENNReal.ofReal (B a * (n : ℝ)^(-(4 : ℤ))) else 0) ≤
      ∑ a, ENNReal.ofReal ((2 * k + B a) * (n : ℝ)^(-(4 : ℤ))) := by
    apply Finset.sum_le_sum
    intro a _
    have hBa := hB a
    split_ifs with hp
    · calc
        _ ≤ ENNReal.ofReal (2 * k * (n : ℝ)^(-(4 : ℤ))) +
            ENNReal.ofReal (B a * (n : ℝ)^(-(4 : ℤ))) :=
          add_le_add (ENNReal.ofReal_le_ofReal (hn a hp)) le_rfl
        _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
    · exact bot_le
  apply (add_le_add le_rfl hsum).trans
  have hnonneg : ∀ a : Fin k, 0 ≤ (2 * (k : ℝ) + B a) * (n : ℝ)^(-(4 : ℤ)) :=
    fun a => mul_nonneg (add_nonneg (by positivity) (hB a)) (by positivity)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hnonneg a),
    ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg (fun a _ => hnonneg a))]
  apply ENNReal.ofReal_le_ofReal
  simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- Consider [a sample array indexed by sample size](hyp:sample) with [measurable observations](hyp:hsample),
[independence within each sample size](hyp:hind), and [common population law mu](hyp:hlaw),
and suppose [the categorical label is measurable](hyp:hlabel). Assume [S is measurable](hyp:hS),
[S has population probability one](hyp:hmuS), [D is nonnegative](hyp:hD), and [distances within S are at most D](hyp:hdiam).
Given [category-specific Lipschitz constants L](hyp:L), suppose [each latent readout has its corresponding Lipschitz bound](hyp:hphi)
and [each positive-mass category-conditional law is the image of its latent law under that readout](hyp:hcond).
Assume [each observation tolerance t is nonnegative](hyp:ht), [each latent tolerance s multiplied by its Lipschitz constant is at most t](hyp:hst),
[every tail coefficient B is nonnegative](hyp:hB), [the conditional empirical failure events at tolerance t are measurable](hyp:hMeas),
and [eventually the latent empirical failure probabilities at tolerance s are at most B times the inverse fourth power of n whenever the latent sample size is at least half the expected category count](hyp:hbound).
Then [there is a positive constant A such that eventually the full empirical Wasserstein failure probability at tolerance t plus D divided by two times k times the square root of twice log n divided by n is at most A times n to the power minus four](goal). -/
-- @node: iid_observational_polynomial_tail_of_latent_tails
lemma iid_observational_polynomial_tail_of_latent_tails
    {Omega X Z : Type*} [MeasurableSpace Omega] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Z] [CompactSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] {k : ℕ} [Nonempty (Fin k)]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X) [IsProbabilityMeasure mu]
    (sample : ∀ n, Fin n → Omega → X)
    (hsample : ∀ n i, Measurable (sample n i))
    (hind : ∀ n, iIndepFun (sample n) Q)
    (hlaw : ∀ n i, Q.map (sample n i) = mu)
    (label : X → Fin k) (hlabel : Measurable label)
    (S : Set X) (hS : MeasurableSet S) (hmuS : mu S = 1)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (latent : Fin k → ProbabilityMeasure Z) (phi : Fin k → Z → X)
    (L : Fin k → ℝ≥0) (hphi : ∀ a, LipschitzWith (L a) (phi a))
    (hcond : ∀ a, 0 < mu.real (label ⁻¹' {a}) →
      cond mu (label ⁻¹' {a}) = (latent a : Measure Z).map (phi a))
    (s : ℕ → Fin k → ℝ) (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (hst : ∀ n a, (L a : ℝ) * s n a ≤ t n)
    (B : Fin k → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hMeas : ∀ n a, 0 < mu.real (label ⁻¹' {a}) → ∀ N : ℕ,
      MeasurableSet {x : Fin N → X | ¬ wasserstein1 (cond mu (label ⁻¹' {a}))
        (empiricalMeasure x) ≤ ENNReal.ofReal (t n)})
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ a, 0 < mu.real (label ⁻¹' {a}) → ∀ N : ℕ,
      n * mu.real (label ⁻¹' {a}) / 2 ≤ N →
      (Measure.pi (fun _ : Fin N => (latent a : Measure Z)))
        {z | ¬ wasserstein1 (latent a : Measure Z) (empiricalMeasure z) ≤
          ENNReal.ofReal (s n a)} ≤ ENNReal.ofReal (B a * (n : ℝ)^(-(4 : ℤ)))) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      Q {w | ¬ wasserstein1 mu (empiricalMeasure (fun i => sample n i w)) ≤
        ENNReal.ofReal (t n + D / 2 *
          (k * Real.sqrt (2 * Real.log n / n)))} ≤
        ENNReal.ofReal (A * (n : ℝ)^(-(4 : ℤ))) := by
  have hk : 0 < k := by simpa only [Fintype.card_fin] using Fintype.card_pos (α := Fin k)
  let A : ℝ := 2 * k + (k : ℝ) * (2 * k) + ∑ a, B a
  have hA : 0 < A := by
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hsum : 0 ≤ ∑ a, B a := Finset.sum_nonneg (fun a _ => hB a)
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound,
    observational_stratified_polynomial_tail_sum hk
      (fun a => mu.real (label ⁻¹' {a})) B hB,
    eventually_gt_atTop (1 : ℕ)] with n hbound hsum hn
  have he : 0 < (k : ℝ) * Real.sqrt (2 * Real.log n / n) := by
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos hnR
    positivity
  exact (iid_observational_wasserstein_failure_le_of_latent_tails Q mu (by omega)
    (sample n) (hsample n) (hind n) (hlaw n) label hlabel S hS hmuS D (t n)
    (k * Real.sqrt (2 * Real.log n / n)) hD (ht n) he hdiam latent phi L hphi
    hcond (s n) (hst n) (fun a => ENNReal.ofReal (B a * (n : ℝ)^(-(4 : ℤ))))
    (hMeas n) hbound).trans hsum

/-- If [n is at least one](hyp:hn) and [log n is at least one](hyp:hlog), then
[the square root of twice log n divided by n is at most the square root of two times n to the power minus the reciprocal of the larger of two and d, times the square of log n](goal). -/
-- @node: observational_frequency_le_sampling_rate
lemma observational_frequency_le_sampling_rate (d : ℕ) {n : ℝ}
    (hn : 1 ≤ n) (hlog : 1 ≤ Real.log n) :
    Real.sqrt (2 * Real.log n / n) ≤
      Real.sqrt 2 * n ^ (-(1 : ℝ) / max 2 d) * (Real.log n)^2 := by
  have hn0 : 0 < n := by linarith
  have hl0 : 0 ≤ Real.log n := by linarith
  have hlogSq : Real.sqrt (Real.log n) ≤ (Real.log n)^2 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨sq_nonneg _, ?_⟩
    have hsq : Real.log n ≤ (Real.log n)^2 := by nlinarith
    have hfour : (Real.log n)^2 ≤ ((Real.log n)^2)^2 := by nlinarith
    exact hsq.trans hfour
  have hexp : -(1 : ℝ) / 2 ≤ -(1 : ℝ) / (max 2 d : ℕ) := by
    have hd : (2 : ℝ) ≤ (max 2 d : ℕ) := by exact_mod_cast le_max_left 2 d
    apply (div_le_div_iff₀ (by norm_num) (by linarith)).mpr
    linarith
  have hpow : n ^ (-(1 : ℝ) / 2) ≤ n ^ (-(1 : ℝ) / (max 2 d : ℕ)) :=
    Real.monotone_rpow_of_base_ge_one hn hexp
  calc
    Real.sqrt (2 * Real.log n / n) =
        Real.sqrt 2 * Real.sqrt (Real.log n) * n ^ (-(1 : ℝ) / 2) := by
      rw [Real.sqrt_div (mul_nonneg (by norm_num) hl0), Real.sqrt_mul (by norm_num),
        neg_div, Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]
      simp only [Real.sqrt_eq_rpow]
      norm_num
      ring
    _ ≤ Real.sqrt 2 * (Real.log n)^2 * n ^ (-(1 : ℝ) / (max 2 d : ℕ)) := by
      gcongr
    _ = _ := by
      norm_cast
      ring

end Papers.TbsNeuralCausalPi
