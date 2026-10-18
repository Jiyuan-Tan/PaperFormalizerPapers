module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleTransfer
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRemainderRates
public import Causalean.Stat.Limit.ContinuousMapping
public import Mathlib.Probability.CondVar
/-! Conditional Chebyshev and the bias/fluctuation assembly in the DML proof.
The conditional second moment is localized on a training-measurable good event;
its convergence in probability suffices without convergence of its expectation. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

-- @node: conditional_sq_good_event_bound
/-- If [the conditioning information is contained in the ambient information](hyp:hm),
[the upper bound V is measurable with respect to that information](hyp:hV),
[T has an integrable square](hyp:hT), and [its conditional second moment is at most V almost surely](hyp:hbound),
then, for [a positive threshold ε](hyp:heps) and [a nonnegative cutoff δ](hyp:hdelta),
[the probability that the absolute value of T is at least ε while V is below δ is at most δ divided by ε squared](goal). -/
lemma conditional_sq_good_event_bound {A : Type*} [mA : MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (m : MeasurableSpace A) (hm : m ≤ mA) [SigmaFinite (μ.trim hm)]
    (T V : A → ℝ) (hV : Measurable[m] V)
    (hT : Integrable (fun a => T a ^ 2) μ)
    (hbound : μ[fun a => T a ^ 2 | m] ≤ᵐ[μ] V)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 ≤ delta) :
    μ.real {a | eps ≤ |T a| ∧ V a < delta} ≤ delta / eps ^ 2 := by
  let : MeasurableSpace A := mA
  let G := {a | V a < delta}
  have hG : MeasurableSet[m] G := hV measurableSet_Iio
  have hGa : MeasurableSet G := hm _ hG
  have hce : (∫ a in G, T a ^ 2 ∂μ) ≤ delta := by
    rw [← setIntegral_condExp hm hT hG]
    calc
      _ ≤ ∫ _ in G, delta ∂μ := by
        apply integral_mono_ae integrable_condExp.restrict (integrable_const _)
        filter_upwards [ae_restrict_of_ae hbound, ae_restrict_mem hGa] with a ha hmem
        exact ha.trans (le_of_lt hmem)
      _ = μ.real G * delta := by simp
      _ ≤ delta := by
        have hmass : μ.real G ≤ 1 := measureReal_le_one
        nlinarith
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ.restrict G) (Eventually.of_forall (fun a => sq_nonneg (T a)))
    hT.restrict (eps ^ 2)
  have hsub : {a | eps ≤ |T a| ∧ V a < delta} ⊆
      {a | eps ^ 2 ≤ T a ^ 2} ∩ G := by
    intro a ha
    change eps ≤ |T a| ∧ V a < delta at ha
    refine ⟨?_, ha.2⟩
    simpa only [Set.mem_ofPred_eq, sq_abs] using
      (sq_le_sq₀ heps.le (abs_nonneg (T a))).2 ha.1
  have hr : (μ.restrict G).real {a | eps ^ 2 ≤ T a ^ 2} =
      μ.real ({a | eps ^ 2 ≤ T a ^ 2} ∩ G) := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply' hGa]
  rw [hr] at hmark
  apply (le_div_iff₀ (sq_pos_of_pos heps)).2
  have hmono := measureReal_mono (μ := μ) hsub
  nlinarith

-- @node: conditional_sq_tail_bound
/-- If [the conditioning information is contained in the ambient information](hyp:hm),
[V is measurable with respect to the conditioning information](hyp:hV),
[T has an integrable square](hyp:hT), and [its conditional second moment is bounded by V almost surely](hyp:hbound),
then, for [ε positive](hyp:heps) and [δ nonnegative](hyp:hdelta),
[the probability that the absolute value of T is at least ε is bounded by the probability that V is at least δ plus δ divided by ε squared](goal). -/
lemma conditional_sq_tail_bound {A : Type*} [mA : MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (m : MeasurableSpace A) (hm : m ≤ mA) [SigmaFinite (μ.trim hm)]
    (T V : A → ℝ) (hV : Measurable[m] V)
    (hT : Integrable (fun a => T a ^ 2) μ)
    (hbound : μ[fun a => T a ^ 2 | m] ≤ᵐ[μ] V)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 ≤ delta) :
    μ.real {a | eps ≤ |T a|} ≤
      μ.real {a | delta ≤ V a} + delta / eps ^ 2 := by
  let : MeasurableSpace A := mA
  calc
    _ ≤ μ.real ({a | delta ≤ V a} ∪ {a | eps ≤ |T a| ∧ V a < delta}) := by
      apply measureReal_mono _ (measure_ne_top μ _)
      intro a ha
      by_cases hv : delta ≤ V a
      · exact Or.inl hv
      · exact Or.inr ⟨ha, lt_of_not_ge hv⟩
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add_right
      (conditional_sq_good_event_bound μ m hm T V hV hT hbound eps delta heps hdelta) _)

-- @node: conditional_sq_tendsto_probability_zero
/-- Suppose [each sample size's conditioning information is contained in the ambient information](hyp:hm),
[each V is measurable with respect to that conditioning information](hyp:hV),
[each T has an integrable square](hyp:hT), and [each conditional second moment of T is at most V almost surely](hyp:hbound).
If [V converges to zero in probability](hyp:hrate), then [T converges to zero in probability](goal). -/
lemma conditional_sq_tendsto_probability_zero {A : Type*} [mA : MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace A) (hm : ∀ n, m n ≤ mA)
    [∀ n, SigmaFinite (μ.trim (hm n))]
    (T V : ℕ → A → ℝ) (hV : ∀ n, Measurable[m n] (V n))
    (hT : ∀ n, Integrable (fun a => T n a ^ 2) μ)
    (hbound : ∀ n, μ[fun a => T n a ^ 2 | m n] ≤ᵐ[μ] V n)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) V atTop
      (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) T atTop
      (fun _ _ => 0) := by
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hrate ⊢
  intro eps heps
  have hreal : Tendsto (fun n => μ.real {a | eps ≤ |T n a|}) atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro b hb
      exact Eventually.of_forall (fun n => hb.trans_le measureReal_nonneg)
    · intro b hb
      let delta := b * eps ^ 2 / 2
      have hd : 0 < delta := by dsimp [delta]; positivity
      have hv := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp
        (hrate delta hd)
      simp only [ENNReal.toReal_zero] at hv
      have hsmall := (tendsto_order.1 hv).2 (b / 2) (by linarith)
      filter_upwards [hsmall] with n hn
      have hvmono : μ.real {a | delta ≤ V n a} ≤
          μ.real {a | delta ≤ ‖V n a - 0‖} := by
        apply measureReal_mono _ (measure_ne_top μ _)
        intro a ha
        change delta ≤ V n a at ha
        simpa only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] using
          ha.trans (le_abs_self _)
      have ht := conditional_sq_tail_bound μ (m n) (hm n) (T n) (V n)
        (hV n) (hT n) (hbound n) eps delta heps hd.le
      have hdelta : delta / eps ^ 2 = b / 2 := by
        dsimp [delta]
        field_simp
      rw [hdelta] at ht
      change μ.real {a | delta ≤ ‖V n a - 0‖} < b / 2 at hn
      linarith
  have ht := ENNReal.tendsto_ofReal hreal
  simpa only [Function.comp_apply, ENNReal.ofReal_zero, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top μ _), sub_zero, Real.norm_eq_abs] using ht

-- The empirical squared score error is nonnegative. Conditional Markov
-- follows from the squared version by applying it to its square root.
-- @node: conditional_nonneg_tendsto_probability_zero
/-- Suppose [each conditioning information set is contained in the ambient information](hyp:hm),
[V is measurable with respect to it at each sample size](hyp:hV),
[each E is integrable](hyp:hE), [each E is nonnegative almost surely](hyp:hpos), and
[the conditional expectation of E is at most V almost surely](hyp:hbound).
If [V converges to zero in probability](hyp:hrate), then [E converges to zero in probability](goal). -/
lemma conditional_nonneg_tendsto_probability_zero {A : Type*} [mA : MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace A) (hm : ∀ n, m n ≤ mA)
    [∀ n, SigmaFinite (μ.trim (hm n))]
    (E V : ℕ → A → ℝ) (hV : ∀ n, Measurable[m n] (V n))
    (hE : ∀ n, Integrable (E n) μ)
    (hpos : ∀ n, 0 ≤ᵐ[μ] E n)
    (hbound : ∀ n, μ[E n | m n] ≤ᵐ[μ] V n)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) V atTop
      (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) E atTop
      (fun _ _ => 0) := by
  have hsq (n : ℕ) : (fun a => Real.sqrt (E n a) ^ 2) =ᵐ[μ] E n :=
    (hpos n).mono (fun a ha => Real.sq_sqrt ha)
  have hs := conditional_sq_tendsto_probability_zero μ m hm
    (fun n a => Real.sqrt (E n a)) V hV
    (fun n => (hE n).congr (hsq n).symm)
    (fun n => (condExp_congr_ae (m := m n) (hsq n)).trans_le (hbound n)) hrate
  have hc : Continuous (fun x : ℝ => x ^ 2) := by fun_prop
  have ht := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hc.continuousAt hs
  simp only [zero_pow (by norm_num : 2 ≠ 0)] at ht
  exact TendstoInMeasure.congr (fun n => hsq n) (Eventually.of_forall (fun _ => rfl)) ht

-- Conditional independence of centered evaluation errors supplies the zero
-- cross-moments. The finite expansion below uses those identities directly,
-- so it needs no topology or standard Borel assumption on the sample space.
-- @node: conditional_centered_sum_second_moment
/-- For a finite family of random variables, if [each variable is square integrable](hyp:hf)
and [the conditional expectation of every product of distinct variables is zero almost surely](hyp:hcross),
then [the conditional second moment of their sum equals the sum of their conditional second moments almost surely](goal). -/
lemma conditional_centered_sum_second_moment {A ι : Type*}
    [mA : MeasurableSpace A] [Fintype ι]
    (μ : Measure A) (m : MeasurableSpace A) (f : ι → A → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hcross : ∀ i j, i ≠ j → μ[fun a => f i a * f j a | m] =ᵐ[μ] 0) :
    μ[fun a => (∑ i, f i a) ^ 2 | m] =ᵐ[μ]
      (fun a => ∑ i, μ[fun a => f i a ^ 2 | m] a) := by
  classical
  let : MeasurableSpace A := mA
  have hid : (fun a => (∑ i, f i a) ^ 2) =
      ∑ i, ∑ j, (fun a => f i a * f j a) := by
    funext a
    simp only [Finset.sum_apply, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have houter := condExp_finsetSum
    (f := fun i => ∑ j, (fun a => f i a * f j a))
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      integrable_finsetSum' Finset.univ (fun j _ => (hf i).integrable_mul (hf j))) m
  have hinner (i : ι) := condExp_finsetSum
    (f := fun j => (fun a => f i a * f j a))
    (fun j (_ : j ∈ (Finset.univ : Finset ι)) => (hf i).integrable_mul (hf j)) m
  have hpair (i j : ι) : μ[fun a => f i a * f j a | m] =ᵐ[μ]
      (fun a => if i = j then μ[fun a => f i a ^ 2 | m] a else 0) := by
    by_cases hij : i = j
    · subst j
      filter_upwards [] with a
      simp only [ite_true, pow_two]
    · filter_upwards [hcross i j hij] with a ha
      simpa only [if_neg hij, Pi.zero_apply] using ha
  rw [hid]
  filter_upwards [houter, ae_all_iff.mpr hinner,
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpair i))] with a ho hi hp
  rw [ho]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  simp only [Finset.sum_apply]
  simp_rw [hp i]
  simp

-- The evaluation average is normalized by sqrt of its size. Equal
-- conditional second moments therefore do not acquire a growing sample-size
-- factor. This is the conditional variance calculation in the DML roadmap.
-- @node: conditional_normalized_sum_second_moment
/-- For a nonempty finite family, suppose [every variable is square integrable](hyp:hf),
[distinct variables have zero conditional cross-moments almost surely](hyp:hcross), and
[every conditional second moment equals V almost surely](hyp:hsecond).
Then [the sum divided by the square root of the number of variables has conditional second moment V almost surely](goal). -/
lemma conditional_normalized_sum_second_moment {A ι : Type*}
    [mA : MeasurableSpace A] [Fintype ι] [Nonempty ι]
    (μ : Measure A) (m : MeasurableSpace A) (f : ι → A → ℝ) (V : A → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hcross : ∀ i j, i ≠ j → μ[fun a => f i a * f j a | m] =ᵐ[μ] 0)
    (hsecond : ∀ i, μ[fun a => f i a ^ 2 | m] =ᵐ[μ] V) :
    μ[fun a => ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ * ∑ i, f i a) ^ 2 | m]
      =ᵐ[μ] V := by
  classical
  let : MeasurableSpace A := mA
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsq : ((Real.sqrt (Fintype.card ι : ℝ))⁻¹) ^ 2 =
      (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hcard.le]
  have hid : (fun a => ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ * ∑ i, f i a) ^ 2) =
      (Fintype.card ι : ℝ)⁻¹ • (fun a => (∑ i, f i a) ^ 2) := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, hsq]
  rw [hid]
  filter_upwards [condExp_smul (Fintype.card ι : ℝ)⁻¹
      (fun a => (∑ i, f i a) ^ 2) m,
    conditional_centered_sum_second_moment μ m f hf hcross,
    ae_all_iff.mpr hsecond] with a hc hs hv
  simp only [Pi.smul_apply, smul_eq_mul] at hc
  rw [hc, hs]
  simp_rw [hv]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

-- The diagonal moments may be bounded by a training-dependent score-error
-- energy; equality of their conditional laws is not required for Chebyshev.
-- @node: conditional_normalized_sum_second_moment_le
/-- For a nonempty finite family, suppose [every variable is square integrable](hyp:hf),
[distinct variables have zero conditional cross-moments almost surely](hyp:hcross), and
[every conditional second moment is at most V almost surely](hyp:hsecond).
Then [the conditional second moment of the sum divided by the square root of the number of variables is at most V almost surely](goal). -/
lemma conditional_normalized_sum_second_moment_le {A ι : Type*}
    [mA : MeasurableSpace A] [Fintype ι] [Nonempty ι]
    (μ : Measure A) (m : MeasurableSpace A) (f : ι → A → ℝ) (V : A → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hcross : ∀ i j, i ≠ j → μ[fun a => f i a * f j a | m] =ᵐ[μ] 0)
    (hsecond : ∀ i, μ[fun a => f i a ^ 2 | m] ≤ᵐ[μ] V) :
    μ[fun a => ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ * ∑ i, f i a) ^ 2 | m]
      ≤ᵐ[μ] V := by
  classical
  let : MeasurableSpace A := mA
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsq : ((Real.sqrt (Fintype.card ι : ℝ))⁻¹) ^ 2 =
      (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hcard.le]
  have hid : (fun a => ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ * ∑ i, f i a) ^ 2) =
      (Fintype.card ι : ℝ)⁻¹ • (fun a => (∑ i, f i a) ^ 2) := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, hsq]
  rw [hid]
  filter_upwards [condExp_smul (Fintype.card ι : ℝ)⁻¹
      (fun a => (∑ i, f i a) ^ 2) m,
    conditional_centered_sum_second_moment μ m f hf hcross,
    ae_all_iff.mpr hsecond] with a hc hs hv
  simp only [Pi.smul_apply, smul_eq_mul] at hc
  rw [hc, hs]
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, V a := by
      gcongr
      exact hv _
    _ = V a := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

-- A triangular evaluation sample has n+1 observations. Conditional second
-- moments going to zero in probability suffice; their unconditional means
-- need not go to zero. This consumes the moment calculation, rather than
-- assuming negligibility of the normalized empirical fluctuation.
-- @node: conditional_normalized_sum_tendsto_probability_zero
/-- Consider [rows of n + 1 random variables](hyp:f) with [conditioning information contained in the ambient information](hyp:hm).
If [all variables are square integrable](hyp:hf), [distinct variables within each row have zero conditional cross-moments](hyp:hcross),
[their conditional second moments are bounded by V almost surely](hyp:hsecond),
[V is measurable with respect to each row's conditioning information](hyp:hV), and
[V converges to zero in probability](hyp:hrate), then [the row sum divided by the square root of n + 1 converges to zero in probability](goal). -/
lemma conditional_normalized_sum_tendsto_probability_zero {A : Type*}
    [mA : MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace A) (hm : ∀ n, m n ≤ mA)
    [∀ n, SigmaFinite (μ.trim (hm n))]
    (f : ∀ n, Fin (n + 1) → A → ℝ) (V : ℕ → A → ℝ)
    (hf : ∀ n i, MemLp (f n i) 2 μ)
    (hcross : ∀ n i j, i ≠ j →
      μ[fun a => f n i a * f n j a | m n] =ᵐ[μ] 0)
    (hsecond : ∀ n i, μ[fun a => f n i a ^ 2 | m n] ≤ᵐ[μ] V n)
    (hV : ∀ n, Measurable[m n] (V n))
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) V atTop
      (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, f n i a)
      atTop (fun _ _ => 0) := by
  classical
  let : MeasurableSpace A := mA
  apply conditional_sq_tendsto_probability_zero μ m hm _ V hV _ _ hrate
  · intro n
    have hs : MemLp (fun a => ∑ i, f n i a) 2 μ := by
      exact memLp_finsetSum Finset.univ (fun i _ => hf n i)
    exact (hs.const_mul (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹).integrable_sq
  · intro n
    simpa only [Fintype.card_fin] using
      conditional_normalized_sum_second_moment_le μ (m n) (f n) (V n)
        (hf n) (hcross n) (hsecond n)

-- Apply the calculation to score differences centered by their conditional
-- training mean. Mathlib's conditional variance inequality controls each
-- centered moment by the uncentered L2 score error from the paper's roadmap.
-- @node: conditional_centered_score_sum_tendsto_probability_zero
/-- For [rows of n + 1 score errors](hyp:g), suppose [each row's conditioning information is contained in the ambient information](hyp:hm),
[all score errors are square integrable](hyp:hg), [their conditional means equal the row's bias almost surely](hyp:hmean),
[distinct errors after subtracting that bias have zero conditional cross-moments](hyp:hcross), and
[the uncentered conditional second moments are at most V almost surely](hyp:henergy).
If [V is measurable with respect to the conditioning information](hyp:hV) and [converges to zero in probability](hyp:hrate),
then [the sum of the n + 1 bias-centered errors divided by the square root of n + 1 converges to zero in probability](goal). -/
lemma conditional_centered_score_sum_tendsto_probability_zero {A : Type*}
    [mA : MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace A) (hm : ∀ n, m n ≤ mA)
    [∀ n, SigmaFinite (μ.trim (hm n))]
    (g : ∀ n, Fin (n + 1) → A → ℝ) (bias V : ℕ → A → ℝ)
    (hg : ∀ n i, MemLp (g n i) 2 μ)
    (hmean : ∀ n i, μ[g n i | m n] =ᵐ[μ] bias n)
    (hcross : ∀ n i j, i ≠ j →
      μ[fun a => (g n i a - bias n a) * (g n j a - bias n a) | m n] =ᵐ[μ] 0)
    (henergy : ∀ n i, μ[fun a => g n i a ^ 2 | m n] ≤ᵐ[μ] V n)
    (hV : ∀ n, Measurable[m n] (V n))
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) V atTop
      (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i, (g n i a - bias n a)) atTop (fun _ _ => 0) := by
  let : MeasurableSpace A := mA
  apply conditional_normalized_sum_tendsto_probability_zero μ m hm
    (fun n i a => g n i a - bias n a) V _ hcross _ hV hrate
  · intro n i
    have hb : MemLp (bias n) 2 μ :=
      (MemLp.condExp (m := m n) (by norm_num) (hg n i)).ae_eq (hmean n i)
    exact (hg n i).sub hb
  · intro n i
    have heq : (fun a => (g n i a - bias n a) ^ 2) =ᵐ[μ]
        (g n i - μ[g n i | m n]) ^ 2 := by
      filter_upwards [hmean n i] with a ha
      simp only [Pi.pow_apply, Pi.sub_apply, ha]
    have hvar := condVar_ae_le_condExp_sq (hm n) (hg n i)
    have hcenter := condExp_congr_ae (m := m n) heq
    exact hcenter.trans_le (hvar.trans (henergy n i))

-- @node: dml_law_of_conditional_fluctuation
/-- Suppose [the conditioning information is contained in the ambient information at each sample size](hyp:hm),
[F is almost everywhere measurable](hyp:hF), [the oracle term U converges in law to Q](hyp:hU), and
[the bias is negligible in probability relative to the inverse square root of twice the quantity n + 1](hyp:hbias).
If [V is measurable with respect to the conditioning information](hyp:hV), [T has an integrable square](hyp:hT),
[its conditional second moment is bounded by V almost surely](hyp:hbound), [V converges to zero in probability](hyp:hrate), and
[F equals U plus the bias multiplied by the square root of n + 1 plus T almost surely](hyp:hdecomp),
then [F converges in law to Q](goal). -/
lemma dml_law_of_conditional_fluctuation {A : Type*} [mA : MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace A) (hm : ∀ n, m n ≤ mA)
    [∀ n, SigmaFinite (μ.trim (hm n))]
    (F U bias T V : ℕ → A → ℝ) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hU : Causalean.Stat.Modes.TendstoInLaw (fun _ => μ) U atTop Q)
    (hbias : Causalean.Stat.IsLittleOp bias
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ)
    (hV : ∀ n, Measurable[m n] (V n))
    (hT : ∀ n, Integrable (fun a => T n a ^ 2) μ)
    (hbound : ∀ n, μ[fun a => T n a ^ 2 | m n] ≤ᵐ[μ] V n)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) V atTop
      (fun _ _ => 0))
    (hdecomp : ∀ n, ∀ᵐ a ∂μ,
      F n a = U n a + Real.sqrt ((n + 1 : ℕ) : ℝ) * bias n a + T n a) :
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ) F atTop Q := by
  have hb := dml_root_n_bias_tendsto_probability μ bias hbias
  have ht := conditional_sq_tendsto_probability_zero μ m hm T V hV hT hbound hrate
  have hn : Continuous (fun x : ℝ => -x) := by fun_prop
  have hneg := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hn.continuousAt ht
  simp only [neg_zero] at hneg
  have hsum := hb.sub hneg
  simp only [sub_neg_eq_add, sub_zero] at hsum
  have hdiff : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => F n a - U n a) atTop (fun _ _ => 0) := by
    apply TendstoInMeasure.congr _ (Eventually.of_forall (fun _ => rfl)) hsum
    intro n
    filter_upwards [hdecomp n] with a ha
    rw [ha]
    ring
  exact tendstoInDistribution_of_tendstoInMeasure_sub F id hU hdiff hF

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [mA : MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z) {μ : Measure A} [IsProbabilityMeasure μ]

-- @node: dmlRV_oracle_law_of_conditional_fluctuation
/-- Suppose [the conditioning information is contained in the ambient information](hyp:hm),
[the evaluation split is nonempty almost surely at sample sizes twice the quantity n + 1](hyp:hI),
[the centered DML estimator multiplied by the square root of n + 1 is almost everywhere measurable](hyp:hF), and
[the similarly scaled evaluation average of the centered true score converges in law to Q](hyp:hU).
If [the bias is negligible relative to the inverse square root of twice the quantity n + 1](hyp:hbias),
[V is measurable with respect to the conditioning information](hyp:hV),
[the scaled evaluation average of the score error minus its bias has an integrable square](hyp:hT),
[its conditional second moment is at most V almost surely](hyp:hbound), and [V converges to zero in probability](hyp:hrate),
then [the DML estimator centered at θ and multiplied by the square root of n + 1 converges in law to Q](goal). -/
lemma dmlRV_oracle_law_of_conditional_fluctuation (S : ObservedSample M μ)
    (I₂ : SampleSplit A) (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (theta : ℝ) (bias V : ℕ → A → ℝ)
    (m : ℕ → MeasurableSpace A) (hm : ∀ n, m n ≤ mA)
    [∀ n, SigmaFinite (μ.trim (hm n))]
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hI : ∀ n, ∀ᵐ a ∂μ, (I₂ (2 * (n + 1)) a).Nonempty)
    (hF : ∀ n, AEMeasurable (fun a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) μ)
    (hU : Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
          ∑ i ∈ I₂ (2 * (n + 1)) a, (truth (S.Z i a) - theta)) atTop Q)
    (hbias : Causalean.Stat.IsLittleOp bias
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ)
    (hV : ∀ n, Measurable[m n] (V n))
    (hT : ∀ n, Integrable (fun a =>
      (Real.sqrt ((n + 1 : ℕ) : ℝ) * ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (score (2 * (n + 1)) a (S.Z i a) - truth (S.Z i a) - bias n a)) ^ 2) μ)
    (hbound : ∀ n, μ[fun a =>
      (Real.sqrt ((n + 1 : ℕ) : ℝ) * ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (score (2 * (n + 1)) a (S.Z i a) - truth (S.Z i a) - bias n a)) ^ 2
        | m n] ≤ᵐ[μ] V n)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) V atTop
      (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) atTop Q := by
  apply dml_law_of_conditional_fluctuation μ m hm _ _ bias _ V Q
    hF hU hbias hV hT hbound hrate
  intro n
  filter_upwards [hI n] with a ha
  exact dmlRV_scaled_oracle_decomposition M S I₂ score truth (2 * (n + 1)) a ha
    theta (bias n a) (Real.sqrt ((n + 1 : ℕ) : ℝ))

-- Conditional Markov replaces a conditional LLN for the nonnegative
-- empirical score error. The oracle second moment still uses its usual LLN.
-- @node: varianceRV_consistent_of_conditional_score_error
/-- Suppose [each conditioning information set is contained in the ambient information](hyp:hm),
[the evaluation splits along the sample-size sequence N are nonempty almost surely](hyp:hI),
[V is measurable with respect to the conditioning information](hyp:hV),
[the evaluation average of squared score errors is integrable](hyp:hE), and
[its conditional expectation is at most V almost surely](hyp:hbound).
If [V converges to zero in probability](hyp:hrate), [the evaluation average of the squared true score centered at θ converges in probability to σ squared](hyp:hOracle), and
[the DML estimator converges in probability to θ](hyp:hMean), then [the estimated score variance converges in probability to σ squared](goal). -/
lemma varianceRV_consistent_of_conditional_score_error (S : ObservedSample M μ)
    (I₂ : SampleSplit A) (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (N : ℕ → ℕ) (theta sigmaSq : ℝ) (V : ℕ → A → ℝ)
    (m : ℕ → MeasurableSpace A) (hm : ∀ n, m n ≤ mA)
    [∀ n, SigmaFinite (μ.trim (hm n))]
    (hI : ∀ n, ∀ᵐ a ∂μ, (I₂ (N n) a).Nonempty)
    (hV : ∀ n, Measurable[m n] (V n))
    (hE : ∀ n, Integrable (fun a => ((I₂ (N n) a).card : ℝ)⁻¹ *
      ∑ i ∈ I₂ (N n) a, (score (N n) a (S.Z i a) - truth (S.Z i a)) ^ 2) μ)
    (hbound : ∀ n, μ[fun a => ((I₂ (N n) a).card : ℝ)⁻¹ *
      ∑ i ∈ I₂ (N n) a, (score (N n) a (S.Z i a) - truth (S.Z i a)) ^ 2
      | m n] ≤ᵐ[μ] V n)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) V atTop
      (fun _ _ => 0))
    (hOracle : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (N n) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (N n) a, (truth (S.Z i a) - theta) ^ 2) atTop
      (fun _ _ => sigmaSq))
    (hMean : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (N n) a - theta) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (N n) a) atTop
      (fun _ _ => sigmaSq) := by
  apply varianceRV_consistent_of_empirical_score_error M S I₂ score truth N
    theta sigmaSq hI _ hOracle hMean
  apply conditional_nonneg_tendsto_probability_zero μ m hm _ V hV hE _ hbound hrate
  intro n
  apply Eventually.of_forall
  intro a
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun i hi => sq_nonneg _))

end Papers.TbsPrteOptimalTransport
