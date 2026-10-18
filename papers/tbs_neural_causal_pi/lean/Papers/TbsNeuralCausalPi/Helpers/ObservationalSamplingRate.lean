module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelCompactLatents
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelZeroDimension
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalRateExponents
public import Papers.TbsNeuralCausalPi.Helpers.EstimationFeasibility
/-! # Observational rates and almost-sure control for complete observations

The finite-stratum sampling assembly is specialized to the prescribed rate.
The positive-dimensional conditional joint-latent tails remain explicit local
inputs; neither they nor the full consistency theorem are asserted here.
The zero-dimensional conclusion uses the proved finite-observation estimate.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- If [all category-specific tail coefficients B are nonnegative](hyp:hB), then
[eventually the logarithmic frequency-tail expression plus the small-count and B-weighted inverse-fourth-power terms for positive-weight labels is at most the inverse fourth power of sample size times the sum of twice the number of labels, twice its square, and all B coefficients](goal). -/
-- @node: observational_fintype_stratified_polynomial_tail_sum
lemma observational_fintype_stratified_polynomial_tail_sum
    {A : Type*} [Fintype A] [Nonempty A]
    (p B : A → ℝ) (hB : ∀ a, 0 ≤ B a) :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (2 * Fintype.card A * Real.exp (-2 * m *
        (((Fintype.card A : ℝ) * Real.sqrt (2 * Real.log m / m)) /
          Fintype.card A)^2)) +
      (∑ a, if 0 < p a then
        ENNReal.ofReal (2 * Fintype.card A * Real.exp (-2 * m *
          ((p a / 2) / Fintype.card A)^2)) +
        ENNReal.ofReal (B a * (m : ℝ)^(-(4 : ℤ))) else 0) ≤
      ENNReal.ofReal ((2 * Fintype.card A + (Fintype.card A : ℝ) *
        (2 * Fintype.card A) + ∑ a, B a) * (m : ℝ)^(-(4 : ℤ))) := by
  let E := Fintype.equivFin A
  have h := observational_stratified_polynomial_tail_sum
    (Fintype.card_pos : 0 < Fintype.card A)
    (p ∘ E.symm) (B ∘ E.symm) (fun a => hB (E.symm a))
  filter_upwards [h] with m hm
  simp only [Function.comp_apply] at hm
  have hsum := E.symm.sum_comp (fun a => if 0 < p a then
    ENNReal.ofReal (2 * Fintype.card A * Real.exp (-2 * m *
      ((p a / 2) / Fintype.card A)^2)) +
      ENNReal.ofReal (B a * (m : ℝ)^(-(4 : ℤ))) else 0)
  rw [hsum, E.symm.sum_comp B] at hm
  exact hm

/-- If [B is nonnegative](hyp:hB) and [eventually the probability of the bad event at sample size m is at most B times m to the power minus four](hyp:hbad),
then [almost surely only finitely many of these bad events occur](goal). -/
-- @node: observational_ae_eventually_of_inverse_fourth_bound
lemma observational_ae_eventually_of_inverse_fourth_bound
    {Omega : Type*} [MeasurableSpace Omega] (Q : Measure Omega)
    (bad : ℕ → Set Omega) (B : ℝ) (hB : 0 ≤ B)
    (hbad : ∀ᶠ m : ℕ in atTop,
      Q (bad m) ≤ ENNReal.ofReal (B * (m : ℝ)^(-(4 : ℤ)))) :
    ∀ᵐ w ∂Q, ∀ᶠ m : ℕ in atTop, w ∉ bad m := by
  apply estimation_ae_eventually_of_inverse_square_bound Q bad B
  filter_upwards [hbad, eventually_ge_atTop (1 : ℕ)] with m hm hm1
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hB
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  simpa only [zpow_neg, zpow_ofNat] using
    inv_anti₀ (by positivity : (0 : ℝ) < (m : ℝ)^2)
      (pow_le_pow_right₀ hmR (by norm_num : 2 ≤ 4))

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- For a Euclidean structural causal model, take [nonnegative bounds K on variable magnitudes and L on mechanism Lipschitz constants](hyp:K,L),
and assume [the variables satisfy the bound K](hyp:hK) and [the continuous mechanisms satisfy the Lipschitz bound L](hyp:hL).
Consider [complete-observation samples indexed by sample size](hyp:sample), with [measurable observations](hyp:hsample),
[independence within each sample size](hyp:hind), and [each observation distributed according to the model's observational law](hyp:hlaw).
Suppose [every stratum-specific tail coefficient B is nonnegative](hyp:hB) and
[eventually, for each positive-mass categorical stratum and every latent sample size at least half its expected count, the compact latent empirical Wasserstein failure probability at the prescribed observational rate is at most B times the inverse fourth power of the full sample size](hyp:hbound).
Then [positive constants A and B' exist such that eventually the full empirical observational Wasserstein error exceeds A times the prescribed rate with probability at most B' times the inverse fourth power of sample size](goal). -/
-- @node: canonical_observational_sampling_rate_of_compact_latent_tails
lemma canonical_observational_sampling_rate_of_compact_latent_tails
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (M : EuclideanSCM kind dims)
    (K L : ℝ≥0) (hK : VariablesBoundedAt M K)
    (hL : ContinuousMechanismsLipschitz M L)
    (sample : ∀ m, Fin m → Omega → Joint kind)
    (hsample : ∀ m i, Measurable (sample m i))
    (hind : ∀ m, iIndepFun (sample m) Q)
    (hlaw : ∀ m i, Q.map (sample m i) = observationalLaw M)
    (B : CategoricalStratum kind → ℝ) (hB : ∀ c, 0 ≤ B c)
    (hbound : ∀ᶠ m : ℕ in atTop, ∀ c,
      0 < (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) →
      ∀ N : ℕ, m * (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) / 2 ≤ N →
      (Measure.pi (fun _ : Fin N =>
        (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K))))
        {z | ¬ wasserstein1
          (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K))
          (empiricalMeasure z) ≤ ENNReal.ofReal (observationalRateScale (∑ j, dims j) m)} ≤
        ENNReal.ofReal (B c * (m : ℝ)^(-(4 : ℤ)))) :
    ∃ A B' : ℝ, 0 < A ∧ 0 < B' ∧ ∀ᶠ m : ℕ in atTop,
      Q {w | ¬ wasserstein1 (observationalLaw M)
        (empiricalMeasure (fun i => sample m i w)) ≤
          ENNReal.ofReal (A * observationalRateScale (∑ j, dims j) m)} ≤
        ENNReal.ofReal (B' * (m : ℝ)^(-(4 : ℤ))) := by
  classical
  letI : Nonempty (CategoricalStratum kind) := ⟨fun _ => ⟨0, by omega⟩⟩
  let k := Fintype.card (CategoricalStratum kind)
  let D : ℝ := 2 * K * Fintype.card (Σ i, Fin (valueDim (kind i)))
  let T : ℝ := fixedLabelLipschitzBudget M L (n * n + n)
  let A : ℝ := T + D / 2 * k * Real.sqrt 2 + 1
  let B' : ℝ := 2 * k + (k : ℝ) * (2 * k) + ∑ c, B c
  have hk : 0 < k := Fintype.card_pos
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hT : 0 ≤ T := NNReal.coe_nonneg _
  have hB' : 0 < B' := by
    have hsum : 0 ≤ ∑ c, B c := Finset.sum_nonneg (fun c _ => hB c)
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    dsimp [B']
    positivity
  refine ⟨A, B', by dsimp [A]; positivity, hB', ?_⟩
  have hlog : Tendsto (fun m : ℕ => Real.log m) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hbound,
    observational_fintype_stratified_polynomial_tail_sum
      (fun c => (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c})) B hB,
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℕ)] with m htail hsum hmLog hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hs : 0 < observationalRateScale (∑ j, dims j) m :=
    observationalRateScale_pos _ (by exact_mod_cast hm)
  have he : 0 < (k : ℝ) * Real.sqrt (2 * Real.log m / m) := by
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hfreq := observational_frequency_le_sampling_rate (∑ j, dims j) hmR hmLog
  have hfreq' : Real.sqrt (2 * Real.log m / m) ≤
      Real.sqrt 2 * observationalRateScale (∑ j, dims j) m := by
    simpa only [observationalRateScale, mul_assoc] using hfreq
  have htol : T * observationalRateScale (∑ j, dims j) m +
      D / 2 * (k * Real.sqrt (2 * Real.log m / m)) ≤
      A * observationalRateScale (∑ j, dims j) m := by
    calc
      _ ≤ T * observationalRateScale (∑ j, dims j) m +
          D / 2 * (k * (Real.sqrt 2 * observationalRateScale (∑ j, dims j) m)) := by
        gcongr
      _ ≤ _ := by dsimp [A]; nlinarith
  have hraw := iid_canonical_observational_failure_le_of_compact_latent_tails
    Q M K L hK hL (by omega : 0 < m) (sample m) (hsample m) (hind m) (hlaw m)
    (observationalRateScale (∑ j, dims j) m)
    (T * observationalRateScale (∑ j, dims j) m)
    (k * Real.sqrt (2 * Real.log m / m)) (mul_nonneg hT hs.le) he le_rfl
    (fun c => ENNReal.ofReal (B c * (m : ℝ)^(-(4 : ℤ)))) htail
  apply le_trans (measure_mono ?_) (hraw.trans hsum)
  intro w hw hgood
  exact hw (hgood.trans (ENNReal.ofReal_le_ofReal htol))

/-- If [the total latent dimension is zero](hyp:hd), consider [complete-observation samples indexed by sample size](hyp:sample)
with [measurable observations](hyp:hsample), [independence within each sample size](hyp:hind),
and [each observation distributed according to the model's observational law](hyp:hlaw).
Then [there is a positive constant A such that almost surely the empirical observational Wasserstein error is eventually at most A times the prescribed observational rate](goal). -/
-- @node: zero_latent_observational_sampling_ae_eventually
lemma zero_latent_observational_sampling_ae_eventually
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (M : EuclideanSCM kind dims) (hd : ∑ j, dims j = 0)
    (sample : ∀ m, Fin m → Omega → Joint kind)
    (hsample : ∀ m i, Measurable (sample m i))
    (hind : ∀ m, iIndepFun (sample m) Q)
    (hlaw : ∀ m i, Q.map (sample m i) = observationalLaw M) :
    ∃ A : ℝ, 0 < A ∧ ∀ᵐ w ∂Q, ∀ᶠ m : ℕ in atTop,
      wasserstein1 (observationalLaw M) (empiricalMeasure (fun i => sample m i w)) ≤
        ENNReal.ofReal (A * observationalRateScale (∑ j, dims j) m) := by
  obtain ⟨A, B, hA, hB, htail⟩ :=
    zero_latent_observational_sampling_rate Q M hd sample hsample hind hlaw
  refine ⟨A, hA, ?_⟩
  have htail' : ∀ᶠ m : ℕ in atTop,
      Q {w | ¬ wasserstein1 (observationalLaw M)
        (empiricalMeasure (fun i => sample m i w)) ≤
          ENNReal.ofReal (A * observationalRateScale (∑ j, dims j) m)} ≤
        ENNReal.ofReal (B * (m : ℝ)^(-(4 : ℤ))) := by
    simpa only [hd, observationalRateScale, max_eq_left (by omega : 0 ≤ 2),
      Nat.cast_ofNat, zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_assoc] using htail
  filter_upwards [observational_ae_eventually_of_inverse_fourth_bound Q _ B hB.le htail']
    with w hw
  filter_upwards [hw] with m hm
  exact not_not.mp hm

/-- If [the total latent dimension is zero](hyp:hd), consider [complete-observation samples indexed by sample size](hyp:sample)
with [measurable observations](hyp:hsample), [independence within each sample size](hyp:hind),
and [each observation distributed according to the model's observational law](hyp:hlaw).
Then [the Wasserstein distance between the empirical observational law and the model's observational law converges to zero almost surely as sample size grows](goal). -/
-- @node: zero_latent_observational_wasserstein_tendsto_zero_ae
lemma zero_latent_observational_wasserstein_tendsto_zero_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (M : EuclideanSCM kind dims) (hd : ∑ j, dims j = 0)
    (sample : ∀ m, Fin m → Omega → Joint kind)
    (hsample : ∀ m i, Measurable (sample m i))
    (hind : ∀ m, iIndepFun (sample m) Q)
    (hlaw : ∀ m i, Q.map (sample m i) = observationalLaw M) :
    ∀ᵐ w ∂Q, Tendsto (fun m => wasserstein1 (observationalLaw M)
      (empiricalMeasure (fun i => sample m i w))) atTop (𝓝 0) := by
  obtain ⟨A, hA, hrate⟩ :=
    zero_latent_observational_sampling_ae_eventually Q M hd sample hsample hind hlaw
  have hlim : Tendsto
      (fun m : ℕ => ENNReal.ofReal (A * observationalRateScale (∑ j, dims j) m))
      atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal
        (tendsto_const_nhds.mul (observationalRateScale_tendsto_zero (∑ j, dims j)))
  filter_upwards [hrate] with w hw
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => bot_le)) hw

end Papers.TbsNeuralCausalPi
