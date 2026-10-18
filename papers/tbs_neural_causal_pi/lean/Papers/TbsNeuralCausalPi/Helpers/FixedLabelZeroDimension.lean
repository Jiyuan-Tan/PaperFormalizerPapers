module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelStrata
public import Papers.TbsNeuralCausalPi.Helpers.FiniteObservationSampling
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalTailRates
/-! # Complete observational sampling with no non-Gumbel latent coordinates

The categorical Gumbels remain random. After fixing their selected labels,
the complete observation is deterministic. The actual canonical law therefore
satisfies the finite-observation sampling bound without a latent tail input.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- If [the total non-Gumbel latent dimension is zero](hyp:hd), [every joint
non-Gumbel latent vector equals zero](goal). -/
-- @node: latent_eq_zero_of_total_dimension_zero
lemma latent_eq_zero_of_total_dimension_zero (hd : ∑ j, dims j = 0)
    (z : Latent dims) : z = 0 := by
  apply WithLp.ofLp_injective
  funext a
  obtain ⟨j, k⟩ := a
  have hj : dims j ≤ ∑ j, dims j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hk := k.isLt
  omega

/-- For [a structural causal model](hyp:M) and [a complete categorical
stratum](hyp:c), [the zero-latent observation](goal) is the fixed-label readout
with that stratum's categorical assignments and the non-Gumbel latent vector set to zero. -/
-- @node: zeroLatentObservation
def zeroLatentObservation (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind) : Joint kind :=
  fixedLabelObservation M (categoricalStratumAssignment c) 0

/-- If [the total non-Gumbel latent dimension is zero](hyp:hd), [the factual
joint observation at every exogenous input equals the zero-latent observation
for its decoded complete categorical stratum](goal). -/
-- @node: factual_eq_zeroLatentObservation
lemma factual_eq_zeroLatentObservation (M : EuclideanSCM kind dims)
    (hd : ∑ j, dims j = 0) (u : Exogenous kind dims) :
    intervenedEval M (fun _ => none) u =
      zeroLatentObservation M
        (observedCategoricalStratum (intervenedEval M (fun _ => none) u)) := by
  exact (factual_eq_fixedLabelObservation_stratum M u).trans
    (congrArg (fixedLabelObservation M (categoricalStratumAssignment
      (observedCategoricalStratum (intervenedEval M (fun _ => none) u))))
        (latent_eq_zero_of_total_dimension_zero hd (jointNonGumbel u)))

/-- If [the total non-Gumbel latent dimension is zero](hyp:hd), [an observation
equals the zero-latent observation for its decoded complete categorical stratum
almost surely under the observational law](goal). -/
-- @node: observational_ae_eq_zeroLatentObservation
lemma observational_ae_eq_zeroLatentObservation (M : EuclideanSCM kind dims)
    (hd : ∑ j, dims j = 0) :
    ∀ᵐ v ∂observationalLaw M,
      v = zeroLatentObservation M (observedCategoricalStratum v) := by
  have hmeas : MeasurableSet {v : Joint kind |
      v = zeroLatentObservation M (observedCategoricalStratum v)} := by
    apply measurableSet_eq_fun measurable_id
    exact (measurable_of_finite (zeroLatentObservation M)).comp (by fun_prop)
  apply (ae_map_iff (by fun_prop [intervenedEval]) hmeas).mpr
  exact Filter.Eventually.of_forall (factual_eq_zeroLatentObservation M hd)

/-- If [the total non-Gumbel latent dimension is zero](hyp:hd) and [the complete
categorical stratum c has nonzero observational probability](hyp:hc), [the
observational law conditional on c is the point mass at its zero-latent
observation](goal). -/
-- @node: categoricalStratum_conditional_observation_dirac_of_dimension_zero
lemma categoricalStratum_conditional_observation_dirac_of_dimension_zero
    (M : EuclideanSCM kind dims) (hd : ∑ j, dims j = 0)
    (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0) :
    cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) =
      Measure.dirac (zeroLatentObservation M c) := by
  let := M.probability
  let : IsProbabilityMeasure (observationalLaw M) := by
    exact Measure.isProbabilityMeasure_map (by fun_prop [intervenedEval])
  exact cond_eq_dirac_of_ae_label_determines (observationalLaw M)
    observedCategoricalStratum (by fun_prop) (zeroLatentObservation M)
    (observational_ae_eq_zeroLatentObservation M hd) c hc

/-- If [the total non-Gumbel latent dimension is zero](hyp:hd), [stratum c has
nonzero observational probability](hyp:hc), and [the sample size N is positive](hyp:hN),
[N independent draws from the observational law conditional on c have zero
probability of exceeding any real tolerance t, interpreted as a nonnegative
threshold, in first Wasserstein distance from that conditional law](goal). -/
-- @node: categoricalStratum_conditional_sampling_failure_zero
lemma categoricalStratum_conditional_sampling_failure_zero
    (M : EuclideanSCM kind dims) (hd : ∑ j, dims j = 0)
    (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0)
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    (Measure.pi (fun _ : Fin N =>
      cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c})))
      {x | ¬ wasserstein1
        (cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}))
        (empiricalMeasure x) ≤ ENNReal.ofReal t} = 0 := by
  rw [categoricalStratum_conditional_observation_dirac_of_dimension_zero M hd c hc]
  exact dirac_empirical_wasserstein_failure_zero hN _ t

/-- For [a structural causal model](hyp:M), [the zero-latent observation diameter
bound](goal) is twice the sum, over all complete categorical strata, of the
one-norms of their zero-latent observations. -/
-- @node: zeroLatentObservationDiameter
def zeroLatentObservationDiameter (M : EuclideanSCM kind dims) : ℝ :=
  2 * ∑ c : CategoricalStratum kind, ‖zeroLatentObservation M c‖

/-- [The zero-latent observation diameter bound is nonnegative](goal). -/
-- @node: zeroLatentObservationDiameter_nonneg
lemma zeroLatentObservationDiameter_nonneg (M : EuclideanSCM kind dims) :
    0 ≤ zeroLatentObservationDiameter M := by
  unfold zeroLatentObservationDiameter
  positivity

/-- [The distance between the zero-latent observations of any two complete
categorical strata is at most the model's zero-latent observation diameter bound](goal). -/
-- @node: zeroLatentObservation_dist_le
lemma zeroLatentObservation_dist_le (M : EuclideanSCM kind dims)
    (c c' : CategoricalStratum kind) :
    dist (zeroLatentObservation M c) (zeroLatentObservation M c') ≤
      zeroLatentObservationDiameter M := by
  have hc : ‖zeroLatentObservation M c‖ ≤
      ∑ a : CategoricalStratum kind, ‖zeroLatentObservation M a‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
  have hc' : ‖zeroLatentObservation M c'‖ ≤
      ∑ a : CategoricalStratum kind, ‖zeroLatentObservation M a‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ c')
  exact (dist_le_norm_add_norm _ _).trans (by
    unfold zeroLatentObservationDiameter
    linarith)

/-- Suppose [the total non-Gumbel latent dimension is zero](hyp:hd), [the sample
size m exceeds one](hyp:hm), [each observation is measurable](hyp:hsample),
[the observations are mutually independent under Q](hyp:hind), and [each has
the model's observational law](hyp:hlaw). Then [the probability that the
empirical law's first Wasserstein distance from the observational law exceeds
one half of the zero-latent diameter bound times the number of complete strata
times the square root of twice log m divided by m is at most twice the number
of complete strata divided by m to the fourth power](goal). -/
-- @node: iid_zero_latent_observational_wasserstein_polynomial_tail
lemma iid_zero_latent_observational_wasserstein_polynomial_tail
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (M : EuclideanSCM kind dims) (hd : ∑ j, dims j = 0)
    {m : ℕ} (hm : 1 < m) (sample : Fin m → Omega → Joint kind)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = observationalLaw M) :
    Q {w | ¬ wasserstein1 (observationalLaw M)
      (empiricalMeasure (fun i => sample i w)) ≤
        ENNReal.ofReal (zeroLatentObservationDiameter M / 2 *
          (Fintype.card (CategoricalStratum kind) * Real.sqrt (2 * Real.log m / m)))} ≤
      ENNReal.ofReal (2 * Fintype.card (CategoricalStratum kind) / (m : ℝ)^4) := by
  let := M.probability
  let : IsProbabilityMeasure (observationalLaw M) :=
    Measure.isProbabilityMeasure_map (by fun_prop [intervenedEval])
  let e := Fintype.equivFin (CategoricalStratum kind)
  let : Nonempty (Fin (Fintype.card (CategoricalStratum kind))) :=
    ⟨e (fun _ => ⟨0, by omega⟩)⟩
  apply iid_finite_observation_wasserstein_polynomial_tail Q (observationalLaw M) hm
    sample hsample hind hlaw
    (fun v => e (observedCategoricalStratum v))
    ((measurable_of_finite e).comp (by fun_prop))
    (fun a => zeroLatentObservation M (e.symm a))
    (by simpa only [Equiv.symm_apply_apply] using
      observational_ae_eq_zeroLatentObservation M hd)
    (zeroLatentObservationDiameter M) (zeroLatentObservationDiameter_nonneg M)
  intro i j
  exact zeroLatentObservation_dist_le M _ _

/-- Suppose [the total non-Gumbel latent dimension is zero](hyp:hd) and [a family
of observation samples is specified for every sample size](hyp:sample), with
[measurable observations](hyp:hsample) that [are mutually independent under Q
at each sample size](hyp:hind) and [each have the model's observational law](hyp:hlaw).
Then [there are positive constants A and B such that, for every sufficiently
large sample size m, the probability that the empirical first Wasserstein error
exceeds A times m to the power minus one half times the square of log m is at
most B divided by m to the fourth power](goal). -/
-- @node: zero_latent_observational_sampling_rate
lemma zero_latent_observational_sampling_rate
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (M : EuclideanSCM kind dims) (hd : ∑ j, dims j = 0)
    (sample : ∀ m, Fin m → Omega → Joint kind)
    (hsample : ∀ m i, Measurable (sample m i))
    (hind : ∀ m, iIndepFun (sample m) Q)
    (hlaw : ∀ m i, Q.map (sample m i) = observationalLaw M) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ m : ℕ in Filter.atTop,
      Q {w | ¬ wasserstein1 (observationalLaw M)
        (empiricalMeasure (fun i => sample m i w)) ≤
          ENNReal.ofReal (A * (m : ℝ)^(-(1 : ℝ) / 2) * (Real.log m)^2)} ≤
        ENNReal.ofReal (B / (m : ℝ)^4) := by
  let k := Fintype.card (CategoricalStratum kind)
  have hk : 0 < k := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, by omega⟩⟩
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  let D := zeroLatentObservationDiameter M
  have hD : 0 ≤ D := zeroLatentObservationDiameter_nonneg M
  let A := D / 2 * k * Real.sqrt 2 + 1
  refine ⟨A, 2 * k, by dsimp [A]; positivity, by positivity, ?_⟩
  have hlog : Filter.Tendsto (fun m : ℕ => Real.log m) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_gt_atTop (1 : ℕ)] with m hmLog hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hfreq := observational_frequency_le_sampling_rate 0 hmR hmLog
  change Real.sqrt (2 * Real.log m / m) ≤
    Real.sqrt 2 * (m : ℝ)^(-(1 : ℝ) / 2) * (Real.log m)^2 at hfreq
  have htol : D / 2 * (k * Real.sqrt (2 * Real.log m / m)) ≤
      A * (m : ℝ)^(-(1 : ℝ) / 2) * (Real.log m)^2 := by
    calc
      _ ≤ D / 2 * (k * (Real.sqrt 2 * (m : ℝ)^(-(1 : ℝ) / 2) *
          (Real.log m)^2)) := by
        gcongr
      _ = (D / 2 * k * Real.sqrt 2) * (m : ℝ)^(-(1 : ℝ) / 2) *
          (Real.log m)^2 := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg m) _)
        dsimp [A]
        linarith
  apply le_trans (measure_mono ?_)
    (iid_zero_latent_observational_wasserstein_polynomial_tail Q M hd hm
      (sample m) (hsample m) (hind m) (hlaw m))
  intro w hw hgood
  exact hw (hgood.trans (ENNReal.ofReal_le_ofReal htol))

end
end Papers.TbsNeuralCausalPi
