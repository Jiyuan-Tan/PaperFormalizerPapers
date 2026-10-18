module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomEvaluationMoments
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndicatorRates
public import Papers.TbsPrteOptimalTransport.Helpers.PluginSplitMoment
public import Papers.TbsPrteOptimalTransport.Helpers.LevelMarginalRates
/-! Held-out concentration of bounded predictors fitted on the training half.
The conditional mean and cross moments come from the random split laws, so
these conclusions allow training-dependent fitted functions. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- Any vanishing multiplier makes the normalized centered sum negligible.
-- This includes the multiplier n^(-1/4) used for marginal recovery.
-- @node: equalHalfSplit_bounded_fitted_score_scaled_fluctuation
/-- For [score functions of training data and one observation at each even sample size](hyp:f), with [a uniform random split into equal training and evaluation halves, independent
of the observations](hyp:hSplit), [jointly measurable scores depending on the training
data and an observation](hyp:hf), [a common absolute bound on all scores](hyp:hB), and
[a deterministic multiplier tending to zero](hyp:hw), [the evaluation-half sum of scores
centered by their population mean at the realized training data, divided by the square
root of the half-sample size and multiplied by that multiplier, converges to zero in
probability](goal). -/
lemma equalHalfSplit_bounded_fitted_score_scaled_fluctuation
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hf : ∀ n, Measurable (f n)) (B : ℝ)
    (hB : ∀ n t o, |f n (t, o)| ≤ B)
    (w : ℕ → ℝ) (hw : Tendsto w atTop (𝓝 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => w n * (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (f n (trainingView M S I₁ (2 * (n + 1)) a, S.Z i a) -
            ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let g := fun n tb => w n * f n tb
  have hg : ∀ n, Measurable (g n) := by intro n; fun_prop
  have hsection : ∀ n t, MemLp (fun o => g n (t, o)) 2 (observationLaw M) := by
    intro n t
    apply MemLp.of_bound ((hg n).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (|w n| * B)
    exact Eventually.of_forall (fun o => by
      simpa only [g, Function.comp_def, id_eq, Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_left (hB n t o) (abs_nonneg (w n)))
  have hfit : ∀ n i, MemLp (fun a => g n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ := by
    intro n i
    have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n
    apply MemLp.of_bound ((hg n).comp (hl.2.1.prodMk (hl.2.2.1 i))).aestronglyMeasurable
      (|w n| * B)
    exact Eventually.of_forall (fun a => by
      simpa only [g, Function.comp_def, id_eq, Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_left (hB n _ _) (abs_nonneg (w n)))
  have he (n : ℕ) (a : A) :
      0 ≤ (∫ o, g n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) ∧
      (∫ o, g n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) ≤ w n ^ 2 * B ^ 2 := by
    refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
    calc
      _ ≤ ∫ _ : Obs X Z, w n ^ 2 * B ^ 2 ∂observationLaw M :=
        integral_mono_ae (hsection n _).integrable_sq (integrable_const _) (by
          apply Eventually.of_forall
          intro o
          dsimp only [g]
          rw [mul_pow]
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          have hab := hB n (trainingView M S I₁ (2 * (n + 1)) a) o
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hab)).mpr hab)
      _ = _ := by simp
  have ht : Tendsto (fun n => w n ^ 2 * B ^ 2) atTop (𝓝 0) := by
    simpa using (hw.pow 2).mul_const (B ^ 2)
  have hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, g n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    have hh := (tendsto_order.1 ht).2 eps heps
    apply (tendsto_congr' _).mpr tendsto_const_nhds
    filter_upwards [hh] with n hn
    rw [show {a | eps ≤ ‖(∫ o, g n
        (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2 ∂observationLaw M) - 0‖} =
        (∅ : Set A) by
      ext a
      simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
        abs_of_nonneg (he n a).1, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr ((he n a).2.trans_lt hn)]
    exact measure_empty
  have hc := equalHalfSplit_centered_fitted_score_fluctuation M μ S I₁ I₂ hSplit
    g hg hsection hfit hrate
  simpa only [g, integral_const_mul, ← mul_sub, ← Finset.mul_sum, mul_left_comm,
    mul_assoc] using hc

-- @node: equalHalfSplit_bounded_fitted_marginal_rate
/-- For [fitted-score functions of training data and one observation at each even sample size](hyp:f), suppose [the sample is split uniformly into equal training and evaluation halves,
independently of the observations](hyp:hSplit), [the fitted scores are jointly measurable
in training data and observation](hyp:hf), and [all scores share a common absolute
bound](hyp:hB). For [a strictly positive rate sequence](hyp:hr) such that [the inverse
square root of the half-sample size divided by that rate tends to zero](hyp:hscale),
[the evaluation-half average minus its population mean at the realized training data
is negligible in probability relative to that rate](goal). -/
lemma equalHalfSplit_bounded_fitted_marginal_rate
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hf : ∀ n, Measurable (f n)) (B : ℝ)
    (hB : ∀ n t o, |f n (t, o)| ≤ B)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hscale : Tendsto (fun n => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ / r n)
      atTop (𝓝 0)) :
    Causalean.Stat.IsLittleOp
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          f n (trainingView M S I₁ (2 * (n + 1)) a, S.Z i a) -
        ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M)
      r μ := by
  have hc := equalHalfSplit_bounded_fitted_score_scaled_fluctuation M μ S I₁ I₂ hSplit
    f hf B hB (fun n => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ / r n) hscale
  have hid (n : ℕ) :
      (fun a => ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ / r n) *
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (f n (trainingView M S I₁ (2 * (n + 1)) a, S.Z i a) -
            ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M)) =ᵐ[μ]
      (fun a => (((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          f n (trainingView M S I₁ (2 * (n + 1)) a, S.Z i a) -
        ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M) / r n) := by
    filter_upwards [(hSplit (2 * (n + 1)) (by omega) ⟨n + 1, by omega⟩).1] with a ha
    have hcard : (I₂ (2 * (n + 1)) a).card = n + 1 := by simpa using ha.2.2.2
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hs : (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
      rw [← pow_two, inv_pow, Real.sq_sqrt hn.le]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    rw [div_mul_eq_mul_div, hs, div_mul_eq_mul_div]
    congr 1
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
  have hd := TendstoInMeasure.congr (fun n => hid n)
    (Eventually.of_forall (fun _ => rfl)) hc
  change Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) _ atTop
    (fun _ _ => 0) at hd
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hd
  intro eps heps
  convert hd eps heps using 1
  funext n
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos (hr n)]
  exact (le_div_iff₀ (hr n)).symm

-- The full-sample quarter rate is slower than held-out root-n concentration.
-- @node: dml_quarter_rate_concentration_scale
/-- [The inverse square root of the evaluation-half size, divided by the full sample
size to the negative one-quarter power, tends to zero along even full sample sizes
starting at two](goal). -/
lemma dml_quarter_rate_concentration_scale :
    Tendsto (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ /
      (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ))) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp hn
  have hl := ht.div_const ((2 : ℝ) ^ (-1 / 4 : ℝ))
  simp only [zero_div] at hl
  convert hl using 1
  funext n
  have hp : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hp.le, Nat.cast_mul, Nat.cast_ofNat,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp.le]
  calc
    _ = (((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) /
        ((n + 1 : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) / (2 : ℝ) ^ (-1 / 4 : ℝ) := by ring
    _ = _ := by rw [← Real.rpow_sub hp]; norm_num

-- @node: equalHalfSplit_bounded_fitted_marginal_quarter_rate
/-- For [score functions of training data and one observation at each even sample size](hyp:f), if [the sample is split uniformly into equal training and evaluation halves,
independently of the observations](hyp:hSplit), [the scores are jointly measurable in
training data and observation](hyp:hf), and [all scores share a common absolute bound](hyp:hB),
then [the evaluation-half average minus its population mean at the realized training
data is negligible in probability relative to the full sample size to the negative
one-quarter power, along even sample sizes starting at two](goal). -/
lemma equalHalfSplit_bounded_fitted_marginal_quarter_rate
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hf : ∀ n, Measurable (f n)) (B : ℝ)
    (hB : ∀ n t o, |f n (t, o)| ≤ B) :
    Causalean.Stat.IsLittleOp
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          f n (trainingView M S I₁ (2 * (n + 1)) a, S.Z i a) -
        ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ))) μ := by
  exact equalHalfSplit_bounded_fitted_marginal_rate M μ S I₁ I₂ hSplit f hf B hB _
    (fun n => Real.rpow_pos_of_pos (by positivity) _) dml_quarter_rate_concentration_scale

-- The factorization is derived from training measurability. Clipping the
-- extension supplies bounded sections even at training views off its range.
-- @node: pBar_training_centered_quarter_rate
/-- With [a uniform random split into equal training and evaluation halves, independent
of the observations](hyp:hSplit), if [the fitted propensity is jointly measurable in
the training information and the instrument–covariate pair](hyp:hTrain) and [every fitted
value lies between zero and one](hyp:hrange), then [for any fixed instrument value, its
evaluation-half fitted marginal average minus its covariate-population mean is negligible
in probability relative to the full sample size to the negative one-quarter power,
along even sample sizes starting at two](goal). -/
lemma pBar_training_centered_quarter_rate
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Set.Icc (0 : ℝ) 1) (z : Z) :
    Causalean.Stat.IsLittleOp
      (fun n a => pBar M S I₂ pHat (2 * (n + 1)) a z -
        ∫ x, pHat (2 * (n + 1)) a z x ∂xLaw M)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ))) μ := by
  have hfactor (n : ℕ) := bounded_training_predictor_factorization
    (trainingView M S I₁ (2 * (n + 1)))
    (fun a (o : Obs X Z) => pHat (2 * (n + 1)) a z o.1)
    (show Measurable[(MeasurableSpace.comap
        (trainingView M S I₁ (2 * (n + 1))) inferInstance).prod inferInstance]
      (Function.uncurry (fun a (o : Obs X Z) => pHat (2 * (n + 1)) a z o.1)) from
      (hTrain (2 * (n + 1))).comp (measurable_fst.prodMk
        (measurable_const.prodMk (measurable_fst.comp measurable_snd))))
    1 zero_le_one (fun a o => by
      rw [abs_of_nonneg (hrange _ a z o.1).1]
      exact (hrange _ a z o.1).2)
  choose F hF hBound hEq using hfactor
  have hc := equalHalfSplit_bounded_fitted_marginal_quarter_rate M μ S I₁ I₂ hSplit
    (fun n tb => F n tb.1 tb.2) hF 1 hBound
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst
        (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY)))
  have hi (n : ℕ) (a : A) :
      (∫ o, pHat (2 * (n + 1)) a z o.1 ∂observationLaw M) =
        ∫ x, pHat (2 * (n + 1)) a z x ∂xLaw M := by
    have hm : Measurable (pHat (2 * (n + 1)) a z) := by
      exact (hTrain (2 * (n + 1))).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    rw [← hmap]
    exact (integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable).symm
  simpa only [← hEq, hi, pBar] using hc

-- @node: firstStageRate_pBar_baseline_quarter_rate
/-- Under [a uniform random split into equal training and evaluation halves independent
of the observations](hyp:hSplit) and [the threshold-crossing model](hyp:h), suppose
[the fitted propensity is jointly measurable in training information and the
instrument–covariate pair](hyp:hTrain), [its values lie between zero and one](hyp:hrange),
and [its maximum population L2 error across instruments is negligible in probability
relative to sample size to the negative one-quarter power](hyp:hRate). Then [for any
fixed instrument value, the evaluation-half fitted marginal average minus the true
baseline marginal mean is negligible in probability at that same rate, along even
sample sizes starting at two](goal). -/
lemma firstStageRate_pBar_baseline_quarter_rate [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Set.Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat) (z : Z) :
    Causalean.Stat.IsLittleOp
      (fun n a => pBar M S I₂ pHat (2 * (n + 1)) a z -
        ∫ x, M.prop z x ∂xLaw M)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ))) μ := by
  have hm (n : ℕ) (a : A) (z : Z) : Measurable (pHat n a z) :=
    (hTrain n).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hp := firstStageRate_baseline_marginal_quarter_rate M μ h pHat hm hrange hRate
  have hz : Causalean.Stat.IsLittleOp
      (fun n a => (∫ x, pHat (2 * (n + 1)) a z x ∂xLaw M) -
        ∫ x, M.prop z x ∂xLaw M)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ))) μ := by
    apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hp
    intro n a
    rw [one_mul]
    exact (Finset.le_sup' (fun z => |(∫ x, pHat (2 * (n + 1)) a z x ∂xLaw M) -
      ∫ x, M.prop z x ∂xLaw M|) (Finset.mem_univ z)).trans (le_abs_self _)
  have hc := pBar_training_centered_quarter_rate M μ S I₁ I₂ hSplit pHat hTrain hrange z
  have hs := hc.add_eventually_nonneg_rate
    (Eventually.of_forall (fun n => Real.rpow_nonneg (by positivity) _)) hz
  convert hs using 1
  funext n a
  ring

-- @node: firstStageRate_pBar_policy_quarter_rate
/-- Under [a uniform random split into equal training and evaluation halves independent
of the observations](hyp:hSplit) and [the threshold-crossing model](hyp:h), suppose
[the fitted propensity is jointly measurable in training information and the
instrument–covariate pair](hyp:hTrain), [its values lie between zero and one](hyp:hrange),
and [its maximum population L2 error across instruments is negligible in probability
relative to sample size to the negative one-quarter power](hyp:hRate). If [the policy
transformation is measurable on unit-interval propensities and preserves that interval](hyp:hphi),
[it has the proposed derivative throughout the closed unit interval](hyp:hd), and
[that derivative is uniformly bounded and uniformly Lipschitz in propensity](hyp:hDerivative),
then [for any fixed instrument value, the evaluation-half average of policy-transformed
fitted propensities minus the true policy marginal mean is negligible in probability
at the same quarter-power rate, along even sample sizes starting at two](goal). -/
lemma firstStageRate_pBar_policy_quarter_rate [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Set.Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (z : Z) :
    Causalean.Stat.IsLittleOp
      (fun n a => pBar M S I₂ (fun n a => policyProp phi (pHat n a))
        (2 * (n + 1)) a z - ∫ x, policyProp phi M.prop z x ∂xLaw M)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ))) μ := by
  have hm (n : ℕ) (a : A) (z : Z) : Measurable (pHat n a z) :=
    (hTrain n).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hp := firstStageRate_policy_marginal_quarter_rate M μ h pHat hm hrange hRate
    phi dphi hphi hd hDerivative
  have hz : Causalean.Stat.IsLittleOp
      (fun n a => (∫ x, phi z x (pHat (2 * (n + 1)) a z x) ∂xLaw M) -
        ∫ x, policyProp phi M.prop z x ∂xLaw M)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ))) μ := by
    apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hp
    intro n a
    rw [one_mul]
    exact (Finset.le_sup'
      (fun z => |(∫ x, phi z x (pHat (2 * (n + 1)) a z x) ∂xLaw M) -
        ∫ x, phi z x (M.prop z x) ∂xLaw M|) (Finset.mem_univ z)).trans (le_abs_self _)
  have hqTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => policyProp phi (pHat n a) zx.1 zx.2) := by
    intro n
    first
    | fun_prop
    | exact hphi.1.comp
        ((measurable_fst.comp measurable_snd).prodMk
          ((measurable_snd.comp measurable_snd).prodMk
            ((hTrain n).subtype_mk (h := fun ax => hrange n ax.1 ax.2.1 ax.2.2))))
  have hc := pBar_training_centered_quarter_rate M μ S I₁ I₂ hSplit
    (fun n a => policyProp phi (pHat n a)) hqTrain
    (fun n a z x => hphi.2 z x _ (hrange n a z x)) z
  have hs := hc.add_eventually_nonneg_rate
    (Eventually.of_forall (fun n => Real.rpow_nonneg (by positivity) _)) hz
  convert hs using 1
  funext n a
  simp only [policyProp]
  ring

-- These are the empirical marginal inputs consumed by finite graph recovery.
-- @node: firstStageRate_pBar_marginals_consistent
/-- Under [a uniform random split into equal training and evaluation halves independent
of the observations](hyp:hSplit) and [the threshold-crossing model](hyp:h), suppose
[the fitted propensity is jointly measurable in training information and the
instrument–covariate pair](hyp:hTrain), [its values lie between zero and one](hyp:hrange),
and [its maximum population L2 error across instruments is negligible in probability
relative to sample size to the negative one-quarter power](hyp:hRate). If [the policy
transformation is measurable on unit-interval propensities and preserves that interval](hyp:hphi),
[it has the proposed derivative throughout the closed unit interval](hyp:hd), and
[that derivative is uniformly bounded and uniformly Lipschitz in propensity](hyp:hDerivative),
then [for every instrument value, both the evaluation-half fitted baseline marginal
average and its policy-transformed counterpart converge in probability to their
respective population marginal means, along even sample sizes starting at two](goal). -/
lemma firstStageRate_pBar_marginals_consistent [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Set.Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi) :
    (∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pBar M S I₂ pHat (2 * (n + 1)) a z) atTop
      (fun _ _ => ∫ x, M.prop z x ∂xLaw M)) ∧
    (∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pBar M S I₂ (fun n a => policyProp phi (pHat n a))
        (2 * (n + 1)) a z) atTop
      (fun _ _ => ∫ x, policyProp phi M.prop z x ∂xLaw M)) := by
  constructor
  · intro z
    have hr := firstStageRate_pBar_baseline_quarter_rate M μ S I₁ I₂ hSplit h
      pHat hTrain hrange hRate z
    have hc := dml_quarter_rate_tendsto_probability_zero μ _ hr
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hc ⊢
    simpa only [sub_zero] using hc
  · intro z
    have hr := firstStageRate_pBar_policy_quarter_rate M μ S I₁ I₂ hSplit h
      pHat hTrain hrange hRate phi dphi hphi hd hDerivative z
    have hc := dml_quarter_rate_tendsto_probability_zero μ _ hr
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hc ⊢
    simpa only [sub_zero] using hc

end Papers.TbsPrteOptimalTransport
