module
public import Papers.TbsPrteOptimalTransport.Helpers.LevelMarginalConcentration
public import Papers.TbsPrteOptimalTransport.Helpers.LevelRecoveryProbability
/-! Structural-zero recovery from the first-stage rate.
The prescribed threshold dominates the quarter rate. False positives on the
zero class and false negatives on positive marginal levels therefore vanish. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter Set
open scoped Classical Topology

-- @node: littleOp_threshold_exceedance_tendsto_zero
/-- If [the error is negligible in probability relative to a reference rate](hyp:he)
and [that rate is eventually no larger than the threshold](hyp:hdom), [the measure of the
event that the error exceeds the threshold tends to zero](goal). -/
lemma littleOp_threshold_exceedance_tendsto_zero {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (e : ℕ → A → ℝ) (r rho : ℕ → ℝ)
    (he : Causalean.Stat.IsLittleOp e r μ)
    (hdom : ∀ᶠ n in atTop, r n ≤ rho n) :
    Tendsto (fun n => μ {a | rho n < e n a}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (he 1 one_pos)
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hdom] with n hn
  apply measure_mono
  intro a ha
  change 1 * r n ≤ ‖e n a‖
  rw [one_mul, Real.norm_eq_abs]
  exact hn.trans (ha.le.trans (le_abs_self _))

-- @node: recovery_threshold_dominates_quarter_rate
/-- If [the threshold multiplied by the sample size to the one-quarter power diverges to
positive infinity](hyp:hgrowth), [along sample sizes twice a positive integer, the threshold
eventually dominates the inverse one-quarter power of the sample size](goal). -/
lemma recovery_threshold_dominates_quarter_rate (rho : ℕ → ℝ)
    (hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n)
      atTop atTop) :
    ∀ᶠ n in atTop, ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ) ≤
      rho (2 * (n + 1)) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hh := (hgrowth.comp hindex).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hh] with n hn
  have hp : 0 < (((2 * (n + 1) : ℕ) : ℝ) ^ (1 / 4 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring, Real.rpow_neg (by positivity)]
  rw [← one_div, div_le_iff₀ hp]
  simpa only [Function.comp_apply, mul_comm] using hn

-- @node: recovery_zero_class_failure_tendsto_zero
/-- If [population marginals are nonnegative](hyp:hp), [the threshold tends to zero](hyp:hrho),
[each marginal estimate is consistent in probability](hyp:hconv), and [threshold exceedances
at zero marginals have vanishing measure](hyp:hzero), [the measure of disagreement between
the set of estimates at or below the threshold and the population zero class tends to zero](goal). -/
lemma recovery_zero_class_failure_tendsto_zero {A Z : Type*}
    [MeasurableSpace A] [Fintype Z]
    (μ : Measure A) (pb : ℕ → A → Z → ℝ) (p : Z → ℝ)
    (hp : ∀ z, 0 ≤ p z) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => p z))
    (hzero : ∀ z, p z = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a |
      Finset.univ.filter (fun z => pb n a z ≤ rho n) ≠
        Finset.univ.filter (fun z => p z = 0)}) atTop (𝓝 0) := by
  let bad := fun n z => if p z = 0 then {a | rho n < pb n a z}
    else {a | pb n a z ≤ rho n}
  have hb : ∀ z, Tendsto (fun n => μ (bad n z)) atTop (𝓝 0) := by
    intro z
    by_cases hz : p z = 0
    · simpa only [bad, if_pos hz] using hzero z hz
    · simpa only [bad, if_neg hz] using
        positive_marginal_threshold_failure_tendsto_zero μ (fun n a => pb n a z)
          (p z) (lt_of_le_of_ne (hp z) (Ne.symm hz)) rho hrho (hconv z)
  have hu := finite_bad_events_tendsto_zero μ bad hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a ha
  by_contra hn
  have hn' : ∀ z, a ∉ bad n z := by
    simpa only [Set.mem_iUnion, not_exists] using hn
  apply ha
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hh := hn' z
  by_cases hz : p z = 0
  · simpa only [bad, if_pos hz, Set.mem_ofPred_eq, not_lt, hz, iff_true] using hh
  · simpa only [bad, if_neg hz, Set.mem_ofPred_eq, hz, iff_false] using hh

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z]

-- @node: firstStageRate_pBar_structural_zero_recovery
/-- Under [an equal half-sample split](hyp:hSplit) and [threshold crossing](hyp:h), if
[the propensity predictor is measurable with respect to the training sample](hyp:hTrain),
[its values lie between zero and one](hyp:hrange), [it satisfies the finite first-stage rate](hyp:hRate),
[the threshold tends to zero](hyp:hrho), and [the threshold times the sample size to the
one-quarter power diverges](hyp:hgrowth), [along even positive sample sizes the probability
that thresholding the held-out baseline marginal estimates misidentifies the population
zero-marginal instruments tends to zero](goal). -/
lemma firstStageRate_pBar_structural_zero_recovery
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n)
      atTop atTop) :
    Tendsto (fun n => μ {a |
      Finset.univ.filter (fun z => pBar M S I₂ pHat (2 * (n + 1)) a z ≤
        rho (2 * (n + 1))) ≠
      Finset.univ.filter (fun z => (∫ x, M.prop z x ∂xLaw M) = 0)}) atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hrate := firstStageRate_pBar_baseline_quarter_rate M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate
  apply recovery_zero_class_failure_tendsto_zero μ _ _
    (fun z => integral_nonneg (fun x => (M.rangeProp z x).1)) _ (hrho.comp hindex)
  · intro z
    have hc := dml_quarter_rate_tendsto_probability_zero μ _ (hrate z)
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hc ⊢
    simpa only [sub_zero] using hc
  · intro z hz
    have he := hrate z
    simp only [hz, sub_zero] at he
    exact littleOp_threshold_exceedance_tendsto_zero μ _ _ _ he
      (recovery_threshold_dominates_quarter_rate rho hgrowth)

-- Invariant level membership identifies the zero marginal with S₀, even
-- though propensity versions may differ on covariate null sets.
-- @node: population_baseline_marginal_zero_iff
/-- Under [threshold crossing](hyp:h) and [a level ordering and membership structure invariant
across covariates for the baseline and comparison propensities](hyp:hOrder), [an instrument's
covariate-averaged baseline propensity is zero if and only if it belongs to baseline level zero](goal). -/
lemma population_baseline_marginal_zero_iff
    (M : LatentIVModel Ω X Z) (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (z : Z) :
    (∫ x, M.prop z x ∂xLaw M) = 0 ↔ z ∈ L.S 0 := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hzero (x : X) : L.pLev 0 x = 0 := by
    rw [hOrder.1 x 0 (by omega)]
    simp [pLevel]
  have hmem (x : X) : z ∈ L.S 0 ↔ M.prop z x = 0 := by
    simpa only [hzero x] using hOrder.2.2.2.2.2.1 x 0 z (Nat.zero_le _)
  constructor
  · intro hz
    have hmeas : Measurable (M.prop z) :=
      h.2.1.comp (measurable_const.prodMk measurable_id)
    have hint := (recovery_unit_interval_memLp M _ hmeas (M.rangeProp z)).integrable
      (by norm_num)
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun x => (M.rangeProp z x).1) hint).mp hz
    obtain ⟨x, hx⟩ := hae.exists
    exact (hmem x).mpr hx
  · intro hz
    have heq : M.prop z = fun _ => 0 := funext (fun x => (hmem x).mp hz)
    rw [heq, integral_zero]

-- @node: firstStageRate_recovered_baseline_zero_failure_tendsto_zero
/-- Under [an equal half-sample split](hyp:hSplit), [threshold crossing](hyp:h),
[training-sample measurability of the propensity predictor](hyp:hTrain), [predictions between
zero and one](hyp:hrange), [the finite first-stage rate](hyp:hRate), [covariate-invariant
level ordering for baseline and policy propensities](hyp:hOrder), and [a structural-zero
threshold identifying the recovered zero class and satisfying the prescribed decay and growth
conditions](hyp:hThreshold), [along even positive sample sizes the probability that the
recovered baseline zero class differs from the population zero class tends to zero](goal). -/
lemma firstStageRate_recovered_baseline_zero_failure_tendsto_zero [DecidableEq Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap : ℝ)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hThreshold : StructuralZeroThreshold rho (pBar M S I₂ pHat)
      (fun n a => (recoveredData M S I₁ I₂ pHat phi rho gap n a).S 0)) :
    Tendsto (fun n => μ {a |
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).S 0 ≠ L.S 0})
      atTop (𝓝 0) := by
  have hz := firstStageRate_pBar_structural_zero_recovery M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate rho hThreshold.2.2.2.1 hThreshold.2.2.2.2
  have hclass : Finset.univ.filter (fun z => (∫ x, M.prop z x ∂xLaw M) = 0) =
      L.S 0 := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact population_baseline_marginal_zero_iff M h _ L hOrder z
  simpa only [hclass, hThreshold.1] using hz

end Papers.TbsPrteOptimalTransport
