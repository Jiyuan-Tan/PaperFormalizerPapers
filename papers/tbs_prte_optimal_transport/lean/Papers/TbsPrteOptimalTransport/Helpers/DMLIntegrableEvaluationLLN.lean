module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomEvaluationLaw
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleSecondMoment
public import Causalean.Stat.Limit.WLLN
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndicatorRates
public import Mathlib.Algebra.Order.Chebyshev
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousEvaluation
/-! Integrable oracle laws of large numbers on the random evaluation half.
The evaluation row has the same product law as a fixed IID row. Transporting
the ordinary weak law therefore requires only a first moment of the statistic,
including when the statistic is the squared centered true score. Empirical
squared score convergence then gives point and variance consistency; the final
assembly specializes these conclusions to the encoded continuous score. -/
public section
set_option linter.unusedFintypeInType false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_oracle_mean_identDistrib
/-- Under [the equal-half sample-splitting assumptions](hyp:hSplit), for [a measurable
observation statistic](hyp:hg), [its average over the enumerated random evaluation half
has the same distribution as its average over the first n plus one observations](goal). -/
lemma equalHalfSplit_oracle_mean_identDistrib
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (g : Obs X Z → ℝ) (hg : Measurable g) (n : ℕ) :
    IdentDistrib
      (fun a => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1),
        g (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a))
      (S.sampleMean g (n + 1)) μ μ := by
  let transform (o : Fin (n + 1) → Obs X Z) :=
    ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i, g (o i)
  have ht : Measurable transform := by fun_prop
  have hrow : Measurable (fun a i =>
      S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a) :=
    measurable_pi_iff.mpr ((equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).2.2.1)
  have hfixed : Measurable (fun a (i : Fin (n + 1)) => S.Z i a) := by fun_prop
  have hmaps := (S.indep.precomp (show Function.Injective
    (fun i : Fin (n + 1) => i.val) from Fin.val_injective)).map_fun_eq_pi_map
      (fun i : Fin (n + 1) => (S.meas i).aemeasurable)
  simp only [S.map_eq] at hmaps
  have hrows : IdentDistrib
      (fun a i => S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)
      (fun a (i : Fin (n + 1)) => S.Z i a) μ μ :=
    ⟨hrow.aemeasurable, hfixed.aemeasurable,
      (equalHalfSplit_evaluation_row_law M μ S I₁ I₂ hSplit n).2.trans hmaps.symm⟩
  have hmean := hrows.comp ht
  convert hmean using 1
  · rfl
  · funext a
    simp only [Function.comp_apply, transform, Causalean.Stat.IIDSample.sampleMean]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i => g (S.Z i a)) (n + 1)).symm

-- @node: equalHalfSplit_oracle_mean_consistent_of_integrable_measurable
/-- Under [equal-half sample splitting](hyp:hSplit), if [an observation statistic is measurable](hyp:hg)
and [integrable under the observation law](hyp:hi), then [its average over the random evaluation
half converges in probability to its population mean along even sample sizes](goal). -/
lemma equalHalfSplit_oracle_mean_consistent_of_integrable_measurable
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (g : Obs X Z → ℝ) (hg : Measurable g)
    (hi : Integrable g (observationLaw M)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a, g (S.Z i a))
      atTop (fun _ _ => ∫ o, g o ∂observationLaw M) := by
  let U := fun n a => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1),
    g (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)
  have hfixed0 : TendstoInMeasure μ (S.sampleMean g) atTop
      (fun _ => ∫ o, g o ∂observationLaw M) := S.sampleMean_tendsto_inProb hg hi
  have hfixed : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n => S.sampleMean g (n + 1)) atTop
      (fun _ _ => ∫ o, g o ∂observationLaw M) :=
    hfixed0.comp (tendsto_add_atTop_nat 1)
  have hU : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      U atTop (fun _ _ => ∫ o, g o ∂observationLaw M) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hfixed ⊢
    intro eps heps
    convert hfixed eps heps using 1
    funext n
    exact (equalHalfSplit_oracle_mean_identDistrib M μ S I₁ I₂ hSplit g hg n).measure_mem_eq
      (show MeasurableSet {r : ℝ | eps ≤ ‖r - ∫ o, g o ∂observationLaw M‖} by
        measurability)
  apply TendstoInMeasure.congr _ (Eventually.of_forall (fun _ => rfl)) hU
  intro n
  filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1]
    with a ha
  have hc : (I₂ (2 * (n + 1)) a).card = n + 1 := by
    rw [← ha.2, Finset.card_image_of_injective _ ha.1, Finset.card_univ, Fintype.card_fin]
  dsimp only [U]
  rw [hc]
  congr 1
  calc
    _ = ∑ i ∈ Finset.univ.image (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a)),
        g (S.Z i a) := (Finset.sum_image (fun i hi j hj hij => ha.1 hij)).symm
    _ = _ := by rw [ha.2]

-- @node: equalHalfSplit_oracle_mean_consistent_of_integrable
/-- Under [equal-half sample splitting](hyp:hSplit), if [an observation statistic is
integrable under the observation law](hyp:hi), then [its evaluation-half average converges
in probability to its population mean along even sample sizes](goal). -/
lemma equalHalfSplit_oracle_mean_consistent_of_integrable
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (g : Obs X Z → ℝ) (hi : Integrable g (observationLaw M)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a, g (S.Z i a))
      atTop (fun _ _ => ∫ o, g o ∂observationLaw M) := by
  let hm := hi.aestronglyMeasurable.aemeasurable
  let gm := hm.mk g
  have heq : g =ᵐ[observationLaw M] gm := hm.ae_eq_mk
  have hconv := equalHalfSplit_oracle_mean_consistent_of_integrable_measurable
    M μ S I₁ I₂ hSplit gm hm.measurable_mk (hi.congr heq)
  have hs : ∀ᵐ a ∂μ, ∀ i : ℕ, g (S.Z i a) = gm (S.Z i a) := by
    apply ae_all_iff.mpr
    intro i
    have hp : MeasurePreserving (S.Z i) μ (observationLaw M) := ⟨S.meas i, S.map_eq i⟩
    exact hp.quasiMeasurePreserving.ae_eq heq
  apply TendstoInMeasure.congr _ _ hconv
  · intro n
    filter_upwards [hs] with a ha
    congr 1
    exact Finset.sum_congr rfl (fun i _ => (ha i).symm)
  · exact Eventually.of_forall (fun _ => (integral_congr_ae heq).symm)

-- @node: finite_mean_sq_le_mean_sq
/-- For [a nonempty finite set](hyp:hs), [the square of the average of any real-valued
function is at most the average of its square](goal). -/
lemma finite_mean_sq_le_mean_sq {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) :
    ((s.card : ℝ)⁻¹ * ∑ i ∈ s, f i) ^ 2 ≤
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ 2 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  calc
    _ = (s.card : ℝ)⁻¹ ^ 2 * (∑ i ∈ s, f i) ^ 2 := mul_pow _ _ _
    _ ≤ (s.card : ℝ)⁻¹ ^ 2 * ((s.card : ℝ) * ∑ i ∈ s, f i ^ 2) :=
      mul_le_mul_of_nonneg_left (sq_sum_le_card_mul_sum_sq (s := s) (f := f)) (sq_nonneg _)
    _ = _ := by field_simp

-- @node: equalHalfSplit_dmlRV_consistent_of_empirical_score_error
/-- Under [equal-half sample splitting](hyp:hSplit), suppose [the true score is integrable](hyp:hi),
[its population mean is theta](hyp:hmean), and [the evaluation-half average squared error
between fitted and true scores converges to zero in probability](hyp:hE). Then [the fitted
evaluation-half mean minus theta converges to zero in probability along even sample sizes](goal). -/
lemma equalHalfSplit_dmlRV_consistent_of_empirical_score_error
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (hi : Integrable truth (observationLaw M))
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (hE : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (score (2 * (n + 1)) a (S.Z i a) - truth (S.Z i a)) ^ 2)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) := by
  let D := fun n a => dmlRV M S I₂ score (2 * (n + 1)) a -
    dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a
  have hI (n : ℕ) : ∀ᵐ a ∂μ, (I₂ (2 * (n + 1)) a).Nonempty := by
    filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1]
      with a ha
    rw [← ha.2]
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  have hsq : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => (D n a)^2) atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hE
    intro n
    filter_upwards [hI n] with a ha
    refine ⟨sq_nonneg _, ?_⟩
    dsimp only [D]
    simp only [dmlRV, dif_pos ha, scoreAverage, splitMean,
      ← mul_sub, ← Finset.sum_sub_distrib]
    exact finite_mean_sq_le_mean_sq _ ha _
  have habs := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun r : ℝ => Real.sqrt r) by fun_prop).continuousAt hsq
  simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at habs
  have hD : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      D atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at habs ⊢
    simpa only [sub_zero, Real.norm_eq_abs, abs_abs] using habs
  have ht := equalHalfSplit_oracle_mean_consistent_of_integrable M μ S I₁ I₂
    hSplit truth hi
  have hT : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) := by
    rw [hmean] at ht
    have horacle : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n a => dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a)
        atTop (fun _ _ => theta) := by
      apply TendstoInMeasure.congr _ (Eventually.of_forall (fun _ => rfl)) ht
      intro n
      filter_upwards [hI n] with a ha
      simp only [dmlRV, dif_pos ha, scoreAverage, splitMean]
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at horacle ⊢
    simpa only [sub_zero] using horacle
  have hn := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun r : ℝ => -r) by fun_prop).continuousAt hD
  have hh := hT.sub hn
  simp only [neg_zero, sub_zero] at hh
  convert hh using 1
  funext n a
  dsimp only [D]
  ring

-- @node: equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp
/-- Under [equal-half sample splitting](hyp:hSplit), suppose [the true score is square integrable](hyp:hLp),
[its population mean is theta](hyp:hmean), and [the evaluation-half average squared fitted-score
error vanishes in probability](hyp:hE). Then [the fitted evaluation-half variance estimator
converges in probability to the true score's population variance centered at theta along even sample sizes](goal). -/
lemma equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (hLp : MemLp truth 2 (observationLaw M))
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (hE : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (score (2 * (n + 1)) a (S.Z i a) - truth (S.Z i a)) ^ 2)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hb := equalHalfSplit_dmlRV_consistent_of_empirical_score_error M μ S I₁ I₂
    hSplit score truth (hLp.integrable (by norm_num)) theta hmean hE
  have hv := equalHalfSplit_oracle_mean_consistent_of_integrable M μ S I₁ I₂ hSplit
    (fun o => (truth o - theta)^2) ((hLp.sub (memLp_const theta)).integrable_sq)
  apply varianceRV_consistent_of_empirical_score_error M S I₂ score truth
    (fun n => 2 * (n + 1)) theta (populationVariance M truth theta) _ hE hv hb
  intro n
  filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1]
    with a ha
  rw [← ha.2]
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

variable [Fintype Z]

-- @node: equalHalfSplit_true_continuous_second_moment_consistent
/-- Suppose [the split satisfies the equal-half assumptions](hyp:hSplit), [the policy map is valid](hyp:hphi),
[its specified derivative is correct](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative),
[the level count is positive](hyp:hK), and [the true nuisances are admissible](hyp:he0).
Under [bounded potential outcomes](hyp:hp), [consistency of observed and potential outcomes](hyp:hcons),
[known outcome endpoints](hyp:hend), [baseline overlap with constant cpi](hyp:hov), and
[policy overlap with that constant](hyp:hpol), [the evaluation-half average squared true continuous
score centered at any theta converges in probability to its population second moment about theta](goal). -/
lemma equalHalfSplit_true_continuous_second_moment_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (theta : ℝ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (psiCont M phi dphi L hK (S.Z i a) (trueNuisance M L) - theta)^2)
      atTop (fun _ _ => populationVariance M
        (fun o => psiCont M phi dphi L hK o (trueNuisance M L)) theta) := by
  have : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hs := true_continuous_total_score_memLp_of_overlap M phi dphi hphi hd
    hDerivative L hK he0 hp hcons hend cpi hov hpol
  exact equalHalfSplit_oracle_mean_consistent_of_integrable M μ S I₁ I₂ hSplit
    (fun o => (psiCont M phi dphi L hK o (trueNuisance M L) - theta)^2)
    ((hs.sub (memLp_const theta)).integrable_sq)

-- Target identification is kept separate: this result centers at the actual
-- population mean of the true score. Neither a score-bias rate nor a normal
-- limit is assumed to prove ordinary consistency and variance consistency.
-- @node: equalHalfSplit_encoded_continuous_mean_variance_consistent
/-- For [score-error functions of the training view and one observation at each even sample size](hyp:f), assume [equal-half sample splitting](hyp:hSplit), [the threshold-crossing model](hyp:h),
[a valid policy map](hyp:hphi), [its specified derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[a positive level count](hyp:hK), [policy-invariant level ordering](hyp:hOrder),
[bounded potential outcomes](hyp:hp), [outcome consistency](hyp:hcons), [known outcome endpoints](hyp:hend),
and [admissible true nuisances](hyp:he0). Suppose [fitted nuisances satisfy clipping](hyp:hclip),
[their shares lie in the simplex](hyp:hshares), [their encoded components are measurable](hyp:hm),
[their component errors satisfy fourth-root little-order rates](hyp:hr), [boundary densities are bounded](hyp:hDensity),
[baseline overlap holds at cpi](hyp:hov), [policy overlap holds at cpi](hyp:hpol), and
[fitted denominators are clipped at cpi](hyp:hden). If [the score error factors through the training
view and one observation](hyp:hscore), [the factor is measurable](hyp:hf), and [its evaluation
values are square integrable](hyp:hfit), then [the fitted evaluation-half mean converges to the
true score's population mean and its variance estimator converges to the true score's population
variance along even sample sizes](goal). -/
lemma equalHalfSplit_encoded_continuous_mean_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a d, Measurable (contComponent M L (eh n a) d))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (hDensity : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n a, ContDenominatorsClipped L (eh n a) cpi)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiCont M phi dphi L hK o (eh (2 * (n + 1)) a) -
        psiCont M phi dphi L hK o (trueNuisance M L) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) :
    let score := fun n a o => psiCont M phi dphi L hK o (eh n a)
    let truth := fun o => psiCont M phi dphi L hK o (trueNuisance M L)
    let theta := ∫ o, truth o ∂observationLaw M
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hE := equalHalfSplit_encoded_continuous_empirical_score_error M μ S I₁ I₂
    hSplit h phi dphi hphi hd hDerivative L hK hOrder hp hcons hend he0
    eh hclip hshares hm hr hDensity cpi hov hpol hden f hscore hf hfit
  have hLp := true_continuous_total_score_memLp_of_overlap M phi dphi hphi hd
    hDerivative L hK he0 hp hcons hend cpi hov hpol
  dsimp only
  exact ⟨equalHalfSplit_dmlRV_consistent_of_empirical_score_error M μ S I₁ I₂
      hSplit _ _ (hLp.integrable (by norm_num)) _ rfl hE,
    equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp M μ S I₁ I₂
      hSplit _ _ hLp _ rfl hE⟩

end Papers.TbsPrteOptimalTransport
