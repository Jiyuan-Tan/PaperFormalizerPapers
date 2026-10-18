module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTreatmentResidual
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryTrainingVariance
/-! Uniform bounds and evaluation consistency for continuous full-interval scores.
The five-term orthogonal-score decomposition gives a bound independent of the
fitted nuisances. Training factorization then transfers population L₂ convergence
to the actual random evaluation half and its variance estimator. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_contFullJ_abs_bound
/-- For [admissible continuous nuisances](hyp:he), [the absolute full-interval
outcome contrast is at most twice the larger absolute outcome endpoint, almost
everywhere under the covariate distribution](goal). -/
lemma fitted_contFullJ_abs_bound (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k : ℕ) :
    ∀ᵐ x ∂xLaw M, |contFullJ L e k x| ≤ 2 * max |M.yMin| |M.yMax| := by
  filter_upwards [(fitted_continuous_full_coordinates M L e he (k + 1)).1.2,
    (fitted_continuous_full_coordinates M L e he k).1.2,
    (fitted_continuous_full_coordinates M L e he k).2.1.2,
    (fitted_continuous_full_coordinates M L e he k).2.2.2] with x hp hm hj hl
  have hplus : |positiveValue e.pLev (k + 1) x * fullValue e.JfullPlus k x| ≤
      max |M.yMin| |M.yMax| := by
    rw [abs_mul]
    exact (mul_le_mul hp hj (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hminus : |positiveValue e.pLev k x * minusFullValue e k x| ≤
      max |M.yMin| |M.yMax| := by
    rw [abs_mul]
    exact (mul_le_mul hm hl (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact (abs_sub _ _).trans (by linarith)

-- @node: fitted_continuous_weighted_full_residual_abs_bound
/-- For [admissible fitted nuisances](hyp:he), under [potential outcomes almost surely
in the outcome domain](hyp:hp), [consistency](hyp:hcons), [known outcome endpoints](hyp:hend),
[a positive denominator floor](hyp:hc), and [assignment probabilities bounded
below by that floor almost everywhere](hyp:hclip), [the absolute instrument-weighted
full-interval outcome residual on either selected side is almost surely at most
twice the larger absolute outcome endpoint divided by the denominator floor](goal). -/
lemma fitted_continuous_weighted_full_residual_abs_bound (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) (k : Fin L.K) :
    ∀ᵐ o ∂observationLaw M,
      |e.gammaFull k o.1 * continuousFullOutcomeResidual L e plus k o| ≤
        2 * max |M.yMin| |M.yMax| / c := by
  filter_upwards [fitted_continuous_full_residual_abs_bound M L e he hp hcons hend
    c hc hclip plus k k.isLt, observationLaw_covariate_ae M _
      (fitted_continuous_gammaFull_coordinates M L e he k).2] with o hr hg
  rw [abs_mul]
  exact (mul_le_mul hg hr (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- @node: fitted_continuous_full_treatment_correction_abs_bound
/-- For [admissible fitted nuisances](hyp:he), [a positive denominator
floor](hyp:hc), and [assignment probabilities bounded below by that floor almost
everywhere](hyp:hclip), [the absolute full-interval treatment correction on the
selected upper or lower side is almost surely at most the larger absolute
outcome endpoint divided by the denominator floor](goal). -/
lemma fitted_continuous_full_treatment_correction_abs_bound (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) (k : Fin L.K) :
    ∀ᵐ o ∂observationLaw M,
      |(e.gammaFull k o.1 *
        (if plus then fullValue e.JfullPlus k o.1 else minusFullValue e k o.1)) *
        RpCont L e (if plus then k.val + 1 else k.val) o| ≤
          max |M.yMin| |M.yMax| / c := by
  have hi : (if plus then k.val + 1 else k.val) ≤ L.K := by
    cases plus <;> simp <;> omega
  filter_upwards [observationLaw_covariate_ae M _
    (fitted_continuous_full_treatment_weight_coordinates M L e he plus k).2,
    fitted_RpCont_abs_bound M L e he c hc hclip _ hi] with o hw hr
  rw [abs_mul]
  exact (mul_le_mul hw hr (abs_nonneg _) (by positivity)).trans_eq (by ring)

-- @node: fitted_continuous_full_score_product_abs_bound
/-- For [admissible fitted nuisances](hyp:he), under [potential outcomes almost surely
in the outcome domain](hyp:hp), [consistency](hyp:hcons), [known outcome endpoints](hyp:hend),
[a positive denominator floor](hyp:hc), and [assignment probabilities bounded
below by that floor almost everywhere](hyp:hclip), [the absolute full-interval
product score is almost surely bounded by twice the larger absolute outcome
endpoint plus six times that endpoint magnitude divided by the denominator floor](goal). -/
lemma fitted_continuous_full_score_product_abs_bound (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) :
    ∀ᵐ o ∂observationLaw M, |psiFullProd L e k o| ≤
      2 * max |M.yMin| |M.yMax| + 6 * max |M.yMin| |M.yMax| / c := by
  filter_upwards [observationLaw_covariate_ae M _
    (fitted_contFullJ_abs_bound M L e he k),
    fitted_continuous_weighted_full_residual_abs_bound M L e he hp hcons hend
      c hc hclip true k,
    fitted_continuous_weighted_full_residual_abs_bound M L e he hp hcons hend
      c hc hclip false k,
    fitted_continuous_full_treatment_correction_abs_bound M L e he c hc hclip true k,
    fitted_continuous_full_treatment_correction_abs_bound M L e he c hc hclip false k]
    with o hj hp hm htp htm
  have hev : |indicator (o.2.1 ∈ higherPolicy L k) -
      indicator (o.2.1 ∈ higherBaseline L k)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  have hfirst : |(indicator (o.2.1 ∈ higherPolicy L k) -
      indicator (o.2.1 ∈ higherBaseline L k)) * contFullJ L e k o.1| ≤
      2 * max |M.yMin| |M.yMax| := by
    rw [abs_mul]
    exact (mul_le_mul hev hj (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  simp only [Bool.true_eq, Bool.false_eq_true, if_true, if_false] at htp htm
  let A := (indicator (o.2.1 ∈ higherPolicy L k) -
    indicator (o.2.1 ∈ higherBaseline L k)) * contFullJ L e k o.1
  let B := e.gammaFull k o.1 * continuousFullOutcomeResidual L e true k o
  let D := e.gammaFull k o.1 * continuousFullOutcomeResidual L e false k o
  let T := (e.gammaFull k o.1 * fullValue e.JfullPlus k o.1) * RpCont L e (k.val+1) o
  let U := (e.gammaFull k o.1 * minusFullValue e k o.1) * RpCont L e k o
  rw [continuous_full_product_correction_decomposition]
  change |A + B - D + T - U| ≤ _
  have htriangle : |A + B - D + T - U| ≤ |A| + |B| + |D| + |T| + |U| := by
    linarith only [abs_add_le A B, abs_sub (A + B) D,
      abs_add_le (A + B - D) T, abs_sub (A + B - D + T) U]
  dsimp only [A, B, D, T, U] at htriangle ⊢
  exact (htriangle.trans
    (add_le_add (add_le_add (add_le_add (add_le_add hfirst hp) hm) htp) htm)).trans_eq
      (by ring)

-- @node: fitted_continuous_full_score_block_abs_bound
/-- For [admissible fitted nuisances](hyp:he), under [potential outcomes almost surely
in the outcome domain](hyp:hp), [consistency](hyp:hcons), [known outcome endpoints](hyp:hend),
[a positive denominator floor](hyp:hc), and [assignment probabilities bounded
below by that floor almost everywhere](hyp:hclip), [the absolute sum of
full-interval product scores across levels is almost surely at most the number
of levels times the sum of twice the larger absolute outcome endpoint and six
times that endpoint magnitude divided by the denominator floor](goal). -/
lemma fitted_continuous_full_score_block_abs_bound (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    ∀ᵐ o ∂observationLaw M, |∑ k ∈ Finset.range L.K, psiFullProd L e k o| ≤
      (L.K : ℝ) * (2 * max |M.yMin| |M.yMax| + 6 * max |M.yMin| |M.yMax| / c) := by
  have hall : ∀ᵐ o ∂observationLaw M, ∀ k : Fin L.K,
      |psiFullProd L e k o| ≤
        2 * max |M.yMin| |M.yMax| + 6 * max |M.yMin| |M.yMax| / c := by
    rw [ae_all_iff]
    intro k
    exact fitted_continuous_full_score_product_abs_bound M L e he hp hcons hend
      c hc hclip k
  filter_upwards [hall] with o ho
  calc
    _ ≤ ∑ k ∈ Finset.range L.K, |psiFullProd L e k o| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range L.K,
        (2 * max |M.yMin| |M.yMax| + 6 * max |M.yMin| |M.yMax| / c) := by
      apply Finset.sum_le_sum
      intro k hk
      exact ho ⟨k, Finset.mem_range.mp hk⟩
    _ = _ := by simp; ring

-- @node: nuisanceRates_training_continuous_full_empirical_score_error
/-- For [an equal training and evaluation split](hyp:hSplit), assume [admissible
reference nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), [potential
outcomes almost surely in the outcome domain](hyp:hp), [consistency](hyp:hcons), [known outcome
endpoints](hyp:hend), [a positive denominator floor](hyp:hc), and [both reference
and fitted assignment probabilities bounded below by that floor almost
everywhere](hyp:hclip). If the componentwise nuisance rates hold for [treatment
probabilities](hyp:hrp), [assignment probabilities](hyp:hrpi), [upper full-interval
means](hyp:hrplus), [lower full-interval means](hyp:hrminus), and [instrument
weights](hyp:hrg), and [the fitted-minus-reference score block is a measurable
predictor based on the training sample](hyp:hm), then [its average squared value
on the evaluation half converges in probability to zero](goal). -/
lemma nuisanceRates_training_continuous_full_empirical_score_error
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o =>
      (∑ k ∈ Finset.range L.K, psiFullProd L (eh n a) k o) -
        ∑ k ∈ Finset.range L.K, psiFullProd L e0 k o)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          ((∑ k ∈ Finset.range L.K, psiFullProd L (eh (2 * (n + 1)) a) k (S.Z i a)) -
            ∑ k ∈ Finset.range L.K, psiFullProd L e0 k (S.Z i a)) ^ 2)
      atTop (fun _ _ => 0) := by
  let C := (L.K : ℝ) *
    (2 * max |M.yMin| |M.yMax| + 6 * max |M.yMin| |M.yMax| / c)
  have hb (n : ℕ) (a : A) : ∀ᵐ o ∂observationLaw M,
      |(∑ k ∈ Finset.range L.K, psiFullProd L (eh n a) k o) -
        ∑ k ∈ Finset.range L.K, psiFullProd L e0 k o| ≤ C + C := by
    filter_upwards [fitted_continuous_full_score_block_abs_bound M L _ (heh n a)
      hp hcons hend c hc (fun i => (hclip n a i).mono (fun _ h => h.2)),
      fitted_continuous_full_score_block_abs_bound M L e0 he0 hp hcons hend c hc
        (fun i => (hclip n a i).mono (fun _ h => h.1))] with o hfit htruth
    exact (abs_sub _ _).trans (add_le_add hfit htruth)
  obtain ⟨f, heq, hf, hfit⟩ :=
    equalHalfSplit_ae_bounded_training_score_factorization M μ S I₁ I₂ hSplit _ hm
      (C + C) hb
  have hr := nuisanceRates_continuous_full_score_block_sq_tendsto_probability_zero
    M μ L e0 eh he0 heh hp hcons hend c hc hclip hrp hrpi hrplus hrminus hrg
  have hr' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [← heq] using hr
  have hE := equalHalfSplit_empirical_fitted_score_energy M μ S I₁ I₂ hSplit
    f hf hfit hr'
  simpa only [← heq] using hE

-- @node: nuisanceRates_training_continuous_full_mean_variance_consistent
/-- For [an equal training and evaluation split](hyp:hSplit), assume [admissible
reference nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), [potential
outcomes almost surely in the outcome domain](hyp:hp), [consistency](hyp:hcons), [known outcome
endpoints](hyp:hend), [a positive denominator floor](hyp:hc), and [both reference
and fitted assignment probabilities bounded below by that floor almost
everywhere](hyp:hclip). If the componentwise nuisance rates hold for [treatment
probabilities](hyp:hrp), [assignment probabilities](hyp:hrpi), [upper full-interval
means](hyp:hrplus), [lower full-interval means](hyp:hrminus), and [instrument
weights](hyp:hrg), and [the fitted-minus-reference score block is a measurable
predictor based on the training sample](hyp:hm), then [the evaluation-half fitted
score mean converges in probability to the reference score's population mean,
and its empirical variance converges in probability to the reference score's
population variance](goal). -/
lemma nuisanceRates_training_continuous_full_mean_variance_consistent
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o =>
      (∑ k ∈ Finset.range L.K, psiFullProd L (eh n a) k o) -
        ∑ k ∈ Finset.range L.K, psiFullProd L e0 k o)) :
    let score := fun n a o => ∑ k ∈ Finset.range L.K, psiFullProd L (eh n a) k o
    let truth := fun o => ∑ k ∈ Finset.range L.K, psiFullProd L e0 k o
    let theta := ∫ o, truth o ∂observationLaw M
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  let : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hE := nuisanceRates_training_continuous_full_empirical_score_error M μ S I₁ I₂
    hSplit L e0 eh he0 heh hp hcons hend c hc hclip hrp hrpi hrplus hrminus hrg hm
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure μ
  have hLp := fitted_continuous_full_score_block_memLp M L e0 he0 hp hcons hend
    c hc (fun i => (hclip 0 (Classical.choice inferInstance) i).mono (fun _ h => h.1))
  dsimp only
  exact ⟨equalHalfSplit_dmlRV_consistent_of_empirical_score_error M μ S I₁ I₂
      hSplit _ _ (hLp.integrable (by norm_num)) _ rfl hE,
    equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp M μ S I₁ I₂
      hSplit _ _ hLp _ rfl hE⟩

end Papers.TbsPrteOptimalTransport
