module
public import Papers.TbsPrteOptimalTransport.Helpers.VarianceScoreComparison
/-! Evaluation-sample decomposition and transfer from oracle statistics on exact recovery.
Equality is needed only at the evaluation observations, so the recovery step may use
all evaluation covariates without requiring independence of the feasible score. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology

-- @node: scaled_difference_zero_of_eq_on_recovery
/-- If [the measure of recovery failure tends to zero](hyp:hG) and [two statistics agree on each recovery event](hyp:heq), then [their difference, multiplied by any deterministic scale, converges in probability to zero](goal). -/
lemma scaled_difference_zero_of_eq_on_recovery {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (G : ℕ → Set A) (f g : ℕ → A → ℝ) (scale : ℕ → ℝ)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → f n a = g n a) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => scale n * (f n a - g n a)) atTop (fun _ _ => 0) := by
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
  intro eps heps
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a ha hmem
  change eps ≤ ‖scale n * (f n a - g n a) - 0‖ at ha
  rw [heq n a hmem, sub_self, mul_zero, sub_zero, norm_zero] at ha
  exact (not_le_of_gt heps) ha

-- @node: probability_limit_transfer_on_recovery
/-- If [the measure of recovery failure tends to zero](hyp:hG), [two statistics agree on each recovery event](hyp:heq), and [the second statistic converges in probability to a constant](hyp:hg), then [the first statistic converges in probability to the same constant](goal). -/
lemma probability_limit_transfer_on_recovery {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (G : ℕ → Set A) (f g : ℕ → A → ℝ) (c : ℝ)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → f n a = g n a)
    (hg : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) g atTop
      (fun _ _ => c)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) f atTop
      (fun _ _ => c) := by
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hg ⊢
  intro eps heps
  have ht := (hg eps heps).add hG
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le)
  intro n
  calc
    _ ≤ μ ({a | eps ≤ ‖g n a - c‖} ∪ (G n)ᶜ) := by
      apply measure_mono
      intro a ha
      by_cases hm : a ∈ G n
      · left
        change eps ≤ ‖g n a - c‖
        change eps ≤ ‖f n a - c‖ at ha
        rwa [heq n a hm] at ha
      · exact Or.inr hm
    _ ≤ _ := measure_union_le _ _

-- @node: law_limit_transfer_on_recovery
/-- If [recovery failure has probability tending to zero](hyp:hG), [two statistics agree on each recovery event](hyp:heq), [each first statistic is almost everywhere measurable](hyp:hf), and [the second statistic converges in distribution to the target probability law](hyp:hg), then [the first statistic converges in distribution to that law](goal). -/
lemma law_limit_transfer_on_recovery {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (G : ℕ → Set A) (f g : ℕ → A → ℝ)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → f n a = g n a)
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hg : Causalean.Stat.Modes.TendstoInLaw (fun _ => μ) g atTop Q) :
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ) f atTop Q := by
  have hd := scaled_difference_zero_of_eq_on_recovery μ G f g (fun _ => 1) hG heq
  simp only [one_mul] at hd
  exact tendstoInDistribution_of_tendstoInMeasure_sub f id hg hd hf

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z) {μ : Measure A}

-- @node: dmlRV_eq_of_score_eq_on_sample
/-- If [two scores agree at every observation in the evaluation sample](hyp:heq), [their DML estimates are equal for that sample](goal). -/
lemma dmlRV_eq_of_score_eq_on_sample (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (f g : ℕ → A → Obs X Z → ℝ) (n : ℕ) (a : A)
    (heq : ∀ i ∈ I₂ n a, f n a (S.Z i a) = g n a (S.Z i a)) :
    dmlRV M S I₂ f n a = dmlRV M S I₂ g n a := by
  unfold dmlRV
  split_ifs with h
  · unfold scoreAverage splitMean
    congr 1
    exact Finset.sum_congr rfl heq
  · rfl

-- @node: varianceRV_eq_of_score_eq_on_sample
/-- If [two scores agree at every observation in the evaluation sample](hyp:heq), [their empirical variance estimates are equal for that sample](goal). -/
lemma varianceRV_eq_of_score_eq_on_sample (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (f g : ℕ → A → Obs X Z → ℝ) (n : ℕ) (a : A)
    (heq : ∀ i ∈ I₂ n a, f n a (S.Z i a) = g n a (S.Z i a)) :
    varianceRV M S I₂ f n a = varianceRV M S I₂ g n a := by
  have hmean := dmlRV_eq_of_score_eq_on_sample M S I₂ f g n a heq
  unfold varianceRV
  split_ifs with h
  · simp only [dmlRV, dif_pos h] at hmean
    unfold sampleVariance
    rw [hmean]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [heq i hi]
  · rfl

-- The bias and the centered score difference are kept separate, as in (II).
-- @node: dmlRV_scaled_oracle_decomposition
/-- For [a nonempty evaluation sample](hyp:h), [the scaled DML estimation error equals the scaled average of the oracle score minus the target, plus the scaled bias, plus the scaled average of the fitted-minus-oracle score difference after subtracting that bias](goal). -/
lemma dmlRV_scaled_oracle_decomposition (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (n : ℕ) (a : A) (h : (I₂ n a).Nonempty) (theta bias scale : ℝ) :
    scale * (dmlRV M S I₂ score n a - theta) =
      scale * ((I₂ n a).card : ℝ)⁻¹ *
        (∑ i ∈ I₂ n a, (truth (S.Z i a) - theta)) + scale * bias +
      scale * ((I₂ n a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ n a, (score n a (S.Z i a) - truth (S.Z i a) - bias) := by
  have hc : ((I₂ n a).card : ℝ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
  simp only [dmlRV, dif_pos h, scoreAverage, splitMean,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

-- @node: dml_statistics_transfer_on_recovery
/-- Suppose [recovery failure has probability tending to zero](hyp:hG), [the feasible and oracle scores agree at all evaluation observations on recovery events along the chosen sample sizes](hyp:heq), and [the scaled, centered feasible estimates are almost everywhere measurable](hyp:hf). If [the scaled, centered oracle estimates converge to the target law](hyp:hlaw) and [the oracle variance estimates converge in probability to the target variance](hyp:hvar), then [the feasible estimates have the same distributional limit and their variance estimates converge in probability to the same variance](goal). -/
lemma dml_statistics_transfer_on_recovery (S : ObservedSample M μ) (I₂ : SampleSplit A)
    [IsProbabilityMeasure μ] (f g : ℕ → A → Obs X Z → ℝ)
    (N : ℕ → ℕ) (G : ℕ → Set A) (scale : ℕ → ℝ) (theta sigmaSq : ℝ)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (N n) a,
      f (N n) a (S.Z i a) = g (N n) a (S.Z i a))
    (hf : ∀ n, AEMeasurable
      (fun a => scale n * (dmlRV M S I₂ f (N n) a - theta)) μ)
    (hlaw : Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => scale n * (dmlRV M S I₂ g (N n) a - theta)) atTop Q)
    (hvar : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ g (N n) a) atTop (fun _ _ => sigmaSq)) :
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => scale n * (dmlRV M S I₂ f (N n) a - theta)) atTop Q ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ f (N n) a) atTop (fun _ _ => sigmaSq) := by
  constructor
  · apply law_limit_transfer_on_recovery μ Q G _ _ hG _ hf hlaw
    intro n a ha
    rw [dmlRV_eq_of_score_eq_on_sample M S I₂ f g (N n) a (heq n a ha)]
  · apply probability_limit_transfer_on_recovery μ G _ _ sigmaSq hG _ hvar
    intro n a ha
    exact varianceRV_eq_of_score_eq_on_sample M S I₂ f g (N n) a (heq n a ha)

end Papers.TbsPrteOptimalTransport
