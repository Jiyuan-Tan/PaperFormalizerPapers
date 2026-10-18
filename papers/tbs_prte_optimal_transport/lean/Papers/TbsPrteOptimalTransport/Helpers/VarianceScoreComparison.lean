module
public import Papers.TbsPrteOptimalTransport.Helpers.Orthogonality
/-! Empirical second-moment and centering comparisons for the DML variance estimator. -/
public section
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory
open Filter
open scoped BigOperators Topology

-- @node: finite_centered_second_moment_identity
/-- For [a nonempty finite sample](hyp:hs), [the average squared deviation from the sample
mean equals the average squared deviation from any reference value minus the squared
distance between the sample mean and that reference value](goal). -/
lemma finite_centered_second_moment_identity {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → ℝ) (theta : ℝ) :
    let avg := (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i
    (s.card : ℝ)⁻¹ * ∑ i ∈ s, (f i - avg) ^ 2 =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, (f i - theta) ^ 2 - (avg - theta) ^ 2 := by
  dsimp only
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hid (a : ℝ) : (∑ i ∈ s, (f i - a) ^ 2) =
      (∑ i ∈ s, f i ^ 2) - 2 * a * (∑ i ∈ s, f i) + s.card * a ^ 2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [hid, hid]
  field_simp
  ring

-- Cauchy-Schwarz is applied after absorbing the nonnegative averaging weight.
-- @node: finite_weighted_second_moment_comparison
/-- With [a nonnegative common weight](hyp:hw), [the absolute difference between two weighted
sums of squares is at most the weighted sum of squared differences plus twice the product
of the square roots of that error sum and the second weighted sum of squares](goal). -/
lemma finite_weighted_second_moment_comparison {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (w : ℝ) (hw : 0 ≤ w) :
    |w * (∑ i ∈ s, f i ^ 2) - w * (∑ i ∈ s, g i ^ 2)| ≤
      w * (∑ i ∈ s, (f i - g i) ^ 2) +
        2 * Real.sqrt (w * ∑ i ∈ s, (f i - g i) ^ 2) *
          Real.sqrt (w * ∑ i ∈ s, g i ^ 2) := by
  have hid : w * (∑ i ∈ s, f i ^ 2) - w * (∑ i ∈ s, g i ^ 2) =
      w * (∑ i ∈ s, (f i - g i) ^ 2) +
        2 * w * (∑ i ∈ s, (f i - g i) * g i) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun i => Real.sqrt w * |f i - g i|) (fun i => Real.sqrt w * |g i|)
  simp only [mul_pow, Real.sq_sqrt hw, sq_abs, ← Finset.mul_sum] at hcs
  have hc : w * |∑ i ∈ s, (f i - g i) * g i| ≤
      Real.sqrt (w * ∑ i ∈ s, (f i - g i) ^ 2) *
        Real.sqrt (w * ∑ i ∈ s, g i ^ 2) := by
    calc
      _ ≤ w * ∑ i ∈ s, |(f i - g i) * g i| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw
      _ ≤ _ := by
        have heq : (∑ i ∈ s, (Real.sqrt w * |f i - g i|) *
            (Real.sqrt w * |g i|)) = w * ∑ i ∈ s, |(f i - g i) * g i| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul]
          calc
            _ = (Real.sqrt w) ^ 2 * (|f i - g i| * |g i|) := by ring
            _ = _ := by rw [Real.sq_sqrt hw]
        rwa [heq] at hcs
  rw [hid]
  calc
    _ ≤ |w * (∑ i ∈ s, (f i - g i) ^ 2)| +
        |2 * w * (∑ i ∈ s, (f i - g i) * g i)| := abs_add_le _ _
    _ = w * (∑ i ∈ s, (f i - g i) ^ 2) +
        2 * (w * |∑ i ∈ s, (f i - g i) * g i|) := by
      rw [abs_of_nonneg (mul_nonneg hw (Finset.sum_nonneg fun i hi => sq_nonneg _))]
      rw [abs_mul, abs_mul, abs_of_nonneg hw]
      norm_num
      ring
    _ ≤ _ := by linarith

-- The three inputs are precisely the empirical score error, the oracle
-- second moment, and the fitted point estimator's centering error.
-- @node: variance_comparison_tendstoInProbability
/-- Suppose [the empirical error converges in probability to zero](hyp:hE), [the oracle
second moment converges in probability to the target variance](hyp:hV), and [the centering
error converges in probability to zero](hyp:hb). If [at each sample size the absolute gap
between the variance estimate and oracle moment is almost surely bounded by the empirical
error, twice the product of the square roots of the error and oracle moment, and the squared
centering error](hyp:hbound), [the variance estimate converges in probability to the target
variance](goal). -/
lemma variance_comparison_tendstoInProbability {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (T E V b : ℕ → A → ℝ) (sigmaSq : ℝ)
    (hE : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) E atTop (fun _ _ => 0))
    (hV : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) V atTop
      (fun _ _ => sigmaSq))
    (hb : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) b atTop (fun _ _ => 0))
    (hbound : ∀ n, ∀ᵐ a ∂μ, |T n a - V n a| ≤
      E n a + 2 * Real.sqrt (E n a) * Real.sqrt (V n a) + (b n a) ^ 2) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ) T atTop
      (fun _ _ => sigmaSq) := by
  let F : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    p.1 + 2 * Real.sqrt p.1 * Real.sqrt p.2.1 + p.2.2^2 + |p.2.1 - sigmaSq|
  have hF : Continuous F := by fun_prop
  have hF0 : F (0, sigmaSq, 0) = 0 := by simp [F]
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hE hV hb ⊢
  intro eps heps
  obtain ⟨delta, hd, hdelta⟩ := Metric.continuousAt_iff.mp
    (hF.continuousAt (x := (0, sigmaSq, 0))) eps heps
  have ht : Tendsto (fun n => μ {a | delta ≤ ‖E n a - 0‖} +
      μ {a | delta ≤ ‖V n a - sigmaSq‖} + μ {a | delta ≤ ‖b n a - 0‖})
      atTop (𝓝 0) := by
    simpa using ((hE delta hd).add (hV delta hd)).add (hb delta hd)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le)
  intro n
  have hsub : ∀ᵐ a ∂μ, a ∈ {a | eps ≤ ‖T n a - sigmaSq‖} →
      a ∈ ({a | delta ≤ ‖E n a - 0‖} ∪ {a | delta ≤ ‖V n a - sigmaSq‖}) ∪
        {a | delta ≤ ‖b n a - 0‖} := by
    filter_upwards [hbound n] with a ha
    intro hat
    by_contra hnot
    have he : |E n a| < delta := by
      simpa only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le,
        sub_zero, Real.norm_eq_abs] using (not_or.mp (not_or.mp hnot).1).1
    have hv : |V n a - sigmaSq| < delta := by
      simpa only [Set.mem_ofPred_eq, not_le, Real.norm_eq_abs] using
        (not_or.mp (not_or.mp hnot).1).2
    have hb' : |b n a| < delta := by
      simpa only [Set.mem_ofPred_eq, not_le, sub_zero, Real.norm_eq_abs] using
        (not_or.mp hnot).2
    have hp : dist (E n a, V n a, b n a) (0, sigmaSq, 0) < delta := by
      simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using
        And.intro he (And.intro hv hb')
    have hf := hdelta hp
    rw [hF0, Real.dist_eq, sub_zero] at hf
    have htri : |T n a - sigmaSq| ≤ |T n a - V n a| + |V n a - sigmaSq| :=
      abs_sub_le _ _ _
    have htf : |T n a - sigmaSq| ≤ F (E n a, V n a, b n a) := by
      dsimp [F]
      linarith
    have : |T n a - sigmaSq| < eps :=
      htf.trans_lt ((le_abs_self _).trans_lt hf)
    exact (not_lt_of_ge (by simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs] using hat)) this
  exact (measure_mono_ae hsub).trans
    ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z) {μ : Measure A}

-- This is the sample analog in the paper, including its fitted-score mean.
-- @node: varianceRV_oracle_second_moment_identity
/-- When [the evaluation split is nonempty](hyp:h), [the fitted-score sample variance equals
the split average of squared score deviations from any reference value minus the squared
deviation of the fitted-score mean from that reference value](goal). -/
lemma varianceRV_oracle_second_moment_identity (S : ObservedSample M μ)
    (I₂ : SampleSplit A) (score : ℕ → A → Obs X Z → ℝ)
    (n : ℕ) (a : A) (h : (I₂ n a).Nonempty) (theta : ℝ) :
    varianceRV M S I₂ score n a =
      ((I₂ n a).card : ℝ)⁻¹ * ∑ i ∈ I₂ n a, (score n a (S.Z i a) - theta) ^ 2 -
        (dmlRV M S I₂ score n a - theta) ^ 2 := by
  simp only [varianceRV, dmlRV, dif_pos h, sampleVariance, scoreAverage, splitMean]
  exact finite_centered_second_moment_identity (I₂ n a) h
    (fun i => score n a (S.Z i a)) theta

-- @node: varianceRV_oracle_comparison
/-- If [the evaluation split is nonempty](hyp:h), [the absolute difference between the
fitted-score variance and the oracle second moment about a reference value is bounded by
the split mean squared fitted-versus-oracle score error, twice the product of its square
root and the square root of the oracle second moment, and the squared deviation of the
fitted-score mean from the reference value](goal). -/
lemma varianceRV_oracle_comparison (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (n : ℕ) (a : A) (h : (I₂ n a).Nonempty) (theta : ℝ) :
    let E := ((I₂ n a).card : ℝ)⁻¹ *
      ∑ i ∈ I₂ n a, (score n a (S.Z i a) - truth (S.Z i a)) ^ 2
    let V := ((I₂ n a).card : ℝ)⁻¹ * ∑ i ∈ I₂ n a, (truth (S.Z i a) - theta) ^ 2
    |varianceRV M S I₂ score n a - V| ≤
      E + 2 * Real.sqrt E * Real.sqrt V + (dmlRV M S I₂ score n a - theta) ^ 2 := by
  dsimp only
  rw [varianceRV_oracle_second_moment_identity M S I₂ score n a h theta]
  have hc := finite_weighted_second_moment_comparison (I₂ n a)
    (fun i => score n a (S.Z i a) - theta) (fun i => truth (S.Z i a) - theta)
    ((I₂ n a).card : ℝ)⁻¹ (by positivity)
  simp only [sub_sub_sub_cancel_right] at hc
  have hid (x y b : ℝ) : x - b - y = (x - y) - b := by ring
  rw [hid]
  exact (abs_sub _ _).trans (by
    rw [abs_of_nonneg (sq_nonneg (dmlRV M S I₂ score n a - theta))]
    linarith)

-- @node: varianceRV_consistent_of_empirical_score_error
/-- Along the selected sample sizes, suppose [the evaluation splits are almost surely
nonempty](hyp:hI), [their mean squared fitted-versus-oracle score error converges in
probability to zero](hyp:hE), [the oracle second moment about the target parameter converges
in probability to the target variance](hyp:hV), and [the fitted-score mean minus the target
parameter converges in probability to zero](hyp:hb). Then [the fitted-score variance
estimator converges in probability to the target variance](goal). -/
lemma varianceRV_consistent_of_empirical_score_error (S : ObservedSample M μ)
    (I₂ : SampleSplit A) (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (N : ℕ → ℕ) (theta sigmaSq : ℝ)
    (hI : ∀ n, ∀ᵐ a ∂μ, (I₂ (N n) a).Nonempty)
    (hE : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (N n) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (N n) a, (score (N n) a (S.Z i a) - truth (S.Z i a)) ^ 2)
      atTop (fun _ _ => 0))
    (hV : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (N n) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (N n) a, (truth (S.Z i a) - theta) ^ 2)
      atTop (fun _ _ => sigmaSq))
    (hb : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (N n) a - theta) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (N n) a) atTop (fun _ _ => sigmaSq) := by
  apply variance_comparison_tendstoInProbability μ _ _ _ _ sigmaSq hE hV hb
  intro n
  filter_upwards [hI n] with a ha
  exact varianceRV_oracle_comparison M S I₂ score truth (N n) a ha theta

end Papers.TbsPrteOptimalTransport
