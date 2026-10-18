module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomEvaluationMoments
/-! Laws of large numbers for the true score on the actual random evaluation
half. The split laws and conditional Chebyshev supply the oracle second moment
needed for consistency of the fitted-score variance estimate. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_oracle_mean_consistent
/-- Under [the equal-half sample-splitting laws](hyp:hSplit), if [an observation function is measurable](hyp:hg) and [square-integrable under the observation law](hyp:hLp), then [its average over the evaluation half converges in probability to its population mean](goal). -/
lemma equalHalfSplit_oracle_mean_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (g : Obs X Z → ℝ) (hg : Measurable g) (hLp : MemLp g 2 (observationLaw M)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a, g (S.Z i a))
      atTop (fun _ _ => ∫ o, g o ∂observationLaw M) := by
  let f := fun n (tb :
      (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z) =>
    (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * g tb.2
  have hf : ∀ n, Measurable (f n) := by intro n; fun_prop
  have hsection : ∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M) :=
    fun n t => hLp.const_mul _
  have hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ := by
    intro n i
    have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n
    have hp : MemLp g 2 (μ.map
        (fun a => S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) := by
      rw [(hl.2.2.2.1 i).2]
      exact hLp
    exact (hp.comp_of_map (hl.2.2.1 i).aemeasurable).const_mul _
  have he (n : ℕ) (a : A) :
      (∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∫ o, g o ^ 2 ∂observationLaw M := by
    simp only [f, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), integral_const_mul]
  have ht : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∫ o, g o ^ 2 ∂observationLaw M) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa using (tendsto_inv_atTop_zero.comp hn).mul_const
      (∫ o, g o ^ 2 ∂observationLaw M)
  have hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    have hh := (tendsto_order.1 (ht.norm)).2 eps (by simpa using heps)
    apply (tendsto_congr' _).mpr tendsto_const_nhds
    filter_upwards [hh] with n hn
    rw [show {a | eps ≤ ‖(∫ o, f n
        (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2 ∂observationLaw M) - 0‖} =
        (∅ : Set A) by
      ext a
      simp only [Set.mem_setOf_eq, he, sub_zero, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr hn]
    exact measure_empty
  have hc := equalHalfSplit_centered_fitted_score_fluctuation M μ S I₁ I₂ hSplit
    f hf hsection hfit hrate
  have hid (n : ℕ) :
      (fun a => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (f n (trainingView M S I₁ (2 * (n + 1)) a, S.Z i a) -
            ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o)
              ∂observationLaw M)) =ᵐ[μ]
      (fun a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a, g (S.Z i a) -
          ∫ o, g o ∂observationLaw M) := by
    filter_upwards [(hSplit (2 * (n + 1)) (by omega) ⟨n + 1, by omega⟩).1] with a ha
    have hcard : (I₂ (2 * (n + 1)) a).card = n + 1 := by simpa using ha.2.2.2
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    simp only [f, integral_const_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcard]
    have hs : (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
      rw [← pow_two, inv_pow, Real.sq_sqrt hn.le]
    have hnn : ((n + 1 : ℕ) : ℝ) ≠ 0 := hn.ne'
    rw [mul_sub, ← mul_assoc, hs]
    rw [← mul_assoc, hs, ← mul_assoc, inv_mul_cancel₀ hnn, one_mul]
  have hd := TendstoInMeasure.congr (fun n => (hid n))
    (Eventually.of_forall (fun _ => rfl)) hc
  change Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
    (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
      ∑ i ∈ I₂ (2 * (n + 1)) a, g (S.Z i a) -
        ∫ o, g o ∂observationLaw M) atTop (fun _ _ => 0) at hd
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hd ⊢
  simpa only [sub_zero] using hd

-- Bounded true scores make their centered squares square-integrable; no
-- fourth-moment condition is added to the paper's compact-support setup.
-- @node: equalHalfSplit_oracle_second_moment_consistent
/-- Under [the equal-half sample-splitting laws](hyp:hSplit), if [the oracle score is measurable](hyp:hg) and [its absolute value is almost surely bounded by a constant](hyp:hB), then [the evaluation average of its squared deviation from any fixed target converges in probability to the corresponding population second moment](goal). -/
lemma equalHalfSplit_oracle_second_moment_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (truth : Obs X Z → ℝ) (hg : Measurable truth)
    (B : ℝ) (hB : ∀ᵐ o ∂observationLaw M, ‖truth o‖ ≤ B) (theta : ℝ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a, (truth (S.Z i a) - theta) ^ 2)
      atTop (fun _ _ => populationVariance M truth theta) := by
  haveI : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hmeas : Measurable (fun o => (truth o - theta) ^ 2) := by fun_prop
  have hsq : MemLp (fun o => (truth o - theta) ^ 2) 2 (observationLaw M) := by
    apply MemLp.of_bound hmeas.aestronglyMeasurable ((max B 0 + |theta|) ^ 2)
    filter_upwards [hB] with o ho
    have habs : |truth o| ≤ B := by simpa only [Real.norm_eq_abs] using ho
    have hd : |truth o - theta| ≤ max B 0 + |theta| :=
      (abs_sub _ _).trans (add_le_add (habs.trans (le_max_left B 0)) (le_refl |theta|))
    have hpos : 0 ≤ max B 0 + |theta| := add_nonneg (le_max_right B 0) (abs_nonneg theta)
    have hsqle : |truth o - theta| ^ 2 ≤ (max B 0 + |theta|) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg (truth o - theta)) hpos).2 hd
    simpa only [Real.norm_eq_abs, abs_pow] using hsqle
  exact equalHalfSplit_oracle_mean_consistent M μ S I₁ I₂ hSplit (fun o => (truth o - theta) ^ 2) hmeas hsq

-- The oracle second-moment LLN is derived above, rather than being an
-- additional convergence premise in the variance-estimator assembly.
-- @node: equalHalfSplit_varianceRV_consistent_of_bounded_truth
/-- For [fitted-score functions of training data and one observation at each even sample size](hyp:f), under [the equal-half sample-splitting laws](hyp:hSplit), suppose [the fitted score factors through the training data and one observation](hyp:hscore), [the representing function is measurable](hyp:hf), [the oracle score is measurable](hyp:hg), and [the oracle score is almost surely bounded](hyp:hB). If [each evaluation-row score error is square-integrable](hyp:hfit), [the population integrated squared score error converges in probability to zero](hyp:hrate), and [the fitted DML estimate converges in probability to the target](hyp:hb), then [its empirical variance estimate converges in probability to the oracle population second moment about that target](goal). -/
lemma equalHalfSplit_varianceRV_consistent_of_bounded_truth
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o, score (2 * (n + 1)) a o =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (truth : Obs X Z → ℝ) (hg : Measurable truth)
    (B : ℝ) (hB : ∀ᵐ o ∂observationLaw M, ‖truth o‖ ≤ B)
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a) -
        truth (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (f n (trainingView M S I₁ (2 * (n + 1)) a, o) - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (theta : ℝ)
    (hb : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  exact equalHalfSplit_varianceRV_consistent M μ S I₁ I₂ hSplit score f hscore hf
    truth hg hfit hrate theta (populationVariance M truth theta)
    (equalHalfSplit_oracle_second_moment_consistent M μ S I₁ I₂ hSplit truth hg B hB theta) hb

-- Population conditional objects are defined only almost everywhere. Pulling
-- their measurable versions through the IID observation law preserves the LLN.
-- @node: equalHalfSplit_oracle_mean_consistent_of_memLp
/-- Under [the equal-half sample-splitting laws](hyp:hSplit), if [an observation function is square-integrable under the observation law](hyp:hLp), then [its average over the evaluation half converges in probability to its population mean](goal). -/
lemma equalHalfSplit_oracle_mean_consistent_of_memLp
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (g : Obs X Z → ℝ) (hLp : MemLp g 2 (observationLaw M)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a, g (S.Z i a))
      atTop (fun _ _ => ∫ o, g o ∂observationLaw M) := by
  let hm := hLp.aestronglyMeasurable.aemeasurable
  let gm := hm.mk g
  have heq : g =ᵐ[observationLaw M] gm := hm.ae_eq_mk
  have hconv := equalHalfSplit_oracle_mean_consistent M μ S I₁ I₂ hSplit
    gm hm.measurable_mk (hLp.ae_eq heq)
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

-- Factor the score difference through training, rather than requiring the
-- population score itself to be an everywhere measurable version.
-- @node: equalHalfSplit_varianceRV_consistent_of_score_difference
/-- For [score-difference functions of training data and one observation at each even sample size](hyp:f), under [the equal-half sample-splitting laws](hyp:hSplit), suppose [the fitted-minus-oracle score factors through training data and one observation](hyp:hscore), [the representing function is measurable](hyp:hf), and [its evaluation rows are square-integrable](hyp:hfit). If [its population integrated square converges in probability to zero](hyp:hrate), [the squared oracle deviation from the target is itself square-integrable](hyp:hLp), and [the fitted DML estimate converges in probability to the target](hyp:hb), then [the fitted empirical variance converges in probability to the oracle population second moment about that target](goal). -/
lemma equalHalfSplit_varianceRV_consistent_of_score_difference
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o, score (2 * (n + 1)) a o - truth o =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (theta : ℝ)
    (hLp : MemLp (fun o => (truth o - theta) ^ 2) 2 (observationLaw M))
    (hb : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have hE := equalHalfSplit_empirical_fitted_score_energy M μ S I₁ I₂ hSplit
    f hf hfit hrate
  have hV := equalHalfSplit_oracle_mean_consistent_of_memLp M μ S I₁ I₂ hSplit
    (fun o => (truth o - theta) ^ 2) hLp
  have hI : ∀ n, ∀ᵐ a ∂μ, (I₂ (2 * (n + 1)) a).Nonempty := by
    intro n
    filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1]
      with a ha
    rw [← ha.2]
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  apply varianceRV_consistent_of_empirical_score_error M S I₂ score truth
    (fun n => 2 * (n + 1)) theta (populationVariance M truth theta) hI _ hV hb
  simpa only [← hscore] using hE

end Papers.TbsPrteOptimalTransport
