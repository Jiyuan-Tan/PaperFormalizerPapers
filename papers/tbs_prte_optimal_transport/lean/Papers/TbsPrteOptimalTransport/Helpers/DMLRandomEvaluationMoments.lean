module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRandomTrainingIndependence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndependentScoreVariance
/-! Conditional fluctuation of fitted scores on the actual random evaluation half.
The deterministic enumeration uses only the split. Its coordinate and pair laws
supply the conditional moments used by the roadmap's Chebyshev argument. -/
@[expose] public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

-- @node: dmlEvaluationIndex
/-- For [an evaluation size one more than a nonnegative integer](hyp:n), [a finite set of observation indices](hyp:J), and [a position below that evaluation size](hyp:i), [the evaluation index](goal) is the index at that position in a fixed enumeration of the set when its cardinality matches the evaluation size, and zero otherwise. -/
noncomputable def dmlEvaluationIndex (n : ℕ) (J : Finset ℕ) (i : Fin (n + 1)) : ℕ :=
  if hJ : J.card = n + 1 then ((J.equivFinOfCardEq hJ).symm i).val else 0

-- @node: dmlEvaluationIndex_enumerates
/-- If [the index set has cardinality equal to the requested evaluation size](hyp:hJ), then [the evaluation enumeration is injective and its image is exactly that set](goal). -/
lemma dmlEvaluationIndex_enumerates (n : ℕ) (J : Finset ℕ) (hJ : J.card = n + 1) :
    Function.Injective (dmlEvaluationIndex n J) ∧
      Finset.univ.image (dmlEvaluationIndex n J) = J := by
  let e := J.equivFinOfCardEq hJ
  have heq : dmlEvaluationIndex n J = fun i => (e.symm i).val := by
    funext i
    simp only [dmlEvaluationIndex, dif_pos hJ, e]
  rw [heq]
  refine ⟨Subtype.val_injective.comp e.symm.injective, ?_⟩
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (e.symm i).property
  · intro hj
    exact Finset.mem_image.mpr ⟨e ⟨j, hj⟩, Finset.mem_univ _, by simp [e]⟩

-- @node: dmlEvaluationIndex_mem
/-- If [the index set has cardinality equal to the requested evaluation size](hyp:hJ), then [the index returned at any valid enumeration position belongs to that set](goal). -/
lemma dmlEvaluationIndex_mem (n : ℕ) (J : Finset ℕ) (hJ : J.card = n + 1)
    (i : Fin (n + 1)) : dmlEvaluationIndex n J i ∈ J := by
  have hi : dmlEvaluationIndex n J i ∈ Finset.univ.image (dmlEvaluationIndex n J) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  simpa only [(dmlEvaluationIndex_enumerates n J hJ).2] using hi

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_evaluationIndex_laws
/-- Under [an equal half split independent of the sample](hyp:hSplit), [the evaluation enumeration almost surely lists the held-out indices exactly once; the training view and each enumerated observation are measurable; each observation has the population law and is independent of training; and each distinct pair is jointly independent of training and mutually independent](goal). The evaluation size is one more than the given index, and the total sample size is twice that. -/
lemma equalHalfSplit_evaluationIndex_laws
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (n : ℕ) :
    let N := 2 * (n + 1)
    let T := trainingView M S I₁ N
    let W := fun i a => S.Z (dmlEvaluationIndex n (I₂ N a) i) a
    (∀ᵐ a ∂μ, Function.Injective (dmlEvaluationIndex n (I₂ N a)) ∧
      Finset.univ.image (dmlEvaluationIndex n (I₂ N a)) = I₂ N a) ∧
    Measurable T ∧ (∀ i, Measurable (W i)) ∧
    (∀ i, IndepFun T (W i) μ ∧ μ.map (W i) = observationLaw M) ∧
    (∀ i j, i ≠ j → IndepFun T (fun a => (W i a, W j a)) μ ∧
      IndepFun (W i) (W j) μ) := by
  dsimp only
  have hn : 2 ≤ 2 * (n + 1) := by omega
  have heven : Even (2 * (n + 1)) := ⟨n + 1, by omega⟩
  have hc (J : Finset ℕ)
      (hJ : J ∈ (Finset.range (2 * (n + 1))).powersetCard (2 * (n + 1) / 2)) :
      (Finset.range (2 * (n + 1)) \ J).card = n + 1 := by
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hJ
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_range, hcard]
    omega
  have hr (i : Fin (n + 1)) (J : Finset ℕ)
      (hJ : J ∈ (Finset.range (2 * (n + 1))).powersetCard (2 * (n + 1) / 2)) :=
    dmlEvaluationIndex_mem n _ (hc J hJ) i
  refine ⟨?_, equalHalfSplit_measurable_trainingView M μ S I₁ I₂ hSplit _ hn heven,
    ?_, ?_, ?_⟩
  · filter_upwards [(hSplit _ hn heven).1] with a ha
    apply dmlEvaluationIndex_enumerates
    simpa using ha.2.2.2
  · intro i
    exact equalHalfSplit_measurable_selected_evaluation M μ S I₁ I₂ hSplit _ hn heven
      (fun J => dmlEvaluationIndex n J i)
  · intro i
    refine ⟨equalHalfSplit_training_indep_selected_evaluation M μ S I₁ I₂ hSplit _ hn heven
      (fun J => dmlEvaluationIndex n J i) (hr i), ?_⟩
    apply equalHalfSplit_selected_evaluation_law M μ S I₁ I₂ hSplit _ hn heven
      (fun J => dmlEvaluationIndex n J i)
    filter_upwards [(hSplit _ hn heven).1] with a ha
    have hcard : (I₂ (2 * (n + 1)) a).card = n + 1 := by simpa using ha.2.2.2
    have hmem := dmlEvaluationIndex_mem n _ hcard i
    apply Finset.mem_range.mp
    rw [← ha.2.1]
    exact Finset.mem_union_right _ hmem
  · intro i j hij
    have hne (J : Finset ℕ)
        (hJ : J ∈ (Finset.range (2 * (n + 1))).powersetCard (2 * (n + 1) / 2)) :
        dmlEvaluationIndex n (Finset.range (2 * (n + 1)) \ J) i ≠
          dmlEvaluationIndex n (Finset.range (2 * (n + 1)) \ J) j :=
      fun h => hij ((dmlEvaluationIndex_enumerates n _ (hc J hJ)).1 h)
    exact ⟨(equalHalfSplit_training_indep_selected_evaluation_pair M μ S I₁ I₂ hSplit
      _ hn heven (fun J => dmlEvaluationIndex n J i)
      (fun J => dmlEvaluationIndex n J j) (hr i) (hr j) hne).1,
      equalHalfSplit_selected_evaluation_pair_indep M μ S I₁ I₂ hSplit
        _ hn heven (fun J => dmlEvaluationIndex n J i)
      (fun J => dmlEvaluationIndex n J j) (hr i) (hr j) hne⟩

-- Population L² convergence is the remaining analytic input. All conditional
-- means and cross moments below are derived from the random-split construction.
-- @node: equalHalfSplit_centered_fitted_score_fluctuation
/-- Under [an equal half split independent of the sample](hyp:hSplit), consider [scores depending on the masked training view and one observation](hyp:f) that [are measurable](hyp:hf), [are population square integrable for every fixed training view](hyp:hsection), and [are square integrable when evaluated at each held-out observation](hyp:hfit). If [their population second moments given the training view converge in probability to zero](hyp:hrate), then [the evaluation sum of scores centered by their training-specific population means, divided by the square root of evaluation size, converges in probability to zero](goal). -/
lemma equalHalfSplit_centered_fitted_score_fluctuation
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hf : ∀ n, Measurable (f n))
    (hsection : ∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (f n (trainingView M S I₁ (2 * (n + 1)) a, S.Z i a) -
            ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  let : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let T := fun n => trainingView M S I₁ (2 * (n + 1))
  let W := fun n (i : Fin (n + 1)) a =>
    S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a
  let m := fun n => MeasurableSpace.comap (T n) inferInstance
  have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit
  have hm : ∀ n, m n ≤ ‹MeasurableSpace A› := fun n => (hl n).2.1.comap_le
  let : ∀ n, SigmaFinite (μ.trim (hm n)) := fun n => inferInstance
  have hmean (n : ℕ) (i : Fin (n + 1)) :
      μ[fun a => f n (T n a, W n i a) | m n] =ᵐ[μ]
        (fun a => ∫ o, f n (T n a, o) ∂observationLaw M) :=
    dml_independent_fitted_score_condExp μ (observationLaw M) (T n) (W n i)
      (hl n).2.1 ((hl n).2.2.1 i) ((hl n).2.2.2.1 i).1
      ((hl n).2.2.2.1 i).2 (f n) (hf n) ((hfit n i).integrable (by norm_num))
  have hcenter (n : ℕ) (i : Fin (n + 1)) :
      MemLp (fun a => f n (T n a, W n i a) -
        ∫ o, f n (T n a, o) ∂observationLaw M) 2 μ := by
    exact (hfit n i).sub ((MemLp.condExp (m := m n) (by norm_num)
      (hfit n i)).ae_eq (hmean n i))
  have ht := conditional_centered_score_sum_tendsto_probability_zero μ m hm
    (fun n i a => f n (T n a, W n i a))
    (fun n a => ∫ o, f n (T n a, o) ∂observationLaw M)
    (fun n a => ∫ o, f n (T n a, o) ^ 2 ∂observationLaw M) hfit hmean
  have hcross : ∀ n (i j : Fin (n + 1)), i ≠ j →
      μ[fun a => (f n (T n a, W n i a) - ∫ o, f n (T n a, o) ∂observationLaw M) *
        (f n (T n a, W n j a) - ∫ o, f n (T n a, o) ∂observationLaw M) | m n] =ᵐ[μ] 0 := by
    intro n i j hij
    exact dml_independent_centered_score_cross_moment μ (observationLaw M) (T n)
      (W n i) (W n j) (hl n).2.1 ((hl n).2.2.1 i) ((hl n).2.2.1 j)
      ((hl n).2.2.2.2 i j hij).1 ((hl n).2.2.2.2 i j hij).2
      ((hl n).2.2.2.1 i).2 ((hl n).2.2.2.1 j).2 (f n) (hf n)
      (fun t => (hsection n t).integrable (by norm_num))
      ((hcenter n i).integrable_mul (hcenter n j))
  have henergy : ∀ n i, μ[fun a => f n (T n a, W n i a) ^ 2 | m n] ≤ᵐ[μ]
      (fun a => ∫ o, f n (T n a, o) ^ 2 ∂observationLaw M) := by
    intro n i
    have hsq : Measurable (fun tb => f n tb ^ 2) := by fun_prop
    exact (dml_independent_fitted_score_condExp μ (observationLaw M) (T n) (W n i)
      (hl n).2.1 ((hl n).2.2.1 i) ((hl n).2.2.2.1 i).1
      ((hl n).2.2.2.1 i).2 (fun tb => f n tb ^ 2) hsq (hfit n i).integrable_sq).le
  have hV : ∀ n, Measurable[m n]
      (fun a => ∫ o, f n (T n a, o) ^ 2 ∂observationLaw M) := by
    intro n
    have hsq : Measurable (fun tb => f n tb ^ 2) := by fun_prop
    have hmeas : Measurable (fun t => ∫ o, f n (t, o) ^ 2 ∂observationLaw M) := by
      first | fun_prop | exact hsq.stronglyMeasurable.integral_prod_right'.measurable
    exact hmeas.comp (Measurable.of_comap_le le_rfl)
  have hconv := ht hcross henergy hV hrate
  apply TendstoInMeasure.congr _ (Eventually.of_forall (fun _ => rfl)) hconv
  intro n
  filter_upwards [(hl n).1] with a ha
  rw [← ha.2, Finset.sum_image]
  exact ha.1.injOn

-- @node: equalHalfSplit_empirical_fitted_score_energy
/-- Under [an equal half split independent of the sample](hyp:hSplit), let [scores depend on the masked training view and one observation](hyp:f), [be measurable](hyp:hf), and [be square integrable at each enumerated held-out observation](hyp:hfit). If [their training-specific population second moments converge in probability to zero](hyp:hrate), then [the average squared score on the evaluation half converges in probability to zero](goal). -/
lemma equalHalfSplit_empirical_fitted_score_energy
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hf : ∀ n, Measurable (f n))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          f n (trainingView M S I₁ (2 * (n + 1)) a, S.Z i a) ^ 2)
      atTop (fun _ _ => 0) := by
  let : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let T := fun n => trainingView M S I₁ (2 * (n + 1))
  let W := fun n (i : Fin (n + 1)) a =>
    S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a
  let m := fun n => MeasurableSpace.comap (T n) inferInstance
  have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit
  have hm : ∀ n, m n ≤ ‹MeasurableSpace A› := fun n => (hl n).2.1.comap_le
  let : ∀ n, SigmaFinite (μ.trim (hm n)) := fun n => inferInstance
  have hconv : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i, f n (T n a, W n i a) ^ 2)
      atTop (fun _ _ => 0) := by
    apply conditional_nonneg_tendsto_probability_zero μ m hm _
      (fun n a => ∫ o, f n (T n a, o) ^ 2 ∂observationLaw M)
    · intro n
      have hsq : Measurable (fun tb => f n tb ^ 2) := by fun_prop
      have hmeas : Measurable (fun t => ∫ o, f n (t, o) ^ 2 ∂observationLaw M) := by
        first | fun_prop | exact hsq.stronglyMeasurable.integral_prod_right'.measurable
      exact hmeas.comp (Measurable.of_comap_le le_rfl)
    · intro n
      simpa only [Finset.sum_apply] using (integrable_finsetSum' Finset.univ
        (fun i _ => (hfit n i).integrable_sq)).const_mul ((n + 1 : ℕ) : ℝ)⁻¹
    · intro n
      exact Eventually.of_forall (fun a => mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
    · intro n
      have hce := dml_independent_empirical_score_energy_condExp μ (observationLaw M)
        (T n) (W n) (hl n).2.1 ((hl n).2.2.1)
        (fun i => ((hl n).2.2.2.1 i).1) (fun i => ((hl n).2.2.2.1 i).2)
        (f n) (hf n) (hfit n)
      simpa only [Fintype.card_fin] using hce.le
    · exact hrate
  apply TendstoInMeasure.congr _ (Eventually.of_forall (fun _ => rfl)) hconv
  intro n
  filter_upwards [(hl n).1] with a ha
  rw [← ha.2, Finset.card_image_of_injective _ ha.1, Finset.card_univ,
    Fintype.card_fin, Finset.sum_image]
  exact ha.1.injOn

-- @node: equalHalfSplit_varianceRV_consistent
/-- Under [an equal half split independent of the sample](hyp:hSplit), suppose [the fitted score is represented by a function of the masked training view and the observation](hyp:hscore), where [that function](hyp:f) [is measurable](hyp:hf) and [the oracle score is measurable](hyp:hg). If [the fitted-minus-oracle errors at held-out observations are square integrable](hyp:hfit), [their training-specific population mean squared error converges in probability to zero](hyp:hrate), [the evaluation average of squared oracle deviations from the target converges in probability to the proposed variance](hyp:hV), and [the fitted DML average is consistent for the target](hyp:hb), then [the empirical fitted-score variance converges in probability to the proposed variance](goal). -/
lemma equalHalfSplit_varianceRV_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o, score (2 * (n + 1)) a o =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n)) (truth : Obs X Z → ℝ) (hg : Measurable truth)
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a) -
        truth (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (f n (trainingView M S I₁ (2 * (n + 1)) a, o) - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (theta sigmaSq : ℝ)
    (hV : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a, (truth (S.Z i a) - theta) ^ 2)
      atTop (fun _ _ => sigmaSq))
    (hb : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => sigmaSq) := by
  have hd : ∀ n, Measurable (fun tb => f n tb - truth tb.2) := by
    intro n
    fun_prop
  have hE := equalHalfSplit_empirical_fitted_score_energy M μ S I₁ I₂ hSplit
    (fun n tb => f n tb - truth tb.2) hd hfit hrate
  have hI : ∀ n, ∀ᵐ a ∂μ, (I₂ (2 * (n + 1)) a).Nonempty := by
    intro n
    filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1] with a ha
    rw [← ha.2]
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  apply varianceRV_consistent_of_empirical_score_error M S I₂ score truth
    (fun n => 2 * (n + 1)) theta sigmaSq hI _ hV hb
  simpa only [hscore] using hE

end Papers.TbsPrteOptimalTransport
