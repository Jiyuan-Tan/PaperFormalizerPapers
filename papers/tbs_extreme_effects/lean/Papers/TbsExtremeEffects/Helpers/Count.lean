module
public import Papers.TbsExtremeEffects.Helpers.Split
public import Papers.TbsExtremeEffects.Helpers.TailSurvival
public import Causalean.Stat.Concentration.TailBounds.BinomialCount
public import Toolkit.Foundations.Probability.Concentration.ChernoffBounds

/-! The evaluation exceedance count and its multiplicative lower-tail bound.
The finite-sample argument uses independence after relabelling, without extending
the experiment to an infinite i.i.d. stream. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

/-- If [each random variable is measurable](hyp:hX), [the variables are independent](hyp:hind), [each lies between zero and one](hyp:h01), and [every variable in the finite set has mean `p`](hyp:hmean), then [the moment-generating function of their sum is bounded by the stated exponential expression](goal).

Tensorisation of the one-observation exponential bound over a finite index set.
@node: finite_bounded_count_mgf
-/
lemma finite_bounded_count_mgf {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (h01 : ∀ i w, X i w ∈ Set.Icc (0 : ℝ) 1)
    (I : Finset ι) {p : ℝ} (hmean : ∀ i ∈ I, ∫ w, X i w ∂P = p) (s : ℝ) :
    mgf (fun w => ∑ i ∈ I, X i w) P s ≤
      Real.exp ((I.card : ℝ) * p * (Real.exp s - 1)) := by
  classical
  have hsum : (fun w => ∑ i ∈ I, X i w) = ∑ i ∈ I, X i := by
    ext w
    simp
  rw [hsum, hind.mgf_sum hX]
  calc
    _ ≤ ∏ _i ∈ I, Real.exp (p * (Real.exp s - 1)) := by
      apply Finset.prod_le_prod (fun i _ => mgf_nonneg)
      intro i hi
      have h := Causalean.Stat.Concentration.mgf_le_of_mem_Icc_zero_one
        (hX i).aemeasurable (ae_of_all P (h01 i)) s
      simpa only [hmean i hi] using h
    _ = _ := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
      congr 1
      ring

/-- If [each random variable is measurable](hyp:hX), [the variables are independent](hyp:hind), [each lies between zero and one](hyp:h01), [their common mean is nonnegative](hyp:hp), and [every variable in the finite set has that mean](hyp:hmean), then [the probability that their sum is at most half its mean is exponentially small](goal).
 
Markov's inequality at tilt `-log 2`, including the half-mean boundary.
@node: finite_bounded_count_lower_tail
-/
lemma finite_bounded_count_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (h01 : ∀ i w, X i w ∈ Set.Icc (0 : ℝ) 1)
    (I : Finset ι) {p : ℝ} (hp : 0 ≤ p)
    (hmean : ∀ i ∈ I, ∫ w, X i w ∂P = p) :
    P.real {w | (∑ i ∈ I, X i w) ≤ (I.card : ℝ) * p / 2} ≤
      Real.exp (-((I.card : ℝ) * p) / 8) := by
  classical
  have hsum : (∑ i ∈ I, ∫ w, X i w ∂P) = (I.card : ℝ) * p := by
    calc
      _ = ∑ _i ∈ I, p := Finset.sum_congr rfl hmean
      _ = _ := by simp
  have hbound :=
    Toolkit.Foundations.Probability.Concentration.measureReal_sum_le_one_sub_mul_le_exp_of_mem_Icc
      P X hX hind h01 I (δ := (1 / 2 : ℝ)) (by norm_num)
  have hhalf : (1 - (1 / 2 : ℝ)) * ((I.card : ℝ) * p) =
      (I.card : ℝ) * p / 2 := by ring
  have hexponent : -((1 / 2 : ℝ) ^ 2) * ((I.card : ℝ) * p) / 2 =
      -((I.card : ℝ) * p) / 8 := by ring
  simpa only [hsum, hhalf, hexponent] using hbound

variable {q d : ℕ} {M : ExtremeModel q d}

/-- [The evaluation count equals the sum, over evaluation indices, of indicators that the sampled covariate exceeds the threshold](goal).
 
The cardinality of the selected evaluation set is its sum of tail indicators.
@node: evalCount_eq_sum_tail_indicators
-/
lemma evalCount_eq_sum_tail_indicators (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (w : E.Om) :
    (evalCount E n t w : ℝ) = ∑ i ∈ evalIndices n,
      if t < l1Norm (sampleU E n w i) then (1 : ℝ) else 0 := by
  classical
  simp [evalCount, evalSet, Finset.sum_boole]

/-- Given [an even sample size](hyp:hn) and [independent identically distributed sampling](hyp:hiid), [the chance that the evaluation count falls below one quarter of the sample-size tail probability has the stated exponential bound](goal).
 
The evaluation count has the roadmap's binomial half-mean lower-tail bound.
@node: evalCount_lower_tail
-/
lemma evalCount_lower_tail (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n) :
    E.P.real {w | (evalCount E n t w : ℝ) < (n : ℝ) * tailProb M t / 4} ≤
      Real.exp (-((n : ℝ) * tailProb M t) / 16) := by
  classical
  let f : Obs q d → ℝ := fun z => if t < l1Norm z.2.2.2 then 1 else 0
  have hf : Measurable f := by
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      measurable_const measurable_const
  let X : Fin n → E.Om → ℝ := fun i w => f (obs E n w i)
  have hX : ∀ i, Measurable (X i) := by
    intro i
    exact hf.comp ((measurable_pi_apply i).comp (measurable_obs_tuple M E n))
  obtain ⟨hind, hlaw⟩ := relabelled_iid M E n hn hiid
  have hindX : iIndepFun X E.P := hind.comp (fun _ => f) (fun _ => hf)
  have hmean : ∀ i ∈ evalIndices n, ∫ w, X i w ∂E.P = tailProb M t := by
    intro i _
    have hmap : (∫ w, X i w ∂E.P) =
        ∫ z, f z ∂E.P.map (fun w => obs E n w i) :=
      (integral_map ((measurable_pi_apply i).comp
        (measurable_obs_tuple M E n)).aemeasurable hf.aestronglyMeasurable).symm
    have hobs : Measurable (observation M) :=
      M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
    rw [hmap, hlaw i, integral_map hobs.aemeasurable hf.aestronglyMeasurable]
    change (∫ w, if t < radius M w then (1 : ℝ) else 0 ∂M.mu) = tailProb M t
    change (∫ w, {w | t < radius M w}.indicator (fun _ => (1 : ℝ)) w ∂M.mu) = _
    rw [integral_indicator_const _ (measurableSet_lt measurable_const (measurable_radius M))]
    simp [tailProb, measureReal_def]
  have hbound := finite_bounded_count_lower_tail E.P X hX hindX
    (fun i w => by dsimp [X, f]; split_ifs <;> norm_num)
    (evalIndices n) (tailProb_nonneg M t) hmean
  have hhalf : ((n / 2 : ℕ) : ℝ) = (n : ℝ) / 2 := by
    obtain ⟨k, hk⟩ := hn.2
    have hdiv : n / 2 = k := by omega
    rw [hdiv, hk]
    norm_num
  rw [(equalSplit_cardinality n hn).2, hhalf] at hbound
  have hsum : ∀ w, (∑ i ∈ evalIndices n, X i w) = (evalCount E n t w : ℝ) := by
    intro w
    exact (evalCount_eq_sum_tail_indicators E n t w).symm
  simp only [hsum] at hbound
  have hsub : {w | (evalCount E n t w : ℝ) < (n : ℝ) * tailProb M t / 4} ⊆
      {w | (evalCount E n t w : ℝ) ≤ (n : ℝ) / 2 * tailProb M t / 2} := by
    intro w hw
    change (evalCount E n t w : ℝ) ≤ _
    change (evalCount E n t w : ℝ) < _ at hw
    linarith
  have hexponent : -((n : ℝ) / 2 * tailProb M t) / 8 =
      -((n : ℝ) * tailProb M t) / 16 := by ring
  rw [hexponent] at hbound
  exact (measureReal_mono hsub).trans hbound

/-- [The real-valued evaluation count is measurable as a function of the experiment outcome](goal).
 
Measurability of the evaluation count follows from its finite indicator sum.
@node: measurable_evalCount_real
-/
@[fun_prop] lemma measurable_evalCount_real (E : NeteExperiment M) (n : ℕ) (t : ℝ) :
    Measurable (fun w => (evalCount E n t w : ℝ)) := by
  simp_rw [evalCount_eq_sum_tail_indicators]
  apply Finset.measurable_fun_sum
  intro i _
  apply Measurable.ite (measurableSet_lt measurable_const ?_) measurable_const measurable_const
  exact measurable_l1Norm.comp (((measurable_pi_apply i).comp
    (measurable_obs_tuple M E n)).snd.snd.snd)

/-- Given [an even sample size](hyp:hn), [i.i.d. sampling](hyp:hiid), [a positive confidence level](hyp:hd), [a confidence level below one](hyp:hd1), and [a sample-size tail-mass budget](hyp:hbudget), [the event that the evaluation count reaches its threshold is measurable, has probability at least `1 - delta / 4`, and ensures a nonzero count](goal).
 
The sample-size budget supplies the measurable count event with positive count.
@node: evaluation_count_event
-/
lemma evaluation_count_event (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    {delta : ℝ} (hd : 0 < delta) (hd1 : delta < 1)
    (hbudget : 16 * Real.log (4 / delta) ≤ (n : ℝ) * tailProb M t) :
    MeasurableSet {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)} ∧
      1 - delta / 4 ≤ E.P.real {w | (n : ℝ) * tailProb M t / 4 ≤
        (evalCount E n t w : ℝ)} ∧
      ∀ w, (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ) →
        evalCount E n t w ≠ 0 := by
  have hmeas : MeasurableSet {w | (n : ℝ) * tailProb M t / 4 ≤
      (evalCount E n t w : ℝ)} :=
    measurableSet_le measurable_const (measurable_evalCount_real E n t)
  have hfailure : E.P.real {w | (evalCount E n t w : ℝ) <
      (n : ℝ) * tailProb M t / 4} ≤ delta / 4 := by
    apply (evalCount_lower_tail E n t hn hiid).trans
    calc
      _ ≤ Real.exp (-Real.log (4 / delta)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = delta / 4 := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  have hcompl : {w | (evalCount E n t w : ℝ) < (n : ℝ) * tailProb M t / 4} =
      {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)}ᶜ := by
    ext w
    simp
  rw [hcompl, measureReal_compl hmeas, probReal_univ] at hfailure
  refine ⟨hmeas, by linarith, ?_⟩
  intro w hw hzero
  have hlog : 0 < Real.log (4 / delta) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hd).mpr
    linarith
  rw [hzero, Nat.cast_zero] at hw
  linarith

/-- Given [an even sample size](hyp:hn) and [i.i.d. sampling](hyp:hiid), [the expected indicator that any sampled direction exceeds the threshold equals the population tail probability](goal).
 
The radial indicator has the population tail mean after random relabelling.
@node: integral_sample_tail_indicator
-/
lemma integral_sample_tail_indicator (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n) (i : Fin n) :
    (∫ w, if t < l1Norm (sampleU E n w i) then (1 : ℝ) else 0 ∂E.P) =
      tailProb M t := by
  classical
  let f : Obs q d → ℝ := fun z => if t < l1Norm z.2.2.2 then 1 else 0
  have hf : Measurable f := by
    first | fun_prop | skip
    exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      measurable_const measurable_const
  have hm : Measurable (fun w => obs E n w i) :=
    (measurable_pi_apply i).comp (measurable_obs_tuple M E n)
  have hobs : Measurable (observation M) := by
    first | fun_prop | skip
    exact M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  have hlaw := (relabelled_iid M E n hn hiid).2 i
  change (∫ w, f (obs E n w i) ∂E.P) = _
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable,
    hlaw, integral_map hobs.aemeasurable hf.aestronglyMeasurable]
  change (∫ w, {w | t < radius M w}.indicator (fun _ => (1 : ℝ)) w ∂M.mu) = _
  rw [integral_indicator_const _ (measurableSet_lt measurable_const (measurable_radius M))]
  simp [tailProb, measureReal_def]

/-- Given [an even sample size](hyp:hn) and [i.i.d. sampling](hyp:hiid), [the evaluation count is integrable and its mean is half the sample size times the tail probability](goal).
 
The evaluation count is integrable, with the exact half-sample tail mean.
@node: evalCount_integrable_mean
-/
lemma evalCount_integrable_mean (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n) :
    Integrable (fun w => (evalCount E n t w : ℝ)) E.P ∧
      (∫ w, (evalCount E n t w : ℝ) ∂E.P) = (n : ℝ) / 2 * tailProb M t := by
  classical
  have hInt (i : Fin n) : Integrable
      (fun w => if t < l1Norm (sampleU E n w i) then (1 : ℝ) else 0) E.P := by
    have hm : Measurable (fun w => l1Norm (sampleU E n w i)) := by
      first | fun_prop | skip
      exact measurable_l1Norm.comp (((measurable_pi_apply i).comp
        (measurable_obs_tuple M E n)).snd.snd.snd)
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_lt measurable_const hm)
  have hcount : Integrable (fun w => (evalCount E n t w : ℝ)) E.P := by
    simp_rw [evalCount_eq_sum_tail_indicators]
    exact integrable_finset_sum _ (fun i _ => hInt i)
  refine ⟨hcount, ?_⟩
  simp_rw [evalCount_eq_sum_tail_indicators]
  rw [integral_finset_sum _ (fun i _ => hInt i)]
  simp_rw [integral_sample_tail_indicator E n t hn hiid]
  rw [Finset.sum_const, (equalSplit_cardinality n hn).2, nsmul_eq_mul]
  congr 1
  obtain ⟨k, hk⟩ := hn.2
  have hdiv : n / 2 = k := by omega
  rw [hdiv, hk]
  push_cast
  ring

/-- Given [an even sample size](hyp:hn), [i.i.d. sampling](hyp:hiid), and [a measurable good event](hyp:hG), [the good-event-clipped squared indicator sum is integrable and has mean at most half the sample size times the tail probability](goal).
 
Clipping to any measurable good event only decreases count square energy.
@node: evaluation_count_square_energy
-/
lemma evaluation_count_square_energy (E : NeteExperiment M) (n : ℕ) (t : ℝ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n)
    (G : Set E.Om) (hG : MeasurableSet G) :
    Integrable (fun w => ∑ i : Fin n, if t < l1Norm (sampleU E n w i) then
      (if w ∈ G ∧ i ∈ evalIndices n then (1 : ℝ) else 0) ^ 2 else 0) E.P ∧
    (∫ w, (∑ i : Fin n, if t < l1Norm (sampleU E n w i) then
      (if w ∈ G ∧ i ∈ evalIndices n then (1 : ℝ) else 0) ^ 2 else 0) ∂E.P) ≤
      (n : ℝ) / 2 * tailProb M t := by
  classical
  have hEq : (fun w => ∑ i : Fin n, if t < l1Norm (sampleU E n w i) then
      (if w ∈ G ∧ i ∈ evalIndices n then (1 : ℝ) else 0) ^ 2 else 0) =
      G.indicator (fun w => (evalCount E n t w : ℝ)) := by
    funext w
    by_cases hw : w ∈ G
    · simp only [Set.indicator_of_mem hw, hw, true_and]
      rw [evalCount_eq_sum_tail_indicators]
      calc
        _ = ∑ i : Fin n, if i ∈ evalIndices n then
            (if t < l1Norm (sampleU E n w i) then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases ht : t < l1Norm (sampleU E n w i) <;>
            by_cases hi : i ∈ evalIndices n <;> simp [ht, hi]
        _ = _ := by
          rw [← Finset.sum_filter]
          simp
    · simp [hw]
  rw [hEq]
  obtain ⟨hInt, hMean⟩ := evalCount_integrable_mean E n t hn hiid
  refine ⟨hInt.indicator hG, ?_⟩
  rw [← hMean]
  apply integral_mono (hInt.indicator hG) hInt
  intro w
  by_cases hw : w ∈ G
  · simp [hw]
  · simp [hw]

end Papers.TbsExtremeEffects
