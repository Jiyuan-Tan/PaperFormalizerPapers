module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLGammaBandTreatment
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryTrainingVariance
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousRegimeConvergence
/-! Evaluation moments for continuous fractional treatment corrections.
The bounded representers and clipped inverse weights give a uniform bound,
including at the structural-zero baseline. This transfers population score
convergence to the random evaluation half and its empirical variance. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

-- @node: continuousPairedTreatmentBlock
/-- For [a latent instrumental-variable model](hyp:M), [treatment levels and
policy bands](hyp:L), [a continuous nuisance fit](hyp:e), and [an observation](hyp:o),
[the paired treatment correction block](goal) sums each fitted band share times
the sum of the lower and upper propensity representers multiplied by their
matching treatment residuals, omitting the lower term at the baseline level. -/
noncomputable def continuousPairedTreatmentBlock (L : LevelData Z X)
    (e : NuisanceCont L) (o : Obs X Z) : ℝ :=
  ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    regularValue e.gamma k j o.1 *
      ((if k = 0 then 0 else alphaLow M L e k (j-1) o.1 * RpCont L e k o) +
        alphaHigh M L e k (j-1) o.1 * RpCont L e (k+1) o)

-- @node: fitted_continuous_gamma_alpha_treatment_abs_bound
/-- If [the fit is admissible](hyp:he), [the denominator bound is positive](hyp:hc),
[positive-level fitted instrument probabilities exceed that bound almost
everywhere](hyp:hden), and [the band level is nonterminal](hyp:hk), [the absolute
value of any fitted regular share times the selected propensity representer and
its treatment residual is almost surely at most five times the sum of absolute
outcome endpoints divided by the denominator bound](goal). -/
lemma fitted_continuous_gamma_alpha_treatment_abs_bound
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (g : RegularIndex L) (plus : Bool) (k j : ℕ) (hk : k < L.K) :
    ∀ᵐ o ∂observationLaw M, |e.gamma g o.1 *
      ((if plus then alphaHigh M L e k j o.1 else alphaLow M L e k j o.1) *
        RpCont L e (if plus then k+1 else k) o)| ≤
      5 * (|M.yMin| + |M.yMax|) * (1 / c) := by
  have hg : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have ha : ∀ᵐ x ∂xLaw M,
      |if plus then alphaHigh M L e k j x else alphaLow M L e k j x| ≤
        5 * (|M.yMin| + |M.yMax|) := by
    cases plus
    · exact (continuous_admissible_alpha_abs_bounds M L e he k j).2
    · exact (continuous_admissible_alpha_abs_bounds M L e he k j).1
  have hi : (if plus then k+1 else k) ≤ L.K := by
    cases plus <;> simp <;> omega
  filter_upwards [observationLaw_covariate_ae M _ hg,
    observationLaw_covariate_ae M _ ha,
    fitted_RpCont_abs_bound M L e he c hc hden _ hi] with o hg ha hr
  rw [abs_mul, abs_mul]
  exact (mul_le_mul hg (mul_le_mul ha hr (abs_nonneg _) (by positivity))
    (by positivity) zero_le_one).trans_eq (one_mul _)

-- @node: fitted_continuous_paired_treatment_block_abs_bound
/-- For [an admissible fit](hyp:he), [a positive denominator bound](hyp:hc), and
[positive-level fitted instrument probabilities bounded below by it almost
everywhere](hyp:hden), [the absolute paired treatment block is almost surely
bounded by the sum over nonterminal levels and their bands of ten times the sum
of absolute outcome endpoints divided by that bound](goal). -/
lemma fitted_continuous_paired_treatment_block_abs_bound
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    ∀ᵐ o ∂observationLaw M, |continuousPairedTreatmentBlock M L e o| ≤
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        10 * (|M.yMin| + |M.yMax|) * (1 / c) := by
  have hb : ∀ᵐ o ∂observationLaw M, ∀ g : RegularIndex L,
      ∀ plus : Bool, ∀ k j : ℕ, k < L.K →
      |e.gamma g o.1 *
        ((if plus then alphaHigh M L e k j o.1 else alphaLow M L e k j o.1) *
          RpCont L e (if plus then k+1 else k) o)| ≤
        5 * (|M.yMin| + |M.yMax|) * (1 / c) := by
    simp only [ae_all_iff]
    intro g plus k j hk
    exact fitted_continuous_gamma_alpha_treatment_abs_bound M L e he c hc hden
      g plus k j hk
  filter_upwards [hb] with o ho
  unfold continuousPairedTreatmentBlock
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
    ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
  have hl := ho ⟨(k,j),hg⟩ false k (j-1) (Finset.mem_range.mp hk)
  have hu := ho ⟨(k,j),hg⟩ true k (j-1) (Finset.mem_range.mp hk)
  simp only [Bool.false_eq_true, if_false, if_true] at hl hu
  rw [continuous_band_lower_correction_eq, mul_add, regularValue, dif_pos hg]
  exact (abs_add_le _ _).trans (by linarith)

-- @node: continuousPairedTreatmentBlock_restrictContShares
/-- [Restricting a continuous nuisance fit's shares leaves its paired treatment
correction block unchanged for every observation](goal). -/
lemma continuousPairedTreatmentBlock_restrictContShares
    (L : LevelData Z X) (e : NuisanceCont L) :
    continuousPairedTreatmentBlock M L (restrictContShares L e) =
      continuousPairedTreatmentBlock M L e := by
  funext o
  simp only [continuousPairedTreatmentBlock, restrictContShares, regularValue,
    alphaLow, alphaHigh, nuValue, RpCont]

-- @node: measurable_decoded_continuous_paired_treatment_block
/-- If [each encoded nuisance component is jointly measurable in its fitting
argument and covariates](hyp:hm), [the paired treatment block obtained by decoding
those components is jointly measurable in the fitting argument and observation](goal). -/
@[fun_prop] lemma measurable_decoded_continuous_paired_treatment_block
    {A : Type*} [MeasurableSpace A] (L : LevelData Z X)
    (F : A → (ℕ × ℕ × ℕ × Z) → X → ℝ)
    (hm : ∀ c, Measurable (fun ax : A × X => F ax.1 c ax.2)) :
    Measurable (fun ao : A × Obs X Z =>
      continuousPairedTreatmentBlock M L (decodeContComponents L (F ao.1)) ao.2) := by
  try fun_prop
  have hF c : Measurable (fun ao : A × Obs X Z => F ao.1 c ao.2.1) := by
    fun_prop
  have hv code k : Measurable (fun ao : A × Obs X Z =>
      positiveValue (fun (i : PositiveIndex L.K) x =>
        F ao.1 (code, i, 0, Classical.choice inferInstance) x) k ao.2.1) := by
    unfold positiveValue
    split_ifs <;> fun_prop
  have hnu k j : Measurable (fun ao : A × Obs X Z =>
      nuValue M (decodeContComponents L (F ao.1)) k j ao.2.1) := by
    simp only [nuValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hbp k j : Measurable (fun ao : A × Obs X Z =>
      boundaryValue (decodeContComponents L (F ao.1)).Mplus k j ao.2.1) := by
    simp only [boundaryValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hbm k j : Measurable (fun ao : A × Obs X Z =>
      minusBoundaryValue (decodeContComponents L (F ao.1)).Mminus k j ao.2.1) := by
    simp only [minusBoundaryValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hmp k j : Measurable (fun ao : A × Obs X Z =>
      meanValue (decodeContComponents L (F ao.1)).Jplus k j ao.2.1) := by
    simp only [meanValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hmm k j : Measurable (fun ao : A × Obs X Z =>
      minusMeanValue (decodeContComponents L (F ao.1)).Jminus k j ao.2.1) := by
    simp only [minusMeanValue, decodeContComponents]
    split_ifs <;> fun_prop
  have hl k j : Measurable (fun ao : A × Obs X Z =>
      alphaLow M L (decodeContComponents L (F ao.1)) k j ao.2.1) := by
    unfold alphaLow
    fun_prop
  have hu k j : Measurable (fun ao : A × Obs X Z =>
      alphaHigh M L (decodeContComponents L (F ao.1)) k j ao.2.1) := by
    unfold alphaHigh
    fun_prop
  have hi (s : Finset Z) : Measurable (fun ao : A × Obs X Z =>
      indicator (ao.2.2.1 ∈ s)) := by
    unfold indicator
    exact Measurable.ite (s.finite_toSet.measurableSet.preimage measurable_snd.snd.fst)
      measurable_const measurable_const
  have hp k : Measurable (fun ao : A × Obs X Z =>
      RpCont L (decodeContComponents L (F ao.1)) k ao.2) := by
    unfold RpCont
    split_ifs
    · fun_prop
    · change Measurable (fun ao : A × Obs X Z =>
        indicator (ao.2.2.1 ∈ L.S k) / positiveValue
          (fun (i : PositiveIndex L.K) x => F ao.1 (2, i, 0, Classical.choice inferInstance) x)
          k ao.2.1 * (ao.2.2.2.1 - positiveValue
          (fun (i : PositiveIndex L.K) x => F ao.1 (1, i, 0, Classical.choice inferInstance) x)
          k ao.2.1))
      fun_prop
  have hg k j : Measurable (fun ao : A × Obs X Z =>
      regularValue (decodeContComponents L (F ao.1)).gamma k j ao.2.1) := by
    simp only [regularValue, decodeContComponents]
    split_ifs <;> fun_prop
  unfold continuousPairedTreatmentBlock
  apply Finset.measurable_sum
  intro k hk
  apply Finset.measurable_sum
  intro j hj
  split_ifs <;> fun_prop

-- @node: training_measurable_continuous_paired_treatment_block
/-- If [every encoded nuisance component is measurable using the first training
split together with the prediction covariates](hyp:hm), [the fitted paired
treatment block is measurable using that training split together with the
evaluation observation](goal). -/
lemma training_measurable_continuous_paired_treatment_block
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ : SampleSplit A)
    (L : LevelData Z X) (eh : ℕ → A → NuisanceCont L)
    (hm : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun n a => contComponent M L (eh n a) c)) :
    TrainingPredictorMeasurable M S I₁
      (fun n a => continuousPairedTreatmentBlock M L (eh n a)) := by
  dsimp only [TrainingPredictorMeasurable] at hm ⊢
  intro n
  let mTrain : MeasurableSpace A := MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
  let : MeasurableSpace A := mTrain
  have hf : Measurable[mTrain.prod inferInstance] (fun ao : A × Obs X Z =>
      continuousPairedTreatmentBlock M L
        (decodeContComponents L (contComponent M L (eh n ao.1))) ao.2) :=
    measurable_decoded_continuous_paired_treatment_block M L
    (fun a => contComponent M L (eh n a)) (fun c => hm c n)
  simp only [decodeContComponents_contComponent] at hf
  convert hf using 1
  funext ⟨a, o⟩
  simp only [Function.uncurry_apply_pair, continuousPairedTreatmentBlock,
    normalizeContAuxiliaryFits, restrictContShares, regularValue, alphaLow,
    alphaHigh, nuValue, RpCont]

-- @node: encoded_training_continuous_paired_treatment_mean_variance_consistent
/-- Suppose [the training and evaluation samples form an equal half split](hyp:hSplit),
[the population nuisance is admissible](hyp:he0), and fitted nuisances [are
clipped](hyp:hclip), [have simplex-valued shares](hyp:hshares), [have measurable
encoded components](hyp:hm), and [have componentwise L² errors that vanish faster
in probability than the inverse fourth root of sample size](hyp:hr), with
[baseline overlap](hyp:hov), [denominator clipping at the overlap constant](hyp:hden),
and [each component measurable from the training split and prediction covariates](hyp:htraincomp).
Then [the evaluation mean of the fitted paired treatment block converges in
probability to the population block's mean, and its evaluation variance converges
in probability to the population block's variance, along sample sizes twice one
plus the index](goal). -/
lemma encoded_training_continuous_paired_treatment_mean_variance_consistent
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a d, Measurable (contComponent M L (eh n a) d))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n a, ContDenominatorsClipped L (eh n a) cpi)
    (htraincomp : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun n a => contComponent M L (eh n a) c)) :
    let score := fun n a => continuousPairedTreatmentBlock M L (eh n a)
    let truth := continuousPairedTreatmentBlock M L (trueNuisance M L)
    let theta := ∫ o, truth o ∂observationLaw M
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a)
      atTop (fun _ _ => populationVariance M truth theta) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hconst : ∀ c, TrainingPredictorMeasurable M S I₁
      (fun (_ : ℕ) (_ : A) => contComponent M L (trueNuisance M L) c) := by
    intro c n
    let : MeasurableSpace A := MeasurableSpace.comap (trainingView M S I₁ n) inferInstance
    exact (contAdmissible_component_measurable M L _ he0 c).comp measurable_snd
  have ht := training_measurable_continuous_paired_treatment_block M S I₁ L eh htraincomp
  have ht0 := training_measurable_continuous_paired_treatment_block M S I₁ L
    (fun _ _ => trueNuisance M L) hconst
  have htrain : TrainingPredictorMeasurable M S I₁ (fun n a o =>
      continuousPairedTreatmentBlock M L (eh n a) o -
        continuousPairedTreatmentBlock M L (trueNuisance M L) o) := by
    intro n
    exact (ht n).sub (ht0 n)
  let er := fun n a => restrictContShares L (eh n a)
  have her n a : ContAdmissible M L (er n a) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n a)
      (hclip n a) (hshares n a) (hm n a)
  have hc : 0 < cpi / 2 := by linarith [hov.1]
  have hp0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have hpf n a (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (er n a).piLev i x :=
    Eventually.of_forall (fun x => (hden n a).1 i x |>.1)
  let C := ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    10 * (|M.yMin| + |M.yMax|) * (1 / (cpi / 2))
  have hbound n a : ∀ᵐ o ∂observationLaw M,
      |continuousPairedTreatmentBlock M L (eh n a) o -
        continuousPairedTreatmentBlock M L (trueNuisance M L) o| ≤ C + C := by
    have hf := fitted_continuous_paired_treatment_block_abs_bound M L (er n a)
      (her n a) (cpi / 2) hc (hpf n a)
    simp only [er, continuousPairedTreatmentBlock_restrictContShares] at hf
    filter_upwards [hf, fitted_continuous_paired_treatment_block_abs_bound M L
      (trueNuisance M L) he0 (cpi / 2) hc hp0] with o hf ht
    exact (abs_sub _ _).trans (add_le_add hf ht)
  have hLp : MemLp (continuousPairedTreatmentBlock M L (trueNuisance M L))
      2 (observationLaw M) :=
    fitted_continuous_paired_band_treatment_block_memLp M L _ he0
      (cpi / 2) hc hp0
  have hrate := encoded_continuous_paired_band_treatment_block_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hr cpi hov hden
  dsimp only
  exact equalHalfSplit_ae_bounded_training_oracle_mean_variance_consistent
    M μ S I₁ I₂ hSplit _ _ _ rfl hLp htrain (C + C) hbound hrate

end Papers.TbsPrteOptimalTransport
