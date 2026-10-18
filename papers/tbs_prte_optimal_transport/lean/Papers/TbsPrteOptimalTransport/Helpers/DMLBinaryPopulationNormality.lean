module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPopulationBiasAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryTrainingVariance
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRootNConsistency
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryPopulationVariance
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryFiniteLabelClipping
/-! Binary oracle normality from the complete population score bias and support-bounded
conditional fluctuations, followed by finite-label recovery transfer. -/
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: equalHalfSplit_ae_bounded_training_l2_factorization
/-- Under [an equal training and evaluation split](hyp:hSplit), if [the score
is measurable using the training observations and a new observation](hyp:hm)
and [its absolute value is bounded by C almost everywhere in the observation
law for every fit](hyp:hb), [at each even sample size it has an exact measurable
representation in the training view and a new observation, with square-integrable
sections for every training view and square-integrable evaluations at every
held-out observation](goal). -/
lemma equalHalfSplit_ae_bounded_training_l2_factorization
    {A : Type*} [MeasurableSpace A]
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ)
    (hm : TrainingPredictorMeasurable M S I₁ score) (C : ℝ)
    (hb : ∀ n a, ∀ᵐ o ∂observationLaw M, |score n a o| ≤ C) :
    ∃ f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) ×
        Obs X Z → ℝ,
      (∀ n a o, score (2 * (n + 1)) a o =
        f n (trainingView M S I₁ (2 * (n + 1)) a, o)) ∧
      (∀ n, Measurable (f n)) ∧
      (∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M)) ∧
      (∀ n i, MemLp (fun a => f n
        (trainingView M S I₁ (2 * (n + 1)) a,
          S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) := by
  letI : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  obtain ⟨g, heq, hg, hfit⟩ :=
    equalHalfSplit_ae_bounded_training_score_factorization M μ S I₁ I₂ hSplit score hm C hb
  let good := fun n t => Integrable (fun o => g n (t, o) ^ 2) (observationLaw M)
  have hgood (n : ℕ) : MeasurableSet {t | good n t} := by
    apply _root_.measurableSet_integrable
    exact (show Measurable (fun tb => g n tb ^ 2) by fun_prop).stronglyMeasurable
  have hactual (n : ℕ) (a : A) : good n (trainingView M S I₁ (2 * (n + 1)) a) := by
    have hs : Measurable (fun o => g n (trainingView M S I₁ (2 * (n + 1)) a, o)) := by
      fun_prop
    apply MemLp.integrable_sq
    apply MemLp.of_bound hs.aestronglyMeasurable C
    simpa only [Real.norm_eq_abs, ← heq] using hb (2 * (n + 1)) a
  let f := fun n tb => if good n tb.1 then g n tb else 0
  have hf (n : ℕ) : Measurable (f n) := by
    exact Measurable.ite ((hgood n).preimage measurable_fst) (hg n) measurable_const
  have hpreserve (n : ℕ) (a : A) (o : Obs X Z) :
      f n (trainingView M S I₁ (2 * (n + 1)) a, o) =
        g n (trainingView M S I₁ (2 * (n + 1)) a, o) := by
    simp only [f, if_pos (hactual n a)]
  refine ⟨f, fun n a o => (heq n a o).trans (hpreserve n a o).symm, hf, ?_, ?_⟩
  · intro n t
    by_cases ht : good n t
    · have hs : Measurable (fun o => g n (t, o)) := by fun_prop
      simpa only [f, if_pos ht] using
        (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mpr ht
    · simpa only [f, if_neg ht] using (MemLp.zero' : MemLp (fun _ : Obs X Z => (0 : ℝ)) 2
        (observationLaw M))
  · intro n i
    simpa only [hpreserve] using hfit n i

-- @node: equalHalfSplit_ae_bounded_training_oracle_remainder_negligible
/-- Under [an equal training and evaluation split](hyp:hSplit), suppose
[the fitted-minus-oracle score is training-measurable](hyp:hm), [is bounded in
absolute value by C almost everywhere for every fit](hyp:hb), [has population
mean squared error converging to zero in probability along even sample sizes](hyp:hrate),
and [has population mean negligible after multiplication by the square root of
the evaluation sample size](hyp:hbias); then [the difference between the fitted
and oracle evaluation averages, multiplied by that same square root, converges
to zero in probability](goal). -/
lemma equalHalfSplit_ae_bounded_training_oracle_remainder_negligible
    {A : Type*} [MeasurableSpace A]
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (C : ℝ) (hb : ∀ n a, ∀ᵐ o ∂observationLaw M, |score n a o - truth o| ≤ C)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (hbias : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ o, score (2 * (n + 1)) a o - truth o ∂observationLaw M))
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ => truth) (2 * (n + 1)) a))
      atTop (fun _ _ => 0) := by
  obtain ⟨f, heq, hf, hsection, hfit⟩ :=
    equalHalfSplit_ae_bounded_training_l2_factorization M μ S I₁ I₂ hSplit
      (fun n a o => score n a o - truth o) hm C hb
  apply equalHalfSplit_oracle_score_remainder_negligible M μ S I₁ I₂ hSplit
    score truth f heq hf hsection hfit
  · simpa only [← heq] using hrate
  · simpa only [← heq] using hbias

-- @node: equalHalfSplit_ae_bounded_training_oracle_clt
/-- Under [an equal training and evaluation split](hyp:hSplit), suppose
[the oracle score has mean theta](hyp:hmean) and [is square-integrable](hyp:hLp),
while [the fitted-minus-oracle score is training-measurable](hyp:hm), [is uniformly
bounded almost everywhere](hyp:hb), [has population mean squared error tending
to zero in probability](hyp:hrate), and [has population mean negligible at the
inverse square root of the evaluation sample size](hyp:hbias); then [the fitted
evaluation average centered at theta and multiplied by the square root of the
evaluation sample size converges in law to a centered Gaussian with the oracle
score's population variance](goal). -/
lemma equalHalfSplit_ae_bounded_training_oracle_clt
    {A : Type*} [MeasurableSpace A]
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (hLp : MemLp truth 2 (observationLaw M))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (C : ℝ) (hb : ∀ n a, ∀ᵐ o ∂observationLaw M, |score n a o - truth o| ≤ C)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (hbias : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ o, score (2 * (n + 1)) a o - truth o ∂observationLaw M))
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  obtain ⟨f, heq, hf, hsection, hfit⟩ :=
    equalHalfSplit_ae_bounded_training_l2_factorization M μ S I₁ I₂ hSplit
      (fun n a o => score n a o - truth o) hm C hb
  have hrem := equalHalfSplit_ae_bounded_training_oracle_remainder_negligible
    M μ S I₁ I₂ hSplit score truth hm C hb hrate hbias
  apply equalHalfSplit_fitted_oracle_dmlRV_clt M μ S I₁ I₂ hSplit truth hLp theta hmean
    score _ hrem
  intro n i
  have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n
  have ht := hLp.comp_measurePreserving
    (show MeasurePreserving
      (fun a => S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)
      μ (observationLaw M) from ⟨hl.2.2.1 i, (hl.2.2.2.1 i).2⟩)
  have hr := (hfit n i).add ht
  simp only [← heq] at hr
  simpa only [Pi.add_def, Function.comp_def, sub_add_cancel] using
    hr.aestronglyMeasurable.aemeasurable

-- @node: nuisanceRates_training_population_binary_clt
/-- Suppose [training and evaluation use equal halves](hyp:hSplit), [the policy
map is valid](hyp:hphi), [its derivative is correctly specified](hyp:hd) and
[bounded and Lipschitz](hyp:hDerivative), [the structural assumptions hold](hyp:hStruct),
[outcome endpoints are known](hyp:hEndpoints), [the instrument admits finite
reduction](hyp:hFinite), and [outcomes are binary almost surely](hyp:hy). If
[the level count is positive](hyp:hK), [baseline levels are measurable](hyp:hlev),
[level order is invariant across covariates](hyp:hOrder), [policy overlap](hyp:hov)
and [baseline overlap](hyp:hbase) hold, [population nuisances](hyp:he0) and
[all fitted nuisances](hyp:heh) are admissible, [policy levels avoid the boundary](hyp:hOff),
[propensity gaps are separated by the specified gap](hyp:hGap), [discrete outcomes
satisfy the specified gap condition](hyp:hOutcome), [c is positive](hyp:hc),
[fitted positive-level instrument probabilities](hyp:hpi) and [regular-cell
probabilities](hyp:htau) are at least c almost everywhere, the finite nuisance
rate conditions hold for [propensities](hyp:hrp), [baseline levels](hyp:hrlev),
[success regressions](hyp:hrP), [level probabilities](hyp:hrpi), [shares](hyp:hrs),
[cell probabilities](hyp:hrt), [regular weights](hyp:hrg), [full weights](hyp:hrfull),
and [tail weights](hyp:hrtail), and [the score difference is training-measurable](hyp:hm),
[the binary evaluation average centered at the discrete target and scaled by
the square root of the half-sample size converges in law to a centered Gaussian
with the population score variance](goal). -/
lemma nuisanceRates_training_population_binary_clt
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hEndpoints : OutcomeEndpointsKnown M)
    (hFinite : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (ch : ℝ) (hOutcome : DiscreteOutcomeGapWitness M L ch)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M L).piLev)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M L).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) (eta0Bin M L).gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (eta0Bin M L).gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (eta0Bin M L).gammaTail))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o =>
      psiBin M phi dphi L hK o (eh n a) -
        psiBin M phi dphi L hK o (eta0Bin M L))) :
    let score := fun n a o => psiBin M phi dphi L hK o (eh n a)
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInLaw (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ score (2 * (n + 1)) a - theta)) atTop
      (gaussianReal 0 (Real.toNNReal (populationVariance M truth theta))) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hpi0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).piLev i x :=
    Eventually.of_forall (fun x => hbase.2 x i i.property.1 i.property.2)
  have htau0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev r x :=
    Eventually.of_forall (fun x => hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have hc' : 0 < min c cpi := lt_min hc hbase.1
  have hpifit (n : ℕ) (a : A) (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eh n a).piLev i x :=
    (hpi n a i).mono (fun _ h => (min_le_left _ _).trans h)
  have htaufit (n : ℕ) (a : A) (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eh n a).tauLev r x :=
    (htau n a r).mono (fun _ h => (min_le_left _ _).trans h)
  have hpitrue (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eta0Bin M L).piLev i x :=
    (hpi0 i).mono (fun _ h => (min_le_right _ _).trans h)
  have htautrue (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eta0Bin M L).tauLev r x :=
    (htau0 r).mono (fun _ h => (min_le_right _ _).trans h)
  obtain ⟨B, D, hB, hD, hder⟩ := hDerivative
  have hbder (z : Z) (x : X) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
      |dphi z x p| ≤ B := (hder z x p p hp hp).1
  let C := (∑ k ∈ Finset.range L.K, (1 + 2 / min c cpi +
    ∑ j ∈ Finset.Icc 1 (L.l k), (1 + 4 / min c cpi +
      ((L.T k j).card + (L.T k (j - 1)).card) * B / min c cpi))) +
    |M.yMin| * (2 + B + 1 / min c cpi)
  have hbtrue := fitted_binary_score_abs_bound M phi dphi hphi B hB hbder L hK
    (eta0Bin M L) he0 hy (min c cpi) hc' hpitrue htautrue
  have hbound (n : ℕ) (a : A) : ∀ᵐ o ∂observationLaw M,
      |psiBin M phi dphi L hK o (eh n a) -
        psiBin M phi dphi L hK o (eta0Bin M L)| ≤ C + C := by
    have hbfit := fitted_binary_score_abs_bound M phi dphi hphi B hB hbder L hK
      (eh n a) (heh n a) hy (min c cpi) hc' (hpifit n a) (htaufit n a)
    filter_upwards [hbfit, hbtrue] with o hh ht
    exact (abs_sub _ _).trans (add_le_add hh ht)
  have hpiboth (n : ℕ) (a : A) (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eta0Bin M L).piLev i x ∧
        min c cpi ≤ (eh n a).piLev i x := by
    filter_upwards [hpitrue i, hpifit n a i] with x ht hh
    exact ⟨ht, hh⟩
  have htauboth (n : ℕ) (a : A) (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eta0Bin M L).tauLev r x ∧
        min c cpi ≤ (eh n a).tauLev r x := by
    filter_upwards [htautrue r, htaufit n a r] with x ht hh
    exact ⟨ht, hh⟩
  have hr := nuisanceRates_binary_score_sq_tendsto_probability_zero_of_branch_convergence M μ
    phi dphi hphi hd ⟨B, D, hB, hD, hder⟩ L hK (eta0Bin M L) eh he0 heh hy
    (min c cpi) hc' hpiboth htauboth hrp hrlev hrP hrpi hrt hrs hrg hrfull hrtail
    (fun k hk j hj =>
      nuisanceRates_population_binary_branch_observation_sq_tendsto_probability_zero M μ
        phi dphi hphi hd ⟨B, D, hB, hD, hder⟩ hStruct hEndpoints hFinite hy L hOrder
        hOff gap hGap cpi hov ch hOutcome eh he0 heh hrp hrlev hrP hrs k j hk hj)
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hd M.prop
    hStruct.2.2.2.1.2.1 M.rangeProp
  have hmean := (population_binary_score_mean_eq_target M hStruct hEndpoints hFinite
    phi dphi hphi hdphi ⟨B, D, hB, hD, hder⟩ L hK hOrder hlev cpi hbase hov hy he0).2
  have hLp := fitted_binary_score_memLp M phi dphi hphi hd ⟨B, D, hB, hD, hder⟩ L hK
    (eta0Bin M L) he0 hy cpi hbase.1 hpi0 htau0
  have hbias := nuisanceRates_population_binary_score_bias_root_n_negligible M μ
    phi dphi hphi hd ⟨B, D, hB, hD, hder⟩ hStruct hy hEndpoints hFinite L hK hlev hOrder
    cpi hov hbase he0 eh heh hOff gap hGap ch hOutcome c hc hpi htau hrp hrlev hrP
    hrpi hrs hrt hrg hrfull hrtail
  have hfitLp (n : ℕ) (a : A) := fitted_binary_score_memLp M phi dphi hphi hd
    ⟨B, D, hB, hD, hder⟩ L hK (eh n a) (heh n a) hy c hc (hpi n a) (htau n a)
  have hi (n : ℕ) (a : A) :
      (∫ o, psiBin M phi dphi L hK o (eh (2 * (n + 1)) a) -
        psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M) =
      (∫ o, psiBin M phi dphi L hK o (eh (2 * (n + 1)) a) ∂observationLaw M) -
        (∫ o, psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M) :=
    integral_sub ((hfitLp _ a).integrable (by norm_num)) (hLp.integrable (by norm_num))
  exact equalHalfSplit_ae_bounded_training_oracle_clt M μ S I₁ I₂ hSplit
    _ _ _ hmean hLp hm (C+C) hbound hr (by simpa only [hi] using hbias)

-- @node: binDMLRegime_population_rootn_on_recovery
/-- Suppose [the split has equal halves](hyp:hSplit), [the policy is valid](hyp:hphi)
with [the specified derivative](hyp:hd) that is [bounded and Lipschitz](hyp:hDerivative),
[the structural assumptions hold](hyp:hStruct), [outcome endpoints are known](hyp:hEndpoints),
[the instrument admits finite reduction](hyp:hFinite), and [outcomes are binary
almost surely](hyp:hy). If [the level count is positive](hyp:hK), [baseline levels
are measurable](hyp:hlev), [level order is invariant](hyp:hOrder), [policy](hyp:hov)
and [baseline](hyp:hbase) overlap hold, [the fitted binary nuisance records on the
recovered level structures](hyp:eHat) [satisfy the finite binary DML regime](hyp:hr),
[the recovery events have probability tending to one](hyp:hG),
[recovered score labels equal the population labels on those events at even
sample sizes](hyp:hLabels), [policy levels avoid the boundary](hyp:hOff), and
[the specified propensity gap separates levels](hyp:hGap), [the feasible binary
DML estimate of the discrete population target has error of order the inverse
square root of the total sample size in probability along even sample sizes](goal). -/
lemma binDMLRegime_population_rootn_on_recovery
    (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hEndpoints : OutcomeEndpointsKnown M)
    (hFinite : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n →
      scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a) =
        scoreRecoveryLabels L)
    (hOff : PolicyLevelOffBoundary L)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
 :
    let score := fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ := by
  have he0 := population_binary_nuisance_admissible M hStruct.2.2.2.1 hy
    (policyProp phi M.prop) L hOrder hlev cpi hov
  have hmono := population_binary_P1_monotone M hStruct hEndpoints hFinite hy
    (policyProp phi M.prop) L hOrder
  obtain ⟨oracle, hm, hc, ha, hrate, hscore, hsorted, heq⟩ :=
    binDMLRegime_rearranged_oracle_score_records_of_scoreLabels_eq M μ S I₁ I₂ pHat phi dphi
      hphi hd rho gap cpi L ch hK eHat hr G hG hLabels
  have hdiff := training_measurable_binary_score_difference M S I₁ phi dphi
    hphi hd L hK (eta0Bin M L) he0 M.rangeProp _ hscore
  have hpi (n : ℕ) (a : A) (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (rearrangeP1 L (oracle n a)).piLev i x :=
    Eventually.of_forall
      ((rearrangeP1_clipped_denominator_lower_bounds L hK (oracle n a) cpi
        (hc n a).2.2 (hc n a).2.1).1 i)
  have htau (n : ℕ) (a : A) (t : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (rearrangeP1 L (oracle n a)).tauLev t x :=
    Eventually.of_forall
      ((rearrangeP1_clipped_denominator_lower_bounds L hK (oracle n a) cpi
        (hc n a).2.2 (hc n a).2.1).2 t)
  obtain ⟨hp, hl, hP, hpi', ht, hs, hf, hg, htail⟩ :=
    binary_component_rates_rearranged_oracle_rates M μ L oracle (eta0Bin M L)
      ha he0 hmono hrate
  obtain ⟨ch0, hch0⟩ := hr.2.2.2
  have ho := nuisanceRates_training_population_binary_clt M μ S I₁ I₂
    hSplit phi dphi hphi hd hDerivative hStruct hEndpoints hFinite hy L hK hlev hOrder
    cpi hov hbase he0 (fun n a => rearrangeP1 L (oracle n a)) hsorted
    hOff gap hGap ch0 hch0 (cpi / 2) (by linarith [hbase.1]) hpi htau
    hp hl hP hpi' hs ht hg hf htail hdiff
  dsimp only at ho ⊢
  apply bigOp_transfer_on_recovery μ G _ _ _ hG
  · intro n a ha
    rw [dmlRV_eq_of_score_eq_on_sample M S I₂ _
      (fun n a o => psiBin M phi dphi L hK o (rearrangeP1 L (oracle n a)))
      (2 * (n + 1)) a (fun i hi => heq n a ha (S.Z i a))]
  · exact dml_rootn_consistent_of_normal_limit μ _ _ _ ho

-- @node: binDMLRegime_lower_bound_rootn_on_recovery_of_scoreLabels_eq
/-- Suppose [the sample is split into equal halves](hyp:hSplit), [the policy
is valid](hyp:hphi) with [the specified derivative](hyp:hd) that is [bounded and
Lipschitz](hyp:hDerivative), [the structural assumptions hold](hyp:hStruct),
[outcome endpoints are known](hyp:hend), [propensities satisfy gap separation](hyp:hGap),
and [the instrument admits finite reduction](hyp:hFinite). If the canonical
levels at the reference covariate have [positive count](hyp:hK), [invariant
order](hyp:hOrder), [baseline overlap](hyp:hov), and [policy overlap](hyp:hpol),
[the fitted binary nuisance records on the recovered level structures](hyp:eHat)
[satisfy the finite binary DML regime](hyp:hr), [policy
levels avoid the boundary](hyp:hOff), [the specified gap witnesses propensity
separation](hyp:hgap), [recovery events have probability tending to one](hyp:hG),
and [score labels agree with the canonical labels on these events at even
sample sizes](hyp:hLabels), [the feasible estimate of the identified lower bound
has error of order the inverse square root of total sample size in probability
along even sample sizes](goal). -/
lemma binDMLRegime_lower_bound_rootn_on_recovery_of_scoreLabels_eq
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (x0 : X) (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (pHat : ℕ → A → Z → X → ℝ) (rho : ℕ → ℝ) (gap ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat)
    (hOff : PolicyLevelOffBoundary (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (G : ℕ → Set A) (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (hLabels : ∀ n a, a ∈ G n → scoreRecoveryLabels (recoveredData M S I₁ I₂ pHat phi rho gap
      (2 * (n + 1)) a) = scoreRecoveryLabels (LevelStructure M.prop (policyProp phi M.prop) x0)) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  have hlev := population_LevelStructure_baseline_measurable M hStruct.2.2.2.1
    (policyProp phi M.prop) x0 hOrder
  have htarget := (discrete_reduction M hStruct.2.2.2.2.2.2 hend hStruct.1
    hStruct.2.1 hStruct.2.2.1 hStruct.2.2.2.1 hStruct.2.2.2.2.1
    hStruct.2.2.2.2.2.1 phi hphi x0 hGap hOrder hFinite).2.2.1
  dsimp only
  rw [htarget]
  exact binDMLRegime_population_rootn_on_recovery M μ S I₁ I₂ hSplit
    phi dphi hphi hd hDerivative hStruct hend hFinite hr.2.2.1 _ hK hlev hOrder
    cpi hpol hov pHat rho gap ch eHat hr G hG hLabels hOff hgap

-- @node: binDMLRegime_rootn_consistent
/-- Suppose [the sample is split into equal halves](hyp:hSplit), [the policy
is valid](hyp:hphi) with [the specified derivative](hyp:hd) that is [bounded and
Lipschitz](hyp:hDerivative), [the structural assumptions hold](hyp:hStruct),
[outcome endpoints are known](hyp:hend), [propensities satisfy gap separation](hyp:hGap),
and [the instrument admits finite reduction](hyp:hFinite). If the canonical
levels at the reference covariate have [positive count](hyp:hK), [invariant
order](hyp:hOrder), [baseline overlap](hyp:hov), and [policy overlap](hyp:hpol),
[the propensity estimator satisfies the finite first-stage rate condition](hyp:hRate),
[policy levels avoid the boundary](hyp:hOff), [the specified gap witnesses
propensity separation](hyp:hgap), and [the fitted binary nuisance records on the
recovered level structures](hyp:eHat) [satisfy the finite binary DML regime](hyp:hr),
[the feasible estimate of the identified lower bound
has error of order the inverse square root of total sample size in probability
along even sample sizes](goal). -/
lemma binDMLRegime_rootn_consistent
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (x0 : X) (hGap : PropensityGapSeparation M.prop (policyProp phi M.prop))
    (hFinite : InstrumentFiniteReduction Z)
    (hK : LevelCountPos (LevelStructure M.prop (policyProp phi M.prop) x0).K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop)
      (LevelStructure M.prop (policyProp phi M.prop) x0))
    (cpi : ℝ)
    (hov : BaselineOverlapWitness M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (hpol : PolicyOverlap M (LevelStructure M.prop (policyProp phi M.prop) x0) cpi)
    (pHat : ℕ → A → Z → X → ℝ) (hRate : FiniteFirstStageRate M μ pHat)
    (rho : ℕ → ℝ) (gap ch : ℝ)
    (hOff : PolicyLevelOffBoundary (LevelStructure M.prop (policyProp phi M.prop) x0))
    (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat) :
    let L := LevelStructure M.prop (policyProp phi M.prop) x0
    let score := fittedBinScore M S I₁ I₂ pHat phi dphi rho gap eHat
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))
    Causalean.Stat.IsBigOp
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      (fun n => (((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) μ := by
  have hG := binDMLRegime_recoveryEvent_compl_tendsto_zero M μ S I₁ I₂ hStruct.2.2.2.1
    pHat hRate phi dphi hphi hd hDerivative x0 gap cpi rho hOrder hOff hgap hK ch eHat hr
  exact binDMLRegime_lower_bound_rootn_on_recovery_of_scoreLabels_eq
    M μ S I₁ I₂ hSplit phi dphi hphi hd hDerivative hStruct hend x0 hGap hFinite hK
    hOrder cpi hov hpol pHat rho gap ch eHat hr hOff hgap
    (fun n => recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1))) hG
    (fun n a ha => (mem_recoveryEvent_iff_scoreRecoveryLabels_eq
      M S I₁ I₂ pHat phi rho gap _ _ a).mp ha)

end Papers.TbsPrteOptimalTransport
