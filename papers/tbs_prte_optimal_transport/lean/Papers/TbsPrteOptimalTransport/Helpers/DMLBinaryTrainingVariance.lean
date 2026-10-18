module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTrainingFactorization
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryVarianceConsistency
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTargetConclusions
/-! Almost-everywhere score bounds on independent held-out observations.
Population bounds may have a different null set for each training value.
Product integration and the independent joint law transfer them to evaluation
rows without imposing pointwise bounds outside the observation support. -/
public section

set_option linter.style.longLine false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

-- @node: independent_training_factor_memLp_of_ae_section_bound
/-- If [the training view is measurable](hyp:hv), [the evaluation observation is
measurable](hyp:hr), [they are independent](hyp:hind), and [the observation has the
population law](hyp:hlaw), then any [measurable function of the two](hyp:hf)
that [is bounded in absolute value by a common constant for almost every population
observation, at every realized training view](hyp:hb) [has a finite second moment
when evaluated on the training view and evaluation observation](goal). -/
lemma independent_training_factor_memLp_of_ae_section_bound
    {A T B : Type*} [MeasurableSpace A] [MeasurableSpace T] [MeasurableSpace B]
    (μ : Measure A) (P : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (view : A → T) (row : A → B) (hv : Measurable view) (hr : Measurable row)
    (hind : IndepFun view row μ) (hlaw : μ.map row = P)
    (f : T × B → ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀ a, ∀ᵐ b ∂P, |f (view a, b)| ≤ C) :
    MemLp (fun a => f (view a, row a)) 2 μ := by
  have hm : Measurable (fun ab : A × B => f (view ab.1, ab.2)) := by fun_prop
  have hprod : ∀ᵐ ab ∂μ.prod P, |f (view ab.1, ab.2)| ≤ C :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.abs measurable_const)).2
      (Eventually.of_forall hb)
  have hLp : MemLp (fun ab : A × B => f (view ab.1, ab.2)) 2 (μ.prod P) :=
    MemLp.of_bound hm.aestronglyMeasurable C
      (hprod.mono fun _ h => by simpa only [Real.norm_eq_abs] using h)
  have hmap : (μ.prod P).map (Prod.map view id) = (μ.map view).prod P := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map μ P hv measurable_id).symm
  have hfactor : MemLp f 2 ((μ.map view).prod P) := by
    rw [← hmap]
    exact (memLp_map_measure_iff hf.aestronglyMeasurable
      (hv.prodMap measurable_id).aemeasurable).2 hLp
  have hjoint : μ.map (fun a => (view a, row a)) = (μ.map view).prod P := by
    rw [hind.map_prod_eq_prod_map_map hv.aemeasurable hr.aemeasurable, hlaw]
  have hfit : MemLp f 2 (μ.map (fun a => (view a, row a))) := by
    rw [hjoint]
    exact hfactor
  exact hfit.comp_of_map (hv.prodMk hr).aemeasurable

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_ae_bounded_training_score_factorization
/-- Under [an equal training and evaluation split](hyp:hSplit), if [the score is
measurable using only training data and its observation argument](hyp:hm) and
[has a common absolute bound almost everywhere under the observation law for every
sample size and training realization](hyp:hb), [the score admits a measurable
factorization through the training view whose evaluations on every held-out row
have finite second moments](goal). -/
lemma equalHalfSplit_ae_bounded_training_score_factorization
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
      (∀ n i, MemLp (fun a => f n
        (trainingView M S I₁ (2 * (n + 1)) a,
          S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) := by
  have hex (n : ℕ) := measurable_training_predictor_factorization
    (trainingView M S I₁ (2 * (n + 1))) (score (2 * (n + 1)))
    (hm (2 * (n + 1)))
  choose g hg heq using hex
  refine ⟨fun n => Function.uncurry (g n), heq, hg, ?_⟩
  intro n i
  have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n
  let : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  apply independent_training_factor_memLp_of_ae_section_bound μ (observationLaw M)
    _ _ hl.2.1 (hl.2.2.1 i) (hl.2.2.2.1 i).1 (hl.2.2.2.1 i).2 _ (hg n) C
  intro a
  simpa only [Function.uncurry_apply_pair, ← heq] using hb (2 * (n + 1)) a

-- @node: equalHalfSplit_ae_bounded_training_oracle_mean_variance_consistent
/-- Under [an equal training and evaluation split](hyp:hSplit), suppose [the
population score has mean equal to the target](hyp:hmean) and [a finite second
moment](hyp:htruth), while [the fitted score error is measurable from training data
and the observation](hyp:hm), [is uniformly bounded almost everywhere for each
training realization](hyp:hb), and [has population mean squared error tending to
zero in probability along even sample sizes](hyp:hrate). Then [the held-out score
mean converges in probability to the target and its empirical variance converges
in probability to the population score variance](goal). -/
lemma equalHalfSplit_ae_bounded_training_oracle_mean_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (htruth : MemLp truth 2 (observationLaw M))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (C : ℝ) (hb : ∀ n a, ∀ᵐ o ∂observationLaw M, |score n a o - truth o| ≤ C)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  let : IsProbabilityMeasure (observationLaw M) := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  obtain ⟨f, heq, hf, hfit⟩ :=
    equalHalfSplit_ae_bounded_training_score_factorization M μ S I₁ I₂ hSplit
      (fun n a o => score n a o - truth o) hm C hb
  have hr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [← heq] using hrate
  have hE := equalHalfSplit_empirical_fitted_score_energy M μ S I₁ I₂
    hSplit f hf hfit hr
  simp only [← heq] at hE
  exact ⟨equalHalfSplit_dmlRV_consistent_of_empirical_score_error M μ S I₁ I₂
      hSplit score truth (htruth.integrable (by norm_num)) theta hmean hE,
    equalHalfSplit_varianceRV_consistent_of_empirical_score_error_memLp M μ S I₁ I₂
      hSplit score truth htruth theta hmean hE⟩

-- @node: equalHalfSplit_ae_bounded_training_feasible_mean_variance_consistent
/-- For [an equal training and evaluation split](hyp:hSplit), assume [the
population score has the target mean](hyp:hmean) and [a finite second
moment](hyp:htruth), and [the oracle score error is measurable from training data
and the observation](hyp:hm), [uniformly bounded almost everywhere for each
training realization](hyp:hb), and [vanishing in population mean square in
probability along even sample sizes](hyp:hrate). If [recovery events have
probability tending to one](hyp:hG) and [the feasible and oracle scores agree on
every evaluation row on those events](hyp:heq), [the feasible score mean and
empirical variance converge in probability to the target and the population score
variance, respectively](goal). -/
lemma equalHalfSplit_ae_bounded_training_feasible_mean_variance_consistent
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → A → Obs X Z → ℝ) (truth : Obs X Z → ℝ)
    (theta : ℝ) (hmean : ∫ o, truth o ∂observationLaw M = theta)
    (htruth : MemLp truth 2 (observationLaw M))
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o => score n a o - truth o))
    (C : ℝ) (hb : ∀ n a, ∀ᵐ o ∂observationLaw M, |score n a o - truth o| ≤ C)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (score (2 * (n + 1)) a o - truth o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0))
    (feasible : ℕ → A → Obs X Z → ℝ) (G : ℕ → Set A)
    (hG : Tendsto (fun n => μ (G n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n a, a ∈ G n → ∀ i ∈ I₂ (2 * (n + 1)) a,
      feasible (2 * (n + 1)) a (S.Z i a) = score (2 * (n + 1)) a (S.Z i a)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ feasible (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ feasible (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
  have ho := equalHalfSplit_ae_bounded_training_oracle_mean_variance_consistent
    M μ S I₁ I₂ hSplit score truth theta hmean htruth hm C hb hrate
  exact dml_mean_variance_transfer_on_recovery M S I₂ feasible score
    (fun n => 2 * (n + 1)) G theta (populationVariance M truth theta)
    hG heq ho.1 ho.2

section Binary
variable [Fintype Z] [DecidableEq Z] (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_training_binary_oracle_mean_variance_consistent
/-- With [equal training and evaluation halves](hyp:hSplit), assume [a valid
policy map](hyp:hphi), [its specified derivative](hyp:hd), [a bounded Lipschitz
policy derivative](hyp:hDerivative), [the structural model assumptions](hyp:hStruct),
[known outcome endpoints](hyp:hEndpoints), [a finite instrument reduction](hyp:hFinite),
and [binary outcomes almost surely](hyp:hy). With [a positive number of propensity
levels](hyp:hK), [measurable level propensities](hyp:hlev), [policy-invariant level
ordering](hyp:hOrder), [policy overlap](hyp:hov), [baseline overlap](hyp:hbase),
[admissible population nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh),
[a positive denominator bound](hyp:hc), [a positive separation margin](hyp:hsep),
[fitted assignment probabilities bounded below almost everywhere](hyp:hpi),
[fitted regular-cell probabilities bounded below almost everywhere](hyp:htau),
[quarter-rate control of instrument propensities](hyp:hrp),
[quarter-rate control of level propensities](hyp:hrlev),
[quarter-rate control of success regressions](hyp:hrP),
[quarter-rate control of assignment probabilities](hyp:hrpi),
[quarter-rate control of instrument shares in every regular cell](hyp:hrs),
[quarter-rate control of regular-cell probabilities](hyp:hrt),
[quarter-rate control of regular weights](hyp:hrg),
[quarter-rate control of full-cell weights](hyp:hrfull),
[quarter-rate control of the tail weight](hyp:hrtail), and
[population pooled thresholds separated from each other and the boundary](hyp:hgap),
suppose also [the fitted binary score error is measurable from training data and
the observation](hyp:hm). Then [the held-out binary score mean converges in
probability to the discrete target and its empirical variance converges to the
population binary score variance](goal). -/
lemma nuisanceRates_training_binary_oracle_mean_variance_consistent
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
    (c sep : ℝ) (hc : 0 < c) (hsep : 0 < sep)
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
    (hgap : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|)
    (hm : TrainingPredictorMeasurable M S I₁ (fun n a o =>
      psiBin M phi dphi L hK o (eh n a) -
        psiBin M phi dphi L hK o (eta0Bin M L))) :
    let score := fun n a o => psiBin M phi dphi L hK o (eh n a)
    let truth := fun o => psiBin M phi dphi L hK o (eta0Bin M L)
    let theta := discreteTarget M false L (policyProp phi M.prop)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M truth theta) := by
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
  obtain ⟨f, hscore, hf, hfit⟩ :=
    equalHalfSplit_ae_bounded_training_score_factorization M μ S I₁ I₂ hSplit
      (fun n a o => psiBin M phi dphi L hK o (eh n a) -
        psiBin M phi dphi L hK o (eta0Bin M L)) hm (C + C) hbound
  exact nuisanceRates_binary_oracle_mean_variance_consistent M μ S I₁ I₂ hSplit
    phi dphi hphi hd ⟨B, D, hB, hD, hder⟩ hStruct hEndpoints hFinite hy L hK
    hlev hOrder cpi hov hbase he0 eh heh c sep hc hsep hpi htau hrp hrlev hrP
    hrpi hrs hrt hrg hrfull hrtail hgap f hscore hf hfit

end Binary

end Papers.TbsPrteOptimalTransport
