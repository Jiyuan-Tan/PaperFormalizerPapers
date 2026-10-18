module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryZeroPolicyBins
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryTailPolicyIndexing
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryAdmissibility
/-! Exact recovery of every population label on the simultaneous marginal good event.
The zero, interior, and terminal bins are assembled before passing to probability
limits, so the event is the population recovery event used by the DML procedure. -/
public section
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z) (h : ThresholdCrossing M)
  (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
  (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
  (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
  (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
  (pb qb : Z → ℝ) (rho : ℝ)
  (hactive : ∀ z, rho < pb z ↔ z ∉ L.S 0)
  (hp : ∀ z, |pb z - ∫ x, M.prop z x ∂xLaw M| < gap / 4)
  (hqr : ∀ z, |qb z - ∫ x, q z x ∂xLaw M| < gap / 4)

include M h q hq L hL hOff hlev hgap hactive hp hqr

-- @node: recoverLevelsAt_population_policy_counts_eq
/-- Suppose the model satisfies threshold crossing, policy propensities
are jointly measurable, the population level structure is invariant
across covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, distinct
propensity values have a positive uniform separation gap, active
baseline vertices are exactly those outside the zero class,
baseline marginal errors are below a quarter-gap, and policy marginal
errors are below a quarter-gap. If [there is at least one positive
baseline level](hyp:hK), [baseline estimates lie in the closed unit interval](hyp:hpb),
[policy estimates lie in that interval](hyp:hqb), and [k is at most the final bin
index](hyp:hk), then [the recovered number of policy classes in bin k equals
the population number](goal). -/
lemma recoverLevelsAt_population_policy_counts_eq
    (hK : 0 < L.K) (hpb : ∀ z, pb z ∈ Icc (0 : ℝ) 1)
    (hqb : ∀ z, qb z ∈ Icc (0 : ℝ) 1) (k : ℕ) (hk : k ≤ L.K) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).l k = L.l k := by
  by_cases hz : k = 0
  · subst k
    exact recoverLevelsAt_zero_policy_count_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr hK
      (fun z => (hpb z).1) (fun z => (hqb z).1)
  by_cases ht : k = L.K
  · subst k
    exact recoverLevelsAt_tail_policy_count_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr hK
      (fun z => (hpb z).2) (fun z => (hqb z).2)
  · exact recoverLevelsAt_lower_policy_count_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr k ⟨by omega, by omega⟩

-- @node: recoverLevelsAt_population_policy_labels_eq
/-- Under threshold crossing, joint measurability of policy
propensities, an invariant population level structure, policy
classes off their lower boundaries before the final bin, measurable
baseline levels, positive uniform propensity separation,
correct activity classification outside the zero baseline class,
baseline marginal errors below a quarter-gap, and policy marginal
errors below a quarter-gap, suppose [there is a positive baseline
level](hyp:hK), [baseline estimates lie in the unit interval](hyp:hpb), and
[policy estimates lie in the unit interval](hyp:hqb). For [a bin index k no
larger than the final index](hyp:hk) and [a policy index j between zero and the
population count in bin k](hyp:hj), [the recovered policy label equals its
population label](goal). -/
lemma recoverLevelsAt_population_policy_labels_eq
    (hK : 0 < L.K) (hpb : ∀ z, pb z ∈ Icc (0 : ℝ) 1)
    (hqb : ∀ z, qb z ∈ Icc (0 : ℝ) 1)
    (k j : ℕ) (hk : k ≤ L.K) (hj : j ≤ L.l k) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).T k j = L.T k j := by
  by_cases hj0 : j = 0
  · subst j
    rw [(hL.2.2.1 k hk).1]
    simp only [recoverLevelsAt, true_or, if_true]
  have hj' : 1 ≤ j ∧ j ≤ L.l k := ⟨by omega, hj⟩
  by_cases hz : k = 0
  · subst k
    exact recoverLevelsAt_zero_policy_label_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr hK
      (fun z => (hpb z).1) (fun z => (hqb z).1) j hj'
  by_cases ht : k = L.K
  · subst k
    exact recoverLevelsAt_tail_policy_label_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr hK
      (fun z => (hpb z).2) (fun z => (hqb z).2) j hj'
  · exact recoverLevelsAt_lower_policy_label_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr k j ⟨by omega, by omega⟩ hj'

-- @node: recoverLevelsAt_population_labels_eq
/-- Suppose threshold crossing holds, policy propensities are jointly
measurable, population levels and classes are invariant across
covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, there is a
positive uniform propensity gap, the activity rule correctly excludes
exactly the zero baseline class, baseline marginal errors are below
a quarter-gap, and policy marginal errors are below a quarter-gap.
If [there is a positive baseline level](hyp:hK), [baseline estimates lie in the
unit interval](hyp:hpb), and [policy estimates lie in the unit interval](hyp:hqb),
then [recovery exactly matches the population baseline count and, in every bin
including the zero and final bins, the policy count, baseline label, and all
policy labels indexed from zero through the population count](goal). -/
lemma recoverLevelsAt_population_labels_eq
    (hK : 0 < L.K) (hpb : ∀ z, pb z ∈ Icc (0 : ℝ) 1)
    (hqb : ∀ z, qb z ∈ Icc (0 : ℝ) 1) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).K = L.K ∧
    ∀ k ≤ L.K,
      (recoverLevelsAt pb qb rho gap : LevelData Z X).l k = L.l k ∧
      (recoverLevelsAt pb qb rho gap : LevelData Z X).S k = L.S k ∧
      ∀ j ≤ L.l k,
        (recoverLevelsAt pb qb rho gap : LevelData Z X).T k j = L.T k j := by
  have hb := recoverLevelsAt_baseline_labels_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr
  refine ⟨hb.1, ?_⟩
  intro k hk
  exact ⟨recoverLevelsAt_population_policy_counts_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr hK hpb hqb k hk, hb.2 k hk,
    fun j hj => recoverLevelsAt_population_policy_labels_eq M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr hK hpb hqb k j hk hj⟩

omit hactive hp hqr in
-- @node: recovery_population_labels_failure_tendsto_zero
/-- Suppose the model satisfies threshold crossing, policy propensities
are jointly measurable, population levels and classes are invariant
across covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, and distinct
propensity values have a positive uniform gap. If [the activity
threshold tends to zero](hyp:hrho), [there is a positive baseline level](hyp:hK),
[all baseline estimates lie in the unit interval](hyp:hpb), [all policy estimates
lie in the unit interval](hyp:hqb), [baseline marginal estimates converge in
probability to their population means](hyp:hpconv), [policy marginal estimates
converge in probability to their population means](hyp:hqconv), and [threshold
exceedance at each zero baseline marginal has measure tending to zero](hyp:hzero),
then [the measure of failure to recover the population baseline count, all bin
counts, all baseline labels, and every policy label on its population index
range tends to zero](goal). -/
lemma recovery_population_labels_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0)) (hK : 0 < L.K)
    (hpb : ∀ n a z, pb n a z ∈ Icc (0 : ℝ) 1)
    (hqb : ∀ n a z, qb n a z ∈ Icc (0 : ℝ) 1)
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (
      (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).K = L.K ∧
      ∀ k ≤ L.K,
        (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).l k = L.l k ∧
        (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).S k = L.S k ∧
        ∀ j ≤ L.l k,
          (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).T k j = L.T k j)})
      atTop (𝓝 0) := by
  have hz := recovery_zero_class_failure_tendsto_zero μ pb
    (fun z => ∫ x, M.prop z x ∂xLaw M)
    (fun z => integral_nonneg (fun x => (M.rangeProp z x).1))
    rho hrho hpconv hzero
  have hconv : ∀ v : RecoveryVertex Z,
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n a => vertexValue (pb n a) (qb n a) v) atTop
        (fun _ _ => vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
          (fun z => ∫ x, q z x ∂xLaw M) v) := by
    rintro ⟨b, z⟩
    cases b
    · exact hpconv z
    · exact hqconv z
  have herr := finite_marginal_errors_tendsto_zero μ
    (fun n a => vertexValue (pb n a) (qb n a))
    (vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
      (fun z => ∫ x, q z x ∂xLaw M)) hconv (gap / 4) (by linarith [hgap.1])
  have hs := hz.add herr
  simp only [add_zero] at hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ => zero_le)
  intro n
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro a hbad
  by_contra hn
  have hg :
      Finset.univ.filter (fun z => pb n a z ≤ rho n) =
        Finset.univ.filter (fun z => (∫ x, M.prop z x ∂xLaw M) = 0) ∧
      ¬ ∃ v, gap / 4 ≤ |vertexValue (pb n a) (qb n a) v -
        vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
          (fun z => ∫ x, q z x ∂xLaw M) v| := by
    simpa only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] using hn
  have ha (z : Z) : rho n < pb n a z ↔ z ∉ L.S 0 := by
    have he := Finset.ext_iff.mp hg.1 z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [population_baseline_marginal_zero_iff M h q L hL z] at he
    exact (not_le).symm.trans (not_congr he)
  have he (v : RecoveryVertex Z) :
      |vertexValue (pb n a) (qb n a) v -
        vertexValue (fun z => ∫ x, M.prop z x ∂xLaw M)
          (fun z => ∫ x, q z x ∂xLaw M) v| < gap / 4 :=
    lt_of_not_ge (fun hh => hg.2 ⟨v, hh⟩)
  exact hbad (recoverLevelsAt_population_labels_eq M h q hq L hL hOff hlev
    gap hgap (pb n a) (qb n a) (rho n) ha
    (fun z => he (false, z)) (fun z => he (true, z)) hK (hpb n a) (hqb n a))

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_recoveryEvent_compl_tendsto_zero
/-- Suppose threshold crossing holds, policy classes before the final
bin avoid their lower boundaries, population baseline levels are
measurable, [the sample split has equal halves](hyp:hSplit), [the
propensity predictor is measurable with respect to the training sample](hyp:hTrain),
[the predictor takes values in the unit interval](hyp:hrange), and [its maximum
instrument-specific population error is little-o in probability of sample size
to the power minus one-quarter](hyp:hRate). If [the policy map is measurable and
preserves the unit interval](hyp:hphi), [has the specified propensity
derivative](hyp:hd), [that derivative is uniformly bounded and Lipschitz](hyp:hDerivative),
[the baseline and transformed policy propensities have the invariant population
level structure](hyp:hLphi), [they have a positive uniform separation gap](hyp:hgapPhi),
[there is a positive baseline level](hyp:hK), [the activity threshold tends to
zero](hyp:hrho), and [sample size to the one-quarter power times the threshold
tends to infinity](hyp:hgrowth), then [the probability of failure of the exact
population recovery event tends to zero along even sample sizes](goal). -/
lemma firstStageRate_recoveryEvent_compl_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (hLphi : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hgapPhi : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (hK : 0 < L.K)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop (𝓝 0))
    (hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n) atTop atTop) :
    Tendsto (fun n => μ (recoveryEvent M S I₁ I₂ pHat phi rho gap L (2 * (n + 1)))ᶜ)
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  change Tendsto (fun n => μ {a | ¬ (_ ∧ _)}) atTop (𝓝 0)
  apply recovery_population_labels_failure_tendsto_zero M h
    (policyProp phi M.prop) hqphi L hLphi hOff hlev gap hgapPhi μ
    (fun n a => pBar M S I₂ pHat (2 * (n + 1)) a)
    (fun n a => pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
    (fun n => rho (2 * (n + 1))) (hrho.comp hindex) hK
    (fun n a z => ⟨pBar_nonneg M μ S I₂ pHat
      (fun n a z x => (hrange n a z x).1) _ a z,
      pBar_le_one M μ S I₂ pHat (fun n a z x => (hrange n a z x).2) _ a z⟩)
    (fun n a z => ⟨pBar_nonneg M μ S I₂
      (fun n a => policyProp phi (pHat n a))
      (fun n a z x => (hphi.2 z x _ (hrange n a z x)).1) _ a z,
      pBar_le_one M μ S I₂ (fun n a => policyProp phi (pHat n a))
      (fun n a z x => (hphi.2 z x _ (hrange n a z x)).2) _ a z⟩)
    hconv.1 hconv.2
  intro z hz
  have he := firstStageRate_pBar_baseline_quarter_rate M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate z
  simp only [hz, sub_zero] at he
  exact littleOp_threshold_exceedance_tendsto_zero μ _ _ _ he
    (recovery_threshold_dominates_quarter_rate rho hgrowth)

end Papers.TbsPrteOptimalTransport

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)
  {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
  (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
  (h : ThresholdCrossing M) (pHat : ℕ → A → Z → X → ℝ)
  (hRate : FiniteFirstStageRate M μ pHat)
  (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
  (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
  (x0 : X) (gap cpi : ℝ) (rho : ℕ → ℝ)
  (hL : LevelOrderInvariant M.prop (policyProp phi M.prop)
    (LevelStructure M.prop (policyProp phi M.prop) x0))
  (hOff : PolicyLevelOffBoundary (LevelStructure M.prop (policyProp phi M.prop) x0))
  (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
  (hK : LevelCountPos' (LevelStructure M.prop (policyProp phi M.prop) x0).K)

include h hRate hphi hd hDerivative hL hOff hgap hK

-- @node: contDMLRegime_recoveryEvent_compl_tendsto_zero
/-- Suppose threshold crossing holds, the first-stage population error
is little-o in probability of sample size to the power minus one-quarter,
the policy map is measurable and preserves the unit interval, has
the specified propensity derivative, that derivative is uniformly
bounded and Lipschitz, the population level structure selected
at the reference covariates is invariant across covariates, its policy
classes before the final bin avoid their lower boundaries, baseline
and policy propensities have a positive uniform separation gap, and
there is at least one positive baseline level. For [continuous-outcome
nuisance estimates based on the recovered data](hyp:eHat), [the finite continuous
DML regime](hyp:hr) implies [that the probability of failure of exact population
recovery tends to zero along even sample sizes](goal). -/
lemma contDMLRegime_recoveryEvent_compl_tendsto_zero
    (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat) :
    Tendsto (fun n => μ (recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1)))ᶜ)
      atTop (𝓝 0) := by
  have hlev : ∀ k, Measurable
      ((LevelStructure M.prop (policyProp phi M.prop) x0).pLev k) := by
    intro k
    first | fun_prop | exact population_LevelStructure_baseline_measurable M h _ x0 hL k
  exact firstStageRate_recoveryEvent_compl_tendsto_zero M h
    (LevelStructure M.prop (policyProp phi M.prop) x0) hOff hlev gap μ S I₁ I₂
    hr.1.1 pHat hr.1.2.2.1.1 hr.1.2.2.1.2.1 hRate phi dphi hphi hd hDerivative
    hL hgap (by change 1 ≤ _ at hK; omega) rho
    hr.1.2.1.2.2.1 hr.1.2.1.2.2.2

-- @node: binDMLRegime_recoveryEvent_compl_tendsto_zero
/-- Suppose threshold crossing holds, the first-stage population error
is little-o in probability of sample size to the power minus one-quarter,
the policy map is measurable and preserves the unit interval, has
the specified propensity derivative, that derivative is uniformly
bounded and Lipschitz, the population level structure selected
at the reference covariates is invariant across covariates, its policy
classes before the final bin avoid their lower boundaries, baseline
and policy propensities have a positive uniform separation gap, and
there is at least one positive baseline level. For [binary-outcome
nuisance estimates based on the recovered data](hyp:eHat), [the finite binary
DML regime](hyp:hr) implies [that the probability of failure of exact population
recovery tends to zero along even sample sizes](goal). -/
lemma binDMLRegime_recoveryEvent_compl_tendsto_zero
    (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (hr : FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi
      (LevelStructure M.prop (policyProp phi M.prop) x0) ch eHat) :
    Tendsto (fun n => μ (recoveryEvent M S I₁ I₂ pHat phi rho gap
      (LevelStructure M.prop (policyProp phi M.prop) x0) (2 * (n + 1)))ᶜ)
      atTop (𝓝 0) := by
  have hlev : ∀ k, Measurable
      ((LevelStructure M.prop (policyProp phi M.prop) x0).pLev k) := by
    intro k
    first | fun_prop | exact population_LevelStructure_baseline_measurable M h _ x0 hL k
  exact firstStageRate_recoveryEvent_compl_tendsto_zero M h
    (LevelStructure M.prop (policyProp phi M.prop) x0) hOff hlev gap μ S I₁ I₂
    hr.1.1 pHat hr.1.2.2.1 hr.1.2.2.2.1 hRate phi dphi hphi hd hDerivative
    hL hgap (by change 1 ≤ _ at hK; omega) rho
    hr.1.2.1.2.2.1 hr.1.2.1.2.2.2

end Papers.TbsPrteOptimalTransport
