module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryInteriorPolicyBins
/-! No omission of population policy classes in interior recovered bins.
Numerical bin identification includes the strictly ordered population component
list. Each included component projects to a complete recovered policy label. -/
public section
set_option linter.style.openClassical false

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

-- @node: recoveryComponents_interior_policy_representatives_subset_numeric_bin
/-- Suppose threshold crossing holds, policy propensities are jointly
measurable, population levels and classes are invariant across
covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, there is a
positive uniform propensity gap, active baseline vertices are exactly
those outside the zero class, baseline marginal errors are below
a quarter-gap, and policy marginal errors are below a quarter-gap.
For [a positive bin k before the final bin](hyp:hk), if [one representative is
chosen from each population policy class in k](hyp:hrep), then [at any covariates
every component in the representative list belongs to the recovered component
list filtered for policy vertices and the numerical bounds of bin k](goal). -/
lemma recoveryComponents_interior_policy_representatives_subset_numeric_bin
    (k : ℕ) (hk : 1 ≤ k ∧ k < L.K) (x : X) (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l k) → rep j ∈ L.T k j) :
    ((List.range (L.l k)).map (fun j =>
      recoveryComponent pb qb rho gap (true, rep (j + 1)))) ⊆
      (recoveryComponents pb qb rho gap).filter (fun C =>
        (∃ z, (true, z) ∈ C) ∧
        (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev k x ≤
          componentAverage pb qb C ∧
        (if k = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
          componentAverage pb qb C ≤ 1 else
          componentAverage pb qb C <
            (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev (k + 1) x)) := by
  intro C hC
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hC
  have hj' : 1 ≤ j + 1 ∧ j + 1 ≤ L.l k := by
    have := List.mem_range.mp hj
    omega
  exact (recoveryComponents_interior_policy_numeric_filter_mem_iff M h q hq L hL
    hOff hlev gap hgap pb qb rho hactive hp hqr k k (j + 1) hk hk.2 hj'
    _ (hrep _ hj') x).mpr rfl

-- @node: recoverLevelsAt_interior_policy_count_ge
/-- Under threshold crossing, joint measurability of policy
propensities, an invariant population level structure, policy
classes off their lower boundaries before the final bin, measurable
baseline levels, positive uniform propensity separation,
correct activity classification outside the zero baseline class,
baseline marginal errors below a quarter-gap, and policy marginal
errors below a quarter-gap, [in every positive bin k before the final
bin](hyp:hk), [the recovered policy count is at least the population policy
count](goal). -/
lemma recoverLevelsAt_interior_policy_count_ge
    (k : ℕ) (hk : 1 ≤ k ∧ k < L.K) :
    L.l k ≤ (recoverLevelsAt pb qb rho gap : LevelData Z X).l k := by
  let rep : ℕ → Z := fun j => if hj : 1 ≤ j ∧ j ≤ L.l k then
    Classical.choose (ordered_policy_level_nonempty M q L hL k j hk.2.le hj.1 hj.2)
    else Classical.choice inferInstance
  have hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l k) → rep j ∈ L.T k j := by
    intro j hj
    simpa only [rep, dif_pos hj] using
      Classical.choose_spec (ordered_policy_level_nonempty M q L hL k j hk.2.le hj.1 hj.2)
  have hn := recovery_interior_policy_representative_list_nodup M q hq L hL hOff
    hlev gap hgap pb qb rho hactive hp hqr k hk.2 rep hrep
  have hs := recoveryComponents_interior_policy_representatives_subset_numeric_bin
    M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr k hk
    (Classical.choice inferInstance) rep hrep
  have hc := (List.subperm_of_subset hn hs).length_le
  simpa only [recoverLevelsAt, List.length_map, List.length_range] using hc

-- @node: recoverLevelsAt_interior_policy_label_exists
/-- Suppose threshold crossing holds, policy propensities are jointly
measurable, population levels and classes are invariant across
covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, there is a
positive uniform propensity gap, active baseline vertices are exactly
those outside the zero class, baseline marginal errors are below
a quarter-gap, and policy marginal errors are below a quarter-gap.
For [a positive bin k before the final bin](hyp:hk) and [a valid positive
population policy index j in that bin](hyp:hj), [some positive index within the
recovered policy count has a recovered label equal to population class j](goal). -/
lemma recoverLevelsAt_interior_policy_label_exists
    (k j : ℕ) (hk : 1 ≤ k ∧ k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ∃ i, (1 ≤ i ∧ i ≤ (recoverLevelsAt pb qb rho gap : LevelData Z X).l k) ∧
      (recoverLevelsAt pb qb rho gap : LevelData Z X).T k i = L.T k j := by
  obtain ⟨z, hz⟩ := ordered_policy_level_nonempty M q L hL k j hk.2.le hj.1 hj.2
  let R : LevelData Z X := recoverLevelsAt pb qb rho gap
  let x : X := Classical.choice inferInstance
  let Qs := (recoveryComponents pb qb rho gap).filter (fun C =>
    (∃ w, (true, w) ∈ C) ∧ R.pLev k x ≤ componentAverage pb qb C ∧
      (if k = R.K then componentAverage pb qb C ≤ 1 else
        componentAverage pb qb C < R.pLev (k + 1) x))
  have hm : recoveryComponent pb qb rho gap (true, z) ∈ Qs :=
    (recoveryComponents_interior_policy_numeric_filter_mem_iff M h q hq L hL
      hOff hlev gap hgap pb qb rho hactive hp hqr k k j hk hk.2 hj z hz x).mpr rfl
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  have hlen : Qs.length = R.l k := rfl
  change ∃ i, (1 ≤ i ∧ i ≤ R.l k) ∧ R.T k i = L.T k j
  refine ⟨i + 1, ⟨by omega, by omega⟩, ?_⟩
  have hget : Qs.getD i ∅ = recoveryComponent pb qb rho gap (true, z) := by
    rw [← List.getElem_eq_getD (h := hi) ∅]
    exact he
  have ht : R.T k (i + 1) = Finset.univ.filter (fun w => (true, w) ∈ Qs.getD i ∅) := by
    change (if i + 1 = 0 ∨ Qs.length < i + 1 then ∅ else
      Finset.univ.filter (fun w => (true, w) ∈ Qs.getD (i + 1 - 1) ∅)) = _
    rw [if_neg (by omega), Nat.add_sub_cancel]
  rw [ht, hget]
  exact recoveryComponent_interior_policy_projection_eq M q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k j hk.2 hj z hz

omit hactive hp hqr in
-- @node: recovery_interior_policy_inclusion_failure_tendsto_zero
/-- Suppose threshold crossing holds, policy propensities are jointly
measurable, population levels and classes are invariant across
covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, and there is
a positive uniform propensity gap. If [the activity threshold tends
to zero](hyp:hrho), [baseline marginal estimates converge in probability to their
population means](hyp:hpconv), [policy marginal estimates converge in probability
to their population means](hyp:hqconv), and [threshold exceedance at each zero
baseline marginal has measure tending to zero](hyp:hzero), then [the measure of
failure of simultaneous inclusion in every positive bin before the final bin
tends to zero, where inclusion means that the recovered policy count is at least
the population count and every positive population policy class occurs as a
positive recovered label in that bin](goal). -/
lemma recovery_interior_policy_inclusion_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (∀ k, (1 ≤ k ∧ k < L.K) →
      L.l k ≤ (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).l k ∧
      ∀ j, (1 ≤ j ∧ j ≤ L.l k) → ∃ i,
        (1 ≤ i ∧ i ≤ (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).l k) ∧
        (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).T k i = L.T k j)})
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
  apply hbad
  intro k hk
  constructor
  · exact recoverLevelsAt_interior_policy_count_ge M h q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) k hk
  · intro j hj
    exact recoverLevelsAt_interior_policy_label_exists M h q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) k j hk hj

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_interior_policy_inclusion_failure_tendsto_zero
/-- Suppose threshold crossing holds, policy classes before the final
bin avoid their lower boundaries, population baseline levels are
measurable, [the sample split has equal halves](hyp:hSplit), [the
propensity predictor is measurable with respect to the training sample](hyp:hTrain),
[the predictor takes values in the unit interval](hyp:hrange), and [its maximum
instrument-specific population error is little-o in probability of sample size
to the power minus one-quarter](hyp:hRate). If [the policy map is measurable and
preserves the unit interval](hyp:hphi), [has the specified propensity derivative](hyp:hd),
[that derivative is uniformly bounded and Lipschitz](hyp:hDerivative), [baseline
and transformed policy propensities have the invariant population level
structure](hyp:hLphi), [they have a positive uniform separation gap](hyp:hgapPhi),
[the activity threshold tends to zero](hyp:hrho), and [sample size to the
one-quarter power times the threshold tends to infinity](hyp:hgrowth), then
[along even sample sizes, the probability that some positive bin before the
final bin has fewer recovered policy classes than population classes or omits
a population policy class from its positive recovered labels tends to zero](goal). -/
lemma firstStageRate_interior_policy_inclusion_failure_tendsto_zero
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
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop (𝓝 0))
    (hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n) atTop atTop) :
    Tendsto (fun n => μ {a | ¬ (∀ k, (1 ≤ k ∧ k < L.K) →
      L.l k ≤ (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).l k ∧
      ∀ j, (1 ≤ j ∧ j ≤ L.l k) → ∃ i,
        (1 ≤ i ∧ i ≤ (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).l k) ∧
        (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).T k i = L.T k j)})
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_interior_policy_inclusion_failure_tendsto_zero M h
    (policyProp phi M.prop) hqphi L hLphi hOff hlev gap hgapPhi μ
    (fun n a => pBar M S I₂ pHat (2 * (n + 1)) a)
    (fun n a => pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
    (fun n => rho (2 * (n + 1))) (hrho.comp hindex) hconv.1 hconv.2
  intro z hz
  have he := firstStageRate_pBar_baseline_quarter_rate M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate z
  simp only [hz, sub_zero] at he
  exact littleOp_threshold_exceedance_tendsto_zero μ _ _ _ he
    (recovery_threshold_dominates_quarter_rate rho hgrowth)

end Papers.TbsPrteOptimalTransport
