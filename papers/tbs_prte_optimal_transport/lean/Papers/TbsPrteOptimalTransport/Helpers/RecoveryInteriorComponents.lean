module
public import Papers.TbsPrteOptimalTransport.Helpers.LevelMarginalPolicyIdentification
public import Papers.TbsPrteOptimalTransport.Helpers.LevelMarginalConcentration
public import Papers.TbsPrteOptimalTransport.Helpers.LevelZeroRecovery
/-! Interior policy classes in the full recovery graph.
Mixed-edge separation prevents a path from leaving its policy class, so the
policy subgraph identification also identifies the full connected component. -/
public section
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)
  (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
  (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
  (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
  (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
  (pb qb : Z → ℝ) (rho : ℝ)
  (hactive : ∀ z, rho < pb z ↔ z ∉ L.S 0)
  (hp : ∀ z, |pb z - ∫ x, M.prop z x ∂xLaw M| < gap / 4)
  (hqr : ∀ z, |qb z - ∫ x, q z x ∂xLaw M| < gap / 4)

include M q hq hL hOff hlev hgap hactive hp hqr

-- @node: recoveryEdge_interior_policy_class_closed
/-- Suppose policy propensities are jointly measurable, the population
level structure is invariant across covariates, nonempty policy classes
before the final bin avoid their lower baseline boundary, baseline
levels are measurable, distinct propensity values have a positive
uniform gap, active baseline vertices are exactly those outside the
zero class, baseline marginal errors are below a quarter-gap,
and policy marginal errors are below a quarter-gap. If [bin k precedes the final bin](hyp:hk),
[j indexes one of its policy classes](hyp:hj), [z belongs to that class](hyp:hz),
and [an edge joins z's policy vertex to v](hyp:he), then [v is a policy vertex
whose instrument belongs to the same class](goal). -/
lemma recoveryEdge_interior_policy_class_closed
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (z : Z) (hz : z ∈ L.T k j) (v : RecoveryVertex Z)
    (he : recoveryEdge pb qb rho gap (true, z) v) :
    v.1 = true ∧ v.2 ∈ L.T k j := by
  let x : X := Classical.choice inferInstance
  rcases v with ⟨b, w⟩
  cases b
  · have hw : w ∉ L.S 0 := by
      apply (hactive w).mp
      simpa only [recoveryActive, Finset.mem_filter, Finset.mem_univ,
        Bool.false_eq_true, false_or, true_and] using he.2.1
    obtain ⟨i, hi, hwi⟩ := finite_baseline_level_exists M q L hL x w
    have hwm := (hL.2.2.2.2.2.1 x i w hi).mpr hwi
    have hi0 : 1 ≤ i := by
      by_contra hn
      have hi0 : i = 0 := by omega
      exact hw (hi0 ▸ hwm)
    have hn := baseline_policy_recovery_no_cross_edge M q hq L hL hOff hlev
      gap hgap i k j ⟨hi0, hi⟩ hk hj w z hwm hz pb qb (hp w) (hqr z)
    have hc : |qb z - pb w| < gap / 2 := he.2.2.2
    exact False.elim (hn (by simpa only [abs_sub_comm] using hc))
  · have heq := ((policy_recoveryEdge_iff_pointwise_equal M q hq L hL hlev
      gap hgap pb qb rho x z w (hqr z) (hqr w)).mp he).2
    have hzq := (hL.2.2.2.2.2.2.1 x k j z hk.le hj.1 hj.2).mp hz
    exact ⟨rfl, (hL.2.2.2.2.2.2.1 x k j w hk.le hj.1 hj.2).mpr
      (heq.symm.trans hzq)⟩

-- @node: recovery_path_interior_policy_class_closed
/-- Under joint measurability of policy propensities, an invariant
population level structure, policy classes off their lower boundaries
before the final bin, measurable baseline levels, positive
uniform propensity separation, correct identification of active
baseline vertices as those outside the zero class,
baseline marginal errors below a quarter-gap, and
policy marginal errors below a quarter-gap,
suppose [k precedes the final bin](hyp:hk), [j is a valid positive policy index
in bin k](hyp:hj), and [z belongs to this class](hyp:hz). If [a graph path leads
from z's policy vertex to v](hyp:he), then [v is a policy vertex in the same
population policy class](goal). -/
lemma recovery_path_interior_policy_class_closed
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (z : Z) (hz : z ∈ L.T k j) (v : RecoveryVertex Z)
    (he : Relation.ReflTransGen (recoveryEdge pb qb rho gap) (true, z) v) :
    v.1 = true ∧ v.2 ∈ L.T k j := by
  induction he with
  | refl => exact ⟨rfl, hz⟩
  | @tail a b _ hab ih =>
    have ha : a = (true, a.2) := by
      ext <;> simp only [ih.1]
    rw [ha] at hab
    exact recoveryEdge_interior_policy_class_closed M q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr k j hk hj a.2 ih.2 b hab

-- @node: recoveryComponent_interior_policy_class_eq
/-- Suppose policy propensities are jointly measurable, population
levels and classes are invariant across covariates, policy classes
before the final bin avoid their lower boundaries, baseline levels
are measurable, distinct propensity values are uniformly separated
by a positive gap, active baseline vertices identify exactly the
complement of the zero class, baseline marginal errors are below a
quarter-gap, and policy marginal errors are below a quarter-gap.
For [a bin k before
the final bin](hyp:hk), [a valid positive policy index j](hyp:hj), and [z in that
policy class](hyp:hz), [the component of z's policy vertex consists exactly of
the policy vertices in that population class](goal). -/
lemma recoveryComponent_interior_policy_class_eq
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (z : Z) (hz : z ∈ L.T k j) :
    recoveryComponent pb qb rho gap (true, z) =
      (L.T k j).image (fun w => (true, w)) := by
  let x : X := Classical.choice inferInstance
  ext v
  constructor
  · intro hv
    have hc := recovery_path_interior_policy_class_closed M q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr k j hk hj z hz v
      (Finset.mem_filter.mp hv).2
    apply Finset.mem_image.mpr
    refine ⟨v.2, hc.2, ?_⟩
    ext <;> simp only [hc.1]
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨by simp [recoveryActive], ?_⟩
    by_cases he : z = w
    · subst w
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      apply (policy_recoveryEdge_iff_pointwise_equal M q hq L hL hlev
        gap hgap pb qb rho x z w (hqr z) (hqr w)).mpr
      exact ⟨he, ((hL.2.2.2.2.2.2.1 x k j z hk.le hj.1 hj.2).mp hz).trans
        ((hL.2.2.2.2.2.2.1 x k j w hk.le hj.1 hj.2).mp hw).symm⟩

-- Structural-zero recovery and simultaneous marginal accuracy supply the
-- hypotheses for every interior policy component on a single good event.
omit hactive hp hqr in
-- @node: recovery_interior_policy_components_failure_tendsto_zero
/-- Suppose policy propensities are jointly measurable, population
levels and classes are invariant across covariates, policy classes
before the final bin avoid their lower boundaries, baseline levels
are measurable, there is positive uniform propensity
separation, and [the model has a threshold-crossing representation](hyp:h).
If [the activity threshold tends to zero](hyp:hrho), [baseline marginal estimates
converge in probability to their population means](hyp:hpconv), [policy marginal
estimates converge in probability to their population means](hyp:hqconv), and
[the measure of threshold exceedance at each zero baseline
marginal tends to zero](hyp:hzero), then [the measure of failure to identify
every policy class before the final bin as exactly its full graph component
tends to zero](goal). -/
lemma recovery_interior_policy_components_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (h : ThresholdCrossing M)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (∀ k, k < L.K →
      ∀ j, (1 ≤ j ∧ j ≤ L.l k) → ∀ z ∈ L.T k j,
        recoveryComponent (pb n a) (qb n a) (rho n) gap (true, z) =
          (L.T k j).image (fun w => (true, w)))}) atTop (𝓝 0) := by
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
  intro k hk j hj z hzk
  exact recoveryComponent_interior_policy_class_eq M q hq L hL hOff hlev gap hgap
    (pb n a) (qb n a) (rho n) ha (fun z => he (false, z)) (fun z => he (true, z))
    k j hk hj z hzk

omit q hq hL hOff hlev hgap hactive hp hqr in
-- @node: firstStageRate_interior_policy_components_failure_tendsto_zero
/-- Suppose [the sample is split into equal halves](hyp:hSplit), [the model
satisfies threshold crossing](hyp:h), [the propensity predictor is measurable
with respect to the training sample](hyp:hTrain), [its values lie in the closed
unit interval](hyp:hrange), and [its maximum instrument-specific population
error is little-o in probability of sample size to the power minus one-quarter](hyp:hRate).
If [the policy map is measurable and preserves the unit interval](hyp:hphi),
[has the specified propensity derivative](hyp:hd), [that derivative is uniformly
bounded and Lipschitz](hyp:hDerivative), [population levels and classes are
invariant across covariates](hyp:hL), [policy classes before the final bin avoid
their lower boundaries](hyp:hOff), [baseline levels are measurable](hyp:hlev),
[there is positive uniform propensity separation](hyp:hgap), [the activity
threshold tends to zero](hyp:hrho), and [sample size to the one-quarter power
times that threshold tends to infinity](hyp:hgrowth), then [along even sample
sizes the probability that any policy class before the final bin fails to equal
its full fitted graph component tends to zero](goal). -/
lemma firstStageRate_interior_policy_components_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop (𝓝 0))
    (hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n) atTop atTop) :
    Tendsto (fun n => μ {a | ¬ (∀ k, k < L.K →
      ∀ j, (1 ≤ j ∧ j ≤ L.l k) → ∀ z ∈ L.T k j,
        recoveryComponent (pBar M S I₂ pHat (2 * (n + 1)) a)
          (pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
          (rho (2 * (n + 1))) gap (true, z) =
            (L.T k j).image (fun w => (true, w)))}) atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hq : Measurable (Function.uncurry (policyProp phi M.prop)) := by
    fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_interior_policy_components_failure_tendsto_zero M
    (policyProp phi M.prop) hq L hL hOff hlev gap hgap μ h
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
