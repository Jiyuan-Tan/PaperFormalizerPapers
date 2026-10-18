module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryBaselineOrder
public import Papers.TbsPrteOptimalTransport.Helpers.LevelGraphRecovery
/-! Ordering interior policy components and locating them between baseline levels.
Marginal gaps dominate fitted-average errors, including the mixed terminal
baseline component, and the comparisons hold simultaneously with high probability. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

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

include M q hq L hL hOff hlev hgap hactive hp hqr

-- @node: recoveryComponent_interior_policy_average_close
/-- Suppose policy propensities are jointly measurable, population
levels and classes are invariant across covariates, policy classes
before the final bin avoid their lower boundaries, baseline levels
are measurable, there is a positive uniform propensity gap,
active baseline vertices are exactly those outside the zero class,
baseline marginal errors are below a quarter-gap, and policy marginal
errors are below a quarter-gap. For [a bin k before the final bin](hyp:hk),
[a valid positive policy index j](hyp:hj), and [z in that policy class](hyp:hz),
[the average fitted value of z's policy component differs from the population
mean of that policy level by less than a quarter-gap](goal). -/
lemma recoveryComponent_interior_policy_average_close
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (z : Z) (hz : z ∈ L.T k j) :
    |componentAverage pb qb (recoveryComponent pb qb rho gap (true, z)) -
      ∫ x, L.qLev k j x ∂xLaw M| < gap / 4 := by
  have hself : (true, z) ∈ recoveryComponent pb qb rho gap (true, z) := by
    exact Finset.mem_filter.mpr ⟨by simp [recoveryActive], Relation.ReflTransGen.refl⟩
  apply componentAverage_close_to_common_value pb qb _ ⟨(true, z), hself⟩
  intro v hv
  have hc := recovery_path_interior_policy_class_closed M q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr k j hk hj z hz v (Finset.mem_filter.mp hv).2
  have he : q v.2 = L.qLev k j :=
    funext (fun x => (hL.2.2.2.2.2.2.1 x k j v.2 hk.le hj.1 hj.2).mp hc.2)
  simpa only [vertexValue, hc.1, if_true, he] using hqr v.2

-- @node: recoveryComponent_interior_policy_average_strict_order
/-- Under joint measurability of policy propensities, an invariant
population level structure, policy classes off their lower boundaries
before the final bin, measurable baseline levels, positive
uniform propensity separation, correct activity classification outside
the zero baseline class, baseline marginal errors below a
quarter-gap, and policy marginal errors below a quarter-gap,
suppose [k precedes the final bin](hyp:hk), [r precedes the final bin](hyp:hr),
[i is a valid positive policy index in k](hyp:hi), [j is a valid positive policy
index in r](hyp:hj), [z belongs to class i in k](hyp:hz), and [w belongs to class j
in r](hyp:hw). If [k is less than r, or the bins coincide and i is less than
j](hyp:hij), then [z's policy component has a strictly smaller average fitted
value than w's](goal). -/
lemma recoveryComponent_interior_policy_average_strict_order
    (k r i j : ℕ) (hk : k < L.K) (hr : r < L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (z w : Z) (hz : z ∈ L.T k i) (hw : w ∈ L.T r j)
    (hij : k < r ∨ k = r ∧ i < j) :
    componentAverage pb qb (recoveryComponent pb qb rho gap (true, z)) <
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) := by
  have ha := abs_lt.mp (recoveryComponent_interior_policy_average_close
    M q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr k i hk hi z hz)
  have hb := abs_lt.mp (recoveryComponent_interior_policy_average_close
    M q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr r j hr hj w hw)
  have hg := population_policy_marginal_lex_gap M q hq L hL hlev gap hgap
    k r i j hk.le hr.le hi hj hij
  linarith [hgap.1]

-- @node: recoveryComponent_interior_policy_average_order_iff
/-- Suppose policy propensities are jointly measurable, population
levels and classes are invariant across covariates, policy classes
before the final bin avoid their lower boundaries, baseline levels
are measurable, there is a positive uniform propensity gap,
active baseline vertices are exactly those outside the zero class,
baseline marginal errors are below a quarter-gap, and policy marginal
errors are below a quarter-gap. For [k before the final bin](hyp:hk),
[r before the final bin](hyp:hr), [a valid positive policy index i in k](hyp:hi),
[a valid positive policy index j in r](hyp:hj), [z in class i of k](hyp:hz), and
[w in class j of r](hyp:hw), [z's policy component has a strictly smaller average
fitted value than w's if and only if k is less than r, or the bins coincide and
i is less than j](goal). -/
lemma recoveryComponent_interior_policy_average_order_iff
    (k r i j : ℕ) (hk : k < L.K) (hr : r < L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (z w : Z) (hz : z ∈ L.T k i) (hw : w ∈ L.T r j) :
    componentAverage pb qb (recoveryComponent pb qb rho gap (true, z)) <
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) ↔
        k < r ∨ k = r ∧ i < j := by
  constructor
  · intro hlt
    by_contra hn
    by_cases heq : k = r ∧ i = j
    · rcases heq with ⟨rfl, rfl⟩
      rw [recoveryComponent_interior_policy_class_eq M q hq L hL hOff hlev
        gap hgap pb qb rho hactive hp hqr k i hk hi z hz,
        recoveryComponent_interior_policy_class_eq M q hq L hL hOff hlev
        gap hgap pb qb rho hactive hp hqr k i hk hi w hw] at hlt
      exact lt_irrefl _ hlt
    · have hrev : r < k ∨ r = k ∧ j < i := by omega
      exact lt_asymm hlt (recoveryComponent_interior_policy_average_strict_order
        M q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr
        r k j i hr hk hj hi w z hw hz hrev)
  · exact recoveryComponent_interior_policy_average_strict_order
      M q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr
      k r i j hk hr hi hj z w hz hw

include h in
-- @node: recoveryComponent_baseline_interior_policy_average_order
/-- Under threshold crossing, joint measurability of policy
propensities, an invariant population level structure, policy
classes off their lower boundaries before the final bin, measurable
baseline levels, positive uniform propensity separation,
correct activity classification outside the zero baseline class,
baseline marginal errors below a quarter-gap, and policy marginal
errors below a quarter-gap, suppose [i is a positive baseline index
within range](hyp:hi), [k precedes the final bin](hyp:hk), [j is a valid positive
policy index in k](hyp:hj), [z belongs to baseline class i](hyp:hz), and [w belongs
to policy class j in k](hyp:hw). Then [the average fitted value of z's baseline
component is strictly below that of w's policy component exactly when i is at
most k, and the reverse strict inequality holds exactly when k is less than i](goal). -/
lemma recoveryComponent_baseline_interior_policy_average_order
    (i k j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K)
    (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (z w : Z) (hz : z ∈ L.S i) (hw : w ∈ L.T k j) :
    (componentAverage pb qb (recoveryComponent pb qb rho gap (false, z)) <
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) ↔ i ≤ k) ∧
    (componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) <
      componentAverage pb qb (recoveryComponent pb qb rho gap (false, z)) ↔ k < i) := by
  have hqclose := abs_lt.mp (recoveryComponent_interior_policy_average_close
    M q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr k j hk hj w hw)
  have hg := population_baseline_policy_marginal_gaps M q hq L hL hOff hlev
    gap hgap i k j hi hk hj
  have lower (hik : i ≤ k) :
      componentAverage pb qb (recoveryComponent pb qb rho gap (false, z)) <
        componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) := by
    have hb := abs_lt.mp (recoveryComponent_nonterminal_baseline_average_close
      M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr
      i ⟨hi.1, hik.trans_lt hk⟩ z hz)
    linarith [hg.1 hik, hgap.1]
  have upper (hki : k < i) :
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) <
        componentAverage pb qb (recoveryComponent pb qb rho gap (false, z)) := by
    by_cases hiK : i < L.K
    · have hb := abs_lt.mp (recoveryComponent_nonterminal_baseline_average_close
        M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr i ⟨hi.1, hiK⟩ z hz)
      linarith [hg.2 hki, hgap.1]
    · have hiK : i = L.K := by omega
      have hb := recoveryComponent_terminal_baseline_average_gt M h q hq L hL hOff
        hlev gap hgap pb qb rho hactive hp hqr (by omega) z (hiK ▸ hz)
      rw [← hiK] at hb
      linarith [hg.2 hki, hgap.1]
  constructor
  · constructor
    · intro hlt
      by_contra hn
      exact lt_asymm hlt (upper (Nat.lt_of_not_ge hn))
    · exact lower
  · constructor
    · intro hlt
      by_contra hn
      exact lt_asymm hlt (lower (Nat.le_of_not_gt hn))
    · exact upper

include h

omit hactive hp hqr in
-- @node: recovery_interior_policy_order_failure_tendsto_zero
/-- Suppose threshold crossing holds, policy propensities are jointly
measurable, population levels and classes are invariant across
covariates, policy classes before the final bin avoid their lower
boundaries, baseline levels are measurable, and there is
a positive uniform propensity gap. If [the activity threshold tends
to zero](hyp:hrho), [baseline marginal estimates converge in probability to their
population means](hyp:hpconv), [policy marginal estimates converge in probability
to their population means](hyp:hqconv), and [threshold exceedance at each zero
baseline marginal has measure tending to zero](hyp:hzero), then [the measure of
failure of the simultaneous component-average ordering tends to zero: policy
components before the final bin are strictly ordered exactly by bin and then
policy index, and every positive baseline component i lies strictly below each
policy component in bin k before the final bin exactly when i is at most k,
with the reverse strict comparison exactly when k is less than i](goal). -/
lemma recovery_interior_policy_order_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Filter.Tendsto rho Filter.atTop (𝓝 0))
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) Filter.atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) Filter.atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (
      (∀ k r i j, k < L.K → r < L.K →
        (1 ≤ i ∧ i ≤ L.l k) → (1 ≤ j ∧ j ≤ L.l r) →
        ∀ z ∈ L.T k i, ∀ w ∈ L.T r j,
          (componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap (true, z)) <
          componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap (true, w)) ↔
              k < r ∨ k = r ∧ i < j)) ∧
      (∀ i k j, (1 ≤ i ∧ i ≤ L.K) → k < L.K →
        (1 ≤ j ∧ j ≤ L.l k) → ∀ z ∈ L.S i, ∀ w ∈ L.T k j,
          (componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap (false, z)) <
          componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap (true, w)) ↔ i ≤ k) ∧
          (componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap (true, w)) <
          componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rho n) gap (false, z)) ↔ k < i))
      )}) atTop (𝓝 0) := by
  have hz := recovery_zero_class_failure_tendsto_zero μ pb
    (fun z => ∫ x, M.prop z x ∂xLaw M)
    (fun z => integral_nonneg (fun x => (M.rangeProp z x).1))
    rho hrho hpconv hzero
  have hconv : ∀ v : RecoveryVertex Z,
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n a => vertexValue (pb n a) (qb n a) v) Filter.atTop
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
  constructor
  · intro k r i j hk hr hi hj z hz w hw
    exact recoveryComponent_interior_policy_average_order_iff M q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) k r i j hk hr hi hj z w hz hw
  · intro i k j hi hk hj z hz w hw
    exact recoveryComponent_baseline_interior_policy_average_order M h q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) i k j hi hk hj z w hz hw

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_interior_policy_order_failure_tendsto_zero
/-- Suppose threshold crossing holds, policy classes before the final
bin avoid their lower boundaries, baseline levels are measurable,
[the sample split has equal halves](hyp:hSplit), [the propensity predictor is
measurable with respect to the training sample](hyp:hTrain), [it takes values
in the unit interval](hyp:hrange), and [its maximum instrument-specific population
error is little-o in probability of sample size to the power minus one-quarter](hyp:hRate).
If [the policy map is measurable and preserves the unit interval](hyp:hphi),
[has the specified propensity derivative](hyp:hd), [that derivative is uniformly
bounded and Lipschitz](hyp:hDerivative), [baseline and transformed policy
propensities have the invariant population level structure](hyp:hLphi), [they
have a positive uniform separation gap](hyp:hgapPhi), [the activity threshold
tends to zero](hyp:hrho), and [sample size to the one-quarter power times the
threshold tends to infinity](hyp:hgrowth), then [along even sample sizes the
probability of failure of the simultaneous component-average ordering tends to
zero: policy components before the final bin are strictly ordered exactly by
bin and then policy index, and a positive baseline component i is strictly below
a policy component in bin k before the final bin exactly when i is at most k,
with the reverse strict comparison exactly when k is less than i](goal). -/
lemma firstStageRate_interior_policy_order_failure_tendsto_zero
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
    (rho : ℕ → ℝ) (hrho : Filter.Tendsto rho Filter.atTop (𝓝 0))
    (hgrowth : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n)
      Filter.atTop Filter.atTop) :
    let pb := fun n a => pBar M S I₂ pHat (2 * (n + 1)) a
    let qb := fun n a =>
      pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a
    let rhoSeq := fun n => rho (2 * (n + 1))
    Tendsto (fun n => μ {a | ¬ (
      (∀ k r i j, k < L.K → r < L.K →
        (1 ≤ i ∧ i ≤ L.l k) → (1 ≤ j ∧ j ≤ L.l r) →
        ∀ z ∈ L.T k i, ∀ w ∈ L.T r j,
          (componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rhoSeq n) gap (true, z)) <
          componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rhoSeq n) gap (true, w)) ↔
              k < r ∨ k = r ∧ i < j)) ∧
      (∀ i k j, (1 ≤ i ∧ i ≤ L.K) → k < L.K →
        (1 ≤ j ∧ j ≤ L.l k) → ∀ z ∈ L.S i, ∀ w ∈ L.T k j,
          (componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rhoSeq n) gap (false, z)) <
          componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rhoSeq n) gap (true, w)) ↔ i ≤ k) ∧
          (componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rhoSeq n) gap (true, w)) <
          componentAverage (pb n a) (qb n a)
            (recoveryComponent (pb n a) (qb n a) (rhoSeq n) gap (false, z)) ↔ k < i))
      )}) atTop (𝓝 0) := by
  have hindex : Filter.Tendsto (fun n : ℕ => 2 * (n + 1)) Filter.atTop Filter.atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_interior_policy_order_failure_tendsto_zero M h
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
