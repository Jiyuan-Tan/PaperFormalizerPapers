module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryTailExclusion
/-! Exact recovery of the policy classes in the zero bin.
Clipped fitted probabilities keep component averages nonnegative. The first
positive baseline endpoint separates this bin from every remaining component,
and the existing ordered component projections give its counts and labels. -/
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



omit [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z] [StandardBorelSpace Z]
  [Nonempty Z] [Fintype Z] [DecidableEq Z] in
-- @node: componentAverage_nonneg
/-- If [all fitted baseline values are nonnegative](hyp:hpb) and [all fitted policy
values are nonnegative](hyp:hqb), then [the average over any finite collection of
recovery vertices is nonnegative, including the empty collection](goal). -/
lemma componentAverage_nonneg
    (hpb : ∀ z, 0 ≤ pb z) (hqb : ∀ z, 0 ≤ qb z)
    (C : Finset (RecoveryVertex Z)) :
    0 ≤ componentAverage pb qb C := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg C.card))
  apply Finset.sum_nonneg
  rintro ⟨b, z⟩ _
  cases b
  · exact hpb z
  · exact hqb z

omit [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X]
  [Nonempty X] [Fintype Z] [DecidableEq Z] in
-- @node: pBar_nonneg
/-- If [every fitted propensity is nonnegative](hyp:hrange), then [its average
over the evaluation subsample is nonnegative at every sample size, realization,
and instrument value](goal). -/
lemma pBar_nonneg
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (S : ObservedSample M μ) (I₂ : SampleSplit A)
    (pHat : ℕ → A → Z → X → ℝ)
    (hrange : ∀ n a z x, 0 ≤ pHat n a z x) (n : ℕ) (a : A) (z : Z) :
    0 ≤ pBar M S I₂ pHat n a z := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun i _ => hrange n a z (S.Z i a).1)

include M h q hq L hL hOff hlev hgap hactive hp hqr

-- @node: recoverLevelsAt_zero_policy_numeric_bin_iff
/-- Under threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, suppose [a
positive baseline level exists](hyp:hK), [baseline fitted values are nonnegative](hyp:hpb),
and [policy fitted values are nonnegative](hyp:hqb). For [a bin strictly below
the terminal bin](hyp:hr), [a valid policy class index in that bin](hyp:hj), and
[an instrument in that class](hyp:hw), [its policy recovery component average
lies at or above the recovered zero endpoint and strictly below the first
positive endpoint at the chosen covariate value exactly when its bin is zero](goal). -/
lemma recoverLevelsAt_zero_policy_numeric_bin_iff
    (hK : 0 < L.K) (hpb : ∀ z, 0 ≤ pb z) (hqb : ∀ z, 0 ≤ qb z)
    (r j : ℕ) (hr : r < L.K) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (w : Z) (hw : w ∈ L.T r j) (x : X) :
    ((recoverLevelsAt pb qb rho gap : LevelData Z X).pLev 0 x ≤
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) ∧
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) <
        (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev 1 x) ↔ r = 0 := by
  have hlo : (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev 0 x ≤
      componentAverage pb qb (recoveryComponent pb qb rho gap (true, w)) :=
    componentAverage_nonneg pb qb hpb hqb _
  rw [(recoverLevelsAt_endpoint_interior_policy_order M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr 1 r j ⟨by omega, hK⟩ hr hj w hw x).2]
  exact ⟨fun hh => by omega, fun he => ⟨hlo, by omega⟩⟩

-- @node: recoveryComponents_zero_policy_numeric_filter_eq
/-- Assume threshold crossing, policy propensity measurability,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
baseline level measurability, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap.
If [a positive
baseline level exists](hyp:hK), [baseline fitted values are nonnegative](hyp:hpb),
and [policy fitted values are nonnegative](hyp:hqb), then [the ordered list of
components containing a policy vertex whose averages are at least the recovered
zero endpoint and strictly below the recovered first positive baseline endpoint
at the chosen covariate value equals the list of components meeting a population
policy class in bin zero](goal). -/
lemma recoveryComponents_zero_policy_numeric_filter_eq
    (hK : 0 < L.K) (hpb : ∀ z, 0 ≤ pb z) (hqb : ∀ z, 0 ≤ qb z) (x : X) :
    (recoveryComponents pb qb rho gap).filter (fun C =>
      (∃ z, (true, z) ∈ C) ∧
      (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev 0 x ≤ componentAverage pb qb C ∧
      (if 0 = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
        componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
          (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev 1 x)) =
    (recoveryComponents pb qb rho gap).filter (fun C =>
      ∃ j, (1 ≤ j ∧ j ≤ L.l 0) ∧ ∃ z ∈ L.T 0 j, (true, z) ∈ C) := by
  have hcount := recoverLevelsAt_baseline_count_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr
  apply List.filter_congr
  intro C hC
  simp only [decide_eq_decide, hcount, if_neg (show 0 ≠ L.K by omega)]
  constructor
  · rintro ⟨⟨w, hw⟩, hlo, hhi⟩
    obtain ⟨r, hr, j, hj0, hj, hwm, _, _⟩ := finite_policy_level_cover M q L hL x w
    have he := recoveryComponents_eq_component_of_mem pb qb rho gap hC hw
    have hrK : r < L.K := by
      by_contra hn
      have hrK : r = L.K := by omega
      subst r
      have ht := recoverLevelsAt_positive_endpoint_le_tail_component
        M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr
        1 j ⟨by omega, hK⟩ ⟨hj0, hj⟩ w hwm x
      rw [he] at ht
      exact (not_lt_of_ge ht) hhi
    have hr0 := (recoverLevelsAt_zero_policy_numeric_bin_iff M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr hK hpb hqb r j hrK ⟨hj0, hj⟩ w hwm x).mp
        (by simpa only [he] using And.intro hlo hhi)
    subst r
    exact ⟨j, ⟨hj0, hj⟩, w, hwm, hw⟩
  · rintro ⟨j, hj, w, hwm, hw⟩
    have hm := (recoverLevelsAt_zero_policy_numeric_bin_iff M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr hK hpb hqb 0 j hK hj w hwm x).mpr rfl
    have he := recoveryComponents_eq_component_of_mem pb qb rho gap hC hw
    exact ⟨⟨w, hw⟩, by simpa only [he] using hm⟩

-- @node: recoveryComponents_zero_policy_numeric_list_eq
/-- Given threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, suppose [a
positive baseline level exists](hyp:hK), [baseline fitted values are nonnegative](hyp:hpb),
[policy fitted values are nonnegative](hyp:hqb), and [the representative rule
selects an instrument from every valid policy class in bin zero](hyp:hrep).
Then [the ordered components containing a policy vertex whose averages are at
least the recovered zero endpoint and strictly below the recovered first positive
baseline endpoint at the chosen covariate value are exactly the representatives'
policy recovery components in increasing class order](goal). -/
lemma recoveryComponents_zero_policy_numeric_list_eq
    (hK : 0 < L.K) (hpb : ∀ z, 0 ≤ pb z) (hqb : ∀ z, 0 ≤ qb z)
    (x : X) (rep : ℕ → Z)
    (hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l 0) → rep j ∈ L.T 0 j) :
    (recoveryComponents pb qb rho gap).filter (fun C =>
      (∃ z, (true, z) ∈ C) ∧
      (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev 0 x ≤ componentAverage pb qb C ∧
      (if 0 = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
        componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
          (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev 1 x)) =
    (List.range (L.l 0)).map (fun j => recoveryComponent pb qb rho gap (true, rep (j + 1))) := by
  rw [recoveryComponents_zero_policy_numeric_filter_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr hK hpb hqb x]
  exact recoveryComponents_interior_policy_class_list_eq M q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr 0 hK rep hrep

-- @node: recoverLevelsAt_zero_policy_count_eq
/-- Under threshold crossing, policy propensity measurability,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
baseline level measurability, positive gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap, if [a positive
baseline level exists](hyp:hK), [baseline fitted values are nonnegative](hyp:hpb),
and [policy fitted values are nonnegative](hyp:hqb), then [the recovered number
of policy classes in bin zero equals its population count](goal). -/
lemma recoverLevelsAt_zero_policy_count_eq
    (hK : 0 < L.K) (hpb : ∀ z, 0 ≤ pb z) (hqb : ∀ z, 0 ≤ qb z) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).l 0 = L.l 0 := by
  let rep : ℕ → Z := fun j => if hj : 1 ≤ j ∧ j ≤ L.l 0 then
    Classical.choose (ordered_policy_level_nonempty M q L hL 0 j (by omega) hj.1 hj.2)
    else Classical.choice inferInstance
  have hrep : ∀ j, (1 ≤ j ∧ j ≤ L.l 0) → rep j ∈ L.T 0 j := by
    intro j hj
    simpa only [rep, dif_pos hj] using
      Classical.choose_spec (ordered_policy_level_nonempty M q L hL 0 j (by omega) hj.1 hj.2)
  have he := congrArg List.length (recoveryComponents_zero_policy_numeric_list_eq
    M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr hK hpb hqb
    (Classical.choice inferInstance) rep hrep)
  simpa only [recoverLevelsAt, List.length_map, List.length_range] using he

-- @node: recoverLevelsAt_zero_policy_label_eq
/-- Assume threshold crossing, a measurable policy propensity,
invariant population level ordering, nonterminal policy levels distinct
from their lower baseline endpoints,
measurable baseline levels, positive propensity gap separation,
an activity threshold excluding exactly the zero baseline class, and
all baseline and policy marginal errors below one quarter of the gap.
With [a
positive baseline level](hyp:hK), [nonnegative baseline fitted values](hyp:hpb),
[nonnegative policy fitted values](hyp:hqb), and [a valid policy class index in
bin zero](hyp:hj), [the recovered instrument set for that class equals its
population instrument set](goal). -/
lemma recoverLevelsAt_zero_policy_label_eq
    (hK : 0 < L.K) (hpb : ∀ z, 0 ≤ pb z) (hqb : ∀ z, 0 ≤ qb z)
    (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l 0) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).T 0 j = L.T 0 j := by
  have hl := recoverLevelsAt_zero_policy_count_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr hK hpb hqb
  have hf := recoveryComponents_zero_policy_numeric_filter_eq M h q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr hK hpb hqb (Classical.choice inferInstance)
  have hvalid : ¬ (j = 0 ∨
      (recoverLevelsAt pb qb rho gap : LevelData Z X).l 0 < j) := by omega
  let Qs := (recoveryComponents pb qb rho gap).filter (fun C =>
    (∃ z, (true, z) ∈ C) ∧
    (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev 0
      (Classical.choice inferInstance) ≤ componentAverage pb qb C ∧
    (if 0 = (recoverLevelsAt pb qb rho gap : LevelData Z X).K then
      componentAverage pb qb C ≤ 1 else componentAverage pb qb C <
        (recoverLevelsAt pb qb rho gap : LevelData Z X).pLev 1
          (Classical.choice inferInstance)))
  change ¬ (j = 0 ∨ Qs.length < j) at hvalid
  change Qs = _ at hf
  change (if j = 0 ∨ Qs.length < j then ∅ else
    Finset.univ.filter (fun z => (true, z) ∈ Qs.getD (j - 1) ∅)) = _
  rw [if_neg hvalid, hf]
  exact recoveryComponents_interior_policy_indexed_projection_eq M q hq L hL hOff hlev
    gap hgap pb qb rho hactive hp hqr 0 j hK hj

omit hactive hp hqr in
-- @node: recovery_zero_policy_labels_failure_tendsto_zero
/-- With threshold crossing, a measurable policy propensity,
invariant level ordering, nonterminal policy levels distinct from their
lower baseline endpoints,
measurable baseline levels, and positive gap separation,
suppose [the activity thresholds tend to zero](hyp:hrho), [a positive baseline
level exists](hyp:hK), [baseline marginal estimates are nonnegative](hyp:hpb),
and [policy marginal estimates are nonnegative](hyp:hqb). If [each instrument's
baseline marginal estimate converges in probability to its population marginal](hyp:hpconv),
[each policy marginal estimate does likewise](hyp:hqconv), and [the measure of
threshold exceedance tends to zero for instruments with zero baseline marginal](hyp:hzero),
then [the measure of failure to recover both the policy class count in bin zero
and every valid class instrument set in that bin tends to zero](goal). -/
lemma recovery_zero_policy_labels_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hK : 0 < L.K)
    (hpb : ∀ n a z, 0 ≤ pb n a z) (hqb : ∀ n a z, 0 ≤ qb n a z)
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (
      (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).l 0 = L.l 0 ∧
      ∀ j, (1 ≤ j ∧ j ≤ L.l 0) →
        (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).T 0 j = L.T 0 j)})
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
  constructor
  · exact recoverLevelsAt_zero_policy_count_eq M h q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) hK (hpb n a) (hqb n a)
  · intro j hj
    exact recoverLevelsAt_zero_policy_label_eq M h q hq L hL hOff hlev
      gap hgap (pb n a) (qb n a) (rho n) ha
      (fun z => he (false, z)) (fun z => he (true, z)) hK (hpb n a) (hqb n a) j hj

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_zero_policy_labels_failure_tendsto_zero
/-- Under threshold crossing, nonterminal policy levels distinct from
their lower baseline endpoints,
measurable baseline levels, [an equal half split of the observed
sample](hyp:hSplit), [a predictor measurable with respect to its training
sample](hyp:hTrain), [fitted propensities between zero and one](hyp:hrange), and
[maximum finite population L2 error across instruments vanishing in probability
faster than sample size to the negative one-quarter power along even sample
sizes](hyp:hRate), consider [a policy map preserving the unit interval](hyp:hphi)
that [is differentiable with the specified derivative](hyp:hd),
with [a bounded Lipschitz derivative](hyp:hDerivative). Suppose [baseline and
transformed policy propensities have the specified invariant level ordering](hyp:hLphi)
and [positive gap separation](hyp:hgapPhi), and [a positive baseline level
exists](hyp:hK). If [the activity threshold tends to zero](hyp:hrho) and [its
product with the fourth root of sample size tends to infinity](hyp:hgrowth),
then [along even sample sizes starting at two, the probability of failing to
recover the policy class count in bin zero and all its valid class instrument
sets tends to zero](goal). -/
lemma firstStageRate_zero_policy_labels_failure_tendsto_zero
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
    Tendsto (fun n => μ {a | ¬ (
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).l 0 = L.l 0 ∧
      ∀ j, (1 ≤ j ∧ j ≤ L.l 0) →
        (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).T 0 j = L.T 0 j)})
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_zero_policy_labels_failure_tendsto_zero M h
    (policyProp phi M.prop) hqphi L hLphi hOff hlev gap hgapPhi μ
    (fun n a => pBar M S I₂ pHat (2 * (n + 1)) a)
    (fun n a => pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
    (fun n => rho (2 * (n + 1))) (hrho.comp hindex) hK
    (fun n a z => pBar_nonneg M μ S I₂ pHat
      (fun n a z x => (hrange n a z x).1) _ a z)
    (fun n a z => pBar_nonneg M μ S I₂
      (fun n a => policyProp phi (pHat n a))
      (fun n a z x => (hphi.2 z x _ (hrange n a z x)).1) _ a z)
    hconv.1 hconv.2
  intro z hz
  have he := firstStageRate_pBar_baseline_quarter_rate M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate z
  simp only [hz, sub_zero] at he
  exact littleOp_threshold_exceedance_tendsto_zero μ _ _ _ he
    (recovery_threshold_dominates_quarter_rate rho hgrowth)

end Papers.TbsPrteOptimalTransport
