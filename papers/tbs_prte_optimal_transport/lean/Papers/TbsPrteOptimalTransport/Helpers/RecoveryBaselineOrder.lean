module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryBaselineCount
public import Papers.TbsPrteOptimalTransport.Helpers.LevelGraphRecovery
/-! Ordering baseline components by their fitted averages.
Nonterminal components contain only their baseline class. Policy vertices in
the terminal component must belong to the tail, so their marginal means cannot
pull its average below the highest population baseline. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

-- @node: componentAverage_gt_of_pointwise_gt
/-- If [a finite set of recovery vertices is nonempty](hyp:hC) and [every fitted vertex value in it strictly exceeds a given bound](hyp:hgt), then [the component average strictly exceeds that bound](goal). -/
lemma componentAverage_gt_of_pointwise_gt {Z : Type*}
    (pb qb : Z → ℝ) (C : Finset (RecoveryVertex Z)) (hC : C.Nonempty)
    (t : ℝ) (hgt : ∀ v ∈ C, t < vertexValue pb qb v) :
    t < componentAverage pb qb C := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  obtain ⟨v, hv⟩ := hC
  have hs := Finset.sum_lt_sum (fun w hw => (hgt w hw).le) ⟨v, hv, hgt v hv⟩
  have hm := mul_lt_mul_of_pos_left hs (inv_pos.mpr hc)
  simpa only [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hc.ne', one_mul, componentAverage] using hm

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

include M q L hL hactive

-- @node: recoveryComponent_positive_baseline_self_mem
/-- Under invariant level ordering and threshold selection of exactly the instruments outside the zero baseline class, take [a positive baseline level no higher than the terminal level](hyp:hi) and [an instrument in that class](hyp:hz). Then [the baseline vertex for that instrument belongs to its own recovery component](goal). -/
lemma recoveryComponent_positive_baseline_self_mem
    (i : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (z : Z) (hz : z ∈ L.S i) :
    (false, z) ∈ recoveryComponent pb qb rho gap (false, z) := by
  let x : X := Classical.choice inferInstance
  have hn : z ∉ L.S 0 := by
    intro hz0
    have he := (hL.2.2.2.2.2.1 x i z hi.2).mp hz
    have he0 := (hL.2.2.2.2.2.1 x 0 z (Nat.zero_le _)).mp hz0
    have hs := hL.2.2.2.2.2.2.2.1 x 0 i (by omega) hi.2
    rw [← he, ← he0] at hs
    exact lt_irrefl _ hs
  apply Finset.mem_filter.mpr
  refine ⟨?_, Relation.ReflTransGen.refl⟩
  simpa only [recoveryActive, Finset.mem_filter, Finset.mem_univ,
    Bool.false_eq_true, false_or, true_and] using (hactive z).mpr hn

include h hq hOff hlev hgap hp hqr

-- @node: recoveryComponent_nonterminal_baseline_average_close
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, take [a positive, nonterminal baseline level](hyp:hi) and [an instrument in that class](hyp:hz). Then [the fitted average of its recovery component differs from the population mean of that baseline level by less than one quarter of the gap](goal). -/
lemma recoveryComponent_nonterminal_baseline_average_close
    (i : ℕ) (hi : 1 ≤ i ∧ i < L.K) (z : Z) (hz : z ∈ L.S i) :
    |componentAverage pb qb (recoveryComponent pb qb rho gap (false, z)) -
      ∫ x, L.pLev i x ∂xLaw M| < gap / 4 := by
  have hself := recoveryComponent_positive_baseline_self_mem M q L hL
    gap pb qb rho hactive i ⟨hi.1, hi.2.le⟩ z hz
  apply componentAverage_close_to_common_value pb qb _ ⟨(false, z), hself⟩
  intro v hv
  have hc := recovery_path_nonterminal_baseline_class_closed M h q hq L hL hOff
    hlev gap hgap pb qb rho hactive hp hqr i hi z hz v (Finset.mem_filter.mp hv).2
  have he : M.prop v.2 = L.pLev i :=
    funext (fun x => (hL.2.2.2.2.2.1 x i v.2 hi.2.le).mp hc.2)
  simpa only [vertexValue, hc.1, Bool.false_eq_true, if_false, he] using hp v.2

omit h in
-- @node: recoveryComponent_terminal_policy_marginal_ge
/-- Under measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, suppose [a policy vertex belongs to a recovery component rooted at a baseline vertex](hyp:hw). Then [its population policy marginal is at least the population mean of the terminal baseline level](goal). -/
lemma recoveryComponent_terminal_policy_marginal_ge
    (z w : Z)
    (hw : (true, w) ∈ recoveryComponent pb qb rho gap (false, z)) :
    (∫ x, L.pLev L.K x ∂xLaw M) ≤ ∫ x, q w x ∂xLaw M := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  let x : X := Classical.choice inferInstance
  obtain ⟨k, hk, j, hj0, hj, hwm, _, _⟩ := finite_policy_level_cover M q L hL x w
  have hkK : k = L.K := by
    by_contra hn
    have hclosed := recovery_path_interior_policy_class_closed M q hq L hL hOff
      hlev gap hgap pb qb rho hactive hp hqr k j (by omega) ⟨hj0, hj⟩ w hwm
      (false, z) (recovery_path_reverse pb qb rho gap (Finset.mem_filter.mp hw).2)
    exact Bool.noConfusion hclosed.1
  subst k
  have hqm : Measurable (q w) := by fun_prop
  have hqi := (recovery_unit_interval_memLp M (q w) hqm
    (fun x => (hL.2.2.2.2.2.2.2.2.2.1 w x).2)).integrable (by norm_num)
  have hpi := (recovery_unit_interval_memLp M (L.pLev L.K) (hlev L.K)
    (fun x => hL.2.2.2.2.2.2.2.2.2.2.1 x L.K (by omega))).integrable (by norm_num)
  apply integral_mono hpi hqi
  intro x
  rw [(hL.2.2.2.2.2.2.1 x L.K j w le_rfl hj0 hj).mp hwm]
  exact (policy_level_bin_bounds M q L hL x L.K j le_rfl (by omega)).1

-- @node: recoveryComponent_terminal_baseline_average_gt
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, suppose [there is at least one positive baseline level](hyp:hK) and [the starting instrument belongs to the terminal baseline class](hyp:hz). Then [the fitted recovery-component average strictly exceeds the terminal baseline population mean minus one quarter of the gap](goal). -/
lemma recoveryComponent_terminal_baseline_average_gt
    (hK : 1 ≤ L.K) (z : Z) (hz : z ∈ L.S L.K) :
    (∫ x, L.pLev L.K x ∂xLaw M) - gap / 4 <
      componentAverage pb qb (recoveryComponent pb qb rho gap (false, z)) := by
  have hself := recoveryComponent_positive_baseline_self_mem M q L hL
    gap pb qb rho hactive L.K ⟨hK, le_rfl⟩ z hz
  apply componentAverage_gt_of_pointwise_gt pb qb _ ⟨(false, z), hself⟩
  rintro ⟨b, w⟩ hw
  cases b
  · have hproj := recoveryComponent_baseline_projection_eq M h q hq L hL hOff
      hlev gap hgap pb qb rho hactive hp hqr L.K ⟨hK, le_rfl⟩ z hz
    have hwm : w ∈ L.S L.K := by
      rw [← hproj]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
    have he : M.prop w = L.pLev L.K :=
      funext (fun x => (hL.2.2.2.2.2.1 x L.K w le_rfl).mp hwm)
    have hb := (abs_lt.mp (hp w)).1
    rw [he] at hb
    change _ < pb w
    linarith
  · have hlo := recoveryComponent_terminal_policy_marginal_ge M q hq L hL hOff
      hlev gap hgap pb qb rho hactive hp hqr z w hw
    have hb := (abs_lt.mp (hqr w)).1
    change _ < qb w
    linarith

-- @node: recoveryComponent_baseline_average_strict_order
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, take [a first level index at least one](hyp:hi), [a strictly larger second index](hyp:hij), [no higher than the terminal index](hyp:hj), and [instruments belonging to the first and second classes respectively](hyp:hz,hw). Then [the recovery component of the first baseline vertex has strictly smaller fitted average than that of the second](goal). -/
lemma recoveryComponent_baseline_average_strict_order
    (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ L.K)
    (z w : Z) (hz : z ∈ L.S i) (hw : w ∈ L.S j) :
    componentAverage pb qb (recoveryComponent pb qb rho gap (false, z)) <
      componentAverage pb qb (recoveryComponent pb qb rho gap (false, w)) := by
  have ha := abs_lt.mp (recoveryComponent_nonterminal_baseline_average_close
    M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr i ⟨hi, by omega⟩ z hz)
  have hg := population_baseline_marginal_gap M h q L hL gap hgap i j hi hij hj
  by_cases hjK : j < L.K
  · have hb := abs_lt.mp (recoveryComponent_nonterminal_baseline_average_close
      M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr j ⟨by omega, hjK⟩ w hw)
    linarith [hgap.1]
  · have he : j = L.K := by omega
    subst j
    have hb := recoveryComponent_terminal_baseline_average_gt M h q hq L hL hOff
      hlev gap hgap pb qb rho hactive hp hqr (by omega) w hw
    linarith [hgap.1]

-- @node: recoveryComponent_baseline_average_order_iff
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, take [two indices between one and the terminal baseline index](hyp:hi,hj) and [instruments in their respective baseline classes](hyp:hz,hw). Then [the first baseline recovery component has strictly smaller fitted average than the second if and only if its population level index is smaller](goal). -/
lemma recoveryComponent_baseline_average_order_iff
    (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.K)
    (z w : Z) (hz : z ∈ L.S i) (hw : w ∈ L.S j) :
    componentAverage pb qb (recoveryComponent pb qb rho gap (false, z)) <
      componentAverage pb qb (recoveryComponent pb qb rho gap (false, w)) ↔ i < j := by
  constructor
  · intro hlt
    rcases lt_trichotomy i j with hij | he | hji
    · exact hij
    · subst j
      have hpj := recoveryComponent_baseline_projection_eq M h q hq L hL hOff
        hlev gap hgap pb qb rho hactive hp hqr i hi z hz
      have hmem : (false, w) ∈ recoveryComponent pb qb rho gap (false, z) := by
        have hw' := hpj.symm ▸ hw
        exact (Finset.mem_filter.mp hw').2
      have heq := recoveryComponent_eq_of_mem pb qb rho gap hmem
      rw [heq] at hlt
      exact False.elim (lt_irrefl _ hlt)
    · exact False.elim (lt_asymm hlt
        (recoveryComponent_baseline_average_strict_order M h q hq L hL hOff hlev
          gap hgap pb qb rho hactive hp hqr j i hj.1 hji hi.2 w z hw hz))
  · intro hij
    exact recoveryComponent_baseline_average_strict_order M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr i j hi.1 hij hj.2 z w hz hw

omit hactive hp hqr in
-- @node: recovery_baseline_order_failure_tendsto_zero
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, and propensity gap separation, suppose [the threshold tends to zero](hyp:hrho), [baseline marginal estimates converge in probability to their population means](hyp:hpconv), [policy marginal estimates do likewise](hyp:hqconv), and [threshold exceedances have measure tending to zero for every zero baseline mean](hyp:hzero). Then [the measure of samples for which strict ordering of fitted recovery-component averages fails to agree with population level ordering for any pair of positive baseline classes and any representatives tends to zero](goal). -/
lemma recovery_baseline_order_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Filter.Tendsto rho Filter.atTop (𝓝 0))
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) Filter.atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) Filter.atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Filter.Tendsto (fun n => μ {a | rho n < pb n a z}) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => μ {a | ¬ (∀ i j,
      (1 ≤ i ∧ i ≤ L.K) → (1 ≤ j ∧ j ≤ L.K) → ∀ z ∈ L.S i, ∀ w ∈ L.S j,
      (componentAverage (pb n a) (qb n a)
        (recoveryComponent (pb n a) (qb n a) (rho n) gap (false, z)) <
      componentAverage (pb n a) (qb n a)
        (recoveryComponent (pb n a) (qb n a) (rho n) gap (false, w)) ↔ i < j))})
      Filter.atTop (𝓝 0) := by
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
  intro i j hi hj z hzi w hwj
  exact recoveryComponent_baseline_average_order_iff M h q hq L hL hOff hlev gap hgap
    (pb n a) (qb n a) (rho n) ha (fun z => he (false, z)) (fun z => he (true, z))
    i j hi hj z w hzi hwj

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_baseline_order_failure_tendsto_zero
/-- Under threshold crossing, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, and measurability of baseline level functions, assume [an equal half sample split](hyp:hSplit), [training-sample measurability of the predictor](hyp:hTrain), [predictions between zero and one](hyp:hrange), [maximum first-stage L2 error negligible relative to sample size to the power minus one quarter](hyp:hRate), [a valid policy map](hyp:hphi), [its differentiability with the specified derivative](hyp:hd), [a bounded Lipschitz policy derivative](hyp:hDerivative), [invariant ordering for the transformed policy levels](hyp:hLphi), and [their propensity gap separation](hyp:hgapPhi). If [the threshold tends to zero](hyp:hrho) and [its product with the fourth root of sample size tends to infinity](hyp:hgrowth), then [along positive even sample sizes, the probability that strict ordering of fitted component averages disagrees with population level ordering for any pair of positive baseline classes and any representatives tends to zero](goal). -/
lemma firstStageRate_baseline_order_failure_tendsto_zero
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
    Filter.Tendsto (fun n => μ {a | ¬ (∀ i j,
      (1 ≤ i ∧ i ≤ L.K) → (1 ≤ j ∧ j ≤ L.K) → ∀ z ∈ L.S i, ∀ w ∈ L.S j,
      (componentAverage (pBar M S I₂ pHat (2 * (n + 1)) a)
        (pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
        (recoveryComponent (pBar M S I₂ pHat (2 * (n + 1)) a)
          (pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
          (rho (2 * (n + 1))) gap (false, z)) <
      componentAverage (pBar M S I₂ pHat (2 * (n + 1)) a)
        (pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
        (recoveryComponent (pBar M S I₂ pHat (2 * (n + 1)) a)
          (pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
          (rho (2 * (n + 1))) gap (false, w)) ↔ i < j))})
      Filter.atTop (𝓝 0) := by
  have hindex : Filter.Tendsto (fun n : ℕ => 2 * (n + 1)) Filter.atTop Filter.atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_baseline_order_failure_tendsto_zero M h
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
