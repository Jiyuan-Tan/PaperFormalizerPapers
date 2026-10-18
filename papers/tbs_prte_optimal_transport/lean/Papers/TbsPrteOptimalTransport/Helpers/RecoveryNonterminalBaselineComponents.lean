module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryBaselineClasses
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryInteriorComponents
/-! Nonterminal positive baseline classes in the full recovery graph.
Interior policy levels cannot meet a baseline component. Tail policy levels
lie above the highest baseline, so they cannot meet a lower baseline either. -/
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
variable (M : LatentIVModel Ω X Z) (h : ThresholdCrossing M)
  (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
  (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
  (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
  (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)

include M h q hq L hL hlev hgap

-- @node: population_nonterminal_baseline_tail_marginal_gap
/-- In a threshold-crossing model with measurable policy propensities, invariant population level ordering, measurable baseline levels, and positive gap separation of distinct population propensities, take [a positive baseline index strictly below the highest baseline](hyp:hi), [a valid positive policy index in the terminal bin](hyp:hj), [an instrument in that baseline class](hyp:hz), and [an instrument in that terminal policy class](hyp:hw). [The terminal policy marginal exceeds the baseline marginal by at least the separation gap](goal). -/
lemma population_nonterminal_baseline_tail_marginal_gap
    (i j : ℕ) (hi : 1 ≤ i ∧ i < L.K) (hj : 1 ≤ j ∧ j ≤ L.l L.K)
    (z w : Z) (hz : z ∈ L.S i) (hw : w ∈ L.T L.K j) :
    gap ≤ (∫ x, q w x ∂xLaw M) - ∫ x, M.prop z x ∂xLaw M := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hqm : Measurable (q w) := by fun_prop
  have hqi := (recovery_unit_interval_memLp M (q w) hqm
    (fun x => (hL.2.2.2.2.2.2.2.2.2.1 w x).2)).integrable (by norm_num)
  have hpi := (recovery_unit_interval_memLp M (L.pLev L.K) (hlev L.K)
    (fun x => hL.2.2.2.2.2.2.2.2.2.2.1 x L.K (by omega))).integrable (by norm_num)
  have hlo : (∫ x, L.pLev L.K x ∂xLaw M) ≤ ∫ x, q w x ∂xLaw M := by
    apply integral_mono hpi hqi
    intro x
    rw [(hL.2.2.2.2.2.2.1 x L.K j w le_rfl hj.1 hj.2).mp hw]
    exact (policy_level_bin_bounds M q L hL x L.K j le_rfl (by omega)).1
  have hez : M.prop z = L.pLev i :=
    funext (fun x => (hL.2.2.2.2.2.1 x i z hi.2.le).mp hz)
  rw [hez]
  have hg := population_baseline_marginal_gap M h q L hL gap hgap
    i L.K hi.1 hi.2 le_rfl
  linarith

include hOff

-- @node: nonterminal_baseline_policy_recovery_no_cross_edge
/-- Assume threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, and positive gap separation. For [a positive nonterminal baseline index](hyp:hi) and [an instrument in that baseline class](hyp:hz), if [its fitted baseline marginal differs from its population value by less than one quarter of the gap](hyp:hpz) and [another instrument's fitted policy marginal satisfies the same error bound](hyp:hqw), then [the absolute difference between these fitted marginals cannot be less than half the gap](goal). -/
lemma nonterminal_baseline_policy_recovery_no_cross_edge
    (i : ℕ) (hi : 1 ≤ i ∧ i < L.K) (z w : Z) (hz : z ∈ L.S i)
    (pb qb : Z → ℝ)
    (hpz : |pb z - ∫ x, M.prop z x ∂xLaw M| < gap / 4)
    (hqw : |qb w - ∫ x, q w x ∂xLaw M| < gap / 4) :
    ¬ |pb z - qb w| < gap / 2 := by
  let x : X := Classical.choice inferInstance
  obtain ⟨k, hk, j, hj0, hj, hw, _, _⟩ := finite_policy_level_cover M q L hL x w
  by_cases hkK : k < L.K
  · exact baseline_policy_recovery_no_cross_edge M q hq L hL hOff hlev
      gap hgap i k j ⟨hi.1, hi.2.le⟩ hkK ⟨hj0, hj⟩ z w hz hw pb qb hpz hqw
  · have he : k = L.K := by omega
    subst k
    have hg := population_nonterminal_baseline_tail_marginal_gap M h q hq L hL hlev
      gap hgap i j hi ⟨hj0, hj⟩ z w hz hw
    have hs : gap ≤ |(∫ x, M.prop z x ∂xLaw M) - ∫ x, q w x ∂xLaw M| := by
      rw [abs_sub_comm]
      exact hg.trans (le_abs_self _)
    have hn : (∫ x, M.prop z x ∂xLaw M) ≠ ∫ x, q w x ∂xLaw M := by
      intro heq
      rw [heq, sub_self] at hg
      exact (not_le_of_gt hgap.1) hg
    exact fun hc => hn ((separated_values_close_iff_equal _ _ _ _ gap
      hpz hqw (Or.inr hs)).mp hc)

variable (pb qb : Z → ℝ) (rho : ℝ)
  (hactive : ∀ z, rho < pb z ↔ z ∉ L.S 0)
  (hp : ∀ z, |pb z - ∫ x, M.prop z x ∂xLaw M| < gap / 4)
  (hqr : ∀ z, |qb z - ∫ x, q z x ∂xLaw M| < gap / 4)

include hactive hp hqr

-- @node: recoveryEdge_nonterminal_baseline_class_closed
/-- Under threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, threshold activity exactly outside the zero baseline class, baseline marginal errors below one quarter of the gap, and policy marginal errors below one quarter of the gap, take [a positive nonterminal baseline index](hyp:hi) and [an instrument in its baseline class](hyp:hz). If [a recovery edge joins its baseline vertex to another vertex](hyp:he), then [that vertex is a baseline vertex whose instrument belongs to the same baseline class](goal). -/
lemma recoveryEdge_nonterminal_baseline_class_closed
    (i : ℕ) (hi : 1 ≤ i ∧ i < L.K) (z : Z) (hz : z ∈ L.S i)
    (v : RecoveryVertex Z) (he : recoveryEdge pb qb rho gap (false, z) v) :
    v.1 = false ∧ v.2 ∈ L.S i := by
  let x : X := Classical.choice inferInstance
  rcases v with ⟨b, w⟩
  cases b
  · have heq := (baseline_recoveryEdge_iff_pointwise_equal M h q L hL gap hgap
      pb qb rho x z w hactive hp).mp he
    have hzi := (hL.2.2.2.2.2.1 x i z hi.2.le).mp hz
    exact ⟨rfl, (hL.2.2.2.2.2.1 x i w hi.2.le).mpr (heq.2.2.2.symm.trans hzi)⟩
  · exact False.elim (nonterminal_baseline_policy_recovery_no_cross_edge M h q hq
      L hL hOff hlev gap hgap i hi z w hz pb qb (hp z) (hqr w) he.2.2.2)

-- @node: recovery_path_nonterminal_baseline_class_closed
/-- Suppose threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, correct activity classification outside the zero baseline class, baseline marginal errors below one quarter of the gap, and policy marginal errors below one quarter of the gap. Starting from [an instrument in a positive nonterminal baseline class](hyp:hi,hz), if [a vertex is reachable from its baseline vertex by a recovery path, including a path of length zero](hyp:he), then [the reached vertex is a baseline vertex in that same class](goal). -/
lemma recovery_path_nonterminal_baseline_class_closed
    (i : ℕ) (hi : 1 ≤ i ∧ i < L.K) (z : Z) (hz : z ∈ L.S i)
    (v : RecoveryVertex Z)
    (he : Relation.ReflTransGen (recoveryEdge pb qb rho gap) (false, z) v) :
    v.1 = false ∧ v.2 ∈ L.S i := by
  induction he with
  | refl => exact ⟨rfl, hz⟩
  | @tail a b _ hab ih =>
    have ha : a = (false, a.2) := by
      ext <;> simp only [ih.1]
    rw [ha] at hab
    exact recoveryEdge_nonterminal_baseline_class_closed M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr i hi a.2 ih.2 b hab

-- @node: recoveryComponent_nonterminal_baseline_class_eq
/-- Assume threshold crossing, measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, positive gap separation, activity exactly outside the zero baseline class, baseline marginal errors below one quarter of the gap, and policy marginal errors below one quarter of the gap. For [a positive nonterminal baseline index](hyp:hi) and [an instrument in that class](hyp:hz), [the recovery component of its baseline vertex consists exactly of all baseline vertices in that population class](goal). -/
lemma recoveryComponent_nonterminal_baseline_class_eq
    (i : ℕ) (hi : 1 ≤ i ∧ i < L.K) (z : Z) (hz : z ∈ L.S i) :
    recoveryComponent pb qb rho gap (false, z) =
      (L.S i).image (fun w => (false, w)) := by
  let x : X := Classical.choice inferInstance
  have nonzero (w : Z) (hw : w ∈ L.S i) : w ∉ L.S 0 := by
    intro hzero
    have hwi := (hL.2.2.2.2.2.1 x i w hi.2.le).mp hw
    have hw0 := (hL.2.2.2.2.2.1 x 0 w (Nat.zero_le _)).mp hzero
    have hs := hL.2.2.2.2.2.2.2.1 x 0 i (by omega) hi.2.le
    rw [← hwi, ← hw0] at hs
    exact lt_irrefl _ hs
  ext v
  constructor
  · intro hv
    have hc := recovery_path_nonterminal_baseline_class_closed M h q hq L hL hOff
      hlev gap hgap pb qb rho hactive hp hqr i hi z hz v (Finset.mem_filter.mp hv).2
    apply Finset.mem_image.mpr
    refine ⟨v.2, hc.2, ?_⟩
    ext <;> simp only [hc.1]
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simpa only [recoveryActive, Finset.mem_filter, Finset.mem_univ,
        Bool.false_eq_true, false_or, true_and] using (hactive w).mpr (nonzero w hw)
    · by_cases he : z = w
      · subst w
        exact Relation.ReflTransGen.refl
      · apply Relation.ReflTransGen.single
        apply (baseline_recoveryEdge_iff_pointwise_equal M h q L hL gap hgap
          pb qb rho x z w hactive hp).mpr
        exact ⟨nonzero z hz, nonzero w hw, he,
          ((hL.2.2.2.2.2.1 x i z hi.2.le).mp hz).trans
            ((hL.2.2.2.2.2.1 x i w hi.2.le).mp hw).symm⟩

omit hactive hp hqr in
-- @node: recovery_nonterminal_baseline_components_failure_tendsto_zero
/-- In a threshold-crossing model with measurable policy propensities, invariant population level ordering, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, and positive gap separation, suppose [the activity threshold tends to zero](hyp:hrho), [each fitted baseline marginal converges in probability to its population value](hyp:hpconv), [each fitted policy marginal does likewise](hyp:hqconv), and [the measure of threshold exceedance at every zero baseline marginal tends to zero](hyp:hzero). [The measure of samples on which any positive nonterminal baseline vertex fails to recover exactly its entire population baseline class tends to zero](goal). -/
lemma recovery_nonterminal_baseline_components_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (∀ i, (1 ≤ i ∧ i < L.K) → ∀ z ∈ L.S i,
      recoveryComponent (pb n a) (qb n a) (rho n) gap (false, z) =
        (L.S i).image (fun w => (false, w)))}) atTop (𝓝 0) := by
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
  intro i hi z hzi
  exact recoveryComponent_nonterminal_baseline_class_eq M h q hq L hL hOff hlev gap hgap
    (pb n a) (qb n a) (rho n) ha (fun z => he (false, z)) (fun z => he (true, z))
    i hi z hzi

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_nonterminal_baseline_components_failure_tendsto_zero
/-- Assume threshold crossing, policy levels avoiding their bins' lower baseline boundaries before the terminal bin, measurable baseline levels, [an equal half split of the observed sample](hyp:hSplit), and [a predictor measurable using the training half](hyp:hTrain), [taking values between zero and one](hyp:hrange), and [having maximum population L2 error across instruments negligible in probability relative to sample size to the negative one-quarter power](hyp:hRate). If [the policy map preserves admissible propensities](hyp:hphi), [has the specified derivative](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative), [the transformed population propensities have the specified invariant level ordering](hyp:hLphi), [they satisfy positive gap separation jointly with the baseline](hyp:hgapPhi), [the threshold tends to zero](hyp:hrho), and [the threshold times the fourth root of sample size tends to infinity](hyp:hgrowth), then [along even sample sizes, the probability that any positive nonterminal baseline component differs from its population baseline class tends to zero](goal). -/
lemma firstStageRate_nonterminal_baseline_components_failure_tendsto_zero
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
    Tendsto (fun n => μ {a | ¬ (∀ i, (1 ≤ i ∧ i < L.K) → ∀ z ∈ L.S i,
      recoveryComponent (pBar M S I₂ pHat (2 * (n + 1)) a)
        (pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
        (rho (2 * (n + 1))) gap (false, z) =
          (L.S i).image (fun w => (false, w)))}) atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_nonterminal_baseline_components_failure_tendsto_zero M h
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
