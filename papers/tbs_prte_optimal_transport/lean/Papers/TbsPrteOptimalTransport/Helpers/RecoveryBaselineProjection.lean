module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryNonterminalBaselineComponents
/-! Baseline projections of full recovery components, including the terminal level.
A terminal component may contain policy vertices. Reversing a path into a lower
baseline class rules out any additional baseline vertices in that component. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

-- @node: recoveryEdge_reverse
/-- If [a recovery edge joins the first vertex to the second](hyp:he), then [a recovery edge also joins the second vertex to the first](goal). -/
lemma recoveryEdge_reverse {Z : Type*} [Fintype Z]
    (pb qb : Z → ℝ) (rho gap : ℝ) {a b : RecoveryVertex Z}
    (he : recoveryEdge pb qb rho gap a b) :
    recoveryEdge pb qb rho gap b a := by
  refine ⟨he.2.1, he.1, he.2.2.1.symm, ?_⟩
  simpa only [abs_sub_comm] using he.2.2.2

-- @node: recovery_path_reverse
/-- If [a path of recovery edges connects the first vertex to the second, allowing a path of length zero](hyp:hp), then [such a path also connects the second vertex to the first](goal). -/
lemma recovery_path_reverse {Z : Type*} [Fintype Z]
    (pb qb : Z → ℝ) (rho gap : ℝ) {a b : RecoveryVertex Z}
    (hp : Relation.ReflTransGen (recoveryEdge pb qb rho gap) a b) :
    Relation.ReflTransGen (recoveryEdge pb qb rho gap) b a := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    exact (Relation.ReflTransGen.single (recoveryEdge_reverse pb qb rho gap hbc)).trans ih

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

-- @node: recoveryComponent_baseline_projection_eq
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, take [a positive baseline level up to and including the terminal level](hyp:hi) and [an instrument in that class](hyp:hz). Then [the baseline projection of the full recovery component rooted at that instrument equals its population baseline class](goal). -/
lemma recoveryComponent_baseline_projection_eq
    (i : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (z : Z) (hz : z ∈ L.S i) :
    Finset.univ.filter (fun w =>
      (false, w) ∈ recoveryComponent pb qb rho gap (false, z)) = L.S i := by
  let x : X := Classical.choice inferInstance
  have hzi := (hL.2.2.2.2.2.1 x i z hi.2).mp hz
  have nonzero (w : Z) (hw : w ∈ L.S i) : w ∉ L.S 0 := by
    intro hw0
    have hwi := (hL.2.2.2.2.2.1 x i w hi.2).mp hw
    have he0 := (hL.2.2.2.2.2.1 x 0 w (Nat.zero_le _)).mp hw0
    have hs := hL.2.2.2.2.2.2.2.1 x 0 i (by omega) hi.2
    rw [← hwi, ← he0] at hs
    exact lt_irrefl _ hs
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hw
    obtain ⟨hwa, hpath⟩ := Finset.mem_filter.mp hw
    by_cases hiK : i < L.K
    · exact (recovery_path_nonterminal_baseline_class_closed M h q hq L hL hOff
        hlev gap hgap pb qb rho hactive hp hqr i ⟨hi.1, hiK⟩ z hz
        (false, w) hpath).2
    · obtain ⟨r, hr, hwr⟩ := finite_baseline_level_exists M q L hL x w
      have hwm := (hL.2.2.2.2.2.1 x r w hr).mpr hwr
      have hw0 : w ∉ L.S 0 := by
        apply (hactive w).mp
        simpa only [recoveryActive, Finset.mem_filter, Finset.mem_univ,
          Bool.false_eq_true, false_or, true_and] using hwa
      have hr0 : 1 ≤ r := by
        by_contra hn
        have he : r = 0 := by omega
        exact hw0 (he ▸ hwm)
      by_cases hrK : r < L.K
      · have hzr := (recovery_path_nonterminal_baseline_class_closed M h q hq L hL
          hOff hlev gap hgap pb qb rho hactive hp hqr r ⟨hr0, hrK⟩ w hwm
          (false, z) (recovery_path_reverse pb qb rho gap hpath)).2
        have he := (hL.2.2.2.2.2.1 x r z hr).mp hzr
        have hs := hL.2.2.2.2.2.2.2.1 x r i (by omega) hi.2
        rw [← hzi, ← he] at hs
        exact False.elim (lt_irrefl _ hs)
      · have he : r = i := by omega
        exact he ▸ hwm
  · intro hw
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
          hzi.trans ((hL.2.2.2.2.2.1 x i w hi.2).mp hw).symm⟩

omit hactive hp hqr in
-- @node: recovery_baseline_projections_failure_tendsto_zero
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, and propensity gap separation, suppose [the threshold tends to zero](hyp:hrho), [baseline marginal estimates converge in probability to their population means](hyp:hpconv), [policy marginal estimates do likewise](hyp:hqconv), and [threshold exceedances have measure tending to zero for every zero baseline mean](hyp:hzero). Then [the measure of samples for which any positive baseline class differs from the baseline projection of a full recovery component rooted at one of its members tends to zero](goal). -/
lemma recovery_baseline_projections_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (∀ i, (1 ≤ i ∧ i ≤ L.K) → ∀ z ∈ L.S i,
      Finset.univ.filter (fun w =>
        (false, w) ∈ recoveryComponent (pb n a) (qb n a) (rho n) gap (false, z)) =
          L.S i)}) atTop (𝓝 0) := by
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
  exact recoveryComponent_baseline_projection_eq M h q hq L hL hOff hlev gap hgap
    (pb n a) (qb n a) (rho n) ha (fun z => he (false, z)) (fun z => he (true, z))
    i hi z hzi

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_baseline_projections_failure_tendsto_zero
/-- Under threshold crossing, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, and measurability of baseline level functions, assume [an equal half sample split](hyp:hSplit), [training-sample measurability of the predictor](hyp:hTrain), [predictions between zero and one](hyp:hrange), [maximum first-stage L2 error negligible relative to sample size to the power minus one quarter](hyp:hRate), [a valid policy map](hyp:hphi), [its differentiability with the specified derivative](hyp:hd), [a bounded Lipschitz policy derivative](hyp:hDerivative), [invariant ordering for the transformed policy levels](hyp:hLphi), and [their propensity gap separation](hyp:hgapPhi). If [the threshold tends to zero](hyp:hrho) and [its product with the fourth root of sample size tends to infinity](hyp:hgrowth), then [along positive even sample sizes, the probability that any positive baseline class differs from the baseline projection of the fitted full recovery component rooted at any of its members tends to zero](goal). -/
lemma firstStageRate_baseline_projections_failure_tendsto_zero
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
    Tendsto (fun n => μ {a | ¬ (∀ i, (1 ≤ i ∧ i ≤ L.K) → ∀ z ∈ L.S i,
      Finset.univ.filter (fun w => (false, w) ∈
        recoveryComponent (pBar M S I₂ pHat (2 * (n + 1)) a)
        (pBar M S I₂ (fun n a => policyProp phi (pHat n a)) (2 * (n + 1)) a)
        (rho (2 * (n + 1))) gap (false, z)) = L.S i)}) atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_baseline_projections_failure_tendsto_zero M h
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
