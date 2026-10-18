module
public import Papers.TbsPrteOptimalTransport.Helpers.LevelMarginalBaselineIdentification
public import Papers.TbsPrteOptimalTransport.Helpers.LevelZeroRecovery
/-! Recovery of the positive baseline classes by the baseline subgraph.
Structural zeros are removed before using the gap; no gap from zero is required. -/
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
variable (M : LatentIVModel Ω X Z)

-- @node: positive_baseline_recovery_close_iff_pointwise_equal
/-- Under [threshold crossing](hyp:h), [invariant ordering of the baseline and policy levels](hyp:hL), and [separation by the propensity gap](hyp:hgap), suppose [the first instrument is outside the zero baseline class](hyp:hz), [the second is also outside that class](hyp:hw), and [their fitted baseline marginals each have error less than one quarter of the gap](hyp:hpz,hpw). Then [their fitted marginals differ by less than half the gap if and only if their population baseline propensities agree at the given covariate value](goal). -/
lemma positive_baseline_recovery_close_iff_pointwise_equal (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
    (pb : Z → ℝ) (x : X) (z w : Z) (hz : z ∉ L.S 0) (hw : w ∉ L.S 0)
    (hpz : |pb z - ∫ t, M.prop z t ∂xLaw M| < gap / 4)
    (hpw : |pb w - ∫ t, M.prop w t ∂xLaw M| < gap / 4) :
    |pb z - pb w| < gap / 2 ↔ M.prop z x = M.prop w x := by
  obtain ⟨i, hi, hzi⟩ := finite_baseline_level_exists M q L hL x z
  obtain ⟨j, hj, hwj⟩ := finite_baseline_level_exists M q L hL x w
  have hzm := (hL.2.2.2.2.2.1 x i z hi).mpr hzi
  have hwm := (hL.2.2.2.2.2.1 x j w hj).mpr hwj
  have hi0 : 1 ≤ i := by
    by_contra hn
    have he : i = 0 := by omega
    exact hz (he ▸ hzm)
  have hj0 : 1 ≤ j := by
    by_contra hn
    have he : j = 0 := by omega
    exact hw (he ▸ hwm)
  rw [baseline_recovery_close_iff_same_level M h q L hL gap hgap
    i j ⟨hi0, hi⟩ ⟨hj0, hj⟩ z w hzm hwm pb hpz hpw]
  exact (population_baseline_class_marginal_equal_iff M h q L hL gap hgap
    i j ⟨hi0, hi⟩ ⟨hj0, hj⟩ z w hzm hwm).symm.trans
    (population_baseline_marginal_eq_iff_pointwise M h q L hL gap hgap x z w)

-- @node: baseline_recoveryEdge_iff_pointwise_equal
/-- Under [threshold crossing](hyp:h), [invariant level ordering](hyp:hL), and [propensity gap separation](hyp:hgap), assume [thresholding selects exactly the instruments outside the zero baseline class](hyp:hactive) and [every fitted baseline marginal has error less than one quarter of the gap](hyp:herr). Then [two baseline vertices share a recovery edge exactly when both instruments are outside the zero class, are distinct, and have equal population baseline propensities at the given covariate value](goal). -/
lemma baseline_recoveryEdge_iff_pointwise_equal (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
    (pb qb : Z → ℝ) (rho : ℝ) (x : X) (z w : Z)
    (hactive : ∀ t, rho < pb t ↔ t ∉ L.S 0)
    (herr : ∀ t, |pb t - ∫ s, M.prop t s ∂xLaw M| < gap / 4) :
    recoveryEdge pb qb rho gap (false, z) (false, w) ↔
      z ∉ L.S 0 ∧ w ∉ L.S 0 ∧ z ≠ w ∧ M.prop z x = M.prop w x := by
  have hn : (false, z) ≠ (false, w) ↔ z ≠ w :=
    ⟨fun hh he => hh (congrArg (fun t : Z => (false, t)) he),
      fun hh he => hh (congrArg Prod.snd he)⟩
  simp only [recoveryEdge, recoveryActive, Finset.mem_filter, Finset.mem_univ,
    Bool.false_eq_true, false_or, true_and, vertexValue, if_false, hn, hactive]
  constructor
  · rintro ⟨hz, hw, hne, hc⟩
    exact ⟨hz, hw, hne, (positive_baseline_recovery_close_iff_pointwise_equal
      M h q L hL gap hgap pb x z w hz hw (herr z) (herr w)).mp hc⟩
  · rintro ⟨hz, hw, hne, he⟩
    exact ⟨hz, hw, hne, (positive_baseline_recovery_close_iff_pointwise_equal
      M h q L hL gap hgap pb x z w hz hw (herr z) (herr w)).mpr he⟩

-- @node: baseline_recovery_path_iff_pointwise_equal
/-- Under [threshold crossing](hyp:h), [invariant level ordering](hyp:hL), [propensity gap separation](hyp:hgap), [exact threshold selection of the nonzero baseline instruments](hyp:hactive), and [baseline marginal errors smaller than one quarter of the gap](hyp:herr), take [two instruments outside the zero baseline class](hyp:hz,hw). Then [a path using only baseline recovery edges connects them, allowing a path of length zero, if and only if their population baseline propensities agree at the given covariate value](goal). -/
lemma baseline_recovery_path_iff_pointwise_equal (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
    (pb qb : Z → ℝ) (rho : ℝ) (x : X)
    (hactive : ∀ t, rho < pb t ↔ t ∉ L.S 0)
    (herr : ∀ t, |pb t - ∫ s, M.prop t s ∂xLaw M| < gap / 4)
    (z w : Z) (hz : z ∉ L.S 0) (hw : w ∉ L.S 0) :
    Relation.ReflTransGen (fun a b => recoveryEdge pb qb rho gap (false, a) (false, b))
      z w ↔ M.prop z x = M.prop w x := by
  constructor
  · intro hp
    induction hp with
    | refl => rfl
    | @tail b c _ hbc ih =>
      have he := (baseline_recoveryEdge_iff_pointwise_equal M h q L hL gap hgap
        pb qb rho x b c hactive herr).mp hbc
      exact (ih he.1).trans he.2.2.2
  · intro he
    by_cases hzw : z = w
    · subst w
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        ((baseline_recoveryEdge_iff_pointwise_equal M h q L hL gap hgap
          pb qb rho x z w hactive herr).mpr ⟨hz, hw, hzw, he⟩)

-- @node: baseline_recovery_path_class_eq
/-- Under [threshold crossing](hyp:h), [invariant level ordering](hyp:hL), [propensity gap separation](hyp:hgap), [exact selection of nonzero baseline instruments](hyp:hactive), and [baseline marginal errors smaller than one quarter of the gap](hyp:herr), let [the level index range from one through the number of positive baseline levels](hyp:hk) and [the starting instrument belong to that level](hyp:hz). Then [the nonzero baseline instruments reachable from it using baseline edges are exactly its population baseline class](goal). -/
lemma baseline_recovery_path_class_eq (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
    (pb qb : Z → ℝ) (rho : ℝ)
    (hactive : ∀ t, rho < pb t ↔ t ∉ L.S 0)
    (herr : ∀ t, |pb t - ∫ s, M.prop t s ∂xLaw M| < gap / 4)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) (z : Z) (hz : z ∈ L.S k) :
    (Finset.univ.filter (fun w => w ∉ L.S 0)).filter (fun w => Relation.ReflTransGen
      (fun a b => recoveryEdge pb qb rho gap (false, a) (false, b)) z w) = L.S k := by
  let x : X := Classical.choice inferInstance
  have hez := (hL.2.2.2.2.2.1 x k z hk.2).mp hz
  have nonzero (t : Z) (ht : t ∈ L.S k) : t ∉ L.S 0 := by
    intro hzero
    have he := (hL.2.2.2.2.2.1 x k t hk.2).mp ht
    have he0 := (hL.2.2.2.2.2.1 x 0 t (Nat.zero_le _)).mp hzero
    have hs := hL.2.2.2.2.2.2.2.1 x 0 k (by omega) hk.2
    rw [← he, ← he0] at hs
    exact lt_irrefl _ hs
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, hp⟩
    have he := (baseline_recovery_path_iff_pointwise_equal M h q L hL gap hgap
      pb qb rho x hactive herr z w (nonzero z hz) hw).mp hp
    exact (hL.2.2.2.2.2.1 x k w hk.2).mpr (he.symm.trans hez)
  · intro hw
    refine ⟨nonzero w hw, ?_⟩
    apply (baseline_recovery_path_iff_pointwise_equal M h q L hL gap hgap
      pb qb rho x hactive herr z w (nonzero z hz) (nonzero w hw)).mpr
    exact hez.trans ((hL.2.2.2.2.2.1 x k w hk.2).mp hw).symm

-- @node: baseline_recovery_path_classes_failure_tendsto_zero
/-- Under [threshold crossing](hyp:h), [invariant level ordering](hyp:hL), and [propensity gap separation](hyp:hgap), suppose [the threshold tends to zero](hyp:hrho), [each fitted baseline marginal converges in probability to its population mean](hyp:hconv), and [the measure of threshold exceedances tends to zero for each instrument with zero population baseline mean](hyp:hzero). Then [the measure of samples for which any positive baseline class fails to equal the threshold-active instruments reachable from any of its members using baseline edges tends to zero](goal). -/
lemma baseline_recovery_path_classes_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ t, M.prop z t ∂xLaw M))
    (hzero : ∀ z, (∫ t, M.prop z t ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a | ¬ (∀ k, (1 ≤ k ∧ k ≤ L.K) → ∀ z ∈ L.S k,
      (Finset.univ.filter (fun w => rho n < pb n a w)).filter (fun w =>
        Relation.ReflTransGen (fun v u => recoveryEdge (pb n a) (qb n a)
          (rho n) gap (false, v) (false, u)) z w) = L.S k)}) atTop (𝓝 0) := by
  have hz := recovery_zero_class_failure_tendsto_zero μ pb
    (fun z => ∫ t, M.prop z t ∂xLaw M)
    (fun z => integral_nonneg (fun t => (M.rangeProp z t).1)) rho hrho hconv hzero
  have herr := finite_marginal_errors_tendsto_zero μ pb
    (fun z => ∫ t, M.prop z t ∂xLaw M) hconv (gap / 4) (by linarith [hgap.1])
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
        Finset.univ.filter (fun z => (∫ t, M.prop z t ∂xLaw M) = 0) ∧
      ¬ ∃ z, gap / 4 ≤ |pb n a z - ∫ t, M.prop z t ∂xLaw M| := by
    simpa only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] using hn
  have hactive (z : Z) : rho n < pb n a z ↔ z ∉ L.S 0 := by
    have he := Finset.ext_iff.mp hg.1 z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [population_baseline_marginal_zero_iff M h q L hL z] at he
    exact (not_le).symm.trans (not_congr he)
  have he (z : Z) : |pb n a z - ∫ t, M.prop z t ∂xLaw M| < gap / 4 :=
    lt_of_not_ge (fun hh => hg.2 ⟨z, hh⟩)
  apply hbad
  intro k hk z hzk
  have hfilter : Finset.univ.filter (fun w => rho n < pb n a w) =
      Finset.univ.filter (fun w => w ∉ L.S 0) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hactive]
  rw [hfilter]
  exact baseline_recovery_path_class_eq M h q L hL gap hgap
    (pb n a) (qb n a) (rho n) hactive he k hk z hzk

-- @node: firstStageRate_baseline_path_classes_failure_tendsto_zero
/-- With [an equal half sample split](hyp:hSplit), [threshold crossing](hyp:h), [a predictor measurable with respect to the training sample](hyp:hTrain), [predictions between zero and one](hyp:hrange), and [maximum first-stage L2 error negligible relative to sample size to the power minus one quarter](hyp:hRate), assume [invariant ordering of baseline and transformed policy levels](hyp:hL), [propensity gap separation for those levels](hyp:hgap), [a threshold tending to zero](hyp:hrho), and [a threshold times the fourth root of sample size tending to infinity](hyp:hgrowth). Then [along positive even sample sizes, the probability that any positive baseline class differs from the active instruments reachable from one of its members using fitted baseline edges tends to zero](goal). -/
lemma firstStageRate_baseline_path_classes_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂) (h : ThresholdCrossing M)
    (pHat : ℕ → A → Z → X → ℝ)
    (hTrain : TrainingPredictorMeasurable M S I₁
      (fun n a (zx : Z × X) => pHat n a zx.1 zx.2))
    (hrange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (hRate : FiniteFirstStageRate M μ pHat) (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (rho : ℕ → ℝ) (hrho : Tendsto rho atTop (𝓝 0))
    (hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) * rho n) atTop atTop) :
    Tendsto (fun n => μ {a | ¬ (∀ k, (1 ≤ k ∧ k ≤ L.K) → ∀ z ∈ L.S k,
      (Finset.univ.filter (fun w => rho (2 * (n + 1)) <
        pBar M S I₂ pHat (2 * (n + 1)) a w)).filter (fun w =>
        Relation.ReflTransGen (fun v u => recoveryEdge
          (pBar M S I₂ pHat (2 * (n + 1)) a)
          (pBar M S I₂ (fun m b => policyProp phi (pHat m b)) (2 * (n + 1)) a)
          (rho (2 * (n + 1))) gap (false, v) (false, u)) z w) = L.S k)})
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hrate := firstStageRate_pBar_baseline_quarter_rate M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate
  apply baseline_recovery_path_classes_failure_tendsto_zero M μ h
    (policyProp phi M.prop) L hL gap hgap _ _ _ (hrho.comp hindex)
  · intro z
    have hc := dml_quarter_rate_tendsto_probability_zero μ _ (hrate z)
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm] at hc ⊢
    simpa only [sub_zero] using hc
  · intro z hz
    have he := hrate z
    simp only [hz, sub_zero] at he
    exact littleOp_threshold_exceedance_tendsto_zero μ _ _ _ he
      (recovery_threshold_dominates_quarter_rate rho hgrowth)

end Papers.TbsPrteOptimalTransport
