module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryBaselineOrder
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryComponentIndexing
/-! Exact indexing of recovered baseline components.
The component count and strict average order identify the sorted baseline list
with the population sequence, so its projections recover each indexed class. -/
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

-- @node: recoveryComponents_baseline_list_eq
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, choose [one representative from each positive baseline class](hyp:hrep). Then [the ordered list of recovered components containing baseline vertices equals the components rooted at these representatives in population level order](goal). -/
lemma recoveryComponents_baseline_list_eq
    (rep : ℕ → Z) (hrep : ∀ i, (1 ≤ i ∧ i ≤ L.K) → rep i ∈ L.S i) :
    (recoveryComponents pb qb rho gap).filter (fun C => ∃ z, (false, z) ∈ C) =
      (List.range L.K).map (fun i => recoveryComponent pb qb rho gap (false, rep (i + 1))) := by
  let Bs := (recoveryComponents pb qb rho gap).filter (fun C => ∃ z, (false, z) ∈ C)
  let f := fun i => recoveryComponent pb qb rho gap (false, rep (i + 1))
  have hself (i : ℕ) (hi : i < L.K) : (false, rep (i + 1)) ∈ f i :=
    recoveryComponent_positive_baseline_self_mem M q L hL gap pb qb rho hactive
      (i + 1) ⟨by omega, by omega⟩ _ (hrep _ ⟨by omega, by omega⟩)
  have hfmem (i : ℕ) (hi : i < L.K) : f i ∈ Bs := by
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa using (show ∃ z, (false, z) ∈ f i from ⟨_, hself i hi⟩)⟩
    simp only [recoveryComponents, List.mem_mergeSort, Finset.mem_toList, Finset.mem_image]
    exact ⟨(false, rep (i + 1)), (Finset.mem_filter.mp (hself i hi)).1, rfl⟩
  have hcover (C : Finset (RecoveryVertex Z)) (hC : C ∈ Bs) :
      ∃ i < L.K, f i = C := by
    have hC' : C ∈ recoveryComponents pb qb rho gap ∧ ∃ z, (false, z) ∈ C := by
      simpa only [Bs, List.mem_filter, decide_eq_true_eq] using hC
    obtain ⟨i, hi, he⟩ := recoveryComponents_baseline_projection_exists
      M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr hC'.1 hC'.2
    have hi' := Finset.mem_Icc.mp hi
    have hr : (false, rep i) ∈ C := by
      have hm := he.symm ▸ hrep i hi'
      exact (Finset.mem_filter.mp hm).2
    refine ⟨i - 1, by omega, ?_⟩
    have heq := recoveryComponents_eq_component_of_mem pb qb rho gap hC'.1 hr
    simpa only [f, Nat.sub_add_cancel hi'.1] using heq
  have hstrict : ((List.range L.K).map f).Pairwise
      (fun C D => componentAverage pb qb C < componentAverage pb qb D) := by
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
    intro i j hi hj hij
    exact recoveryComponent_baseline_average_strict_order M h q hq L hL hOff hlev
      gap hgap pb qb rho hactive hp hqr (i + 1) (j + 1) (by omega)
      (by omega) (by simpa using List.mem_range.mp hj) _ _
      (hrep _ ⟨by omega, by simpa using List.mem_range.mp hi⟩)
      (hrep _ ⟨by omega, by simpa using List.mem_range.mp hj⟩)
  have hnodup : Bs.Nodup := by
    apply List.Nodup.filter
    unfold recoveryComponents
    exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  have hncanon : ((List.range L.K).map f).Nodup :=
    hstrict.nodup
  have hperm : Bs.Perm ((List.range L.K).map f) := by
    apply (List.perm_ext_iff_of_nodup hnodup hncanon).mpr
    intro C
    constructor
    · intro hC
      obtain ⟨i, hi, he⟩ := hcover C hC
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, he⟩
    · intro hC
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hC
      exact hfmem i (List.mem_range.mp hi)
  apply List.Perm.eq_of_pairwise (le := fun C D =>
    componentAverage pb qb C ≤ componentAverage pb qb D) _
    ((recoveryComponents_pairwise_average_le pb qb rho gap).filter _) _ hperm
  · intro C D hC hD hCD hDC
    obtain ⟨i, hi, rfl⟩ := hcover C hC
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hD
    have hj' := List.mem_range.mp hj
    have ho := recoveryComponent_baseline_average_order_iff M h q hq L hL hOff
      hlev gap hgap pb qb rho hactive hp hqr (i + 1) (j + 1)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ _ _
      (hrep _ ⟨by omega, by omega⟩) (hrep _ ⟨by omega, by omega⟩)
    have hor := recoveryComponent_baseline_average_order_iff M h q hq L hL hOff
      hlev gap hgap pb qb rho hactive hp hqr (j + 1) (i + 1)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ _ _
      (hrep _ ⟨by omega, by omega⟩) (hrep _ ⟨by omega, by omega⟩)
    have he : i = j := by
      have hnij : ¬ i + 1 < j + 1 := fun ht => (not_lt_of_ge hDC) (ho.mpr ht)
      have hnji : ¬ j + 1 < i + 1 := fun ht => (not_lt_of_ge hCD) (hor.mpr ht)
      omega
    exact congrArg f he
  · exact hstrict.imp (fun hh => hh.le)

-- @node: recoverLevelsAt_positive_baseline_label_eq
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, let [the index range from one through the population number of positive baseline levels](hyp:hi). Then [the recovered baseline class at that index equals the population class at the same index](goal). -/
lemma recoverLevelsAt_positive_baseline_label_eq
    (i : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).S i = L.S i := by
  let rep : ℕ → Z := fun k => if hk : 1 ≤ k ∧ k ≤ L.K then
    Classical.choose (ordered_baseline_level_nonempty M q L hL k hk)
    else Classical.choice inferInstance
  have hrep : ∀ k, (1 ≤ k ∧ k ≤ L.K) → rep k ∈ L.S k := by
    intro k hk
    simpa only [rep, dif_pos hk] using
      Classical.choose_spec (ordered_baseline_level_nonempty M q L hL k hk)
  have hlist := recoveryComponents_baseline_list_eq M h q hq L hL hOff hlev gap hgap
    pb qb rho hactive hp hqr rep hrep
  have hget : ((List.range L.K).map (fun k =>
      recoveryComponent pb qb rho gap (false, rep (k + 1)))).getD (i - 1) ∅ =
      recoveryComponent pb qb rho gap (false, rep i) := by
    simp [List.getD, List.getElem?_map, List.getElem?_range (show i - 1 < L.K by omega),
      Nat.sub_add_cancel hi.1]
  change (if i = 0 then _ else _) = _
  rw [if_neg (by omega), hlist, hget]
  exact recoveryComponent_baseline_projection_eq M h q hq L hL hOff hlev gap hgap
    pb qb rho hactive hp hqr i hi _ (hrep i hi)

-- @node: recoverLevelsAt_baseline_labels_eq
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, [the recovered number of positive baseline levels is correct and every baseline class from zero through the terminal index equals its population counterpart](goal). -/
lemma recoverLevelsAt_baseline_labels_eq :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).K = L.K ∧
    ∀ i ≤ L.K, (recoverLevelsAt pb qb rho gap : LevelData Z X).S i = L.S i := by
  refine ⟨recoverLevelsAt_baseline_count_eq M h q hq L hL hOff hlev gap hgap
    pb qb rho hactive hp hqr, ?_⟩
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    change Finset.univ.filter (fun z => pb z ≤ rho) = L.S 0
    ext z
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, not_not] using
      not_congr (hactive z)
  · exact recoverLevelsAt_positive_baseline_label_eq M h q hq L hL hOff hlev gap hgap
      pb qb rho hactive hp hqr i ⟨by omega, hi⟩

omit hactive hp hqr in
-- @node: recovery_baseline_labels_failure_tendsto_zero
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, and propensity gap separation, suppose [the threshold tends to zero](hyp:hrho), [baseline marginal estimates converge in probability to their population means](hyp:hpconv), [policy marginal estimates converge in probability to their population means](hyp:hqconv), and [threshold exceedances have measure tending to zero for every zero baseline mean](hyp:hzero). Then [the measure of samples with an incorrect baseline level count or any incorrect indexed baseline class, including the zero class, tends to zero](goal). -/
lemma recovery_baseline_labels_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (𝓝 0))
    (hpconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => pb n a z) atTop (fun _ _ => ∫ x, M.prop z x ∂xLaw M))
    (hqconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) atTop (fun _ _ => ∫ x, q z x ∂xLaw M))
    (hzero : ∀ z, (∫ x, M.prop z x ∂xLaw M) = 0 →
      Tendsto (fun n => μ {a | rho n < pb n a z}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {a |
      ¬ ((recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).K = L.K ∧
        ∀ i ≤ L.K, (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).S i = L.S i)})
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
  exact hbad (recoverLevelsAt_baseline_labels_eq M h q hq L hL hOff hlev gap hgap
    (pb n a) (qb n a) (rho n) ha (fun z => he (false, z)) (fun z => he (true, z)))

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_baseline_labels_failure_tendsto_zero
/-- Under threshold crossing, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, and measurability of baseline level functions, assume [an equal half sample split](hyp:hSplit), [training-sample measurability of the predictor](hyp:hTrain), [predictions between zero and one](hyp:hrange), [maximum first-stage L2 error negligible relative to sample size to the power minus one quarter](hyp:hRate), [a valid policy map](hyp:hphi), [its differentiability with the specified derivative](hyp:hd), [a bounded Lipschitz policy derivative](hyp:hDerivative), [invariant ordering for the transformed policy levels](hyp:hLphi), and [their propensity gap separation](hyp:hgapPhi). If [the threshold tends to zero](hyp:hrho) and [its product with the fourth root of sample size tends to infinity](hyp:hgrowth), then [along positive even sample sizes, the probability of an incorrect baseline level count or any incorrect indexed baseline class from zero through the terminal level tends to zero](goal). -/
lemma firstStageRate_baseline_labels_failure_tendsto_zero
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
    Tendsto (fun n => μ {a |
      ¬ ((recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).K = L.K ∧
        ∀ i ≤ L.K, (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).S i = L.S i)})
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_baseline_labels_failure_tendsto_zero M h
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
