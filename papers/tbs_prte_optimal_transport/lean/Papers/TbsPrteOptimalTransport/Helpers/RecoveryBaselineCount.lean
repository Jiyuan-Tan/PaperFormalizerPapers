module
public import Papers.TbsPrteOptimalTransport.Helpers.RecoveryBaselineProjection
/-! Counting the recovered positive baseline components.
The baseline projection gives a bijection between components containing baseline
vertices and the nonempty positive population classes, including the terminal class. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

-- @node: recoveryComponent_eq_of_mem
/-- If [a vertex belongs to the recovery component of another vertex](hyp:hb), then [the recovery components rooted at these two vertices are equal](goal). -/
lemma recoveryComponent_eq_of_mem {Z : Type*} [Fintype Z]
    (pb qb : Z → ℝ) (rho gap : ℝ) {a b : RecoveryVertex Z}
    (hb : b ∈ recoveryComponent pb qb rho gap a) :
    recoveryComponent pb qb rho gap b = recoveryComponent pb qb rho gap a := by
  have hab := (Finset.mem_filter.mp hb).2
  ext v
  simp only [recoveryComponent, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hbv⟩
    exact ⟨hv, hab.trans hbv⟩
  · rintro ⟨hv, hav⟩
    exact ⟨hv, (recovery_path_reverse pb qb rho gap hab).trans hav⟩

-- @node: recoveryComponents_eq_component_of_mem
/-- If [a set occurs in the list of recovered components](hyp:hC) and [a vertex belongs to that set](hyp:hv), then [the recovery component rooted at that vertex equals the set](goal). -/
lemma recoveryComponents_eq_component_of_mem {Z : Type*} [Fintype Z] [DecidableEq Z]
    (pb qb : Z → ℝ) (rho gap : ℝ) {C : Finset (RecoveryVertex Z)}
    (hC : C ∈ recoveryComponents pb qb rho gap) {v : RecoveryVertex Z} (hv : v ∈ C) :
    recoveryComponent pb qb rho gap v = C := by
  simp only [recoveryComponents, List.mem_mergeSort, Finset.mem_toList,
    Finset.mem_image] at hC
  obtain ⟨a, _, rfl⟩ := hC
  exact recoveryComponent_eq_of_mem pb qb rho gap hv

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

-- @node: recoveryComponents_baseline_projection_exists
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of every baseline level function, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, suppose [a set is a recovered component](hyp:hC) and [contains a baseline vertex](hyp:hB). Then [its baseline projection equals a population class with index between one and the number of positive baseline levels](goal). -/
lemma recoveryComponents_baseline_projection_exists
    {C : Finset (RecoveryVertex Z)} (hC : C ∈ recoveryComponents pb qb rho gap)
    (hB : ∃ z, (false, z) ∈ C) :
    ∃ i ∈ Finset.Icc 1 L.K,
      Finset.univ.filter (fun w => (false, w) ∈ C) = L.S i := by
  obtain ⟨z, hz⟩ := hB
  have he := recoveryComponents_eq_component_of_mem pb qb rho gap hC hz
  have hza := (Finset.mem_filter.mp (he.symm ▸ hz)).1
  have hn : z ∉ L.S 0 := by
    apply (hactive z).mp
    simpa only [recoveryActive, Finset.mem_filter, Finset.mem_univ,
      Bool.false_eq_true, false_or, true_and] using hza
  let x : X := Classical.choice inferInstance
  obtain ⟨i, hi, hzi⟩ := finite_baseline_level_exists M q L hL x z
  have hzm := (hL.2.2.2.2.2.1 x i z hi).mpr hzi
  have hi0 : 1 ≤ i := by
    by_contra hn0
    have he0 : i = 0 := by omega
    exact hn (he0 ▸ hzm)
  refine ⟨i, Finset.mem_Icc.mpr ⟨hi0, hi⟩, ?_⟩
  rw [← he]
  exact recoveryComponent_baseline_projection_eq M h q hq L hL hOff hlev gap hgap
    pb qb rho hactive hp hqr i ⟨hi0, hi⟩ z hzm

-- @node: recoveryComponents_baseline_projection_image
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, [the set of baseline projections of recovered components containing baseline vertices is exactly the set of positive population baseline classes, including the terminal class](goal). -/
lemma recoveryComponents_baseline_projection_image :
    (((recoveryComponents pb qb rho gap).filter
      (fun C => ∃ z, (false, z) ∈ C)).toFinset.image
        (fun C => Finset.univ.filter (fun w => (false, w) ∈ C))) =
      (Finset.Icc 1 L.K).image L.S := by
  ext B
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨C, ⟨hC, hB⟩, rfl⟩
    obtain ⟨i, hi, he⟩ := recoveryComponents_baseline_projection_exists
      M h q hq L hL hOff hlev gap hgap pb qb rho hactive hp hqr hC hB
    exact ⟨i, hi, he.symm⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' := Finset.mem_Icc.mp hi
    obtain ⟨z, hz⟩ := ordered_baseline_level_nonempty M q L hL i hi'
    let C := recoveryComponent pb qb rho gap (false, z)
    have he : Finset.univ.filter (fun w => (false, w) ∈ C) = L.S i :=
      recoveryComponent_baseline_projection_eq M h q hq L hL hOff hlev gap hgap
        pb qb rho hactive hp hqr i hi' z hz
    have hzc : (false, z) ∈ C := by
      have hz' := he.symm ▸ hz
      exact (Finset.mem_filter.mp hz').2
    refine ⟨C, ⟨?_, ⟨z, hzc⟩⟩, he⟩
    simp only [recoveryComponents, List.mem_mergeSort, Finset.mem_toList, Finset.mem_image]
    exact ⟨(false, z), (Finset.mem_filter.mp hzc).1, rfl⟩

-- @node: recoverLevelsAt_baseline_count_eq
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, propensity gap separation, exact threshold selection of nonzero baseline instruments, and baseline and policy marginal errors smaller than one quarter of the gap, [the recovered number of positive baseline levels equals the population number](goal). -/
lemma recoverLevelsAt_baseline_count_eq :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).K = L.K := by
  let Bs := (recoveryComponents pb qb rho gap).filter (fun C => ∃ z, (false, z) ∈ C)
  let proj := fun C : Finset (RecoveryVertex Z) =>
    Finset.univ.filter (fun w => (false, w) ∈ C)
  have hinj : Set.InjOn proj (↑Bs.toFinset) := by
    intro C hC D hD he
    have hC' : C ∈ recoveryComponents pb qb rho gap ∧ ∃ z, (false, z) ∈ C := by
      simpa only [Finset.mem_coe, Bs, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq] using hC
    have hD' : D ∈ recoveryComponents pb qb rho gap ∧ ∃ z, (false, z) ∈ D := by
      simpa only [Finset.mem_coe, Bs, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq] using hD
    obtain ⟨z, hz⟩ := hC'.2
    have hzd : (false, z) ∈ D := by
      have hz' : z ∈ proj C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      rw [he] at hz'
      exact (Finset.mem_filter.mp hz').2
    exact (recoveryComponents_eq_component_of_mem pb qb rho gap hC'.1 hz).symm.trans
      (recoveryComponents_eq_component_of_mem pb qb rho gap hD'.1 hzd)
  have hSinj : Set.InjOn L.S (↑(Finset.Icc 1 L.K)) := by
    intro i hi j hj he
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    obtain ⟨z, hz⟩ := ordered_baseline_level_nonempty M q L hL i hi'
    have hzj : z ∈ L.S j := he ▸ hz
    let x : X := Classical.choice inferInstance
    have hei := (hL.2.2.2.2.2.1 x i z hi'.2).mp hz
    have hej := (hL.2.2.2.2.2.1 x j z hj'.2).mp hzj
    rcases lt_trichotomy i j with hij | hij | hji
    · exact False.elim ((hL.2.2.2.2.2.2.2.1 x i j hij hj'.2).ne (hei.symm.trans hej))
    · exact hij
    · exact False.elim ((hL.2.2.2.2.2.2.2.1 x j i hji hi'.2).ne (hej.symm.trans hei))
  have hnodup : Bs.Nodup := by
    apply List.Nodup.filter
    unfold recoveryComponents
    exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  change Bs.length = L.K
  calc
    Bs.length = Bs.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = (Bs.toFinset.image proj).card := (Finset.card_image_iff.mpr hinj).symm
    _ = ((Finset.Icc 1 L.K).image L.S).card := congrArg Finset.card
      (recoveryComponents_baseline_projection_image M h q hq L hL hOff hlev gap hgap
        pb qb rho hactive hp hqr)
    _ = (Finset.Icc 1 L.K).card := Finset.card_image_iff.mpr hSinj
    _ = L.K := by simp

omit hactive hp hqr in
-- @node: recovery_baseline_count_failure_tendsto_zero
/-- Under threshold crossing, measurability of the policy propensity, invariant level ordering, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, measurability of baseline level functions, and propensity gap separation, suppose [the threshold tends to zero](hyp:hrho), [each fitted baseline marginal converges in probability to its population mean](hyp:hpconv), [each fitted policy marginal does likewise](hyp:hqconv), and [threshold exceedances have measure tending to zero whenever the population baseline mean is zero](hyp:hzero). Then [the measure of samples with an incorrect recovered number of positive baseline levels tends to zero](goal). -/
lemma recovery_baseline_count_failure_tendsto_zero
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
      (recoverLevelsAt (pb n a) (qb n a) (rho n) gap : LevelData Z X).K ≠ L.K})
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
  exact hbad (recoverLevelsAt_baseline_count_eq M h q hq L hL hOff hlev gap hgap
    (pb n a) (qb n a) (rho n) ha (fun z => he (false, z)) (fun z => he (true, z)))

omit q hq hL hgap hactive hp hqr in
-- @node: firstStageRate_baseline_count_failure_tendsto_zero
/-- Under threshold crossing, nonempty interior policy levels distinct from their lower baseline boundaries in every nonterminal bin, and measurability of baseline level functions, assume [an equal half sample split](hyp:hSplit), [training-sample measurability of the predictor](hyp:hTrain), [predictions between zero and one](hyp:hrange), [maximum first-stage L2 error negligible relative to sample size to the power minus one quarter](hyp:hRate), [a valid policy map](hyp:hphi), [its differentiability with the specified derivative](hyp:hd), [a bounded Lipschitz policy derivative](hyp:hDerivative), [invariant ordering for the transformed policy levels](hyp:hLphi), and [their propensity gap separation](hyp:hgapPhi). If [the threshold tends to zero](hyp:hrho) and [its product with the fourth root of sample size tends to infinity](hyp:hgrowth), then [along positive even sample sizes, the probability of an incorrect recovered number of positive baseline levels tends to zero](goal). -/
lemma firstStageRate_baseline_count_failure_tendsto_zero
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
      (recoveredData M S I₁ I₂ pHat phi rho gap (2 * (n + 1)) a).K ≠ L.K})
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hqphi : Measurable (Function.uncurry (policyProp phi M.prop)) := by fun_prop
  have hconv := firstStageRate_pBar_marginals_consistent M μ S I₁ I₂ hSplit h
    pHat hTrain hrange hRate phi dphi hphi hd hDerivative
  apply recovery_baseline_count_failure_tendsto_zero M h
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
