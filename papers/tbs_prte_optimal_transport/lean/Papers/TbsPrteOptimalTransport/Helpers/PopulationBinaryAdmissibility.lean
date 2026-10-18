module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryScoreMean
/-! Population probability ranges and admissibility of the binary nuisance vector. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_instrument_set_probability_measurable
/-- [The conditional probability of any finite set of instrument values is a measurable
function of the covariates](goal). -/
@[fun_prop] lemma population_instrument_set_probability_measurable (C : Finset Z) :
    Measurable (fun x => ∑ z ∈ C, instProb M z x) := by
  first
  | fun_prop
  | apply Finset.measurable_sum
    intro z hz
    exact (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal

-- @node: population_instrument_set_probability_range
/-- [The conditional probability of a finite set of instrument values lies between zero
and one at every covariate value](goal). -/
lemma population_instrument_set_probability_range (C : Finset Z) (x : X) :
    (∑ z ∈ C, instProb M z x) ∈ Icc (0 : ℝ) 1 := by
  haveI := M.instKernel_markov
  change (∑ z ∈ C, (M.instKernel x).real {z}) ∈ Icc (0 : ℝ) 1
  rw [sum_measureReal_singleton]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

-- @node: population_levelShares_range
/-- [Each instrument's population share within a policy level lies between zero and one
at every covariate value](goal). -/
lemma population_levelShares_range (L : LevelData Z X) (k j : ℕ) (z : Z) (x : X) :
    levelShares M L k j z x ∈ Icc (0 : ℝ) 1 := by
  unfold levelShares
  split_ifs with hz
  · have hnonneg : ∀ z, 0 ≤ instProb M z x := fun _ => ENNReal.toReal_nonneg
    have hle : instProb M z x ≤ ∑ w ∈ L.T k j, instProb M w x :=
      Finset.single_le_sum (fun w _ => hnonneg w) hz
    change instProb M z x / (∑ w ∈ L.T k j, instProb M w x) ∈ Icc (0 : ℝ) 1
    exact ⟨div_nonneg (hnonneg z) (Finset.sum_nonneg (fun w _ => hnonneg w)),
      div_le_one_of_le₀ hle (Finset.sum_nonneg (fun w _ => hnonneg w))⟩
  · exact ⟨le_rfl, zero_le_one⟩

-- @node: population_binary_joint_kernel_range
/-- If [the outcome is binary almost surely](hyp:hy), then [for almost every covariate
value, the product of outcome and treatment lies between zero and one almost surely
under their joint conditional distribution with the instrument](goal). -/
lemma population_binary_joint_kernel_range (hy : OutcomeBinaryAE M) :
    ∀ᵐ x ∂xLaw M, ∀ᵐ a : ℝ × ℝ × Z
      ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x,
      a.1 * a.2.1 ∈ Icc (0 : ℝ) 1 := by
  have hj := M.measY.prodMk (M.measW.prodMk M.measZ)
  have hm := M.measX.prodMk hj
  have hs : MeasurableSet {p : X × (ℝ × ℝ × Z) |
      p.2.1 * p.2.2.1 ∈ Icc (0 : ℝ) 1} := by
    exact measurableSet_Icc.preimage (by fun_prop)
  have hr : ∀ᵐ p : X × (ℝ × ℝ × Z)
      ∂(M.law.toMeasure.map (fun s => (M.Xv s, M.Y s, M.W s, M.Zv s))),
      p.2.1 * p.2.2.1 ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hm.aemeasurable hs).2
    filter_upwards [hy] with s hs
    rcases hs with hs | hs <;> rcases M.rangeW s with hw | hw <;> simp [hs, hw]
  rw [← compProd_map_condDistrib hj.aemeasurable] at hr
  exact Measure.ae_ae_of_ae_compProd hr

-- @node: population_treatedSuccess_range
/-- If [the outcome is binary almost surely](hyp:hy), then [the population treated-success
average in any baseline level lies between zero and one for almost every covariate
value](goal). -/
lemma population_treatedSuccess_range (hy : OutcomeBinaryAE M) (L : LevelData Z X)
    (k : ℕ) : ∀ᵐ x ∂xLaw M, treatedSuccess M L k x ∈ Icc (0 : ℝ) 1 := by
  by_cases hk : k = 0
  · subst k
    simp only [treatedSuccess, if_pos rfl]
    exact Filter.Eventually.of_forall (fun _ => ⟨le_rfl, zero_le_one⟩)
  filter_upwards [population_binary_joint_kernel_range M hy] with x hx
  let joint := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
  let sel := joint.restrict {a : ℝ × ℝ × Z | a.2.2 ∈ (L.S k : Set Z)}
  have hr : ∀ᵐ a ∂sel, a.1 * a.2.1 ∈ Icc (0 : ℝ) 1 :=
    hx.filter_mono (ae_mono Measure.restrict_le_self)
  have hi : Integrable (fun a : ℝ × ℝ × Z => a.1 * a.2.1) sel := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hr] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg ha.1] using ha.2
  have hlo : 0 ≤ ∫ a : ℝ × ℝ × Z, a.1 * a.2.1 ∂sel :=
    integral_nonneg_of_ae (hr.mono (fun _ ha => ha.1))
  have hhi : (∫ a : ℝ × ℝ × Z, a.1 * a.2.1 ∂sel) ≤ sel.real univ := by
    calc
      _ ≤ ∫ _ : ℝ × ℝ × Z, (1 : ℝ) ∂sel :=
        integral_mono_ae hi (integrable_const _) (hr.mono (fun _ ha => ha.2))
      _ = sel.real univ := by simp
  simp only [treatedSuccess, if_neg hk]
  change (sel univ).toReal⁻¹ * (∫ a, a.1 * a.2.1 ∂sel) ∈ Icc (0 : ℝ) 1
  rw [← div_eq_inv_mul]
  exact ⟨div_nonneg hlo ENNReal.toReal_nonneg,
    div_le_one_of_le₀ hhi ENNReal.toReal_nonneg⟩

-- @node: ordered_baseline_level_nonempty
/-- If [the baseline and policy propensity levels obey the specified invariant ordering](hyp:hL)
and [the baseline level index is between one and the number of levels](hyp:hk), then
[that baseline level contains at least one instrument value](goal). -/
lemma ordered_baseline_level_nonempty (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) :
    (L.S k).Nonempty := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hi : k - 1 < (finiteLevels (fun z => M.prop z x)).length := by
    rw [hL.2.2.2.1 x]
    omega
  have hm : L.pLev k x ∈ finiteLevels (fun z => M.prop z x) := by
    rw [hL.1 x k (by omega), pLevel, if_neg (by omega),
      if_pos (by rw [hL.2.2.2.1 x]; exact hk.2), List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  obtain ⟨⟨z, hz⟩, _⟩ := finiteLevels_mem _ (inferInstance : Finite Z) hm
  exact ⟨z, (hL.2.2.2.2.2.1 x k z hk.2).mpr hz⟩

-- @node: ordered_baseline_level_measurable
/-- Under [the threshold-crossing assumptions](hyp:h), if [the baseline and policy levels
obey the specified invariant ordering](hyp:hL) and [the baseline index is between one
and the number of levels](hyp:hk), then [its baseline propensity level is measurable
in the covariates](goal). -/
@[fun_prop] lemma ordered_baseline_level_measurable (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) : Measurable (L.pLev k) := by
  obtain ⟨z, hz⟩ := ordered_baseline_level_nonempty M q L hL k hk
  have heq : L.pLev k = M.prop z := by
    funext x
    exact ((hL.2.2.2.2.2.1 x k z hk.2).mp hz).symm
  rw [heq]
  exact h.2.1.comp (measurable_const.prodMk measurable_id)

-- @node: population_LevelStructure_baseline_measurable
/-- Under [the threshold-crossing assumptions](hyp:h), if [the level structure constructed
at the reference covariate value has an invariant baseline and policy ordering](hyp:hL),
then [every baseline propensity level in that structure is measurable in the covariates](goal). -/
@[fun_prop] lemma population_LevelStructure_baseline_measurable (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (x0 : X)
    (hL : LevelOrderInvariant M.prop q (LevelStructure M.prop q x0)) (k : ℕ) :
    Measurable ((LevelStructure M.prop q x0).pLev k) := by
  by_cases hk0 : k = 0
  · subst k
    have heq : (LevelStructure M.prop q x0).pLev 0 = fun _ => (0 : ℝ) := by
      funext x
      simp [LevelStructure, pLevel]
    rw [heq]
    fun_prop
  by_cases hk : k ≤ (LevelStructure M.prop q x0).K
  · exact ordered_baseline_level_measurable M h q _ hL k ⟨by omega, hk⟩
  · have heq : (LevelStructure M.prop q x0).pLev k = fun _ => (1 : ℝ) := by
      funext x
      have hlen := hL.2.2.2.1 x
      change pLevel (finiteLevels (fun z => M.prop z x)) k = 1
      rw [pLevel, if_neg hk0, if_neg (by omega)]
    rw [heq]
    fun_prop

-- @node: population_binary_nuisance_admissible
/-- Under [threshold crossing](hyp:h) and [an almost surely binary outcome](hyp:hy), suppose
[baseline and policy levels have an invariant ordering](hyp:hOrder), [all baseline
propensity levels are measurable](hyp:hlev), and [policy overlap holds with the given
constant](hyp:hov). Then [the population binary nuisance vector satisfies all binary
admissibility requirements](goal). -/
lemma population_binary_nuisance_admissible (h : ThresholdCrossing M)
    (hy : OutcomeBinaryAE M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ) (hov : PolicyOverlap M L cpi) :
    BinAdmissible M L (eta0Bin M L) := by
  have hm : ∀ C : Finset Z, Measurable (fun x => ∑ z ∈ C, instProb M z x) :=
    population_instrument_set_probability_measurable M
  have hr := population_instrument_set_probability_range M
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact Filter.Eventually.of_forall (fun x => M.rangeProp z x)
  · intro z
    exact h.2.1.comp (measurable_const.prodMk measurable_id)
  · intro k
    filter_upwards [population_treatedSuccess_range M hy L k] with x hx
    exact ⟨hOrder.2.2.2.2.2.2.2.2.2.2.1 x k (by omega), hx, hr (L.S k) x⟩
  · intro k
    exact ⟨hlev k, treatedSuccess_measurable M L k, hm (L.S k)⟩
  · intro a
    exact Filter.Eventually.of_forall (fun x => ⟨hr (L.T a.val.1 a.val.2) x,
      hr (policyUnion L a.val.1 a.val.2) x⟩)
  · intro a
    exact ⟨hm (L.T a.val.1 a.val.2), hm (policyUnion L a.val.1 a.val.2)⟩
  · intro a z
    exact Filter.Eventually.of_forall (population_levelShares_range M L a.val.1 a.val.2 z)
  · intro a z
    exact population_levelShares_measurable M L a.val.1 a.val.2 z
  · intro a
    apply Filter.Eventually.of_forall
    intro x
    refine ⟨population_policy_level_shares_sum_one M q L hOrder cpi hov
      a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2 x, ?_⟩
    intro z hz
    simp only [eta0Bin, levelShares, if_neg hz]
  · intro k
    apply Filter.Eventually.of_forall
    intro x
    have hp := hr (higherPolicy L k) x
    have hb := hr (higherBaseline L k) x
    change (∑ z ∈ higherPolicy L k, instProb M z x) -
      (∑ z ∈ higherBaseline L k, instProb M z x) ∈ Icc (-1 : ℝ) 1
    constructor <;> linarith [hp.1, hp.2, hb.1, hb.2]
  · intro k
    exact (hm (higherPolicy L k)).sub (hm (higherBaseline L k))
  · exact Filter.Eventually.of_forall (hr (policyUnion L L.K 1))
  · exact hm (policyUnion L L.K 1)

end Papers.TbsPrteOptimalTransport
