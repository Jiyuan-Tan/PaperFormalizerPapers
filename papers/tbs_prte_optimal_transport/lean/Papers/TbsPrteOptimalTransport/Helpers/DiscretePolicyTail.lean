module
public import Papers.TbsPrteOptimalTransport.Helpers.DiscreteIV
public import Papers.TbsPrteOptimalTransport.Helpers.FiniteRangeReduction
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedReduction
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedBoundary
/-! Finite conditional policy weights and their observable tail contribution. -/
public section
set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: finite_policy_weight_sum
/-- [The policy weight at a covariate value and latent rank equals the sum over instrument
values of their conditional probabilities times the difference between the policy and
baseline treatment indicators](goal). -/
lemma finite_policy_weight_sum (q : Z → X → ℝ) (x : X) (t : ℝ) :
    policyWeight M q x t = ∑ z, instProb M z x *
      ((if t ≤ q z x then 1 else 0) - (if t ≤ M.prop z x then 1 else 0)) := by
  letI : IsMarkovKernel M.instKernel := M.instKernel_markov
  have hm : Measurable (fun z =>
      ((if t ≤ q z x then 1 else 0) - (if t ≤ M.prop z x then 1 else 0) : ℝ)) := by
    fun_prop
  have hi : Integrable (fun z =>
      ((if t ≤ q z x then 1 else 0) - (if t ≤ M.prop z x then 1 else 0) : ℝ))
      (M.instKernel x) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with z
    split_ifs <;> norm_num
  simpa only [policyWeight, integral_fintype hi, instProb, Measure.real,
    smul_eq_mul]

-- @node: finite_last_baseline_supremum
/-- [The last level in the finite list of baseline propensity scores equals their supremum
over instrument values at the given covariate value](goal). -/
lemma finite_last_baseline_supremum (x : X) :
    pLevel (finiteLevels (fun z => M.prop z x))
      (finiteLevels (fun z => M.prop z x)).length = pHigh M.prop x := by
  let ps := finiteLevels (fun z => M.prop z x)
  have hp := finite_levels_ranges (fun z => M.prop z x) (fun z => M.rangeProp z x)
    (inferInstance : Finite Z)
  have hupper (z : Z) : M.prop z x ≤ pLevel ps ps.length := by
    by_cases hz : M.prop z x = 0
    · rw [hz]
      exact (hp.1 ps.length (by dsimp only [ps]; omega)).1
    · have hm : M.prop z x ∈ ps := (finiteLevels_mem_iff _ (inferInstance : Finite Z) _).mpr
        ⟨mem_range_self z, lt_of_le_of_ne (M.rangeProp z x).1 (Ne.symm hz)⟩
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
      have hn : ps.length ≠ 0 := by omega
      have hlast : ps.length - 1 < ps.length := by omega
      have hle := (finiteLevels_sorted (fun z => M.prop z x) (inferInstance : Finite Z)).strictMono_get.monotone
        (show (⟨i, hi⟩ : Fin ps.length) ≤ ⟨ps.length - 1, hlast⟩ by simp only [Fin.le_def]; omega)
      change ps[i] ≤ ps[ps.length - 1] at hle
      rw [he] at hle
      simpa only [pLevel, if_neg hn, if_pos le_rfl, List.getD_eq_getElem _ _ hlast] using hle
  unfold pHigh
  apply le_antisymm
  · by_cases hn : ps.length = 0
    · have hz := hupper (Classical.arbitrary Z)
      have hzero : pLevel ps ps.length = 0 := by simp [pLevel, hn]
      rw [hzero]
      exact (M.rangeProp (Classical.arbitrary Z) x).1.trans (le_csSup ⟨1, by
        rintro y ⟨z, rfl⟩; exact (M.rangeProp z x).2⟩ (mem_range_self (Classical.arbitrary Z)))
    · have hlast : ps.length - 1 < ps.length := by omega
      have hm := finiteLevels_mem (fun z => M.prop z x) (inferInstance : Finite Z)
        (List.getElem_mem hlast)
      have he : pLevel ps ps.length = ps[ps.length - 1] := by
        simp only [pLevel, if_neg hn, if_pos le_rfl, List.getD_eq_getElem _ _ hlast]
      rw [he]
      exact le_csSup ⟨1, by rintro y ⟨z, rfl⟩; exact (M.rangeProp z x).2⟩ hm.1
  · exact csSup_le (range_nonempty _) (by rintro y ⟨z, rfl⟩; exact hupper z)

-- @node: final_policy_union_membership
/-- If [the baseline and policy propensity levels obey the common ordering recorded by the
level data](hyp:hL), then [an instrument value belongs to the final policy union exactly
when its policy propensity is at least the last baseline level](goal). -/
lemma final_policy_union_membership (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (z : Z) :
    z ∈ policyUnion L L.K 1 ↔ L.pLev L.K x ≤ q z x := by
  rcases hL with ⟨hbase, hpolicy, hboundary, hcount, hlength, hS, hT,
    hstrict, hqstrict, hinputs, hpRange, hqRange⟩
  have hmem : q z x ∈ policyLevelsAt M.prop q x L.K ↔ L.pLev L.K x ≤ q z x := by
    simp only [policyLevelsAt, Finset.mem_sort, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and, hcount x, lt_self_iff_false,
      if_false]
    rw [← hbase x L.K (by omega)]
    have hend : pLevel (finiteLevels (fun z => M.prop z x)) (L.K + 1) = 1 := by
      simp only [pLevel, hcount x, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, if_false, Nat.not_succ_le_self]
    rw [hend]
    constructor
    · exact fun h => h.2.1
    · intro h
      exact ⟨⟨z, rfl⟩, h, (hinputs z x).2.2⟩
  constructor
  · intro hz
    obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hz
    have hjl : j ≤ L.l L.K := by have := Finset.mem_range.mp hj; omega
    by_cases hj1 : 1 ≤ j
    · rw [if_pos hj1] at hzj
      have he := (hT x L.K j z le_rfl hj1 hjl).mp hzj
      have hpj := hpolicy x L.K j le_rfl (by omega)
      rw [if_neg (by omega), if_pos hjl] at hpj
      have hidx : j - 1 < (policyLevelsAt M.prop q x L.K).length := by
        rw [hlength x L.K le_rfl]; omega
      apply hmem.mp
      rw [he, hpj, List.getD_eq_getElem _ _ hidx]
      exact List.getElem_mem hidx
    · simp only [if_neg hj1, Finset.notMem_empty] at hzj
  · intro hz
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (hmem.mpr hz)
    have hil : i + 1 ≤ L.l L.K := by rw [hlength x L.K le_rfl] at hi; omega
    apply Finset.mem_biUnion.mpr
    refine ⟨i + 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [if_pos (by omega)]
    apply (hT x L.K (i + 1) z le_rfl (by omega) hil).mpr
    rw [hpolicy x L.K (i + 1) le_rfl (by omega),
      if_neg (by omega), if_pos hil, Nat.add_sub_cancel,
      List.getD_eq_getElem _ _ hi]
    exact he.symm

-- @node: discrete_policy_tail_bound
/-- Under [the threshold-crossing model](hyp:h), if [the policy transformation is a valid
policy map](hyp:hp) and [its propensity levels and the baseline levels obey the common
ordering recorded by the level data](hyp:hL), then [the endpoint-weighted integral of the
positive and negative policy weights above the last baseline level equals the discrete
tail contribution, for either the upper or lower bound](goal). -/
lemma discrete_policy_tail_bound (h : ThresholdCrossing M)
    (phi : Z → X → ℝ → ℝ) (hp : IsPolicyMap phi) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (upper : Bool) (x : X) :
    (∫ u in Ioc (L.pLev L.K x) 1,
      (if upper then M.yMax else M.yMin) * max 0 (policyWeight M (policyProp phi M.prop) x u) +
      (if upper then M.yMin else M.yMax) * min 0 (policyWeight M (policyProp phi M.prop) x u)) =
      tailContribution M upper L (policyProp phi M.prop) x := by
  have hlast : L.pLev L.K x = pHigh M.prop x := by
    rw [hL.1 x L.K (by omega), ← hL.2.2.2.1 x]
    exact finite_last_baseline_supremum M x
  rw [hlast, connected_policy_tail_bound M h phi hp upper x]
  letI : IsMarkovKernel M.instKernel := M.instKernel_markov
  rw [integral_fintype (Integrable.of_finite)]
  unfold tailContribution
  rw [← hlast]
  congr 1
  calc
    _ = ∑ z ∈ policyUnion L L.K 1,
        (M.instKernel x).real {z} • max 0 (policyProp phi M.prop z x - L.pLev L.K x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro z _ hz
      have hq : policyProp phi M.prop z x ≤ L.pLev L.K x :=
        (lt_of_not_ge (fun hq => hz ((final_policy_union_membership M _ L hL x z).mpr hq))).le
      rw [max_eq_left (sub_nonpos.mpr hq), smul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      have hq := (final_policy_union_membership M _ L hL x z).mp hz
      rw [max_eq_right (sub_nonneg.mpr hq)]
      rfl

-- @node: finite_policy_conditional_bound_sum
/-- Under [the threshold-crossing model](hyp:h) and [a finite instrument reduction](hyp:hf),
if [the policy transformation is a valid policy map](hyp:hp) and [the baseline and policy
levels obey the ordering recorded by the level data](hyp:hL), then [the conditional bound
equals the sum of baseline interval lengths times their quantile-product integrals, plus
the tail contribution; ranks are matched for the upper bound and reversed for the lower
bound](goal). -/
lemma finite_policy_conditional_bound_sum (h : ThresholdCrossing M)
    (hf : InstrumentFiniteReduction Z) (phi : Z → X → ℝ → ℝ) (hp : IsPolicyMap phi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (upper : Bool) (x : X) :
    conditionalBoundIntegrand M upper (policyWeight M (policyProp phi M.prop)) x =
      (∑ k ∈ Finset.range L.K, (L.pLev (k + 1) x - L.pLev k x) *
        ∫ t in Ioo (0 : ℝ) 1,
          (conditionalIntervalQuantiles M (policyWeight M (policyProp phi M.prop)) x k).1 t *
          (conditionalIntervalQuantiles M (policyWeight M (policyProp phi M.prop)) x k).2
            (if upper then t else 1 - t)) +
      tailContribution M upper L (policyProp phi M.prop) x := by
  rw [finite_conditional_bound_eq_interval_sum M hf upper _ x, hL.2.2.2.1 x]
  have he (k : ℕ) (hk : k ≤ L.K + 1) :
      pLevel (finiteLevels (fun z => M.prop z x)) k = L.pLev k x := (hL.1 x k hk).symm
  rw [he L.K (by omega), discrete_policy_tail_bound M h phi hp L hL upper x]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [he k (by omega), he (k + 1) (by omega)]

end Papers.TbsPrteOptimalTransport
