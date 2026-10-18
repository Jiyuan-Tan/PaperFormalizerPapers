module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBoundaryRegularity
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryAdmissibility
/-! Admissibility of the constructed continuous population nuisance vector.
The terminal band uses the raw level-one quantile, whose measurability follows
from rational CDF superlevel sets, including fibers with an empty superlevel set. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: measurable_kernel_raw_upper_quantile
/-- For a Markov probability kernel, [its raw level-one outcome quantile is a measurable
function of the conditioning variable](goal), including when the defining quantile set is empty. -/
@[fun_prop] lemma measurable_kernel_raw_upper_quantile
    {B : Type*} [MeasurableSpace B] (K : Kernel B ℝ) [IsMarkovKernel K] :
    Measurable (fun b => Causalean.Stat.quantile (K b) 1) := by
  let E : Set B := ⋃ q : ℚ, {b | (1 : ℝ) ≤ cdf (K b) q}
  have hE : MeasurableSet E := by
    apply MeasurableSet.iUnion
    intro q
    simp_rw [cdf_eq_real]
    exact measurableSet_le measurable_const
      ((K.measurable_coe measurableSet_Iic).ennreal_toReal)
  have he (b : B) : b ∈ E ↔ (Causalean.Stat.quantileSet (K b) 1).Nonempty := by
    constructor
    · intro hb
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hb
      exact ⟨q, hq⟩
    · rintro ⟨y, hy⟩
      obtain ⟨q, hq⟩ := exists_rat_gt y
      exact Set.mem_iUnion.mpr ⟨q, Causalean.Stat.quantileSet_up_closed hy hq.le⟩
  apply measurable_of_Iio
  intro r
  have hset : (fun b => Causalean.Stat.quantile (K b) 1) ⁻¹' Iio r =
      (Eᶜ ∩ {b : B | (0 : ℝ) < r}) ∪
        ⋃ q : ℚ, {b | (q : ℝ) < r ∧ (1 : ℝ) ≤ cdf (K b) q} := by
    ext b
    by_cases hb : b ∈ E
    · have hn := (he b).mp hb
      have hbd := Causalean.Stat.bddBelow_quantileSet (μ := K b) (by norm_num : (0 : ℝ) < 1)
      simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff,
        mem_compl_iff, hb, not_true_eq_false, false_and, false_or, mem_iUnion, mem_ofPred_eq]
      change sInf (Causalean.Stat.quantileSet (K b) 1) < r ↔ _
      constructor
      · intro hr
        obtain ⟨y, hy, hyr⟩ := (csInf_lt_iff hbd hn).mp hr
        obtain ⟨q, hyq, hqr⟩ := exists_rat_btwn hyr
        exact ⟨q, hqr, Causalean.Stat.quantileSet_up_closed hy hyq.le⟩
      · rintro ⟨q, hqr, hq⟩
        exact (csInf_le hbd hq).trans_lt hqr
    · have hempty : Causalean.Stat.quantileSet (K b) 1 = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp (fun hn => hb ((he b).mpr hn))
      have hnone : ¬ ∃ q : ℚ, (q : ℝ) < r ∧ (1 : ℝ) ≤ cdf (K b) q := by
        rintro ⟨q, _, hq⟩
        exact hb (Set.mem_iUnion.mpr ⟨q, hq⟩)
      simp only [mem_preimage, mem_Iio, Causalean.Stat.quantile, hempty,
        Real.sInf_empty, mem_union, mem_inter_iff, mem_compl_iff, hb,
        not_false_eq_true, true_and, mem_ofPred_eq, mem_iUnion, hnone, or_false]
  rw [hset]
  apply MeasurableSet.union
  · exact hE.compl.inter (by by_cases hr : (0 : ℝ) < r <;> simp [hr])
  · apply MeasurableSet.iUnion
    intro q
    simp_rw [cdf_eq_real]
    exact (by by_cases hqr : (q : ℝ) < r <;> simp [hqr] :
      MeasurableSet {b : B | (q : ℝ) < r}).inter
        (measurableSet_le measurable_const
          ((K.measurable_coe measurableSet_Iic).ennreal_toReal))

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_terminal_bandBoundary_measurable
/-- If [the baseline and policy levels have a covariate-invariant ordering](hyp:hL)
and [all baseline levels are measurable](hyp:hlev), then, for
[a bin before the final baseline bin](hyp:hk), [the terminal band boundary is measurable](goal). -/
@[fun_prop] lemma population_terminal_bandBoundary_measurable
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (hlev : ∀ k, Measurable (L.pLev k))
    (k : ℕ) (hk : k < L.K) :
    Measurable (bandBoundary M L k (L.l k + 1)) := by
  first | fun_prop | skip
  let K := outcomeKernel (latentMarginal M true)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  obtain ⟨D, hD, hDeq⟩ := exists_normalized_interval_kernel K (L.pLev k)
    (L.pLev (k+1)) (hlev k) (hlev (k+1)) M.yMin
  letI := hD
  have heq (x : X) : D x = discreteGapLaw M L k x := by
    have ha := hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega)
    have hab := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
    rw [hDeq, if_pos hab, discreteGapLaw,
      canonical_treated_increment M x _ _ ha.1 hab.le]
  have hkap (x : X) : kappa L k (L.l k + 1) x = 1 := by
    have hab := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
    unfold kappa
    rw [hL.2.1 x k (L.l k + 1) hk.le (by omega),
      if_neg (by omega), if_neg (by omega)]
    exact div_self (sub_pos.mpr hab).ne'
  convert measurable_kernel_raw_upper_quantile D using 1
  funext x
  simp only [bandBoundary, hkap, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, one_ne_zero, or_self, if_false, heq]

-- @node: population_treated_all_band_mean_measurable
/-- If [policy propensities are jointly measurable](hyp:hq),
[the level ordering is invariant across covariates](hyp:hL), and
[baseline levels are measurable](hyp:hlev), then for [a nonfinal bin](hyp:hk)
and [a band index from zero through its policy-level count](hyp:hj),
[the selected treated-outcome band mean is measurable, on either side](goal). -/
@[fun_prop] lemma population_treated_all_band_mean_measurable
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) :
    Measurable (treatedBandMean M L plus false k j) := by
  first | fun_prop | skip
  have ha := population_bandBoundary_measurable M q hq L hL hlev k j hk hj
  have hb : Measurable (bandBoundary M L k (j+1)) := by
    by_cases hlt : j < L.l k
    · exact population_bandBoundary_measurable M q hq L hL hlev k (j+1) hk (by omega)
    · have hjEq : j = L.l k := by omega
      subst j
      exact population_terminal_bandBoundary_measurable M q L hL hlev k hk
  exact population_treated_band_mean_measurable M L plus k j ha hb

-- @node: population_continuous_nuisance_admissible
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[jointly measurable policy propensities](hyp:hq), [covariate-invariant level ordering](hyp:hL),
[measurable baseline levels](hyp:hlev), [baseline overlap](hyp:hov), and
[policy overlap with the same constant](hyp:hpol),
[the population continuous-outcome nuisance vector is admissible](goal). -/
lemma population_continuous_nuisance_admissible
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi) :
    ContAdmissible M L (trueNuisance M L) := by
  have hm := population_instrument_set_probability_measurable M
  have hr := population_instrument_set_probability_range M
  have hb := population_bandBoundary_measurable M q hq L hL hlev
  have hfull := population_continuous_full_nuisance_ranges M h he q L hL cpi hov
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact Eventually.of_forall (M.rangeProp z)
  · intro z
    exact h.2.2.2.1.2.1.comp (measurable_const.prodMk measurable_id)
  · intro k
    exact Eventually.of_forall (fun x => hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega))
  · intro k
    exact hlev k
  · intro k
    exact Eventually.of_forall (hr (L.S k))
  · intro k
    exact hm (L.S k)
  · intro a
    exact Eventually.of_forall (hr (L.T a.val.1 a.val.2))
  · intro a
    exact hm (L.T a.val.1 a.val.2)
  · intro a z
    exact Eventually.of_forall (population_levelShares_range M L a.val.1 a.val.2 z)
  · intro a z
    exact population_levelShares_measurable M L a.val.1 a.val.2 z
  · intro k
    apply Eventually.of_forall
    intro x
    have hp := hr (higherPolicy L k) x
    have hb := hr (higherBaseline L k) x
    change (∑ z ∈ higherPolicy L k, instProb M z x) -
      (∑ z ∈ higherBaseline L k, instProb M z x) ∈ Icc (-1 : ℝ) 1
    constructor <;> linarith [hp.1, hp.2, hb.1, hb.2]
  · intro k
    exact (hm (higherPolicy L k)).sub (hm (higherBaseline L k))
  · intro a
    exact Eventually.of_forall (hr (policyUnion L a.val.1 a.val.2))
  · intro a
    exact hm (policyUnion L a.val.1 a.val.2)
  · exact Eventually.of_forall (hr (policyUnion L L.K 1))
  · exact hm (policyUnion L L.K 1)
  · exact population_continuous_boundary_nuisance_range M h he q L hL
  · intro a
    first | fun_prop | exact population_continuous_boundary_nuisance_measurable M q hq L hL hlev a
  · intro a
    exact Eventually.of_forall (population_boundary_indicator_mean_range M L true a.val.1 a.val.2)
  · intro a
    first | fun_prop | exact population_boundary_indicator_mean_measurable M L true _ _ (hb _ _ a.property.1 a.property.2)
  · intro a
    exact Eventually.of_forall (population_boundary_indicator_mean_range M L false a.val.1 a.val.2)
  · intro a
    first | fun_prop | exact population_boundary_indicator_mean_measurable M L false _ _ (hb _ _ a.property.2.1 a.property.2.2)
  · intro a
    exact population_treated_band_mean_range M h he L true a.val.1 a.val.2
  · intro a
    first | fun_prop | exact population_treated_all_band_mean_measurable M q hq L hL hlev true _ _ a.property.1 a.property.2
  · intro a
    exact population_treated_band_mean_range M h he L false a.val.1 a.val.2
  · intro a
    first | fun_prop | exact population_treated_all_band_mean_measurable M q hq L hL hlev false _ _ a.property.2.1 a.property.2.2
  · exact hfull.1
  · intro k
    fun_prop
  · exact hfull.2
  · intro k
    fun_prop
  · intro a
    apply Eventually.of_forall
    intro x
    refine ⟨population_policy_level_shares_sum_one M q L hL cpi hpol
      a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2 x, ?_⟩
    intro z hz
    simp only [trueNuisance, levelShares, if_neg hz]

end Papers.TbsPrteOptimalTransport
