module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryRegularity
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryTarget
/-! Integrability of population treatment corrections for regular binary products. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_binary_Rp_measurable
/-- If [the population binary nuisance specification is admissible](hyp:he),
[the treatment residual correction at any baseline level is measurable](goal). -/
@[fun_prop] lemma population_binary_Rp_measurable (L : LevelData Z X)
    (he : BinAdmissible M L (eta0Bin M L)) (k : ℕ) :
    Measurable (Rp L (eta0Bin M L) k) := by
  first
  | fun_prop
  |
    have hlev : Measurable (positiveValue (eta0Bin M L).pLev k) := by
      unfold positiveValue
      split_ifs with hk
      · exact (he.2.2.2.1 ⟨k, hk⟩).1
      · fun_prop
    have hpi : Measurable (positiveValue (eta0Bin M L).piLev k) := by
      unfold positiveValue
      split_ifs with hk
      · exact (he.2.2.2.1 ⟨k, hk⟩).2.2
      · fun_prop
    have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S k)) := by
      unfold indicator
      exact Measurable.ite ((L.S k).finite_toSet.measurableSet.preimage measurable_snd.fst)
        measurable_const measurable_const
    unfold Rp
    split_ifs
    · fun_prop
    · exact (hi.div (hpi.comp measurable_fst)).mul
        (measurable_snd.snd.fst.sub (hlev.comp measurable_fst))

-- @node: population_binary_Rp_integrable
/-- Under [baseline overlap with the specified positive lower bound](hyp:hov) and
[admissibility of the population binary nuisance specification](hyp:he),
[the treatment residual correction at any baseline level is integrable under
the observation distribution](goal). -/
lemma population_binary_Rp_integrable (L : LevelData Z X) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi)
    (he : BinAdmissible M L (eta0Bin M L)) (k : ℕ) :
    Integrable (Rp L (eta0Bin M L) k) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hw : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
    have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    apply (ae_map_iff hobs.aemeasurable
      (measurableSet_Icc.preimage measurable_snd.snd.fst)).2
    exact Filter.Eventually.of_forall (fun s => by
      rcases M.rangeW s with hs | hs <;> simp [hs])
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · have hk0 : k ≠ 0 := by omega
    have hp := observationLaw_covariate_ae M _ ((he.2.2.1 ⟨k, hk⟩).mono fun _ hx => hx.1)
    apply Integrable.of_bound (population_binary_Rp_measurable M L he k).aestronglyMeasurable
      (2 / cpi)
    filter_upwards [hw, hp] with o hwo hpo
    have hpi := hov.2 o.1 k hk.1 hk.2
    have hpi0 := hov.1.trans_le hpi
    have hb : |o.2.2.1 - L.pLev k o.1| ≤ 2 := by
      change L.pLev k o.1 ∈ Icc (0 : ℝ) 1 at hpo
      rw [abs_le]
      constructor <;> linarith [hwo.1, hwo.2, hpo.1, hpo.2]
    have hi : |indicator (o.2.1 ∈ L.S k)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    simp only [Rp, if_neg hk0, positiveValue, dif_pos hk, eta0Bin,
      Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hpi0]
    calc
      _ ≤ (1 / (levelSetProb M L).1 k o.1) * 2 :=
        mul_le_mul (div_le_div_of_nonneg_right hi hpi0.le) hb (abs_nonneg _) (by positivity)
      _ = 2 / (levelSetProb M L).1 k o.1 := by ring
      _ ≤ 2 / cpi := div_le_div_of_nonneg_left (by norm_num) hov.1 hpi
  · have hz : Rp L (eta0Bin M L) k = fun _ => (0 : ℝ) := by
      funext o
      by_cases hk0 : k = 0 <;> simp [Rp, hk0, positiveValue, hk]
    rw [hz]
    exact integrable_const 0

-- @node: population_binary_weighted_Rp_integrable
/-- Under [baseline overlap with the specified positive lower bound](hyp:hov) and
[admissibility of the population binary nuisance specification](hyp:he), if
[a covariate weight is measurable](hyp:hw) and [its absolute value is almost surely
bounded by the given constant](hyp:hb), [the weight times the treatment residual
correction is integrable under the observation distribution](goal). -/
lemma population_binary_weighted_Rp_integrable (L : LevelData Z X) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi)
    (he : BinAdmissible M L (eta0Bin M L)) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w) (C : ℝ)
    (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ C) :
    Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) k o)
      (observationLaw M) := by
  exact (population_binary_Rp_integrable M L cpi hov he k).bdd_mul
    (hw.comp measurable_fst).aestronglyMeasurable (observationLaw_covariate_ae M _ hb)

-- @node: population_binary_RqBin_measurable
/-- Under [the threshold-crossing treatment model](hyp:h), if [the policy derivative
evaluated at the baseline propensity is jointly measurable in instrument and covariates](hyp:hdphi)
and [the population binary nuisance specification is admissible](hyp:he),
[the policy-level residual correction at any pair of indices is measurable](goal). -/
@[fun_prop] lemma population_binary_RqBin_measurable (h : ThresholdCrossing M)
    (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (he : BinAdmissible M L (eta0Bin M L)) (k j : ℕ) :
    Measurable (RqBin dphi L (eta0Bin M L) k j) := by
  first
  | fun_prop
  |
    have htau : Measurable (regularValue (eta0Bin M L).tauLev k j) := by
      unfold regularValue
      split_ifs with ha
      · exact (he.2.2.2.2.2.1 ⟨(k,j), ha⟩).1
      · fun_prop
    have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.T k j)) := by
      unfold indicator
      exact Measurable.ite ((L.T k j).finite_toSet.measurableSet.preimage measurable_snd.fst)
        measurable_const measurable_const
    change Measurable (fun o => RqBin dphi L (eta0Bin M L) k j o)
    simp_rw [population_RqBin_residual_factorization]
    split_ifs
    · simp only [zero_mul]
      fun_prop
    · exact (((htau.comp measurable_fst).inv.mul hi).mul
        (hdphi.comp (measurable_snd.fst.prodMk measurable_fst))).mul
        (measurable_snd.snd.fst.sub
          (h.2.1.comp (measurable_snd.fst.prodMk measurable_fst)))

-- @node: population_binary_RqBin_integrable
/-- Under [the threshold-crossing treatment model](hyp:h), suppose [the policy
derivative at baseline propensities is jointly measurable](hyp:hdphi), [its bound
is nonnegative](hyp:hB), and [its absolute value never exceeds that bound](hyp:hb).
If [the baseline and policy levels have covariate-invariant ordering](hyp:hL),
[policy-level overlap holds with the specified positive lower bound](hyp:hov), and
[the population binary nuisance specification is admissible](hyp:he), [the policy-level
residual correction is integrable under the observation distribution](goal). -/
lemma population_binary_RqBin_integrable (h : ThresholdCrossing M)
    (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he : BinAdmissible M L (eta0Bin M L)) (k j : ℕ) :
    Integrable (RqBin dphi L (eta0Bin M L) k j) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  by_cases ha : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k
  · have hj : ¬(j = 0 ∨ L.l k < j) := by omega
    have ht : ∀ x, cpi ≤ (levelSetProb M L).2 k j x := fun x =>
      hov.2 x k j ha.1 ha.2.1 ha.2.2 (ordered_policy_level_nonempty M _ L hL k j ha.1 ha.2.1 ha.2.2)
    have hw : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
      have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
      apply (ae_map_iff hobs.aemeasurable
        (measurableSet_Icc.preimage measurable_snd.snd.fst)).2
      exact Filter.Eventually.of_forall (fun s => by
        rcases M.rangeW s with hs | hs <;> simp [hs])
    apply Integrable.of_bound
      (population_binary_RqBin_measurable M h dphi hdphi L he k j).aestronglyMeasurable
      (2 * B / cpi)
    filter_upwards [hw] with o ho
    have ht0 : 0 < (levelSetProb M L).2 k j o.1 := hov.1.trans_le (ht o.1)
    have hr : |o.2.2.1 - M.prop o.2.1 o.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [(M.rangeProp o.2.1 o.1).1, (M.rangeProp o.2.1 o.1).2,
        ho.1, ho.2]
    have hi : |indicator (o.2.1 ∈ L.T k j)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    rw [population_RqBin_residual_factorization]
    simp only [if_neg hj, regularValue,
      dif_pos ha, eta0Bin, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht0]
    calc
      _ ≤ (((levelSetProb M L).2 k j o.1)⁻¹ * 1 * B) * 2 := by
        gcongr <;> first | fun_prop | assumption | positivity | exact hb _ _
      _ = (2 * B) / (levelSetProb M L).2 k j o.1 := by ring
      _ ≤ (2 * B) / cpi := div_le_div_of_nonneg_left (by positivity) hov.1 (ht o.1)
  · have hz : RqBin dphi L (eta0Bin M L) k j = fun _ => (0 : ℝ) := by
      funext o
      rw [population_RqBin_residual_factorization]
      by_cases hj : j = 0 ∨ L.l k < j
      · simp [hj]
      · simp [hj, regularValue, ha]
    rw [hz]
    exact integrable_const 0

-- @node: population_binary_weighted_RqBin_integrable
/-- Under [the threshold-crossing treatment model](hyp:h), suppose [the policy derivative
at baseline propensities is jointly measurable](hyp:hdphi), [its bound is nonnegative](hyp:hB),
and [its absolute value never exceeds that bound](hyp:hb). If [baseline and policy
levels have covariate-invariant ordering](hyp:hL), [policy-level overlap holds with
the specified positive lower bound](hyp:hov), [the population binary nuisance specification
is admissible](hyp:he), [the covariate weight is measurable](hyp:hw), and [its absolute
value is almost surely bounded by the given constant](hyp:hwB), [the weighted policy-level
residual correction is integrable under the observation distribution](goal). -/
lemma population_binary_weighted_RqBin_integrable (h : ThresholdCrossing M)
    (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (he : BinAdmissible M L (eta0Bin M L)) (k j : ℕ)
    (w : X → ℝ) (hw : Measurable w) (C : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ C) :
    Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k j o)
      (observationLaw M) := by
  exact (population_binary_RqBin_integrable M h dphi hdphi B hB hb phi L hL cpi hov he k j).bdd_mul
    (hw.comp measurable_fst).aestronglyMeasurable (observationLaw_covariate_ae M _ hwB)

-- All seven integrability inputs of the regular-product tower calculation are
-- discharged from the stated overlap and bounded population constructions.
-- @node: population_binary_regular_product_mean_of_overlap
/-- Under [the threshold-crossing treatment model](hyp:h), suppose [the policy is a
valid policy map](hyp:hphi), [its derivative at baseline propensities is jointly
measurable](hyp:hdphi), [the derivative bound is nonnegative](hyp:hB), and [the derivative's
absolute value never exceeds that bound](hyp:hb). With [covariate-invariant ordering
of baseline and policy levels](hyp:hL), [measurable baseline levels](hyp:hlev),
[baseline overlap](hyp:hov), [policy-level overlap](hyp:hpol), [almost-surely binary
outcomes](hyp:hy), and [admissible population binary nuisances](hyp:he), for [a baseline
interval below the final level](hyp:hk) and [a positive policy-level index within
that interval's range](hyp:hj), [the regular product score is integrable and its
expectation equals the covariate average of the regular weight times the lower
binary band contribution](goal). -/
lemma population_binary_regular_product_mean_of_overlap (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (he : BinAdmissible M L (eta0Bin M L))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Integrable (psiProdBin phi dphi L (eta0Bin M L) k j) (observationLaw M) ∧
    (∫ o, psiProdBin phi dphi L (eta0Bin M L) k j o ∂observationLaw M) =
      ∫ x, gamma M L k j x * hMinus phi L (eta0Bin M L) k j x ∂xLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hg : Measurable (gamma M L k j) := (he.2.2.2.2.2.1 a).2
  have hgb : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.1 a] with x hx
    have hxg : gamma M L k j x ∈ Icc (0 : ℝ) 1 := hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg hxg.1]
    exact hxg.2
  have iP (m : ℕ) := population_binary_weighted_RP_integrable M L cpi hov hy he m
    (gamma M L k j) hg 1 hgb
  have ip (m : ℕ) := population_binary_weighted_Rp_integrable M L cpi hov he m
    (gamma M L k j) hg 1 hgb
  have iq (l : ℕ) := population_binary_weighted_RqBin_integrable M h dphi hdphi B hB hb
    phi L hL cpi hpol he k l (gamma M L k j) hg 1 hgb
  have hm := population_hMinus_measurable M h phi hphi L hlev k j
  have ih : Integrable (fun o : Obs X Z => hMinus phi L (eta0Bin M L) k j o.1)
      (observationLaw M) := by
    apply Integrable.of_bound (hm.comp measurable_fst).aestronglyMeasurable 1
    filter_upwards [observationLaw_covariate_ae M _
      (binary_auxiliary_ranges M phi L (eta0Bin M L) hphi he k hk j hj.1 hj.2)] with o ho
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg ho.1.1]
    exact ho.1.2
  have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k j)) := by
    unfold indicator
    exact Measurable.ite ((policyUnion L k j).finite_toSet.measurableSet.preimage
      measurable_snd.fst) measurable_const measurable_const
  have hib : ∀ o : Obs X Z, ‖indicator (o.2.1 ∈ policyUnion L k j)‖ ≤ 1 := by
    intro o
    unfold indicator
    split_ifs <;> norm_num
  exact population_binary_regular_product_mean M h phi dphi hphi hdphi L hL hlev k j
    ⟨hk.le, hj⟩ (iP (k+1)) (iP k) (ip (k+1)) (ip k) (iq j) (iq (j-1))
    (ih.mul_bdd hi.aestronglyMeasurable (Filter.Eventually.of_forall hib))

-- @node: binary_regular_weight_direction_regular
/-- If [a binary nuisance perturbation is admissible around a nuisance specification](hyp:hd),
[all its regular product weight perturbations are measurable and share a nonnegative,
finite almost-sure bound under the covariate distribution](goal). -/
lemma binary_regular_weight_direction_regular (L : LevelData Z X) (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : RegularIndex L,
      Measurable (del.gamma a) ∧ ∀ᵐ x ∂xLaw M, ‖del.gamma a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨4 / r, by positivity, ?_⟩
  intro a
  have hm0 : Measurable (eta.gamma a) := by
    have hm : Measurable (fun x => eta.gamma a x + 0 * del.gamma a x) :=
      (h0.2.2.2.2.2.1 a).2
    simpa only [zero_mul, add_zero] using hm
  have hmt : Measurable (fun x => eta.gamma a x + (r / 2) * del.gamma a x) :=
    (ht.2.2.2.2.2.1 a).2
  constructor
  · have hid : del.gamma a = fun x =>
        ((eta.gamma a x + (r / 2) * del.gamma a x) - eta.gamma a x) / (r / 2) := by
      funext x
      field_simp
      <;> ring
    rw [hid]
    exact (hmt.sub hm0).div_const _
  · filter_upwards [h0.2.2.2.2.1 a, ht.2.2.2.2.1 a] with x hx0 hxt
    have hb0 : eta.gamma a x + 0 * del.gamma a x ∈ Icc (0 : ℝ) 1 := hx0.2
    have hbt : eta.gamma a x + (r / 2) * del.gamma a x ∈ Icc (0 : ℝ) 1 := hxt.2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hr]
      nlinarith [hb0.1, hb0.2, hbt.1, hbt.2]
    · apply (le_div_iff₀ hr).2
      nlinarith [hb0.1, hb0.2, hbt.1, hbt.2]

-- This is the paper's gamma-direction cancellation, with its conditional
-- centering and analytic hypotheses derived from the population constructions.
-- @node: population_binary_regular_weight_orthogonality_of_admissible
/-- Under [the threshold-crossing treatment model](hyp:h), suppose [the policy is a
valid policy map](hyp:hphi), [its derivative at baseline propensities is jointly
measurable](hyp:hdphi), [the derivative bound is nonnegative](hyp:hB), and [the derivative's
absolute value never exceeds that bound](hyp:hb). With [covariate-invariant ordering
of baseline and policy levels](hyp:hL), [measurable baseline levels](hyp:hlev),
[baseline overlap](hyp:hov), [policy-level overlap](hyp:hpol), [almost-surely binary
outcomes](hyp:hy), and [an admissible nuisance perturbation at the population
specification](hyp:hd), for [a baseline interval below the final level](hyp:hk) and
[a positive policy-level index within that interval's range](hyp:hj), [the expected
regular product score has derivative zero at zero when only its regular weight
is varied linearly in that direction](goal). -/
lemma population_binary_regular_weight_orthogonality_of_admissible (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ k, Measurable (L.pLev k)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {eta0Bin M L with gamma := fun a x =>
        (eta0Bin M L).gamma a x + t * del.gamma a x} k j o
      ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hreg⟩ := binary_regular_weight_direction_regular M L (eta0Bin M L) del hd
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  obtain ⟨hw, hwB⟩ := hreg a
  have iP (m : ℕ) := population_binary_weighted_RP_integrable M L cpi hov hy he m
    (del.gamma a) hw C hwB
  have ip (m : ℕ) := population_binary_weighted_Rp_integrable M L cpi hov he m
    (del.gamma a) hw C hwB
  have iq (l : ℕ) := population_binary_weighted_RqBin_integrable M h dphi hdphi B hB hb
    phi L hL cpi hpol he k l (del.gamma a) hw C hwB
  have hq := population_pooledQBin_measurable M h phi hphi L hlev k j
  have hl := population_pooledQBin_measurable M h phi hphi L hlev k (j-1)
  have hp : Measurable (positiveValue (eta0Bin M L).pLev (k+1)) := by
    unfold positiveValue
    split_ifs
    · exact hlev (k+1)
    · fun_prop
  have hboundary : Measurable (fun x => positiveValue (eta0Bin M L).pLev (k+1) x -
      binFullJ L (eta0Bin M L) k x) := by fun_prop
  obtain ⟨ires, hz⟩ := population_binary_component_correction_zero M h phi dphi hdphi L hL
    k j (del.gamma a) hw
    (binary_Dbd_measurable phi L (eta0Bin M L) k j hq hl hboundary)
    (binary_Edom_measurable phi L (eta0Bin M L) k j hl hboundary)
    (binary_Iact_measurable phi L (eta0Bin M L) k j hq hl hboundary)
    (iP (k+1)) (iP k) (ip (k+1)) (ip k) (iq j) (iq (j-1))
  have ibase := (population_binary_regular_product_mean_of_overlap M h phi dphi hphi hdphi
    B hB hb L hL hlev cpi hov hpol hy he k j hk hj).1
  have hval : regularValue del.gamma k j = del.gamma a := by
    funext x
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le, hj⟩)]
    rfl
  have heq : (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {eta0Bin M L with gamma := fun a x =>
        (eta0Bin M L).gamma a x + t * del.gamma a x} k j o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiProdBin phi dphi L (eta0Bin M L) k j o ∂observationLaw M) := by
    funext t
    simp_rw [binary_regular_product_weight_path, hval, mul_assoc]
    rw [integral_add ibase (ires.const_mul t), integral_const_mul, hz, mul_zero, add_zero]
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport
