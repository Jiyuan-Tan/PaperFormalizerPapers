module
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailAdmissibility
/-! Bounded observation-law tail scores along admissible simultaneous paths. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Clipping is only a measurable representative; the score itself is unchanged a.e.
-- @node: commonTailScore_integrable_of_binary_admissible_treatment_version
/-- If [the policy is measurable and maps propensities into the unit interval](hyp:hphi),
[it has the specified propensity derivative](hyp:hDiff), [that derivative is uniformly
bounded and Lipschitz](hyp:hDerivative), [there is at least one level](hyp:hK), [the
binary nuisance values are admissible](hyp:he), and [a positive constant](hyp:hc)
[bounds the final assignment denominator from below almost everywhere](hyp:hpi),
then, for [a measurable replacement treatment variable](hyp:hwm) [lying between zero
and one almost surely](hyp:hw), [the common tail score evaluated with that treatment
variable is integrable under the observation distribution](goal). -/
lemma commonTailScore_integrable_of_binary_admissible_treatment_version
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x)
    (w : Obs X Z → ℝ) (hwm : Measurable w)
    (hw : ∀ᵐ o ∂observationLaw M, w o ∈ Icc (0 : ℝ) 1) :
    Integrable (fun o => commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail
      (o.1, o.2.1, w o, o.2.2.2))
      (observationLaw M) := by
  haveI : IsProbabilityMeasure (observationLaw M) :=
    Measure.isProbabilityMeasure_map
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  let pc : Z → X → ℝ := fun z x => max 0 (min 1 (e.prop z x))
  have hpc : Measurable (fun zx : Z × X => pc zx.1 zx.2) := by
    apply measurable_from_prod_countable_right
    intro z
    have hm := he.2.1 z
    dsimp only [pc]
    fun_prop
  have hpcR : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hq : Measurable (fun zx : Z × X => phi zx.1 zx.2 (pc zx.1 zx.2)) :=
    hphi.1.comp (measurable_fst.prodMk
      (measurable_snd.prodMk (hpc.subtype_mk (h := fun zx => hpcR zx.1 zx.2))))
  have hdq := policy_derivative_graph_measurable phi dphi hphi hDiff pc hpc hpcR
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hpk : Measurable (positiveValue e.pLev L.K) := by
    change Measurable (fun x => positiveValue e.pLev L.K x)
    simpa only [positiveValue, dif_pos hidx] using (he.2.2.2.1 ⟨L.K,hidx⟩).1
  have hpm : Measurable (positiveValue e.piLev L.K) := by
    change Measurable (fun x => positiveValue e.piLev L.K x)
    simpa only [positiveValue, dif_pos hidx] using (he.2.2.2.1 ⟨L.K,hidx⟩).2.2
  have hgm : Measurable e.gammaTail := he.2.2.2.2.2.2.2.2.2.2.2.2
  have hi (s : Finset Z) : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ s)) := by
    unfold indicator
    exact Measurable.ite (s.finite_toSet.measurableSet.preimage measurable_snd.fst)
      measurable_const measurable_const
  have hib (s : Finset Z) (o : Obs X Z) : |indicator (o.2.1 ∈ s)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  have hpco : Measurable (fun o : Obs X Z => pc o.2.1 o.1) :=
    hpc.comp (measurable_snd.fst.prodMk measurable_fst)
  have hqo : Measurable (fun o : Obs X Z => phi o.2.1 o.1 (pc o.2.1 o.1)) :=
    hq.comp (measurable_snd.fst.prodMk measurable_fst)
  have hdqo : Measurable (fun o : Obs X Z => dphi o.2.1 o.1 (pc o.2.1 o.1)) :=
    hdq.comp (measurable_snd.fst.prodMk measurable_fst)
  have hm : Measurable (fun o => commonTailScore M phi dphi L pc e.pLev e.piLev e.gammaTail
      (o.1, o.2.1, w o, o.2.2.2)) := by
    unfold commonTailScore
    first
    | fun_prop
    | apply Measurable.sub
      · exact ((measurable_const.mul (hi _)).mul (hqo.sub (hpk.comp measurable_fst))).add
          (((measurable_const.mul (hi _)).mul hdqo).mul (hwm.sub hpco))
      · split_ifs <;> fun_prop
  have hpkB : ∀ᵐ x ∂xLaw M, positiveValue e.pLev L.K x ∈ Icc (0 : ℝ) 1 := by
    simpa only [positiveValue, dif_pos hidx] using
      (he.2.2.1 ⟨L.K,hidx⟩).mono (fun _ hx => hx.1)
  have hgB : ∀ᵐ x ∂xLaw M, e.gammaTail x ∈ Icc (0 : ℝ) 1 :=
    he.2.2.2.2.2.2.2.2.2.2.2.1
  have hclip : Integrable (fun o => commonTailScore M phi dphi L pc e.pLev e.piLev e.gammaTail
      (o.1, o.2.1, w o, o.2.2.2))
      (observationLaw M) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (|M.yMin| * (2 + 2*B + 2/c))
    filter_upwards [hw, observationLaw_covariate_ae M _ hpkB,
      observationLaw_covariate_ae M _ hgB, observationLaw_covariate_ae M _ hpi]
      with o hwo hpo hgo hpio
    have hp := hpcR o.2.1 o.1
    have hqr := hphi.2 o.2.1 o.1 _ hp
    have hdB : |dphi o.2.1 o.1 (pc o.2.1 o.1)| ≤ B := (hb _ _ _ _ hp hp).1
    have hqB : |phi o.2.1 o.1 (pc o.2.1 o.1) - positiveValue e.pLev L.K o.1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [hqr.1, hqr.2, hpo.1, hpo.2]
    have hwB : |w o - pc o.2.1 o.1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [hwo.1, hwo.2, hp.1, hp.2]
    have hwpB : |w o - positiveValue e.pLev L.K o.1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [hwo.1, hwo.2, hpo.1, hpo.2]
    have hgabs : |e.gammaTail o.1| ≤ 1 := by
      rw [abs_of_nonneg hgo.1]; exact hgo.2
    have hrec : |(positiveValue e.piLev L.K o.1)⁻¹| ≤ 1/c := by
      rw [abs_inv, abs_of_pos (hc.trans_le hpio), one_div]
      exact inv_anti₀ hc hpio
    have hk : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
    rw [Real.norm_eq_abs]
    simp only [commonTailScore, if_neg hk, div_eq_mul_inv]
    calc
      _ ≤ |M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
          (phi o.2.1 o.1 (pc o.2.1 o.1) - positiveValue e.pLev L.K o.1)| +
        |M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
          dphi o.2.1 o.1 (pc o.2.1 o.1) * (w o - pc o.2.1 o.1)| +
        |M.yMin * e.gammaTail o.1 * indicator (o.2.1 ∈ L.S L.K) *
          (positiveValue e.piLev L.K o.1)⁻¹ *
            (w o - positiveValue e.pLev L.K o.1)| :=
        by
          apply (abs_sub_le _ 0 _).trans
          simp only [sub_zero, zero_sub, abs_neg]
          exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ |M.yMin| * 1 * 2 + |M.yMin| * 1 * B * 2 +
          |M.yMin| * 1 * 1 * (1/c) * 2 := by
        simp only [abs_mul]
        gcongr <;> first | exact hib _ o | assumption
      _ = _ := by ring
  apply hclip.congr
  have hpall : ∀ᵐ x ∂xLaw M, ∀ z, e.prop z x ∈ Icc (0 : ℝ) 1 := ae_all_iff.mpr he.1
  filter_upwards [observationLaw_covariate_ae M _ hpall] with o ho
  have heq : pc o.2.1 o.1 = e.prop o.2.1 o.1 := by
    simp only [pc, min_eq_right (ho _).2, max_eq_right (ho _).1]
  simp only [commonTailScore, heq]

-- @node: commonTailScore_integrable_of_binary_admissible
/-- If [the policy is measurable and maps propensities into the unit interval](hyp:hphi),
[it has the specified propensity derivative](hyp:hDiff), [that derivative is uniformly
bounded and Lipschitz](hyp:hDerivative), [there is at least one level](hyp:hK), [the
binary nuisance values are admissible](hyp:he), and [a positive constant](hyp:hc)
[bounds the final assignment denominator from below almost everywhere](hyp:hpi),
then [the common tail score is integrable under the observation distribution](goal). -/
lemma commonTailScore_integrable_of_binary_admissible
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x) :
    Integrable (commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail)
      (observationLaw M) := by
  have hw : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
    have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    apply (ae_map_iff hobs.aemeasurable
      (measurableSet_Icc.preimage measurable_snd.snd.fst)).2
    exact Eventually.of_forall (fun s => by
      rcases M.rangeW s with hs | hs <;> simp [hs])
  exact commonTailScore_integrable_of_binary_admissible_treatment_version M
    phi dphi hphi hDiff hDerivative L hK e he c hc hpi
    (fun o => o.2.2.1) measurable_snd.snd.fst hw

-- Replacing W by its true conditional mean keeps the same bounded-score argument.
-- @node: commonTailScore_centered_integrable_of_binary_admissible
/-- If [the model satisfies threshold crossing](hyp:h), [the policy is measurable and
maps propensities into the unit interval](hyp:hphi), [it has the specified propensity
derivative](hyp:hDiff), [that derivative is uniformly bounded and Lipschitz](hyp:hDerivative),
[there is at least one level](hyp:hK), [the binary nuisance values are admissible](hyp:he),
and [a positive constant](hyp:hc) [bounds the final assignment denominator from below
almost everywhere](hyp:hpi), then [the common tail score with treatment replaced by
its true conditional mean and outcome set to zero is observation-integrable](goal). -/
lemma commonTailScore_centered_integrable_of_binary_admissible
    (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x) :
    Integrable (fun o : Obs X Z => commonTailScore M phi dphi L
      e.prop e.pLev e.piLev e.gammaTail (o.1, o.2.1, M.prop o.2.1 o.1, 0))
      (observationLaw M) := by
  have hm : Measurable (fun o : Obs X Z => M.prop o.2.1 o.1) := by
    first | fun_prop | exact h.2.1.comp (measurable_snd.fst.prodMk measurable_fst)
  have hi := commonTailScore_integrable_of_binary_admissible_treatment_version M
    phi dphi hphi hDiff hDerivative L hK e he c hc hpi
    (fun o => M.prop o.2.1 o.1) hm
    (Eventually.of_forall (fun o => M.rangeProp o.2.1 o.1))
  convert hi using 1
  funext o
  rfl

-- The neighborhood is common in x; an a.e. pointwise neighborhood would not
-- suffice for a population integral along the nuisance path.
-- @node: binary_final_denominator_uniform_neighborhood
/-- If [there is at least one level](hyp:hK), [baseline assignment probabilities have
the specified positive overlap bound](hyp:hov), and [the binary nuisance direction is
admissible at the truth](hyp:hd), then [throughout some common neighborhood of zero,
the perturbed final-level assignment denominator is at least half the overlap
constant for almost every covariate value](goal). -/
lemma binary_final_denominator_uniform_neighborhood
    (L : LevelData Z X) (hK : LevelCountPos L.K) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ positiveValue (eta0Bin M L + t • del).piLev L.K x := by
  obtain ⟨C, hC, hb⟩ := binary_assignment_denominator_direction_regular M L
    (eta0Bin M L) del hd
  have hcpi := hov.1
  have radius : 0 < cpi / (2*(C+1)) := by positivity
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  change |t| < cpi / (2*(C+1)) at ht
  filter_upwards [(hb ⟨L.K,hidx⟩).2] with x hx
  simp only [Real.norm_eq_abs] at hx
  have hmul : |t * del.piLev ⟨L.K,hidx⟩ x| ≤ |t| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp ht
  have htrue := hov.2 x L.K hK le_rfl
  change cpi ≤ (eta0Bin M L).piLev ⟨L.K,hidx⟩ x at htrue
  simp only [positiveValue, dif_pos hidx]
  change cpi/2 ≤ (eta0Bin M L).piLev ⟨L.K,hidx⟩ x + t * del.piLev ⟨L.K,hidx⟩ x
  nlinarith [neg_abs_le (t * del.piLev ⟨L.K,hidx⟩ x), abs_nonneg t]

-- All analytic premises for the actual observation-score integral here are
-- consequences of admissibility, the policy assumptions, and population overlap.
-- @node: population_binary_tail_joint_path_integrable_of_admissible
/-- If [the policy is measurable and maps propensities into the unit interval](hyp:hphi),
[it has the specified propensity derivative](hyp:hDiff), [that derivative is uniformly
bounded and Lipschitz](hyp:hDerivative), [there is at least one level](hyp:hK), [baseline
assignment probabilities have the specified positive overlap bound](hyp:hov), and
[the binary nuisance direction is admissible at the truth](hyp:hd), then [the common
tail score is observation-integrable along the simultaneous affine nuisance path
for every path parameter sufficiently near zero](goal). -/
lemma population_binary_tail_joint_path_integrable_of_admissible
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    ∀ᶠ t : ℝ in nhds 0, Integrable (commonTailScore M phi dphi L
      (eta0Bin M L + t • del).prop (eta0Bin M L + t • del).pLev
      (eta0Bin M L + t • del).piLev (eta0Bin M L + t • del).gammaTail)
      (observationLaw M) := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr),
    binary_final_denominator_uniform_neighborhood M L hK cpi hov del hd] with t ht hpi
  exact commonTailScore_integrable_of_binary_admissible M phi dphi hphi hDiff hDerivative
    L hK _ (hpath t ht) (cpi/2) (by have hc := hov.1; positivity) hpi

end Papers.TbsPrteOptimalTransport
