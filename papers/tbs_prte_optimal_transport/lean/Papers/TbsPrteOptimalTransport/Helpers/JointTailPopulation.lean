module
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailIntegrability
/-! Tower identification and orthogonality of the actual simultaneous tail-score path. -/
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

-- Policy maps are measurable on [0,1]. Clipping supplies a global representative
-- for the tower step, and admissibility identifies it with the actual score a.e.
-- @node: population_commonTailScore_finite_mean_of_binary_admissible
/-- If [the model satisfies threshold crossing](hyp:h), [the policy is measurable and
maps propensities into the unit interval](hyp:hphi), [it has the specified propensity
derivative](hyp:hDiff), [that derivative is uniformly bounded and Lipschitz](hyp:hDerivative),
[there is at least one level](hyp:hK), [the binary nuisance values are admissible](hyp:he),
and [a positive constant](hyp:hc) [bounds the final assignment denominator from below
almost everywhere](hyp:hpi), then [the population mean of the common tail score equals
the covariate average of its finite instrument-probability-weighted mean with
treatment replaced by its true conditional mean and outcome set to zero](goal). -/
lemma population_commonTailScore_finite_mean_of_binary_admissible
    (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x) :
    (∫ o, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
      ∂observationLaw M) =
    ∫ x, ∑ z, instProb M z x * commonTailScore M phi dphi L
      e.prop e.pLev e.piLev e.gammaTail (x, z, M.prop z x, 0) ∂xLaw M := by
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
  have hi (s : Finset Z) : Measurable (fun zx : Z × X => indicator (zx.1 ∈ s)) := by
    unfold indicator
    exact Measurable.ite (s.finite_toSet.measurableSet.preimage measurable_fst)
      measurable_const measurable_const
  have hmprop := h.2.1
  have hf : Measurable (fun zx : Z × X => commonTailScore M phi dphi L
      pc e.pLev e.piLev e.gammaTail (zx.2, zx.1, M.prop zx.1 zx.2, 0)) := by
    unfold commonTailScore
    first
    | fun_prop
    | apply Measurable.sub
      · exact ((measurable_const.mul (hi _)).mul (hq.sub (hpk.comp measurable_snd))).add
          (((measurable_const.mul (hi _)).mul hdq).mul (h.2.1.sub hpc))
      · split_ifs <;> fun_prop
  have hw : Measurable (fun zx : Z × X => M.yMin *
      (indicator (zx.1 ∈ policyUnion L L.K 1) * dphi zx.1 zx.2 (pc zx.1 zx.2) -
        e.gammaTail zx.2 / positiveValue e.piLev L.K zx.2 *
          indicator (zx.1 ∈ L.S L.K))) := by
    first
    | fun_prop
    | exact measurable_const.mul (((hi _).mul hdq).sub
        (((hgm.comp measurable_snd).div (hpm.comp measurable_snd)).mul (hi _)))
  have heq : ∀ᵐ x ∂xLaw M, ∀ z, pc z x = e.prop z x := by
    filter_upwards [ae_all_iff.mpr he.1] with x hx
    intro z
    simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
  have heqo := observationLaw_covariate_ae M _ heq
  have hic := commonTailScore_centered_integrable_of_binary_admissible M h
    phi dphi hphi hDiff hDerivative L hK e he c hc hpi
  have hia := commonTailScore_integrable_of_binary_admissible M
    phi dphi hphi hDiff hDerivative L hK e he c hc hpi
  have hicp : Integrable (fun o : Obs X Z => commonTailScore M phi dphi L
      pc e.pLev e.piLev e.gammaTail (o.1, o.2.1, M.prop o.2.1 o.1, 0))
      (observationLaw M) := by
    apply hic.congr
    filter_upwards [heqo] with o ho
    simp only [commonTailScore, ho o.2.1]
  have hiap : Integrable (commonTailScore M phi dphi L pc e.pLev e.piLev e.gammaTail)
      (observationLaw M) := by
    apply hia.congr
    filter_upwards [heqo] with o ho
    simp only [commonTailScore, ho o.2.1]
  have hr : Integrable (fun o : Obs X Z => (M.yMin *
      (indicator (o.2.1 ∈ policyUnion L L.K 1) * dphi o.2.1 o.1 (pc o.2.1 o.1) -
        e.gammaTail o.1 / positiveValue e.piLev L.K o.1 *
          indicator (o.2.1 ∈ L.S L.K))) *
        (o.2.2.1 - M.prop o.2.1 o.1)) (observationLaw M) := by
    have hs := hiap.sub hicp
    convert hs using 1
    funext o
    simp only [Pi.sub_apply]
    rw [commonTailScore_treatment_centered_decomposition M phi dphi L hK]
    ring
  calc
    _ = ∫ o, commonTailScore M phi dphi L pc e.pLev e.piLev e.gammaTail o
        ∂observationLaw M := by
      apply integral_congr_ae
      filter_upwards [heqo] with o ho
      simp only [commonTailScore, ho o.2.1]
    _ = ∫ x, ∑ z, instProb M z x * commonTailScore M phi dphi L
        pc e.pLev e.piLev e.gammaTail (x, z, M.prop z x, 0) ∂xLaw M :=
      (population_commonTailScore_finite_conditional_mean M h phi dphi L hK
        pc e.pLev e.piLev e.gammaTail hf hw hicp hr).2
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      apply Finset.sum_congr rfl
      intro z _
      simp only [commonTailScore, hx z]

-- The finite conditional mean has a quadratic integrated remainder. The tower
-- identity transfers that derivative to the actual observation-score path.
-- @node: population_binary_tail_joint_orthogonality_of_admissible
/-- If [the model satisfies threshold crossing](hyp:h), [the policy is measurable and
maps propensities into the unit interval](hyp:hphi), [it has the specified propensity
derivative](hyp:hDiff), [that derivative is uniformly bounded and Lipschitz](hyp:hDerivative),
[there is at least one level](hyp:hK), [the levels preserve the ordering of the true
and policy propensities](hyp:hOrder), [baseline assignment probabilities have the
specified positive overlap bound](hyp:hov), and [the binary nuisance direction is
admissible at the truth](hyp:hd), then [the population mean of the common tail score
has derivative zero at zero along the simultaneous affine path through all binary
nuisance components](goal). -/
lemma population_binary_tail_joint_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o, commonTailScore M phi dphi L
      (eta0Bin M L + t • del).prop (eta0Bin M L + t • del).pLev
      (eta0Bin M L + t • del).piLev (eta0Bin M L + t • del).gammaTail o
      ∂observationLaw M) 0 0 := by
  have hfinite := population_binary_tail_finite_mean_joint_orthogonality_of_admissible
    M h phi dphi hphi hDiff hDerivative L hK cpi hov del hd
  apply hfinite.congr_of_eventuallyEq
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr),
    binary_final_denominator_uniform_neighborhood M L hK cpi hov del hd] with t ht hpi
  rw [population_commonTailScore_finite_mean_of_binary_admissible M h
    phi dphi hphi hDiff hDerivative L hK _ (hpath t ht)
    (cpi/2) (by have hc := hov.1; positivity) hpi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hlevel : ∀ z ∈ L.S L.K,
      M.prop z x = positiveValue (eta0Bin M L).pLev L.K x := by
    intro z hz
    simp only [positiveValue, dif_pos hidx, eta0Bin]
    exact (hOrder.2.2.2.2.2.1 x L.K z le_rfl).mp hz
  have hmass : ∑ z ∈ L.S L.K, instProb M z x =
      positiveValue (eta0Bin M L).piLev L.K x := by
    simp only [positiveValue, dif_pos hidx, eta0Bin, levelSetProb]
  exact commonTailScore_joint_finite_conditional_mean M phi dphi L hK
    M.prop del.prop (eta0Bin M L).pLev del.pLev (eta0Bin M L).piLev del.piLev
    (eta0Bin M L).gammaTail del.gammaTail x (fun z => instProb M z x) t
    hlevel hmass rfl

end Papers.TbsPrteOptimalTransport
