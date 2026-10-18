module
public import Papers.TbsPrteOptimalTransport.Helpers.GapBounds
public import Papers.TbsPrteOptimalTransport.Helpers.AttainingVersion
public import Mathlib.MeasureTheory.Measure.OpenPos
/-! Disintegration and integrable objectives of arbitrary feasible treated laws. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
open Causalean.Stat Toolkit.Tricks.Probability.Moments
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: feasible_treated_disintegration
/-- If [a joint law of latent rank, covariates, and treated outcome is feasible](hyp:hp),
then [combining the independent uniform-rank and covariate law with its conditional
outcome kernel recovers that joint law](goal). -/
lemma feasible_treated_disintegration (pi : Measure ((ℝ × X) × ℝ))
    (hp : IsFeasibleTreated (transportData M) pi) :
    (Causalean.Stat.unifOI.prod (xLaw M)) ⊗ₘ outcomeKernel pi = pi := by
  letI := hp.1
  have hm : pi.fst = Causalean.Stat.unifOI.prod (xLaw M) := hp.2.2.1
  rw [← hm]
  simp only [outcomeKernel, dif_pos (inferInstance : IsFiniteMeasure pi)]
  exact Measure.disintegrate pi pi.condKernel

-- @node: feasible_treated_kernel_supported
/-- If [the treated joint law is feasible](hyp:hp), then [its conditional outcome kernel
assigns zero mass outside the outcome domain for almost every rank-covariate pair under
the product of the uniform-rank and covariate laws](goal). -/
lemma feasible_treated_kernel_supported (pi : Measure ((ℝ × X) × ℝ))
    (hp : IsFeasibleTreated (transportData M) pi) :
    ∀ᵐ ux ∂Causalean.Stat.unifOI.prod (xLaw M), outcomeKernel pi ux M.Ysetᶜ = 0 := by
  letI := hp.1
  letI := outcomeKernel_isMarkov pi
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hs : ∀ᵐ a ∂pi, a.2 ∈ M.Yset := by
    have ha : ∀ᵐ a ∂pi, a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2 ∈ M.Yset :=
      ae_iff.mpr hp.2.1
    exact ha.mono fun a ha => ha.2
  rw [← feasible_treated_disintegration M pi hp] at hs
  exact (Measure.ae_ae_of_ae_compProd hs).mono fun ux hux => ae_iff.mp hux

-- @node: feasible_treated_kernel_section_supported
/-- If [the treated joint law is feasible](hyp:hp), then [for almost every covariate
value, its conditional outcome kernel assigns zero mass outside the outcome domain at
Lebesgue-almost every rank in the closed unit interval](goal). -/
lemma feasible_treated_kernel_section_supported (pi : Measure ((ℝ × X) × ℝ))
    (hp : IsFeasibleTreated (transportData M) pi) :
    ∀ᵐ x ∂xLaw M, ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
      outcomeKernel pi (u, x) M.Ysetᶜ = 0 := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hs : ∀ᵐ xu ∂(xLaw M).prod Causalean.Stat.unifOI,
      outcomeKernel pi (xu.2, xu.1) M.Ysetᶜ = 0 := by
    have hh : ∀ᵐ ux ∂((xLaw M).prod Causalean.Stat.unifOI).map Prod.swap,
        outcomeKernel pi ux M.Ysetᶜ = 0 := by
      rw [Measure.prod_swap]
      exact feasible_treated_kernel_supported M pi hp
    exact ae_of_ae_map measurable_swap.aemeasurable hh
  simpa only [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc] using
    Measure.ae_ae_of_ae_prod hs

-- @node: feasible_treated_weighted_integrable
/-- If [the designated endpoints are the outcome domain's minimum and maximum](hyp:he),
[the target weight is integrable under the covariate and uniform-rank laws](hyp:hi), and
[the treated joint law is feasible](hyp:hp), then [outcome times target weight is
integrable under that joint law](goal). -/
lemma feasible_treated_weighted_integrable (he : OutcomeEndpointsKnown M)
    (om : X → ℝ → ℝ) (hi : TargetWeightIntegrable M om)
    (pi : Measure ((ℝ × X) × ℝ)) (hp : IsFeasibleTreated (transportData M) pi) :
    Integrable (fun a : (ℝ × X) × ℝ => a.2 * om a.1.2 a.1.1) pi := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hi' : Integrable (Function.uncurry om) ((xLaw M).prod Causalean.Stat.unifOI) := by
    simpa only [TargetWeightIntegrable, Causalean.Stat.unifOI,
      restrict_Ioo_eq_restrict_Icc] using hi
  have hw : Integrable (fun ux : ℝ × X => om ux.2 ux.1) pi.fst := by
    rw [hp.2.2.1]
    exact hi'.swap
  have hwj := hw.comp_measurable measurable_fst
  have hb : ∀ᵐ a ∂pi, ‖a.2‖ ≤ outcomeMagnitude M := by
    have hs : ∀ᵐ a ∂pi, a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2 ∈ M.Yset :=
      ae_iff.mpr hp.2.1
    exact hs.mono fun a ha => outcome_norm_le_magnitude M he ha.2
  exact hwj.bdd_mul (by fun_prop) hb

-- @node: feasible_treated_objective_disintegration
/-- If [the designated endpoints are the outcome domain's minimum and maximum](hyp:he),
[the target weight is integrable under the covariate and uniform-rank laws](hyp:hi), and
[the treated joint law is feasible](hyp:hp), then [the rank integral of its conditional
mean outcome times the target weight is integrable over covariates, and its covariate
average equals the treated objective](goal). -/
lemma feasible_treated_objective_disintegration (he : OutcomeEndpointsKnown M)
    (om : X → ℝ → ℝ) (hi : TargetWeightIntegrable M om)
    (pi : Measure ((ℝ × X) × ℝ)) (hp : IsFeasibleTreated (transportData M) pi) :
    Integrable (fun x => ∫ u in Icc (0 : ℝ) 1,
      (∫ y, y ∂outcomeKernel pi (u, x)) * om x u) (xLaw M) ∧
    thetaComp om pi = ∫ x, (∫ u in Icc (0 : ℝ) 1,
      (∫ y, y ∂outcomeKernel pi (u, x)) * om x u) ∂xLaw M := by
  letI := hp.1
  letI := outcomeKernel_isMarkov pi
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hf := feasible_treated_weighted_integrable M he om hi pi hp
  rw [← feasible_treated_disintegration M pi hp] at hf
  have hmean := hf.integral_compProd
  simp only [Kernel.prodMkLeft_apply, Kernel.const_apply, integral_mul_const] at hmean
  constructor
  · simpa only [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc] using hmean.integral_prod_right
  · change (∫ a, a.2 * om a.1.2 a.1.1 ∂pi) = _
    conv_lhs => rw [← feasible_treated_disintegration M pi hp]
    rw [Measure.integral_compProd hf]
    simp only [integral_mul_const]
    rw [integral_prod_symm _ hmean]
    simp only [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc]

-- @node: treated_compatible_conditional_instrument
/-- If [a treated joint law satisfies the observed treated-data compatibility
restrictions](hyp:hp), then [for almost every covariate value and almost every instrument
value under its conditional law, integrating the conditional probability of any
measurable outcome set over ranks from zero to the propensity score equals the canonical
treated submeasure of that set](goal). -/
lemma treated_compatible_conditional_instrument (pi : Measure ((ℝ × X) × ℝ))
    (hp : TreatedCompatible (transportData M) pi) :
    ∀ᵐ x ∂xLaw M, ∀ᵐ z ∂condDistrib M.Zv M.Xv M.law.toMeasure x,
      ∀ A : Set ℝ, MeasurableSet A →
        (∫ u in Ioc 0 (M.prop z x), (outcomeKernel pi (u, x) A).toReal) =
          (canonSubmeasure M true x (M.prop z x) A).toReal := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hswap : ((xLaw M) ⊗ₘ condDistrib M.Zv M.Xv M.law.toMeasure).map Prod.swap = zxLaw M := by
    change ((M.law.toMeasure.map M.Xv) ⊗ₘ condDistrib M.Zv M.Xv M.law.toMeasure).map Prod.swap = zxLaw M
    rw [compProd_map_condDistrib M.measZ.aemeasurable,
      Measure.map_map measurable_swap (M.measX.prodMk M.measZ)]
    rfl
  have hs : ∀ᵐ zx ∂((xLaw M) ⊗ₘ condDistrib M.Zv M.Xv M.law.toMeasure).map Prod.swap,
      ∀ A : Set ℝ, MeasurableSet A →
        (∫ u in Ioc 0 (M.prop zx.1 zx.2), (outcomeKernel pi (u, zx.2) A).toReal) =
          (canonSubmeasure M true zx.2 (M.prop zx.1 zx.2) A).toReal := by
    rw [hswap]
    exact treated_compatible_toReal (transportData M) pi hp
  exact Measure.ae_ae_of_ae_compProd (ae_of_ae_map measurable_swap.aemeasurable hs)

-- @node: treated_cumulative_evaluation_continuous
/-- For a probability kernel indexed by rank, if [the propensity is continuous in the
instrument](hyp:hc) and [takes values in the closed unit interval](hyp:hp), then
[the mass of any fixed outcome set obtained by integrating the kernel from zero to the
propensity varies continuously with the instrument](goal). -/
@[fun_prop] lemma treated_cumulative_evaluation_continuous
    (K : Kernel ℝ ℝ) [IsMarkovKernel K] (p : Z → ℝ)
    (hc : Continuous p) (hp : ∀ z, p z ∈ Icc (0 : ℝ) 1) (A : Set ℝ) :
    Continuous (fun z => (((volume.restrict (Ioc 0 (p z))).bind K) A).toReal) := by
  have hLip : LipschitzOnWith 1
      (fun q : ℝ => (((volume.restrict (Ioc 0 q)).bind K) A).toReal) (Icc (0 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, selRegion, ↓reduceIte] using
      selected_kernel_lipschitz K true a b ha hb A
  exact hLip.continuousOn.comp_continuous hc hp

-- @node: feasible_treated_conditional_feasible
/-- Under [the model's structural assumptions](hyp:h), if [propensities are continuous
on instrument components for almost every covariate value](hyp:hc), [the instrument has
finitely many connected components](hyp:hfin), and [the treated joint law is
feasible](hyp:hp), then [for almost every covariate value its rank-indexed conditional
outcome kernel is a probability kernel supported on the outcome domain almost everywhere
and reproduces the canonical treated submeasures at every attainable propensity](goal). -/
lemma feasible_treated_conditional_feasible (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (pi : Measure ((ℝ × X) × ℝ)) (hp : IsFeasibleTreated (transportData M) pi) :
    ∀ᵐ x ∂xLaw M, ConditionalTreatedFeasible M x
      ((outcomeKernel pi).comap (fun u : ℝ => (u, x)) (by fun_prop)) := by
  letI := outcomeKernel_isMarkov pi
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  letI : Finite (ConnectedComponents Z) := hfin
  obtain ⟨kap, hkap, hversion, hpos⟩ := h.2.2.2.2.2.1
  filter_upwards [feasible_treated_kernel_section_supported M pi hp,
    treated_compatible_conditional_instrument M pi hp.2.2.2, hc, hversion]
    with x hs hobs hcont hkapx
  let K := (outcomeKernel pi).comap (fun u : ℝ => (u, x)) (by fun_prop)
  let K0 := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  have hpcont := continuous_of_finite_components (fun z => M.prop z x) hcont
  haveI : Measure.IsOpenPosMeasure (condDistrib M.Zv M.Xv M.law.toMeasure x) := by
    refine ⟨fun O hO hne => ?_⟩
    rw [← hkapx]
    exact ne_of_gt (hpos x O hO hne)
  refine ⟨inferInstance, hs, ?_⟩
  rintro p ⟨z, rfl⟩ A hA
  have heq : (fun z => (((volume.restrict (Ioc 0 (M.prop z x))).bind K) A).toReal) =ᵐ[
      condDistrib M.Zv M.Xv M.law.toMeasure x]
      (fun z => (((volume.restrict (Ioc 0 (M.prop z x))).bind K0) A).toReal) := by
    filter_upwards [hobs] with z hz
    rw [← markov_bind_evaluation_integral _ K A hA]
    exact hz A hA
  have he := Measure.eq_of_ae_eq heq
    (treated_cumulative_evaluation_continuous K _ hpcont (fun z => M.rangeProp z x) A)
    (treated_cumulative_evaluation_continuous K0 _ hpcont (fun z => M.rangeProp z x) A)
  calc
    _ = (((volume.restrict (Ioc 0 (M.prop z x))).bind K) A).toReal :=
      markov_bind_evaluation_integral _ K A hA
    _ = _ := congrFun he z

-- @node: feasible_treated_conditional_objective_bounds
/-- Under [the model's structural assumptions](hyp:h), [known minimum and maximum
outcomes](hyp:he), [continuity of propensities on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), if [the target weight is
integrable](hyp:hi) and [the treated joint law is feasible](hyp:hp), then [for almost every
covariate value the rank integral of its weighted conditional mean outcome lies between
the conditional lower and upper bound integrands](goal). -/
lemma feasible_treated_conditional_objective_bounds (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hi : TargetWeightIntegrable M om) (pi : Measure ((ℝ × X) × ℝ))
    (hp : IsFeasibleTreated (transportData M) pi) :
    ∀ᵐ x ∂xLaw M,
      conditionalBoundIntegrand M false om x ≤
        (∫ u in Icc (0 : ℝ) 1, (∫ y, y ∂outcomeKernel pi (u, x)) * om x u) ∧
      (∫ u in Icc (0 : ℝ) 1, (∫ y, y ∂outcomeKernel pi (u, x)) * om x u) ≤
        conditionalBoundIntegrand M true om x := by
  filter_upwards [conditional_feasible_objective_bounds M h he hc hfin om hi,
    feasible_treated_conditional_feasible M h hc hfin pi hp] with x hb hf
  exact (hb _ hf).2

-- @node: feasible_treated_integrated_objective_bounds
/-- Under [the model's structural assumptions](hyp:h), [known minimum and maximum
outcomes](hyp:he), [continuity of propensities on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), if [the target weight is
integrable](hyp:hi), [the conditional lower bound is integrable over covariates](hyp:hl),
[the conditional upper bound is integrable over covariates](hyp:hu), and [the treated
joint law is feasible](hyp:hp), then [its objective lies between the covariate-averaged
lower and upper bounds](goal). -/
lemma feasible_treated_integrated_objective_bounds (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hi : TargetWeightIntegrable M om)
    (hl : Integrable (conditionalBoundIntegrand M false om) (xLaw M))
    (hu : Integrable (conditionalBoundIntegrand M true om) (xLaw M))
    (pi : Measure ((ℝ × X) × ℝ)) (hp : IsFeasibleTreated (transportData M) pi) :
    covariateLowerValue M om ≤ thetaComp om pi ∧
      thetaComp om pi ≤ covariateUpperValue M om := by
  have hd := feasible_treated_objective_disintegration M he om hi pi hp
  have hb := feasible_treated_conditional_objective_bounds M h he hc hfin om hi pi hp
  rw [hd.2]
  exact ⟨integral_mono_ae hl hd.1 (hb.mono fun x hx => hx.1),
    integral_mono_ae hd.1 hu (hb.mono fun x hx => hx.2)⟩

-- @node: attaining_version_lower_isLeast
/-- Under [the model's structural assumptions](hyp:h), [known minimum and maximum
outcomes](hyp:he), [continuity of propensities on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), suppose [the target weight is
measurable](hyp:hm) and [integrable](hyp:hi), [the rank-quantile extension is jointly
measurable, outcome-supported, and agrees with gap quantiles at interior ranks](hyp:hQ),
and [the outcome kernel is an attaining version for this weight and extension](hyp:hK).
Then [the covariate-averaged lower bound is the least feasible treated objective value
and equals the treated lower endpoint](goal). -/
lemma attaining_version_lower_isLeast (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    IsLeast (treatedValueSet (transportData M) om) (covariateLowerValue M om) ∧
      thetaLower1 (transportData M) om = covariateLowerValue M om := by
  letI := hK.1
  let pi := (Causalean.Stat.unifOI.prod (xLaw M)).bind
    (fun ux => (K ux).map (fun y => (ux, y)))
  have hp : IsFeasibleTreated (transportData M) pi :=
    ⟨supported_joint_probability M K,
      supported_joint_support M h K hK.2.1, supported_joint_marginal M K,
      attaining_version_joint_compatible M h hc hfin om hm Q hQ K hK⟩
  have heq : thetaComp om pi = covariateLowerValue M om :=
    attaining_version_joint_cost M h he hc hfin om hm hi Q hQ K hK
  have hl := attaining_version_conditional_bound_integrable M h he hc hfin om hm hi Q hQ K hK
  have hleast : IsLeast (treatedValueSet (transportData M) om) (covariateLowerValue M om) := by
    refine ⟨⟨pi, hp, heq.symm⟩, ?_⟩
    rintro v ⟨pi', hp', rfl⟩
    have hd := feasible_treated_objective_disintegration M he om hi pi' hp'
    have hb := feasible_treated_conditional_objective_bounds M h he hc hfin om hi pi' hp'
    rw [hd.2]
    exact integral_mono_ae hl hd.1 (hb.mono fun x hx => hx.1)
  exact ⟨hleast, hleast.csInf_eq⟩

-- @node: quantile_negation_ae
/-- [For any probability distribution on the real line, the quantile of its negation
equals the negative original quantile at the complementary rank, for almost every rank
under the uniform law on the open unit interval](goal). -/
lemma quantile_negation_ae (nu : Measure ℝ) [IsProbabilityMeasure nu] :
    quantile (nu.map (fun y => -y)) =ᵐ[unifOI] fun t => -quantile nu (1-t) := by
  haveI : IsProbabilityMeasure (nu.map (fun y => -y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let R : ℝ → ℝ := fun t => -quantile nu (1-t)
  have hR : MonotoneOn R (Ioo (0 : ℝ) 1) := by
    intro a ha b hb hab
    apply neg_le_neg
    exact monotoneOn_quantile nu (by constructor <;> linarith [hb.1, hb.2])
      (by constructor <;> linarith [ha.1, ha.2]) (by linarith)
  have hqr : AEMeasurable (quantile nu) (unifOI.map (fun t : ℝ => 1-t)) := by
    rw [map_one_sub_unifOI]
    exact aemeasurable_quantile_unifOI nu
  have hm : AEMeasurable (fun t : ℝ => quantile nu (1-t)) unifOI :=
    hqr.comp_aemeasurable (by fun_prop)
  have hmap : unifOI.map R = nu.map (fun y => -y) := by
    change unifOI.map ((fun y : ℝ => -y) ∘ (fun t => quantile nu (1-t))) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hm]
    have hqmap : unifOI.map (fun t => quantile nu (1-t)) = nu := by
      change unifOI.map (quantile nu ∘ (fun t : ℝ => 1-t)) = nu
      rw [← AEMeasurable.map_map_of_aemeasurable hqr (by fun_prop),
        map_one_sub_unifOI, quantile_map_uniform]
    rw [hqmap]
  have hc := countable_ne_quantile_of_monotoneOn_of_map_eq _ R hR hmap
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hc.ae_notMem volume] with t ht hmem
  exact (not_ne_iff.mp (fun hne => ht ⟨hmem, hne⟩)).symm

-- @node: weightLaw_negation
/-- If [the target weight is measurable](hyp:hm), [the gap index is below the number of
gaps at the given covariate value](hyp:hk), and [the gap has strictly positive
length](hyp:hab), then [the distribution of the negated weight on that gap is the
distribution of the original weight reflected about zero](goal). -/
lemma weightLaw_negation (om : X → ℝ → ℝ) (hm : TargetWeightMeasurable om)
    (x : X) (k : ℕ) (hk : k < (CondRangeDecomposition M x).count)
    (hab : (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k) :
    weightLaw M (fun x u => -om x u) x k = (weightLaw M om x k).map (fun y => -y) := by
  have ha := gap_weight_aemeasurable M om hm x k hk
  exact (AEMeasurable.map_map_of_aemeasurable (by fun_prop) ha).symm

-- @node: conditional_bound_weight_negation
/-- If [the target weight is measurable](hyp:hm), then [at each covariate value the
conditional lower bound for the negated weight equals the negative conditional upper
bound for the original weight](goal). -/
lemma conditional_bound_weight_negation (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (x : X) :
    conditionalBoundIntegrand M false (fun x u => -om x u) x =
      -conditionalBoundIntegrand M true om x := by
  let D := CondRangeDecomposition M x
  have hg : ∀ k < D.count,
      max 0 (D.gapHi k - D.gapLo k) *
        (∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M (fun x u => -om x u) x k).1 t *
          (gapQuantiles M (fun x u => -om x u) x k).2 (1-t)) =
      -(max 0 (D.gapHi k - D.gapLo k) *
        ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t * (gapQuantiles M om x k).2 t) := by
    intro k hk
    by_cases hab : D.gapLo k < D.gapHi k
    · haveI : IsProbabilityMeasure (gapUnif M x k) := uniformInterval_isProbability _ _ hab
      haveI : IsProbabilityMeasure (weightLaw M om x k) :=
        Measure.isProbabilityMeasure_map (gap_weight_aemeasurable M om hm x k hk)
      have hq := quantile_negation_ae (weightLaw M om x k)
      have hqr : ∀ᵐ t ∂unifOI,
          quantile ((weightLaw M om x k).map (fun y => -y)) (1-t) =
            -quantile (weightLaw M om x k) t := by
        have hh : ∀ᵐ t ∂unifOI.map (fun t : ℝ => 1-t),
            quantile ((weightLaw M om x k).map (fun y => -y)) t =
              -quantile (weightLaw M om x k) (1-t) := by
          rw [map_one_sub_unifOI]
          exact hq
        simpa only [sub_sub_cancel] using ae_of_ae_map (by fun_prop) hh
      have hi : (∫ t in Ioo (0 : ℝ) 1,
          (gapQuantiles M (fun x u => -om x u) x k).1 t *
            (gapQuantiles M (fun x u => -om x u) x k).2 (1-t)) =
          -(∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
            (gapQuantiles M om x k).2 t) := by
        calc
          _ = ∫ t in Ioo (0 : ℝ) 1, -((gapQuantiles M om x k).1 t *
              (gapQuantiles M om x k).2 t) := by
            apply integral_congr_ae
            filter_upwards [hqr] with t ht
            simp only [gapQuantiles, weightLaw_negation M om hm x k hk hab, ht, mul_neg]
          _ = _ := integral_neg _
      rw [hi, mul_neg]
    · rw [max_eq_left (sub_nonpos.mpr (le_of_not_gt hab))]
      simp only [zero_mul, neg_zero]
  have hgs : (∑ k ∈ Finset.range D.count,
      max 0 (D.gapHi k - D.gapLo k) *
        ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M (fun x u => -om x u) x k).1 t *
          (gapQuantiles M (fun x u => -om x u) x k).2 (1-t)) =
      -(∑ k ∈ Finset.range D.count, max 0 (D.gapHi k - D.gapLo k) *
        ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t * (gapQuantiles M om x k).2 t) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k hk => hg k (Finset.mem_range.mp hk)
  have ht : (∫ u in D.tail, M.yMin * max 0 (-om x u) + M.yMax * min 0 (-om x u)) =
      -(∫ u in D.tail, M.yMax * max 0 (om x u) + M.yMin * min 0 (om x u)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hw : 0 ≤ om x u
    · rw [max_eq_right hw, min_eq_left hw, max_eq_left (neg_nonpos.mpr hw),
        min_eq_right (neg_nonpos.mpr hw)]
      ring
    · have hw' := (le_of_not_ge hw)
      rw [max_eq_left hw', min_eq_right hw', max_eq_right (neg_nonneg.mpr hw'),
        min_eq_left (neg_nonneg.mpr hw')]
      ring
  simp only [conditionalBoundIntegrand, Bool.false_eq_true, ↓reduceIte]
  rw [hgs, ht]
  simp only [mul_neg, integral_neg, Finset.sum_neg_distrib, neg_add_rev]
  ring

-- @node: thetaComp_weight_negation
/-- [Negating the target weight negates the component objective for any joint law of
latent rank, covariates, and outcome](goal). -/
lemma thetaComp_weight_negation (om : X → ℝ → ℝ) (pi : Measure ((ℝ × X) × ℝ)) :
    thetaComp (fun x u => -om x u) pi = -thetaComp om pi := by
  simp only [thetaComp, mul_neg, integral_neg]

-- @node: endpoint_gap_quantile_rank_extension
/-- Under [the model's structural assumptions](hyp:h), [known minimum and maximum
outcomes](hyp:he), [continuity of propensities on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), [there exists a jointly measurable
extension of the gap quantiles that, for almost every covariate value and every gap of
positive length, lies in the outcome domain at all ranks in the closed unit interval
and agrees with the gap quantile at every interior rank](goal). -/
lemma endpoint_gap_quantile_rank_extension (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) :
    ∃ Q : X → ℕ → ℝ → ℝ, RankKernelExtensionReading M Q := by
  obtain ⟨Q, hQmeas, hQeq⟩ := measurable_gap_quantile_extension M h he hc hfin
  refine ⟨Q, hQmeas, ?_⟩
  filter_upwards [hQeq, conditional_gap_quantile_supported M h he hfin hc] with x hQx hx
  intro k hk hab
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [hQx k hk hab t ht]
    exact hx k hk hab t ht
  intro t ht
  rw [hQx k hk hab t ⟨ht.1.le, ht.2.le⟩]
  simp only [endpointGapQuantile, if_neg (ne_of_gt ht.1), if_neg (ne_of_lt ht.2)]

-- @node: conditional_sharp_bounds_assembly
/-- Under [the model's structural assumptions](hyp:h), [known minimum and maximum
outcomes](hyp:he), [measurability of the target weight](hyp:hm), [integrability of that
weight](hyp:hi), [continuity of propensities on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), [both conditional bound integrands are
integrable over covariates, their averages are respectively the least and greatest
feasible treated objective values, and those averages equal the treated lower and upper
endpoints](goal). -/
lemma conditional_sharp_bounds_assembly (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z) :
    Integrable (conditionalBoundIntegrand M false om) (xLaw M) ∧
      Integrable (conditionalBoundIntegrand M true om) (xLaw M) ∧
      IsLeast (treatedValueSet (transportData M) om) (covariateLowerValue M om) ∧
      IsGreatest (treatedValueSet (transportData M) om) (covariateUpperValue M om) ∧
      thetaLower1 (transportData M) om = covariateLowerValue M om ∧
      thetaUpper1 (transportData M) om = covariateUpperValue M om := by
  obtain ⟨Q, hQ⟩ := endpoint_gap_quantile_rank_extension M h he hc hfin
  obtain ⟨K, hK⟩ := exists_attaining_kernel_version M om Q h he hm hc hfin hQ
  have hl := attaining_version_conditional_bound_integrable M h he hc hfin om hm hi Q hQ K hK
  have hleast := attaining_version_lower_isLeast M h he hc hfin om hm hi Q hQ K hK
  let omNeg : X → ℝ → ℝ := fun x u => -om x u
  have hmNeg : TargetWeightMeasurable omNeg := by
    change Measurable (fun xu : X × Icc (0 : ℝ) 1 => -om xu.1 xu.2.val)
    exact hm.neg
  have hiNeg : TargetWeightIntegrable M omNeg := hi.neg
  obtain ⟨Kn, hKn⟩ := exists_attaining_kernel_version M omNeg Q h he hmNeg hc hfin hQ
  have hln := attaining_version_conditional_bound_integrable M h he hc hfin omNeg hmNeg hiNeg Q hQ Kn hKn
  have hu : Integrable (conditionalBoundIntegrand M true om) (xLaw M) := by
    apply hln.neg.congr
    filter_upwards [] with x
    change -conditionalBoundIntegrand M false (fun x u => -om x u) x = _
    rw [conditional_bound_weight_negation M om hm, neg_neg]
  have hv : covariateLowerValue M omNeg = -covariateUpperValue M om := by
    change (∫ x, conditionalBoundIntegrand M false (fun x u => -om x u) x ∂xLaw M) = _
    simp_rw [conditional_bound_weight_negation M om hm]
    exact integral_neg _
  letI := hKn.1
  let pin := (unifOI.prod (xLaw M)).bind (fun ux => (Kn ux).map (fun y => (ux, y)))
  have hpin : IsFeasibleTreated (transportData M) pin :=
    ⟨supported_joint_probability M Kn, supported_joint_support M h Kn hKn.2.1,
      supported_joint_marginal M Kn,
      attaining_version_joint_compatible M h hc hfin omNeg hmNeg Q hQ Kn hKn⟩
  have hcost : thetaComp om pin = covariateUpperValue M om := by
    have hh := attaining_version_joint_cost M h he hc hfin omNeg hmNeg hiNeg Q hQ Kn hKn
    change thetaComp (fun x u => -om x u) pin = covariateLowerValue M omNeg at hh
    rw [thetaComp_weight_negation, hv] at hh
    exact neg_injective hh
  have hgreatest : IsGreatest (treatedValueSet (transportData M) om) (covariateUpperValue M om) := by
    refine ⟨⟨pin, hpin, hcost.symm⟩, ?_⟩
    rintro v ⟨pi, hp, rfl⟩
    exact (feasible_treated_integrated_objective_bounds M h he hc hfin om hi hl hu pi hp).2
  exact ⟨hl, hu, hleast.1, hgreatest, hleast.2, hgreatest.csSup_eq⟩

end Papers.TbsPrteOptimalTransport
