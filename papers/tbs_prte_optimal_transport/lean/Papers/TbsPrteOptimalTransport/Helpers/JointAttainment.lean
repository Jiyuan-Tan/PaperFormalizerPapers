module
public import Papers.TbsPrteOptimalTransport.Helpers.RegionIntegration
/-! Joint-law integration for the conditional attaining kernel. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: kernel_joint_bind_eq_compProd
/-- [Drawing a first coordinate from a sigma-finite measure and then a second
coordinate from a sigma-finite conditional kernel gives the same joint measure
as the measure–kernel product](goal). -/
lemma kernel_joint_bind_eq_compProd {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (mu : Measure A) [SFinite mu]
    (K : Kernel A B) [IsSFiniteKernel K] :
    mu.bind (fun a => (K a).map (fun b => (a, b))) = mu ⊗ₘ K := by
  have hm : Measurable (fun a => (K a).map (fun b => (a, b))) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.map_apply measurable_prodMk_left hs]
    exact Kernel.measurable_kernel_prodMk_left hs
  ext s hs
  rw [Measure.bind_apply hs hm.aemeasurable, Measure.compProd_apply hs]
  apply lintegral_congr
  intro a
  exact Measure.map_apply measurable_prodMk_left hs

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: supported_joint_probability
/-- [Combining an independent uniform rank and the model's covariate distribution
with a probability kernel for outcomes produces a joint probability measure](goal). -/
lemma supported_joint_probability (K : Kernel (ℝ × X) ℝ) [IsMarkovKernel K] :
    IsProbabilityMeasure ((Causalean.Stat.unifOI.prod (xLaw M)).bind
      (fun ux => (K ux).map (fun y => (ux, y)))) := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  rw [kernel_joint_bind_eq_compProd]
  infer_instance

-- @node: supported_joint_marginal
/-- [The rank–covariate marginal of the joint law formed by drawing outcomes from
a probability kernel is the product of the uniform rank law and the model's
covariate law](goal). -/
lemma supported_joint_marginal (K : Kernel (ℝ × X) ℝ) [IsMarkovKernel K] :
    ((Causalean.Stat.unifOI.prod (xLaw M)).bind
      (fun ux => (K ux).map (fun y => (ux, y)))).fst =
        Causalean.Stat.unifOI.prod (xLaw M) := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  rw [kernel_joint_bind_eq_compProd, Measure.fst_compProd]

-- @node: supported_joint_support
/-- Under [the model's structural assumptions](hyp:h), if [each conditional outcome
law assigns zero mass outside the model's outcome set](hyp:hs), then [the joint
law assigns zero mass outside rank–outcome pairs with rank between zero and one
and outcome in that set](goal). -/
lemma supported_joint_support (h : StructuralAssumptions M)
    (K : Kernel (ℝ × X) ℝ) [IsMarkovKernel K]
    (hs : ∀ ux, K ux M.Ysetᶜ = 0) :
    ((Causalean.Stat.unifOI.prod (xLaw M)).bind
      (fun ux => (K ux).map (fun y => (ux, y))))
        {a | a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2 ∈ M.Yset}ᶜ = 0 := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  rw [kernel_joint_bind_eq_compProd]
  have hu : ∀ᵐ ux ∂Causalean.Stat.unifOI.prod (xLaw M),
      ux.1 ∈ Icc (0 : ℝ) 1 := by
    apply (measurePreserving_fst (μ := Causalean.Stat.unifOI)
      (ν := xLaw M)).quasiMeasurePreserving.ae
    exact (ae_restrict_mem measurableSet_Ioo).mono fun u hu => ⟨hu.1.le, hu.2.le⟩
  have ha : ∀ᵐ a ∂(Causalean.Stat.unifOI.prod (xLaw M)) ⊗ₘ K,
      a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2 ∈ M.Yset := by
    apply Measure.ae_compProd_of_ae_ae
    · exact (measurable_fst.fst measurableSet_Icc).inter
        (measurable_snd h.2.2.2.2.2.2.1.measurableSet)
    · filter_upwards [hu] with ux hux
      have hy : ∀ᵐ y ∂K ux, y ∈ M.Yset := ae_iff.mpr (hs ux)
      exact hy.mono fun y hy => ⟨hux, hy⟩
  exact ae_iff.mp ha

-- @node: supported_joint_weighted_integrable
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
if [the target weight is integrable over covariates and ranks](hyp:hi) and [every
conditional outcome law is supported on the model's outcome set](hyp:hs), then
[the outcome multiplied by the target weight is integrable under the joint law](goal). -/
lemma supported_joint_weighted_integrable (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (om : X → ℝ → ℝ)
    (hi : TargetWeightIntegrable M om) (K : Kernel (ℝ × X) ℝ)
    [IsMarkovKernel K] (hs : ∀ ux, K ux M.Ysetᶜ = 0) :
    Integrable (fun a : (ℝ × X) × ℝ => a.2 * om a.1.2 a.1.1)
      ((Causalean.Stat.unifOI.prod (xLaw M)) ⊗ₘ K) := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  let mu := Causalean.Stat.unifOI.prod (xLaw M)
  have hw : Integrable (fun ux : ℝ × X => om ux.2 ux.1) mu := by
    have hi' : Integrable (Function.uncurry om) ((xLaw M).prod Causalean.Stat.unifOI) := by
      simpa only [TargetWeightIntegrable, Causalean.Stat.unifOI,
        restrict_Ioo_eq_restrict_Icc] using hi
    exact hi'.swap
  have hwj : Integrable (fun a : (ℝ × X) × ℝ => om a.1.2 a.1.1) (mu ⊗ₘ K) := by
    have hw' : Integrable (fun ux : ℝ × X => om ux.2 ux.1)
        ((mu ⊗ₘ K).map Prod.fst) := by
      rw [← Measure.fst, Measure.fst_compProd]
      exact hw
    exact hw'.comp_measurable measurable_fst
  have hb : ∀ᵐ a ∂mu ⊗ₘ K, ‖a.2‖ ≤ outcomeMagnitude M := by
    apply Measure.ae_compProd_of_ae_ae
    · exact measurableSet_le measurable_snd.norm measurable_const
    · filter_upwards [] with ux
      exact supported_outcome_norm_bound M h he (K ux) (hs ux)
  exact hwj.bdd_mul (by fun_prop) hb

-- @node: supported_joint_objective_disintegration
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
if [the target weight is integrable over covariates and ranks](hyp:hi) and [every
conditional outcome law is supported on the outcome set](hyp:hs), then [the joint
weighted-outcome objective equals the covariate average of the rank integral of
the conditional outcome mean times the target weight](goal). -/
lemma supported_joint_objective_disintegration (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (om : X → ℝ → ℝ)
    (hi : TargetWeightIntegrable M om) (K : Kernel (ℝ × X) ℝ)
    [IsMarkovKernel K] (hs : ∀ ux, K ux M.Ysetᶜ = 0) :
    thetaComp om ((Causalean.Stat.unifOI.prod (xLaw M)) ⊗ₘ K) =
      ∫ x, (∫ u in Icc (0 : ℝ) 1, (∫ y, y ∂K (u, x)) * om x u) ∂xLaw M := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hf := supported_joint_weighted_integrable M h he om hi K hs
  have hmean := hf.integral_compProd
  simp only [Kernel.prodMkLeft_apply, Kernel.const_apply, integral_mul_const] at hmean
  rw [thetaComp, Measure.integral_compProd hf]
  simp only [integral_mul_const]
  rw [integral_prod_symm _ hmean]
  simp only [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc]

-- @node: attaining_version_joint_cost
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of the propensity on instrument components](hyp:hc), and [finitely many
instrument components](hyp:hfin), suppose [the target weight is measurable](hyp:hm)
and [integrable](hyp:hi), [the rank functions provide a rank-kernel extension](hyp:hQ),
and [the outcome kernel is an attaining version for those rank functions and
weights](hyp:hK). Then [the weighted-outcome objective of the resulting joint
law equals the covariate-integrated lower value](goal). -/
lemma attaining_version_joint_cost (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q)
    (K : Kernel (ℝ × X) ℝ) (hK : IsAttainingKernelVersion M om Q K) :
    thetaComp om ((Causalean.Stat.unifOI.prod (xLaw M)).bind
      (fun ux => (K ux).map (fun y => (ux, y)))) = covariateLowerValue M om := by
  letI := hK.1
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  rw [kernel_joint_bind_eq_compProd,
    supported_joint_objective_disintegration M h he om hi K hK.2.1]
  exact attaining_version_integrated_bound M h he hc hfin om hm hi Q hQ K hK

end Papers.TbsPrteOptimalTransport
