module
public import Papers.TbsNeuralCausalPi.Helpers.DescendantNoise
public import Papers.TbsNeuralCausalPi.Helpers.InterventionalMoments
/-! # Adjustment by integrating the independent descendant simulation

The finite interventional moment follows by induction through the structural
evaluation from bounded non-Gumbel inputs and Lipschitz continuous mechanisms.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false
set_option linter.unusedVariables false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- If [there is no hidden confounding](hyp:hnoconf) and [the model's named
latent inputs are jointly independent](hyp:hind), then [the observed
non-descendant vector is independent of the exogenous vector restricted to
the latent inputs used by strict descendants of the treatment](goal). -/
-- @node: nonDescendant_indep_private_noise
lemma nonDescendant_indep_private_noise
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM) (T : Fin n) :
    IndepFun (fun u => nonDescendantProjection (dag := dag) T
      (intervenedEval M.toEuclideanSCM (fun _ => none) u))
      (restrictLatentFamily (descendantLatentIndices (dag := dag) (C := C) T))
      M.latentLaw := by
  let S := descendantLatentIndices (dag := dag) (C := C) T
  let A : Exogenous kind dims → Joint kind := fun u =>
    nonDescendantProjection (dag := dag) T
      (intervenedEval M.toEuclideanSCM (fun _ => none) u)
  have hm : Measurable A := by
    first | fun_prop | skip
    have hv : Measurable (intervenedEval M.toEuclideanSCM (fun _ => none)) :=
      evalSteps_measurable M.toEuclideanSCM (fun _ => none) (n*n+n)
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro ⟨i,j⟩
    dsimp [A, nonDescendantProjection]
    split_ifs
    · exact (measurable_pi_apply _).comp (scm_ofLp_measurable.comp hv)
    · exact measurable_const
  have he : A ∘ restrictLatentFamily Sᶜ = A := by
    funext u
    apply WithLp.ofLp_injective
    funext ⟨i,j⟩
    dsimp [A, nonDescendantProjection]
    split_ifs with hi
    · exact (nonDescendantEval_restrict_complement_noise M hnoconf T u i
        (Finset.mem_filter.mp hi).2.2 j).symm
    · rfl
  have h := (restrictLatentFamily_indepFun M.toEuclideanSCM hind Sᶜ S
    disjoint_compl_left).comp hm measurable_id
  change IndepFun A (restrictLatentFamily S) M.toEuclideanSCM.latentLaw
  simpa only [he, Function.id_comp] using h

/-- For [a scalar outcome](hyp:hY) and [a nonnegative regularity constant](hyp:L),
assume [jointly independent named latent inputs](hyp:hind), [no hidden
confounding](hyp:hnoconf), [continuous mechanisms Lipschitz with that
constant](hyp:hcont), [categorical propensities Lipschitz with that
constant](hyp:hprop), [variables bounded by the given bound](hyp:hbound), and
[an admissible intervention at the chosen treatment dose](hyp:ht). Then [the
descendant mean is integrable over the observational non-descendant law, and
its integral equals the mean outcome under that treatment intervention](goal). -/
-- @node: descendantMean_adjustment_and_integrable
lemma descendantMean_adjustment_and_integrable (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hY : valueDim (kind Y) = 1) (K : ℝ) (L : ℝ≥0)
    (hind : LatentBlocksIndependent M.toEuclideanSCM) (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) (t : ℝ)
    (ht : AdmissibleIntervention kind (singleIntervention T t)) :
    Integrable (fun a => descendantMean M T Y hY a t)
      ((observationalLaw M.toEuclideanSCM).map (nonDescendantProjection (dag := dag) T)) ∧
    meanOutcome M.toEuclideanSCM T Y hY t =
      ∫ a, descendantMean M T Y hY a t ∂((observationalLaw M.toEuclideanSCM).map
        (nonDescendantProjection (dag := dag) T)) := by
  have hinterventional : Integrable (fun u => scalarOutcome Y hY
      (intervenedEval M.toEuclideanSCM (singleIntervention T t) u)) M.latentLaw := by
    simpa only [CanonicalSCM.toEuclideanSCM] using
      interventional_scalarOutcome_integrable M.toEuclideanSCM
        L hcont K hbound (singleIntervention T t) ht Y hY
  letI := M.latentLaw_probability
  let v := intervenedEval M.toEuclideanSCM (fun _ => none)
  let A : Exogenous kind dims → Joint kind :=
    fun u => nonDescendantProjection (dag := dag) T (v u)
  let Z : Exogenous kind dims → Exogenous kind dims :=
    restrictLatentFamily (descendantLatentIndices (dag := dag) (C := C) T)
  let F : Joint kind × Exogenous kind dims → ℝ := fun z =>
    scalarOutcome Y hY (intervenedEval M.toEuclideanSCM
      (fun i => if i = T then some (WithLp.toLp 1 (fun _ => t)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j => z.1.ofLp ⟨i,j⟩)) else none) z.2)
  have hv : Measurable v := by
    first | fun_prop | exact evalSteps_measurable M.toEuclideanSCM _ _
  have hproj : Measurable (nonDescendantProjection (dag := dag) (kind := kind) T) := by
    first | fun_prop | skip
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro ⟨i,j⟩
    dsimp [nonDescendantProjection]
    split_ifs <;> fun_prop
  have hA : Measurable A := hproj.comp hv
  have hZ : Measurable Z := restrictLatentFamily_measurable _
  have hF : Measurable F := by
    first | fun_prop | skip
    have hd := (descendantEval_measurable M T).comp
      ((measurable_fst.prodMk (measurable_const (a := t))).prodMk measurable_snd)
    exact (measurable_pi_apply _).comp (scm_ofLp_measurable.comp hd)
  have hindep : IndepFun A Z M.latentLaw :=
    nonDescendant_indep_private_noise M hnoconf hind T
  have heq (u : Exogenous kind dims) : F (A u, Z u) =
      scalarOutcome Y hY (intervenedEval M.toEuclideanSCM (singleIntervention T t) u) := by
    exact congrArg (scalarOutcome Y hY)
      ((descendantEval_restrict_private_noise M T (A u) t u).symm.trans
        (descendantEval_eq_singleIntervention M T t u))
  have hiF : Integrable F ((M.latentLaw.map A).prod (M.latentLaw.map Z)) := by
    rw [← hindep.map_prod_eq_prod_map_map hA.aemeasurable hZ.aemeasurable]
    apply (integrable_map_measure hF.aestronglyMeasurable
      (hA.prodMk hZ).aemeasurable).2
    change Integrable (fun u => F (A u, Z u)) M.latentLaw
    simpa only [heq] using hinterventional
  have he := integral_indepFun_eq_iterated M.latentLaw A Z F
    hA.aemeasurable hZ.aemeasurable hindep hiF
  have hmean (a : Joint kind) :
      (∫ z, F (a,z) ∂M.latentLaw.map Z) = descendantMean M T Y hY a t :=
    (descendantMean_eq_integral_private_noise M T Y hY a t).symm
  have hlaw : M.latentLaw.map A =
      (observationalLaw M.toEuclideanSCM).map (nonDescendantProjection (dag := dag) T) := by
    exact (Measure.map_map hproj hv).symm
  constructor
  · have hi := hiF.integral_prod_left
    simpa only [hmean, hlaw] using hi
  · simpa only [heq, hmean, hlaw, meanOutcome, CanonicalSCM.toEuclideanSCM] using he

/-- For [a scalar outcome](hyp:hY) and [a nonnegative regularity constant](hyp:L),
if [the named latent inputs are jointly independent](hyp:hind), [there is no
hidden confounding](hyp:hnoconf), [continuous mechanisms are Lipschitz with
that constant](hyp:hcont), [categorical propensities are Lipschitz with that
constant](hyp:hprop), [variables satisfy the given uniform bound](hyp:hbound),
and [the chosen treatment intervention is admissible](hyp:ht), then [the
interventional mean outcome equals the descendant mean averaged over the
observational distribution of non-descendants](goal). -/
-- @node: descendantMean_adjustment
lemma descendantMean_adjustment (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hY : valueDim (kind Y) = 1) (K : ℝ) (L : ℝ≥0)
    (hind : LatentBlocksIndependent M.toEuclideanSCM) (hnoconf : NoHiddenConfounding G)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) (t : ℝ)
    (ht : AdmissibleIntervention kind (singleIntervention T t)) :
    meanOutcome M.toEuclideanSCM T Y hY t =
      ∫ a, descendantMean M T Y hY a t ∂((observationalLaw M.toEuclideanSCM).map
        (nonDescendantProjection (dag := dag) T)) :=
  (descendantMean_adjustment_and_integrable M T Y hY K L hind hnoconf hcont hprop hbound t ht).2

end
end Papers.TbsNeuralCausalPi
