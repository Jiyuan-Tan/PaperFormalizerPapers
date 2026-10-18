module
public import Papers.TbsNeuralCausalPi.Helpers.DescendantNoise
public import Causalean.Mathlib.MeasureTheory.CondExpPreimage
/-! # Structural descendant simulation as an observational regression version

Independence identifies the joint input law as a product. Fubini on each
measurable covariate event then identifies the conditional expectation.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section

/-- Suppose [the observation map is measurable](hyp:hv), [the covariate map
is measurable](hyp:hs), [the noise map is measurable](hyp:hz), [the outcome is measurable](hyp:hY)
and [integrable after observation](hyp:hiY), and [the simulation function is
measurable](hyp:hF). If [the observed covariates and noise are independent](hyp:hind)
and [simulation at their realized values exactly reproduces the observed
outcome](hyp:heq), then [averaging simulation over the noise law gives the
conditional mean of the outcome given the covariates, almost everywhere
under the observation law](goal). -/
-- @node: regression_version_of_independent_simulation
lemma regression_version_of_independent_simulation
    {Ω V X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    [MeasurableSpace X] [MeasurableSpace Z]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (v : Ω → V) (s : V → X) (z : Ω → Z)
    (hv : Measurable v) (hs : Measurable s) (hz : Measurable z)
    (Y : V → ℝ) (hY : Measurable Y) (hiY : Integrable (fun u => Y (v u)) mu)
    (F : X × Z → ℝ) (hF : Measurable F)
    (hind : IndepFun (s ∘ v) z mu)
    (heq : ∀ u, F (s (v u), z u) = Y (v u)) :
    (fun w => ∫ e, F (s w, e) ∂mu.map z) =ᵐ[mu.map v]
      (mu.map v)[Y | MeasurableSpace.comap s inferInstance] := by
  let rho := mu.map v
  let eta := mu.map z
  let xi := mu.map (s ∘ v)
  have hp : mu.map (fun u => (s (v u), z u)) = xi.prod eta :=
    hind.map_prod_eq_prod_map_map (hs.comp hv).aemeasurable hz.aemeasurable
  have hiF : Integrable F (xi.prod eta) := by
    rw [← hp]
    apply (integrable_map_measure hF.aestronglyMeasurable
      ((hs.comp hv).prodMk hz).aemeasurable).2
    change Integrable (fun u => F (s (v u), z u)) mu
    simpa only [heq] using hiY
  have hm : Measurable (fun x => ∫ e, F (x,e) ∂eta) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  have hxis : rho.map s = xi := Measure.map_map hs hv
  have hi : Integrable (fun w => ∫ e, F (s w,e) ∂eta) rho := by
    apply (integrable_map_measure hm.aestronglyMeasurable hs.aemeasurable).1
    rw [hxis]
    exact hiF.integral_prod_left
  have hy : Integrable Y rho :=
    (integrable_map_measure hY.aestronglyMeasurable hv.aemeasurable).2 hiY
  have hsm : AEStronglyMeasurable[MeasurableSpace.comap s inferInstance]
      (fun w => ∫ e, F (s w,e) ∂eta) rho := by
    exact (hm.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable.aestronglyMeasurable
  apply (Causalean.Mathlib.MeasureTheory.condExp_eq_of_integral_preimage_eq
    rho s hs Y _ hy hi hsm ?_).symm
  intro S hS
  let H : X × Z → ℝ := (S ×ˢ Set.univ).indicator F
  have hH : Integrable H (xi.prod eta) := hiF.indicator (hS.prod MeasurableSet.univ)
  have he := integral_indepFun_eq_iterated mu (s ∘ v) z H
    (hs.comp hv).aemeasurable hz.aemeasurable hind hH
  have hleft : (∫ u, H (s (v u), z u) ∂mu) = ∫ w in s ⁻¹' S, Y w ∂rho := by
    rw [← integral_indicator (hS.preimage hs), integral_map hv.aemeasurable
      (hY.indicator (hS.preimage hs)).aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases hu : s (v u) ∈ S <;> simp [H, hu, heq]
  have hright : (∫ x, ∫ e, H (x,e) ∂eta ∂xi) =
      ∫ w in s ⁻¹' S, (∫ e, F (s w,e) ∂eta) ∂rho := by
    rw [← integral_indicator (hS.preimage hs)]
    have hinner : (fun x => ∫ e, H (x,e) ∂eta) =
        S.indicator (fun x => ∫ e, F (x,e) ∂eta) := by
      funext x
      by_cases hx : x ∈ S <;> simp [H, hx]
    rw [hinner, ← hxis, integral_map hs.aemeasurable
      (hm.indicator hS).aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by
      by_cases hw : s w ∈ S <;> simp [hw]
  exact hleft.symm.trans (he.trans hright)

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- Suppose [the outcome is scalar](hyp:hY) and [treatment is scalar](hyp:hT), with
[a nonnegative regularity constant L](hyp:L), [independent latent blocks](hyp:hind),
[no hidden confounding](hyp:hnoconf), [L-Lipschitz continuous mechanisms](hyp:hcont),
[L-Lipschitz categorical propensities](hyp:hprop), and [variables bounded
at K](hyp:hbound). Then [the descendant simulation mean at the observed
non-descendants and treatment equals the conditional mean of the outcome
given those covariates and treatment, almost everywhere under the
observational law](goal). -/
-- @node: descendantMean_regression_version
lemma descendantMean_regression_version (M : CanonicalSCM kind dims dag G C)
    (T Y : Fin n) (hY : valueDim (kind Y) = 1) (hT : valueDim (kind T) = 1)
    (K : ℝ) (L : ℝ≥0) (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hnoconf : NoHiddenConfounding G) (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K) :
    (fun v => descendantMean M T Y hY (nonDescendantProjection (dag := dag) T v)
      (scalarOutcome T hT v)) =ᵐ[observationalLaw M.toEuclideanSCM]
      (observationalLaw M.toEuclideanSCM)[scalarOutcome Y hY |
        MeasurableSpace.comap (fun v => (nonDescendantProjection (dag := dag) T v,
          scalarOutcome T hT v)) (borel _)] := by
  classical
  letI : BorelSpace (Joint kind) := ⟨rfl⟩
  letI := M.latentLaw_probability
  let v := intervenedEval M.toEuclideanSCM (fun _ => none)
  let s : Joint kind → Joint kind × ℝ := fun w =>
    (nonDescendantProjection (dag := dag) T w, scalarOutcome T hT w)
  let z : Exogenous kind dims → Exogenous kind dims := restrictLatentFamily (descendantLatentIndices (dag := dag) (C := C) T)
  let F : (Joint kind × ℝ) × Exogenous kind dims → ℝ := fun w =>
    scalarOutcome Y hY (intervenedEval M.toEuclideanSCM
      (fun i => if i = T then some (WithLp.toLp 1 (fun _ => w.1.2)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j => w.1.1.ofLp ⟨i,j⟩)) else none) w.2)
  have hv : Measurable v := by
    first | fun_prop | exact evalSteps_measurable M.toEuclideanSCM _ _
  have hs : Measurable s := by
    first | fun_prop | skip
    apply Measurable.prodMk
    · apply scm_toLp_measurable.comp
      apply measurable_pi_lambda
      rintro ⟨i,j⟩
      dsimp [nonDescendantProjection]
      split_ifs <;> fun_prop
    · fun_prop [scalarOutcome]
  have hz : Measurable z := restrictLatentFamily_measurable _
  have hFY : Measurable (scalarOutcome Y hY : Joint kind → ℝ) := by
    fun_prop [scalarOutcome]
  have hF : Measurable F := by
    first | fun_prop | exact hFY.comp (descendantEval_measurable M T)
  have hiY : Integrable (fun u => scalarOutcome Y hY (v u)) M.latentLaw := by
    apply Integrable.of_bound (hFY.comp hv).aestronglyMeasurable K
    filter_upwards [hbound.2] with u hu
    exact hu.1 Y _
  have hindep : IndepFun (s ∘ v) z M.latentLaw :=
    nonDescendant_treatment_indep_private_noise M hnoconf hind T hT
  have heq : ∀ u, F (s (v u), z u) = scalarOutcome Y hY (v u) := by
    intro u
    exact congrArg (scalarOutcome Y hY)
      (observationalEval_descendant_noise_factorization M T hT u)
  have h := regression_version_of_independent_simulation M.latentLaw v s z hv hs hz
    (scalarOutcome Y hY) hFY hiY F hF hindep heq
  have hmean : (fun w => ∫ e, F (s w,e) ∂M.latentLaw.map z) =
      (fun w => descendantMean M T Y hY
        (nonDescendantProjection (dag := dag) T w) (scalarOutcome T hT w)) := by
    funext w
    exact (descendantMean_eq_integral_private_noise M T Y hY _ _).symm
  rw [hmean] at h
  rw [← (inferInstance : BorelSpace (Joint kind × ℝ)).measurable_eq]
  exact h


end
end Papers.TbsNeuralCausalPi
