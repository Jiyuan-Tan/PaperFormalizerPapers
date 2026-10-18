module
public import Papers.TbsNeuralCausalPi.Helpers.EvaluationKernels
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseOverlap
public import Mathlib.Probability.Kernel.Disintegration.Unique
/-! # Lifting overlap through an independent structural simulation

A treatment generated from a parent vector and noise independent of a larger
covariate vector has the same transition kernel at both levels of conditioning.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

-- @node: independent_simulation_joint_eq_compProd
/-- If [the covariate vector is measurable](hyp:ha), [the private noise is
measurable](hyp:hz), [the simulation rule is measurable](hyp:hF), and [the covariates
and noise are independent](hyp:hind), [the joint law of the covariates and simulated
outcome equals the covariate law combined with the transition law obtained by
integrating the simulation rule over the noise distribution](goal). -/
lemma independent_simulation_joint_eq_compProd
    {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (a : Ω → X) (z : Ω → Z) (F : X × Z → ℝ)
    (ha : Measurable a) (hz : Measurable z) (hF : Measurable F)
    (hind : IndepFun a z mu) :
    mu.map (fun u => (a u, F (a u, z u))) =
      (mu.map a).compProd (privateNoiseUpdateKernel (mu.map z) F hF) := by
  haveI : IsProbabilityMeasure (mu.map z) := Measure.isProbabilityMeasure_map hz.aemeasurable
  have hp := hind.map_prod_eq_prod_map_map ha.aemeasurable hz.aemeasurable
  have hH : Measurable (fun w : X × Z => (w.1, F w)) := by fun_prop
  have he : mu.map (fun u => (a u, F (a u, z u))) =
      ((mu.map a).prod (mu.map z)).map (fun w => (w.1, F w)) := by
    rw [← hp, Measure.map_map hH (ha.prodMk hz)]
    rfl
  rw [he]
  ext S hS
  rw [Measure.map_apply hH hS, Measure.prod_apply (hS.preimage hH),
    Measure.compProd_apply hS]
  apply lintegral_congr
  intro x
  change _ = ((mu.map z).map (fun e => F (x,e))) (Prod.mk x ⁻¹' S)
  rw [Measure.map_apply (show Measurable (fun e : Z => F (x,e)) from
    hF.comp measurable_prodMk_left) (measurable_prodMk_left hS)]
  rfl

-- @node: independent_simulation_overlap_lift
/-- Suppose [the larger covariate vector is measurable](hyp:ha), [the parent vector
is a measurable function of it](hyp:hp), [the private noise is measurable](hyp:hz),
[the treatment simulation rule is measurable](hyp:hF), and [the larger covariate
vector is independent of the noise](hyp:hind). On [a measurable treatment set](hyp:hI),
let [a candidate conditional density depend on parents and treatment](hyp:p); if
[it represents the conditional treatment law given parents almost everywhere](hyp:hdensity)
and [it is at least the nonnegative part of the overlap constant throughout that
set for almost every parent vector](hyp:hoverlap), [the joint law of the larger
covariate vector and treatment dominates the product of the covariate law and the
reference measure restricted to that set, scaled by that constant's nonnegative
part](goal). -/
lemma independent_simulation_overlap_lift
    {Ω A X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace X] [MeasurableSpace Z]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (a : Ω → A) (parent : A → X) (z : Ω → Z) (F : X × Z → ℝ)
    (ha : Measurable a) (hp : Measurable parent) (hz : Measurable z) (hF : Measurable F)
    (hind : IndepFun a z mu)
    (rho : Measure ℝ) [SFinite rho] (I : Set ℝ) (hI : MeasurableSet I)
    (p : X × ℝ → ℝ≥0∞) (delta : ℝ)
    (hdensity : ∀ᵐ x ∂mu.map (parent ∘ a),
      (mu.map (fun u => (parent (a u), F (parent (a u), z u)))).condKernel x =
        rho.withDensity (fun t => p (x,t)))
    (hoverlap : ∀ᵐ x ∂mu.map (parent ∘ a),
      ∀ t ∈ I, ENNReal.ofReal delta ≤ p (x,t)) :
    ENNReal.ofReal delta • ((mu.map a).prod (rho.restrict I)) ≤
      mu.map (fun u => (a u, F (parent (a u), z u))) := by
  haveI : IsProbabilityMeasure (mu.map z) := Measure.isProbabilityMeasure_map hz.aemeasurable
  let k := privateNoiseUpdateKernel (mu.map z) F hF
  let joint := mu.map (fun u => (parent (a u), F (parent (a u), z u)))
  have hjoint : joint = (mu.map (parent ∘ a)).compProd k :=
    independent_simulation_joint_eq_compProd mu (parent ∘ a) z F (hp.comp ha) hz hF
      (hind.comp hp measurable_id)
  have hfst : joint.fst = mu.map (parent ∘ a) :=
    Measure.fst_map_prodMk (hF.comp ((hp.comp ha).prodMk hz))
  have heq : ∀ᵐ x ∂mu.map (parent ∘ a), k x = joint.condKernel x := by
    rw [← hfst]
    exact eq_condKernel_of_measure_eq_compProd k (by rw [hfst]; exact hjoint)
  have hden : ∀ᵐ x ∂mu.map (parent ∘ a), k x = rho.withDensity (fun t => p (x,t)) := by
    filter_upwards [heq, hdensity] with x hx hd
    exact hx.trans hd
  have hlow := overlap_conditional_measure_le (mu.map (parent ∘ a)) rho k p I hI delta hden hoverlap
  have hlow' : ∀ᵐ x ∂mu.map a, ENNReal.ofReal delta • rho.restrict I ≤ k (parent x) := by
    rw [← Measure.map_map hp ha] at hlow
    exact ae_of_ae_map hp.aemeasurable hlow
  let F' : A × Z → ℝ := fun w => F (parent w.1, w.2)
  have hF' : Measurable F' := by fun_prop
  have hactual := independent_simulation_joint_eq_compProd mu a z F' ha hz hF' hind
  rw [hactual]
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul, Measure.prod_apply hS, Measure.compProd_apply hS,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hlow'] with x hx
  exact hx (Prod.mk x ⁻¹' S)

end
end Papers.TbsNeuralCausalPi
