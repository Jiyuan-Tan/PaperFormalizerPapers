module
public import Papers.TbsPrteOptimalTransport.Helpers.Canonical
public import Papers.TbsPrteOptimalTransport.Helpers.SharpnessConstruction
public import Papers.TbsPrteOptimalTransport.Helpers.SharpnessModel
/-! Conditional factorization of the sharpness instrument extension. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

/-- For a latent probability law and an instrument kernel indexed by covariates,
if [the covariate map is measurable](hyp:hc), [adjoining an instrument draw
conditional on those covariates yields a joint law that factors into the covariate
law and the product of the instrument kernel with the conditional latent law](goal). -/
-- @node: sharpness_extension_joint_factorization
lemma sharpness_extension_joint_factorization
    {A C Z : Type*} [MeasurableSpace A] [MeasurableSpace C] [MeasurableSpace Z]
    [StandardBorelSpace A] [Nonempty A]
    (ν : Measure A) [IsProbabilityMeasure ν] (c : A → C) (hc : Measurable c)
    (κ : Kernel C Z) [IsMarkovKernel κ] :
    (ν ⊗ₘ κ.comap c hc).map (fun a => (c a.1, (a.2, a.1))) =
      (ν.map c) ⊗ₘ (κ.prod (condDistrib id c ν)) := by
  let J := condDistrib id c ν
  haveI : IsProbabilityMeasure (ν.map c) := Measure.isProbabilityMeasure_map hc.aemeasurable
  have hdis : (ν.map c) ⊗ₘ J = ν.map (fun a => (c a, a)) :=
    compProd_map_condDistrib measurable_id.aemeasurable
  have hg := factorized_kernel_statistic_joint (ν.map c) J κ
    (fun a (_ : C) => a) (by fun_prop)
  rw [hdis, Measure.map_map (by fun_prop) (by fun_prop)] at hg
  have he := sharpness_map_compProd_comap ν
    (κ.comap (Prod.snd : A × C → C) measurable_snd)
    (fun a => (a, c a)) (measurable_id.prodMk hc)
  have he' : (ν ⊗ₘ κ.comap c hc).map (fun a => ((a.1, c a.1), a.2)) =
      ((ν.map c) ⊗ₘ (J.prod κ)).map (fun a => ((a.2.1, a.1), a.2.2)) := by
    exact he.trans hg.symm
  have hh := congrArg (fun η : Measure ((A × C) × Z) =>
    η.map (fun a => (a.1.2, (a.2, a.1.1)))) he'
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hh
  have hswap : ((ν.map c) ⊗ₘ (J.prod κ)).map
      (fun a => (a.1, (a.2.2, a.2.1))) =
      (ν.map c) ⊗ₘ (κ.prod J) := by
    change ((ν.map c) ⊗ₘ (J.prod κ)).map (Prod.map id Prod.swap) = _
    rw [← Measure.compProd_map measurable_swap, Kernel.map_prod_swap]
  exact hh.trans hswap

-- @node: sharpness_extension_conditional_factorization
/-- If [the covariate map is measurable](hyp:hc) and [the latent statistic is
measurable](hyp:hv), then after adjoining an instrument draw from a kernel
depending only on covariates, [the conditional joint law of the instrument and
that statistic equals the product of the instrument kernel and the statistic's
conditional law, for almost every covariate value under the extended law](goal). -/
lemma sharpness_extension_conditional_factorization
    {A C Z V : Type*} [MeasurableSpace A] [MeasurableSpace C] [MeasurableSpace Z]
    [MeasurableSpace V] [StandardBorelSpace A] [Nonempty A]
    [StandardBorelSpace Z] [Nonempty Z] [StandardBorelSpace V] [Nonempty V]
    (ν : Measure A) [IsProbabilityMeasure ν] (c : A → C) (hc : Measurable c)
    (κ : Kernel C Z) [IsMarkovKernel κ] (v : A → V) (hv : Measurable v) :
    let P := ν ⊗ₘ κ.comap c hc
    condDistrib (fun a => (a.2, v a.1)) (fun a => c a.1) P
      =ᵐ[P.map (fun a => c a.1)] fun x => (κ x).prod
        (condDistrib (fun a => v a.1) (fun a => c a.1) P x) := by
  dsimp only
  let P := ν ⊗ₘ κ.comap c hc
  have hfst : P.map Prod.fst = ν := Measure.fst_compProd _ _
  have hbase : P.map (fun a => c a.1) = ν.map c := by
    rw [← hfst, Measure.map_map hc measurable_fst]
    rfl
  have hj := sharpness_extension_joint_factorization ν c hc κ
  have hm := congrArg (fun η : Measure (C × (Z × A)) =>
    η.map (Prod.map id (Prod.map id v))) hj
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.compProd_map (measurable_id.prodMap hv),
    ← Kernel.map_prod_map _ _ measurable_id hv, Kernel.map_id] at hm
  have hV : condDistrib (fun a => v a.1) (fun a => c a.1) P
      =ᵐ[ν.map c] (condDistrib id c ν).map v := by
    have hcomp := condDistrib_comp c measurable_id.aemeasurable hv (μ := ν) (mβ := inferInstance)
    have hsame : condDistrib (fun a => v a.1) (fun a => c a.1) P
        =ᵐ[P.map (fun a => c a.1)] condDistrib v c ν := by
      apply sharpness_conditional_law_unique P ν _ _ c v (by fun_prop) (by fun_prop) hc hv
      rw [← hfst, Measure.map_map (hc.prodMk hv) measurable_fst]
      rfl
    rw [hbase] at hsame
    exact hsame.trans hcomp
  have hcond : condDistrib (fun a => (a.2, v a.1)) (fun a => c a.1) P
      =ᵐ[P.map (fun a => c a.1)] κ.prod ((condDistrib id c ν).map v) := by
    apply condDistrib_ae_eq_of_measure_eq_compProd _ (by fun_prop)
    rw [hbase]
    exact hm
  rw [hbase] at hcond ⊢
  filter_upwards [hcond, hV] with x hx hvx
  rw [hx, hvx, Kernel.prod_apply]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: sharpness_threshold_model_exogeneity
/-- If [the original propensity is measurable](hyp:hp) and [the extended
probability law adjoins the original instrument kernel to the candidate latent
law conditional on covariates](hyp:hExt), [the resulting threshold model makes
the instrument conditionally independent of resistance and both potential
outcomes given covariates](goal). -/
lemma sharpness_threshold_model_exogeneity
    (P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z))
    (hp : Measurable (Function.uncurry M.prop))
    (piT : Measure ((ℝ × X) × (ℝ × ℝ))) [IsProbabilityMeasure piT]
    (hExt : P.toMeasure = piT ⊗ₘ M.instKernel.comap
      (fun a : (ℝ × X) × (ℝ × ℝ) => a.1.2) (by fun_prop)) :
    InstrumentExogeneity (sharpnessThresholdModel M P hp) := by
  let N := sharpnessThresholdModel M P hp
  haveI := M.instKernel_markov
  have hfactor := sharpness_extension_conditional_factorization piT
    (fun a : (ℝ × X) × (ℝ × ℝ) => a.1.2) (by fun_prop) M.instKernel
    (fun a => (min 1 (max 0 a.1.1), a.2.1, a.2.2)) (by fun_prop)
  dsimp only at hfactor
  simp only [← hExt] at hfactor
  have hinst : condDistrib N.Zv N.Xv P.toMeasure =ᵐ[xLaw N] M.instKernel := by
    apply condDistrib_ae_eq_of_measure_eq_compProd _ N.measZ.aemeasurable
    change P.toMeasure.map (fun a => (a.1.1.2, a.2)) =
      (P.toMeasure.map (fun a => a.1.1.2)) ⊗ₘ M.instKernel
    rw [hExt, sharpness_map_compProd_comap piT M.instKernel
      (fun a : (ℝ × X) × (ℝ × ℝ) => a.1.2) (by fun_prop)]
    have hfst : (piT ⊗ₘ M.instKernel.comap
        (fun a : (ℝ × X) × (ℝ × ℝ) => a.1.2) (by fun_prop)).map Prod.fst = piT :=
      Measure.fst_compProd _ _
    have hbase := congrArg (fun η : Measure ((ℝ × X) × (ℝ × ℝ)) =>
      η.map (fun a => a.1.2)) hfst
    rw [Measure.map_map (by fun_prop) measurable_fst] at hbase
    simp only [Function.comp_def] at hbase
    rw [hbase]
  change condDistrib (fun a => (N.Zv a, (N.U a, N.Y0 a, N.Y1 a))) N.Xv
    N.law.toMeasure =ᵐ[xLaw N] _ at hfactor
  change condDistrib (fun a => (N.Zv a, (N.U a, N.Y0 a, N.Y1 a))) N.Xv
    N.law.toMeasure =ᵐ[xLaw N] _
  filter_upwards [hfactor, hinst] with x hx hi
  change _ = (condDistrib N.Zv N.Xv P.toMeasure x).prod _
  rw [hi]
  exact hx

/-- If [the original domains are compact and Borel](hyp:hD), [the original model
satisfies threshold crossing](hyp:hThreshold) and [common instrument support](hyp:hSupport),
and [both outcome marginals of a candidate joint probability law are feasible](hyp:hf),
[there exists a model preserving that entire latent law, satisfying potential
outcome support, consistency, instrument exogeneity, uniform resistance, common
instrument support and compact Borel domains, sharing the original outcome domain,
propensity and instrument–covariate law, and selecting treatment exactly when
resistance does not exceed propensity](goal). -/
-- @node: feasible_joint_exogenous_threshold_completion
lemma feasible_joint_exogenous_threshold_completion
    (hD : DomainsCompactBorel M) (hThreshold : ThresholdCrossing M)
    (hSupport : CommonInstrumentSupport M)
    (piT : Measure ((ℝ × X) × (ℝ × ℝ))) [IsProbabilityMeasure piT]
    (hf : IsFeasiblePair (transportData M) (piT.map (fun a => (a.1, a.2.1)))
      (piT.map (fun a => (a.1, a.2.2)))) :
    ∃ N : LatentIVModel (((ℝ × X) × (ℝ × ℝ)) × Z) X Z,
      N.law.toMeasure.map (fun a => ((N.U a, N.Xv a), (N.Y0 a, N.Y1 a))) = piT ∧
      PotentialSupport N ∧ Consistency N ∧ InstrumentExogeneity N ∧
      UniformResistance N ∧ CommonInstrumentSupport N ∧ DomainsCompactBorel N ∧
      N.Yset = M.Yset ∧ N.prop = M.prop ∧ zxLaw N = zxLaw M ∧
      (∀ a, N.W a = if N.U a ≤ N.prop (N.Zv a) (N.Xv a) then 1 else 0) := by
  obtain ⟨P, hfst, hZX, hs, hExt⟩ := feasible_joint_instrument_extension M hD piT hf
  let N := sharpnessThresholdModel M P hThreshold.2.1
  refine ⟨N, sharpness_threshold_model_joint M P _ piT hfst (hs.mono fun _ h => h.1),
    sharpness_threshold_model_potential_support M P _ (hs.mono fun _ h => h.2),
    sharpness_threshold_model_consistency M P _,
    sharpness_threshold_model_exogeneity M P _ piT hExt,
    sharpness_threshold_model_uniform M P _ piT hfst (hs.mono fun _ h => h.1)
      (feasible_joint_uniform_marginal M piT hf),
    sharpness_threshold_model_common_support M P _ hZX hSupport,
    hD, rfl, rfl, hZX, sharpness_threshold_model_selection M P _⟩

/-- If [the original model satisfies threshold crossing](hyp:hThreshold) and a
second model [has the same propensity](hyp:hprop), [the same instrument–covariate
law](hyp:hZX), and [the same observed law](hyp:hObs), [its conditional treatment
mean given instrument and covariates equals its propensity almost everywhere
under its instrument–covariate law](goal). -/
-- @node: sharpness_observed_threshold_mean
lemma sharpness_observed_threshold_mean
    {B : Type*} [MeasurableSpace B] (N : LatentIVModel B X Z)
    (hThreshold : ThresholdCrossing M)
    (hprop : N.prop = M.prop) (hZX : zxLaw N = zxLaw M)
    (hObs : observedLaw N = observedLaw M) :
    ∀ᵐ zx ∂zxLaw N,
      (∫ w, w ∂condDistrib N.W (fun a => (N.Zv a, N.Xv a)) N.law.toMeasure zx) =
        N.prop zx.1 zx.2 := by
  have hj : N.law.toMeasure.map (fun a => ((N.Zv a, N.Xv a), N.W a)) =
      M.law.toMeasure.map (fun a => ((M.Zv a, M.Xv a), M.W a)) := by
    have he := congrArg (fun η : Measure (ℝ × ℝ × Z × X) =>
      η.map (fun a => ((a.2.2.1, a.2.2.2), a.2.1))) hObs
    rw [observedLaw, observedLaw,
      Measure.map_map (by fun_prop) (N.measY.prodMk
        (N.measW.prodMk (N.measZ.prodMk N.measX))),
      Measure.map_map (by fun_prop) (M.measY.prodMk
        (M.measW.prodMk (M.measZ.prodMk M.measX)))] at he
    exact he
  have hcond := sharpness_conditional_law_unique N.law.toMeasure M.law.toMeasure
    (fun a => (N.Zv a, N.Xv a)) N.W (fun a => (M.Zv a, M.Xv a)) M.W
    (N.measZ.prodMk N.measX) N.measW (M.measZ.prodMk M.measX) M.measW hj
  change condDistrib N.W (fun a => (N.Zv a, N.Xv a)) N.law.toMeasure
    =ᵐ[zxLaw N] _ at hcond
  rw [hZX] at hcond ⊢
  filter_upwards [hcond, hThreshold.2.2.2] with zx hx ht
  rw [hx, hprop]
  exact ht

-- @node: sharpness_prescribed_latent_marginal
/-- If [a model's joint law of resistance, covariates and both potential outcomes
equals a prescribed candidate law](hyp:hj), [its resistance–covariate–potential
outcome marginal for either treatment state equals the corresponding marginal
of that candidate law](goal). -/
lemma sharpness_prescribed_latent_marginal
    {B : Type*} [MeasurableSpace B] (N : LatentIVModel B X Z)
    (piT : Measure ((ℝ × X) × (ℝ × ℝ)))
    (hj : N.law.toMeasure.map
      (fun a => ((N.U a, N.Xv a), (N.Y0 a, N.Y1 a))) = piT) (w : Bool) :
    latentMarginal N w = latentJointMarginal piT w := by
  have he := congrArg (fun η : Measure ((ℝ × X) × (ℝ × ℝ)) =>
    η.map (fun a => (a.1, if w then a.2.2 else a.2.1))) hj
  have hm : Measurable (fun a : (ℝ × X) × (ℝ × ℝ) =>
      (a.1, if w then a.2.2 else a.2.1)) := by
    cases w <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  rw [Measure.map_map hm ((N.measU.prodMk N.measX).prodMk
    (N.measY0.prodMk N.measY1))] at he
  simpa only [latentMarginal, latentJointMarginal, potential, Function.comp_def, ite_apply] using he

end Papers.TbsPrteOptimalTransport
