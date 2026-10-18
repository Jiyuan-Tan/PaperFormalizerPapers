module
public import Papers.TbsPrteOptimalTransport.Helpers.SharpnessConstruction
/-! Deterministic threshold completion of the feasible joint-law extension. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

/-- Given [an original latent instrument model](hyp:M), [an extended probability
law of resistance, covariates, both potential outcomes and the instrument](hyp:P),
and [measurability of the original propensity](hyp:hp), the [threshold completion](goal)
uses [resistance clipped to the unit interval](step:1) and [treatment equal to one
exactly when this resistance does not exceed the original propensity](step:2).
It retains the given probability law and coordinate potential outcomes,
covariates and instrument, and sets the observed outcome to the selected potential outcome. -/
-- @node: sharpnessThresholdModel
noncomputable def sharpnessThresholdModel
    (P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z))
    (hp : Measurable (Function.uncurry M.prop)) :
    LatentIVModel (((ℝ × X) × (ℝ × ℝ)) × Z) X Z := by
  let U := fun a : ((ℝ × X) × (ℝ × ℝ)) × Z => min 1 (max 0 a.1.1.1)
  let W := fun a : ((ℝ × X) × (ℝ × ℝ)) × Z =>
    if U a ≤ M.prop a.2 a.1.1.2 then (1 : ℝ) else 0
  have hU : Measurable U := by fun_prop
  have hP : Measurable (fun a : ((ℝ × X) × (ℝ × ℝ)) × Z =>
      M.prop a.2 a.1.1.2) := by
    fun_prop
  have hW : Measurable W := by
    exact measurable_const.ite (measurableSet_le hU hP) measurable_const
  exact {
    law := P
    Yset := M.Yset
    yMin := M.yMin
    yMax := M.yMax
    dX := M.dX
    covariateCoordinates := M.covariateCoordinates
    coordinates_isEmbedding := M.coordinates_isEmbedding
    Y0 := fun a => a.1.2.1
    Y1 := fun a => a.1.2.2
    U := U
    W := W
    rangeU := fun a => ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    rangeW := fun a => by dsimp [W]; split_ifs <;> simp
    Y := fun a => W a * a.1.2.2 + (1 - W a) * a.1.2.1
    Xv := fun a => a.1.1.2
    Zv := Prod.snd
    prop := M.prop
    rangeProp := M.rangeProp
    measY0 := by fun_prop
    measY1 := by fun_prop
    measU := hU
    measW := hW
    measY := by fun_prop
    measX := by fun_prop
    measZ := by fun_prop
    instKernel := condDistrib Prod.snd (fun a => a.1.1.2) P.toMeasure
    instKernel_markov := inferInstance
    instKernel_version := Filter.EventuallyEq.rfl }

/-- If [the conditioning variable in the first population is measurable](hyp:hc),
[its response is measurable](hyp:hd), [the conditioning variable in the second
population is measurable](hyp:hc'), [its response is measurable](hyp:hd'), and
[the two joint laws of conditioning variable and response coincide](hyp:heq),
[their conditional response laws coincide almost everywhere under the first
population's conditioning-variable law](goal). -/
-- @node: sharpness_conditional_law_unique
lemma sharpness_conditional_law_unique
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [StandardBorelSpace D] [Nonempty D]
    (ν : Measure A) (ν' : Measure B) [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (c : A → C) (d : A → D) (c' : B → C) (d' : B → D)
    (hc : Measurable c) (hd : Measurable d) (hc' : Measurable c') (hd' : Measurable d')
    (heq : ν.map (fun a => (c a, d a)) = ν'.map (fun b => (c' b, d' b))) :
    condDistrib d c ν =ᵐ[ν.map c] condDistrib d' c' ν' := by
  have hbase : ν.map c = ν'.map c' := by
    have h := congrArg (fun η : Measure (C × D) => η.map Prod.fst) heq
    simpa only [Measure.map_map measurable_fst (hc.prodMk hd),
      Measure.map_map measurable_fst (hc'.prodMk hd'), Function.comp_def] using h
  apply condDistrib_ae_eq_of_measure_eq_compProd c hd.aemeasurable
  rw [hbase, compProd_map_condDistrib hd'.aemeasurable]
  exact heq

-- @node: sharpness_threshold_model_joint
/-- If [the original propensity is measurable](hyp:hp), [the extended law has
the prescribed candidate latent marginal](hyp:hfst), and [its resistance coordinate
lies in the unit interval almost surely](hyp:hs), [the threshold completion's
joint law of resistance, covariates and both potential outcomes equals that
candidate law](goal). -/
lemma sharpness_threshold_model_joint
    (P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z))
    (hp : Measurable (Function.uncurry M.prop))
    (piT : Measure ((ℝ × X) × (ℝ × ℝ)))
    (hfst : P.toMeasure.map Prod.fst = piT)
    (hs : ∀ᵐ a ∂P.toMeasure, a.1.1.1 ∈ Icc (0 : ℝ) 1) :
    let N := sharpnessThresholdModel M P hp
    N.law.toMeasure.map (fun a => ((N.U a, N.Xv a), (N.Y0 a, N.Y1 a))) = piT := by
  change P.toMeasure.map (fun a =>
    ((min 1 (max 0 a.1.1.1), a.1.1.2), (a.1.2.1, a.1.2.2))) = piT
  rw [← hfst]
  apply Measure.map_congr
  filter_upwards [hs] with a ha
  rw [max_eq_right ha.1, min_eq_right ha.2]

-- @node: sharpness_threshold_model_consistency
/-- If [the original propensity is measurable](hyp:hp), [the threshold completion
satisfies consistency: its observed outcome equals the potential outcome selected
by treatment almost surely](goal). -/
lemma sharpness_threshold_model_consistency
    (P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z))
    (hp : Measurable (Function.uncurry M.prop)) :
    Consistency (sharpnessThresholdModel M P hp) := by
  exact Filter.Eventually.of_forall fun _ => rfl

-- @node: sharpness_threshold_model_selection
/-- If [the original propensity is measurable](hyp:hp), [at every realization
the threshold completion assigns treatment one when resistance is at most
propensity, and zero otherwise](goal). -/
lemma sharpness_threshold_model_selection
    (P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z))
    (hp : Measurable (Function.uncurry M.prop)) :
    let N := sharpnessThresholdModel M P hp
    ∀ a, N.W a = if N.U a ≤ N.prop (N.Zv a) (N.Xv a) then 1 else 0 := by
  intro N a
  rfl

-- @node: sharpness_threshold_model_potential_support
/-- If [the original propensity is measurable](hyp:hp) and [both potential outcome
coordinates belong to the original outcome domain almost surely under the
extended law](hyp:hs), [the threshold completion satisfies potential outcome support](goal). -/
lemma sharpness_threshold_model_potential_support
    (P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z))
    (hp : Measurable (Function.uncurry M.prop))
    (hs : ∀ᵐ a ∂P.toMeasure, a.1.2.1 ∈ M.Yset ∧ a.1.2.2 ∈ M.Yset) :
    PotentialSupport (sharpnessThresholdModel M P hp) := by
  exact ⟨hs.mono fun _ h => h.1, hs.mono fun _ h => h.2⟩

-- @node: sharpness_threshold_model_uniform
/-- If [the original propensity is measurable](hyp:hp), [the extended law has
the candidate latent marginal](hyp:hfst), [its resistance coordinate lies in the
unit interval almost surely](hyp:hs), and [the candidate resistance–covariate
marginal is the product of the uniform law and the original covariate law](hyp:hu),
[the threshold completion has uniform resistance conditional on covariates](goal). -/
lemma sharpness_threshold_model_uniform
    (P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z))
    (hp : Measurable (Function.uncurry M.prop))
    (piT : Measure ((ℝ × X) × (ℝ × ℝ)))
    (hfst : P.toMeasure.map Prod.fst = piT)
    (hs : ∀ᵐ a ∂P.toMeasure, a.1.1.1 ∈ Icc (0 : ℝ) 1)
    (hu : piT.map Prod.fst = Causalean.Stat.unifOI.prod (xLaw M)) :
    UniformResistance (sharpnessThresholdModel M P hp) := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  let N := sharpnessThresholdModel M P hp
  have hj := sharpness_threshold_model_joint M P hp piT hfst hs
  have hUX : N.law.toMeasure.map (fun a => (N.U a, N.Xv a)) =
      Causalean.Stat.unifOI.prod (xLaw M) := by
    have hh := congrArg (fun η : Measure ((ℝ × X) × (ℝ × ℝ)) => η.map Prod.fst) hj
    rw [Measure.map_map measurable_fst ((N.measU.prodMk N.measX).prodMk
      (N.measY0.prodMk N.measY1))] at hh
    exact hh.trans hu
  have hXU : N.law.toMeasure.map (fun a => (N.Xv a, N.U a)) =
      (xLaw M).prod Causalean.Stat.unifOI := by
    have hh := congrArg (fun η : Measure (ℝ × X) => η.map Prod.swap) hUX
    rw [Measure.map_map measurable_swap (N.measU.prodMk N.measX), Measure.prod_swap] at hh
    exact hh
  have hX : xLaw N = xLaw M := by
    have hh := congrArg (fun η : Measure (X × ℝ) => η.map Prod.fst) hXU
    rw [Measure.map_map measurable_fst (N.measX.prodMk N.measU), Measure.map_fst_prod] at hh
    simpa only [measure_univ, one_smul, Function.comp_def, xLaw] using hh
  change condDistrib N.U N.Xv N.law.toMeasure =ᵐ[xLaw N]
    Kernel.const X Causalean.Stat.unifOI
  apply condDistrib_ae_eq_of_measure_eq_compProd N.Xv N.measU.aemeasurable
  change _ = (xLaw N) ⊗ₘ Kernel.const X Causalean.Stat.unifOI
  rw [hX, Measure.compProd_const]
  exact hXU

-- @node: sharpness_threshold_model_common_support
/-- If [the original propensity is measurable](hyp:hp), [the extended law matches
the original instrument–covariate law](hyp:hZX), and [the original model has
common instrument support](hyp:hSupport), [the threshold completion also has
common instrument support](goal). -/
lemma sharpness_threshold_model_common_support
    (P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z))
    (hp : Measurable (Function.uncurry M.prop))
    (hZX : P.toMeasure.map (fun a => (a.2, a.1.1.2)) = zxLaw M)
    (hSupport : CommonInstrumentSupport M) :
    CommonInstrumentSupport (sharpnessThresholdModel M P hp) := by
  let N := sharpnessThresholdModel M P hp
  have hXZ : N.law.toMeasure.map (fun a => (N.Xv a, N.Zv a)) =
      M.law.toMeasure.map (fun a => (M.Xv a, M.Zv a)) := by
    have hh := congrArg (fun η : Measure (Z × X) => η.map Prod.swap) hZX
    rw [zxLaw, Measure.map_map measurable_swap (M.measZ.prodMk M.measX),
      Measure.map_map measurable_swap (by fun_prop)] at hh
    exact hh
  have hX : xLaw N = xLaw M := by
    have hh := congrArg (fun η : Measure (X × Z) => η.map Prod.fst) hXZ
    rw [Measure.map_map measurable_fst (N.measX.prodMk N.measZ),
      Measure.map_map measurable_fst (M.measX.prodMk M.measZ)] at hh
    exact hh
  obtain ⟨κ, hκ, hv, hfull⟩ := hSupport
  refine ⟨κ, hκ, ?_, hfull⟩
  have hcond := sharpness_conditional_law_unique N.law.toMeasure M.law.toMeasure
    N.Xv N.Zv M.Xv M.Zv N.measX N.measZ M.measX M.measZ hXZ
  change condDistrib N.Zv N.Xv N.law.toMeasure =ᵐ[xLaw N] _ at hcond
  rw [hX] at hcond ⊢
  exact hv.trans hcond.symm

/-- If [the original domains are compact and Borel](hyp:hD), [the original model
satisfies threshold crossing](hyp:hThreshold) and [common instrument support](hyp:hSupport),
and [both outcome marginals of a candidate joint probability law are feasible](hyp:hf),
[there exists a model preserving that latent law, satisfying potential outcome
support, consistency, uniform resistance, common instrument support and compact
Borel domains, sharing the original outcome domain, propensity and
instrument–covariate law, and assigning treatment one exactly when resistance
does not exceed propensity](goal). -/
-- @node: feasible_joint_threshold_completion
lemma feasible_joint_threshold_completion
    (hD : DomainsCompactBorel M) (hThreshold : ThresholdCrossing M)
    (hSupport : CommonInstrumentSupport M)
    (piT : Measure ((ℝ × X) × (ℝ × ℝ))) [IsProbabilityMeasure piT]
    (hf : IsFeasiblePair (transportData M) (piT.map (fun a => (a.1, a.2.1)))
      (piT.map (fun a => (a.1, a.2.2)))) :
    ∃ N : LatentIVModel (((ℝ × X) × (ℝ × ℝ)) × Z) X Z,
      N.law.toMeasure.map (fun a => ((N.U a, N.Xv a), (N.Y0 a, N.Y1 a))) = piT ∧
      PotentialSupport N ∧ Consistency N ∧ UniformResistance N ∧
      CommonInstrumentSupport N ∧ DomainsCompactBorel N ∧
      N.Yset = M.Yset ∧ N.prop = M.prop ∧ zxLaw N = zxLaw M ∧
      (∀ a, N.W a = if N.U a ≤ N.prop (N.Zv a) (N.Xv a) then 1 else 0) := by
  obtain ⟨P, hfst, hZX, hs, hExt⟩ := feasible_joint_instrument_extension M hD piT hf
  let N := sharpnessThresholdModel M P hThreshold.2.1
  refine ⟨N, sharpness_threshold_model_joint M P _ piT hfst (hs.mono fun _ h => h.1),
    sharpness_threshold_model_potential_support M P _ (hs.mono fun _ h => h.2),
    sharpness_threshold_model_consistency M P _,
    sharpness_threshold_model_uniform M P _ piT hfst (hs.mono fun _ h => h.1)
      (feasible_joint_uniform_marginal M piT hf),
    sharpness_threshold_model_common_support M P _ hZX hSupport,
    hD, rfl, rfl, hZX, sharpness_threshold_model_selection M P _⟩

end Papers.TbsPrteOptimalTransport
