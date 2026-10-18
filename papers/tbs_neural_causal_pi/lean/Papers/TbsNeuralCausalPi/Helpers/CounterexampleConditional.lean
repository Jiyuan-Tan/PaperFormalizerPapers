module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleWitness
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalEvaluation
public import Papers.TbsNeuralCausalPi.Helpers.CategoricalSelectorLaw
public import Causalean.Mathlib.MeasureTheory.CondExpPreimage
/-! # Conditional categorical probabilities of the counterexample -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

-- @node: counterexample_condExp_of_indep
/-- For [a measurable random variable x](hyp:hx) and [a measurable random variable z](hyp:hz)
that [are independent](hyp:hind), and [a measurable real function of their pair](hyp:hF)
[bounded in absolute value by one](hyp:hb),
[its conditional expectation given x equals, almost surely, its integral over the marginal distribution of z with x held fixed](goal). -/
lemma counterexample_condExp_of_indep
    {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → X) (z : Ω → Z) (hx : Measurable x) (hz : Measurable z)
    (hind : IndepFun x z μ) (F : X × Z → ℝ) (hF : Measurable F)
    (hb : ∀ v, ‖F v‖ ≤ 1) :
    μ[fun u => F (x u, z u) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      fun u => ∫ w, F (x u, w) ∂μ.map z := by
  letI := Measure.isProbabilityMeasure_map (μ := μ) hx.aemeasurable
  letI := Measure.isProbabilityMeasure_map (μ := μ) hz.aemeasurable
  have hFi : Integrable F ((μ.map x).prod (μ.map z)) :=
    Integrable.of_bound hF.aestronglyMeasurable 1 (ae_of_all _ hb)
  have hY : Integrable (fun u => F (x u, z u)) μ :=
    Integrable.of_bound (hF.comp (hx.prodMk hz)).aestronglyMeasurable 1
      (ae_of_all _ (fun u => hb _))
  have hm : Measurable (fun v => ∫ w, F (v,w) ∂μ.map z) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  have hm' : Integrable (fun u => ∫ w, F (x u,w) ∂μ.map z) μ := by
    apply Integrable.of_bound (hm.comp hx).aestronglyMeasurable 1
    apply ae_of_all
    intro u
    simpa using norm_integral_le_of_norm_le_const (μ := μ.map z)
      (ae_of_all _ (fun w => hb (x u, w)))
  apply Causalean.Mathlib.MeasureTheory.condExp_eq_of_integral_preimage_eq
    μ x hx _ _ hY hm' ((hm.comp (comap_measurable x)).aestronglyMeasurable)
  intro S hS
  have hp := hind.map_prod_eq_prod_map_map hx.aemeasurable hz.aemeasurable
  calc
    _ = ∫ v in S ×ˢ Set.univ, F v ∂μ.map (fun u => (x u,z u)) := by
      rw [setIntegral_map (hS.prod MeasurableSet.univ) hF.aestronglyMeasurable
        (hx.prodMk hz).aemeasurable]
      rw [show (fun u => (x u,z u)) ⁻¹' (S ×ˢ Set.univ) = x ⁻¹' S by
        ext u; simp]
    _ = ∫ v in S ×ˢ Set.univ, F v ∂(μ.map x).prod (μ.map z) := by rw [hp]
    _ = ∫ v in S, ∫ w, F (v,w) ∂μ.map z ∂μ.map x := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
      exact integral_prod F (hFi.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl))
    _ = _ := setIntegral_map hS hm.aestronglyMeasurable hx.aemeasurable
-- @node: counterexample_selector_condExp
/-- Let [x](hyp:hx) and [the two-dimensional noise vector G](hyp:hG) be measurable,
[independent](hyp:hind) random variables, with [G having the standard two-coordinate Gumbel distribution](hyp:hlaw).
For [a measurable probability-vector function p](hyp:hp) [taking values in the two-category probability simplex](hyp:hps),
and [a certificate that the selector's category count is positive](hyp:hk),
[each probability coordinate equals almost surely the conditional probability, given x, that the Gumbel selector chooses that category](goal). -/
lemma counterexample_selector_condExp
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → X) (G : Ω → Fin 2 → ℝ) (hx : Measurable x) (hG : Measurable G)
    (hind : IndepFun x G μ) (hlaw : μ.map G = gumbelInputs 2)
    (p : X → L1Vec 2) (hp : Measurable p)
    (hps : ∀ v, (p v).ofLp ∈ probabilitySimplex 2)
    (hk : ∀ m, Sum.inr 2 = (Sum.inr m : NodeKind) → 0 < m) (j : Fin 2) :
    (fun u => (p (x u)).ofLp j) =ᵐ[μ]
      μ[fun u => if canonicalSelector (.inr 2) hk (p (x u)) (WithLp.toLp 1 (G u)) = j
        then (1 : ℝ) else 0 | MeasurableSpace.comap x inferInstance] := by
  let sel : X × (Fin 2 → ℝ) → Fin 2 := fun v =>
    canonicalSelector (.inr 2) hk (p v.1) (WithLp.toLp 1 v.2)
  have hs : Measurable sel := by
    apply firstArgmax_getD_measurable
    intro l
    fun_prop
  let F := fun v => if sel v = j then (1 : ℝ) else 0
  have hF : Measurable F :=
    Measurable.ite (hs (measurableSet_singleton j)) measurable_const measurable_const
  have h := counterexample_condExp_of_indep μ x G hx hG hind F hF
    (fun v => by dsimp [F]; split <;> norm_num)
  have hi (v : X) : (∫ w, F (v,w) ∂gumbelInputs 2) = (p v).ofLp j := by
    have hs' : Measurable (fun w : Fin 2 → ℝ => sel (v,w)) := hs.comp measurable_prodMk_left
    have hm := congrArg (fun nu : Measure (Fin 2) => nu {j})
      (canonicalSelector_categorical_law hk (p v) (hps v))
    change ((gumbelInputs 2).map (fun w => sel (v,w))) {j} = _ at hm
    rw [Measure.map_apply hs' (measurableSet_singleton j)] at hm
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton j)] at hm
    simp only [Set.mem_singleton_iff, Set.indicator_apply, Pi.one_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hm
    have hFeq : (fun w => F (v,w)) =
        {w | sel (v,w) = j}.indicator (fun _ => (1 : ℝ)) := by
      funext w
      simp [F, Set.indicator]
    have hI := integral_indicator_one (μ := gumbelInputs 2)
      (hs' (measurableSet_singleton j))
    have hI' : (∫ w, {w | sel (v,w) = j}.indicator (fun _ => (1 : ℝ)) w
        ∂gumbelInputs 2) = (gumbelInputs 2).real ((fun w => sel (v,w)) ⁻¹' {j}) := by
      simpa only [Pi.one_def, Set.preimage, Set.mem_singleton_iff] using hI
    rw [hFeq, hI']
    exact (congrArg ENNReal.toReal hm).trans (ENNReal.toReal_ofReal ((hps v).1 j))
  rw [hlaw] at h
  have heq : (fun u => F (x u,G u)) = (fun u =>
      if canonicalSelector (.inr 2) hk (p (x u)) (WithLp.toLp 1 (G u)) = j
        then (1 : ℝ) else 0) := by
    funext u
    dsimp only [F, sel]
    split_ifs <;> first | rfl | contradiction
  rw [heq] at h
  filter_upwards [h.symm] with u hu
  exact (hi (x u)).symm.trans hu

-- @node: counterexample_structuralInputRV_eq_visit
/-- [A node's observational structural input equals the structural input formed from the evaluation history at the node's position in the topological order, together with the same latent realization](goal). -/
lemma counterexample_structuralInputRV_eq_visit
    {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    (M : EuclideanSCM kind dims) (i : Fin n) (u : Exogenous kind dims) :
    structuralInputRV M i u =
      structuralInput M i (evalSteps M (fun _ => none) u (M.dag.topoOrder i)) u := by
  apply PiLp.ext
  rintro (⟨p,k⟩ | ⟨a,k⟩)
  · exact (evalSteps_coordinate_eq_intervenedEval M (fun _ => none) u p.val _
      (M.dag.topoOrder_lt _ _ (M.dag.mem_parents.mp p.property)) k).symm
  · rfl

-- @node: counterexampleTrueSCM_conditional_probability
/-- [In the true counterexample, each treatment probability produced by the structural function equals almost surely the conditional probability of selecting that category given the treatment node's structural input](goal). -/
lemma counterexampleTrueSCM_conditional_probability (j : Fin 2) :
    (fun u => (counterexampleTrueSCM.f 1
      (structuralInputRV counterexampleTrueSCM.toEuclideanSCM 1 u)).ofLp j) =ᵐ[counterexampleTrueSCM.latentLaw]
      counterexampleTrueSCM.latentLaw[fun u =>
        if counterexampleTrueSCM.toEuclideanSCM.categoricalLabel 1 2 rfl
          (structuralInputRV counterexampleTrueSCM.toEuclideanSCM 1 u)
          (WithLp.toLp 1 (fun l : Fin 2 => (categoricalNoise 1 u).ofLp l)) = j
        then (1 : ℝ) else 0 |
          MeasurableSpace.comap (structuralInputRV counterexampleTrueSCM.toEuclideanSCM 1) (borel _)] := by
  letI := counterexampleTrueSCM.latentLaw_probability
  let M := counterexampleTrueSCM.toEuclideanSCM
  letI := M.probability
  let X := structuralInputRV M 1
  let G := fun (u : Exogenous backdoorKind counterexampleDims) (l : Fin 2) =>
    (categoricalNoise 1 u).ofLp l
  let p : StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) 1 → L1Vec 2 := counterexampleTrueSCM.f 1
  have hx : Measurable X := by
    change Measurable (fun u => structuralInput M 1 (evalSteps M (fun _ => none) u (3*3+3)) u)
    fun_prop
  have hg : Measurable G := by
    dsimp only [G]
    fun_prop [categoricalNoise]
  have hp : Measurable p := counterexampleStructuralWeights_measurable 1
  have hind : IndepFun X G M.latentLaw := by
    have he : X = fun u => structuralInput M 1 (evalSteps M (fun _ => none) u
        (M.dag.topoOrder 1)) u := funext (counterexample_structuralInputRV_eq_visit M 1)
    rw [he]
    exact structuralInput_evalSteps_indep_current_gumbels M counterexampleTrueSCM_independent
      1 (fun _ => none) 2 rfl
  have hlaw : M.latentLaw.map G = gumbelInputs 2 :=
    canonical_categorical_noise_law counterexampleTrueSCM 1 2 rfl
  have hps (v) : (p v).ofLp ∈ probabilitySimplex 2 := counterexampleTruePropensity_simplex _
  have h := counterexample_selector_condExp M.latentLaw X G hx hg hind hlaw p hp hps
    (fun m hm => by cases hm; decide) j
  convert h using 1 <;> try rfl
  apply congrArg (fun f : Exogenous backdoorKind counterexampleDims → ℝ =>
    M.latentLaw[f | MeasurableSpace.comap X inferInstance])
  funext u
  apply ite_congr
  · rfl
  · intro _; rfl
  · intro _; rfl

-- @node: counterexampleTrueSCM_propensity
/-- [The true counterexample's categorical probability functions are Lipschitz with constant 20 and equal the corresponding conditional category probabilities given structural inputs](goal). -/
lemma counterexampleTrueSCM_propensity :
    CategoricalPropensityLipschitz counterexampleTrueSCM.toEuclideanSCM counterexampleTrueSCM.f 20 := by
  refine ⟨counterexampleTrueSCM_propensity_lipschitz, ?_⟩
  intro i k hi j
  fin_cases i <;> simp [backdoorKind] at hi
  subst k
  convert counterexampleTrueSCM_conditional_probability j using 1 <;> try rfl

-- @node: counterexampleTrueSCM_categorical
/-- [The true counterexample has positive categorical weights, conditional category probabilities given by normalized weights, a Gumbel argmax selection rule, and the prescribed independent-coordinate Gumbel noise distribution](goal). -/
lemma counterexampleTrueSCM_categorical :
    CategoricalGumbelArgmax counterexampleTrueSCM.toEuclideanSCM counterexampleTrueSCM.f := by
  refine ⟨counterexampleTrueSCM_weights_positive, ?_, ?_, ?_⟩
  · intro i k hi j
    fin_cases i <;> simp [backdoorKind] at hi
    subst k
    have hsum (u : Exogenous backdoorKind counterexampleDims) :
        ∑ l, (counterexampleTrueSCM.f 1
          (structuralInputRV counterexampleTrueSCM.toEuclideanSCM 1 u)).ofLp l = 1 :=
      (counterexampleTruePropensity_simplex _).2
    have h := counterexampleTrueSCM_propensity.2 1 2 rfl j
    convert h using 1 <;> try rfl
    funext u
    exact (congrArg (fun a : ℝ =>
      (counterexampleTrueSCM.f 1 (structuralInputRV counterexampleTrueSCM.toEuclideanSCM 1 u)).ofLp j / a)
      (hsum u)).trans (div_one _)
  · intro i k hi x hx g
    fin_cases i <;> simp [backdoorKind] at hi
    subst k
    rfl
  · intro i k hi
    exact canonical_categorical_noise_law counterexampleTrueSCM i k hi

-- @node: counterexampleTrueSCM_atoms
/-- [The true counterexample satisfies the counterexample assumptions: independent latent blocks, a Gumbel decomposition, categorical Gumbel argmax selection, Lipschitz continuous structural and propensity functions, bounded observed variables, and regular latent distributions](goal). -/
lemma counterexampleTrueSCM_atoms : counterexampleAtoms counterexampleTrueSCM :=
  ⟨counterexampleTrueSCM_independent, counterexampleTrueSCM_gumbel_decomposition,
    counterexampleTrueSCM_categorical,
    ⟨20, counterexampleTrueSCM_continuous_lipschitz, counterexampleTrueSCM_propensity⟩,
    counterexampleTrueSCM_variables_bounded, counterexampleTrueSCM_regular⟩

end
end Papers.TbsNeuralCausalPi
