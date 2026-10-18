module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleWitness
/-! # Actual intervention laws and effect of the limiting counterexample SCM -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: counterexampleTrueSCM_covariate_latent_law
/-- [The covariate's latent coordinate in the constructed true structural causal
model equals minus one or zero, each with probability one half](goal). -/
lemma counterexampleTrueSCM_covariate_latent_law :
    counterexampleTrueSCM.latentLaw.map (fun u =>
      (blockProjection 0 u).ofLp ⟨0, by decide⟩) =
      ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (-1 : ℝ) +
      ENNReal.ofReal (1/2 : ℝ) • Measure.dirac 0 := by
  have hm : Measurable (blockProjection (kind := backdoorKind) (dims := counterexampleDims) 0) := by
    fun_prop [blockProjection]
  have he : Measurable (fun x : L1Vec (counterexampleDims 0) => x.ofLp ⟨0, by decide⟩) := by
    fun_prop
  rw [show (fun u : Exogenous backdoorKind counterexampleDims =>
      (blockProjection 0 u).ofLp ⟨0, by decide⟩) =
      (fun x : L1Vec (counterexampleDims 0) => x.ofLp ⟨0, by decide⟩) ∘ blockProjection 0 from rfl,
    ← Measure.map_map he hm, counterexampleTrueSCM_block_law]
  change ((counterexampleTrueFiniteLatentLaw.map (counterexampleBlockProjection 0)).map _) = _
  rw [Measure.map_map he (counterexampleBlockProjection_measurable 0)]
  rw [counterexampleTrueFiniteLatentLaw, ← Measure.sum_fintype,
    Measure.map_sum (he.comp (counterexampleBlockProjection_measurable 0)).aemeasurable,
    Measure.sum_fintype]
  simp only [Measure.map_smul, Measure.map_dirac' (he.comp (counterexampleBlockProjection_measurable 0))]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, counterexampleTrueLatentWeight,
    counterexampleBlockProjection, counterexampleTrueLatentAtom]
  simp only [← add_smul]
  norm_num [← ENNReal.ofReal_add]
  rfl

-- @node: counterexampleTruePrivateCoordinates
/-- From [a realization of all exogenous variables](hyp:u), the [private-coordinate
vector](goal) collects the covariate's latent coordinate followed by the two
latent coordinates of the outcome mechanism. -/
def counterexampleTruePrivateCoordinates (u : Exogenous backdoorKind counterexampleDims) : L1Vec 3 :=
  WithLp.toLp 1 ![(blockProjection 0 u).ofLp ⟨0, by decide⟩,
    (blockProjection 2 u).ofLp ⟨0, by decide⟩,
    (blockProjection 2 u).ofLp ⟨1, by decide⟩]

-- @node: counterexampleTruePrivateCoordinates_measurable
/-- [The map collecting the covariate and outcome mechanisms' three private
coordinates is measurable](goal). -/
@[fun_prop] lemma counterexampleTruePrivateCoordinates_measurable :
    Measurable counterexampleTruePrivateCoordinates := by
  unfold counterexampleTruePrivateCoordinates
  fun_prop [blockProjection]

-- @node: counterexampleTruePrivateCoordinates_law
/-- [The distribution of the three private coordinates under the constructed true
structural causal model equals the specified finite latent distribution](goal). -/
lemma counterexampleTruePrivateCoordinates_law :
    counterexampleTrueSCM.latentLaw.map counterexampleTruePrivateCoordinates =
      counterexampleTrueFiniteLatentLaw := by
  let := counterexampleTrueSCM.latentLaw_probability
  let X := fun u : Exogenous backdoorKind counterexampleDims =>
    (blockProjection 0 u).ofLp ⟨0, by decide⟩
  let Z := fun u : Exogenous backdoorKind counterexampleDims =>
    ((blockProjection 2 u).ofLp ⟨0, by decide⟩,
      (blockProjection 2 u).ofLp ⟨1, by decide⟩)
  have hx : Measurable X := by dsimp [X]; fun_prop [blockProjection]
  have hz : Measurable Z := by dsimp [Z]; fun_prop [blockProjection]
  have hind : IndepFun X Z counterexampleTrueSCM.latentLaw := by
    have h := counterexampleTrueSCM_independent.indepFun
      (i := Sum.inl (0 : Fin 3)) (j := Sum.inl (2 : Fin 3)) (by decide)
    exact h.comp (φ := fun x : L1Vec 1 => x.ofLp ⟨0, by decide⟩)
      (ψ := fun z : L1Vec 2 => (z.ofLp ⟨0, by decide⟩, z.ofLp ⟨1, by decide⟩))
      (by fun_prop) (by fun_prop)
  have hj := (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hz.aemeasurable).mp hind
  rw [show counterexampleTrueSCM.latentLaw.map X = _ from
      counterexampleTrueSCM_covariate_latent_law,
    show counterexampleTrueSCM.latentLaw.map Z = _ from
      counterexampleTrueSCM_bernoulli_joint_law] at hj
  let pack : ℝ × (ℝ × ℝ) → L1Vec 3 := fun z => WithLp.toLp 1 ![z.1,z.2.1,z.2.2]
  have hp : Measurable pack := by dsimp [pack]; fun_prop
  have h := congrArg (fun mu : Measure (ℝ × (ℝ × ℝ)) => mu.map pack) hj
  rw [Measure.map_map hp (hx.prodMk hz)] at h
  change counterexampleTrueSCM.latentLaw.map counterexampleTruePrivateCoordinates = _ at h
  rw [h]
  simp only [Measure.prod_add, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.dirac_prod_dirac, Measure.map_add _ _ hp, Measure.map_smul, Measure.map_dirac' hp]
  norm_num [counterexampleTrueFiniteLatentLaw, Fintype.sum_prod_type, Fin.sum_univ_succ,
    counterexampleTrueLatentWeight, counterexampleTrueLatentAtom, pack]
  simp (disch := positivity) only [smul_smul, ← ENNReal.ofReal_mul]
  norm_num
  ac_rfl

-- @node: counterexampleTruePrivateCoordinates_ae_atoms
/-- [Almost surely under the constructed true structural causal model's latent
distribution, the three private coordinates form one of the specified finite
latent atoms](goal). -/
lemma counterexampleTruePrivateCoordinates_ae_atoms :
    ∀ᵐ u ∂counterexampleTrueSCM.latentLaw,
      counterexampleTruePrivateCoordinates u ∈ Set.range counterexampleTrueLatentAtom := by
  apply (ae_map_iff counterexampleTruePrivateCoordinates_measurable.aemeasurable
    (Set.finite_range counterexampleTrueLatentAtom).measurableSet).mp
  rw [counterexampleTruePrivateCoordinates_law]
  exact counterexampleTrueFiniteLatentLaw_ae_atoms

-- @node: counterexampleTrueSCM_intervention_outcome_ae
/-- For either binary treatment assignment, [the constructed true structural
causal model's outcome under intervention equals the specified finite-model
intervention outcome evaluated at the three private coordinates, almost surely
under the model's latent distribution](goal). -/
lemma counterexampleTrueSCM_intervention_outcome_ae (t : Bool) :
    (fun u => backdoorOutcome
      (intervenedEval counterexampleTrueSCM.toEuclideanSCM (binaryAssignment t) u))
      =ᵐ[counterexampleTrueSCM.latentLaw]
        counterexampleTrueInterventionOutcome t ∘ counterexampleTruePrivateCoordinates := by
  filter_upwards [counterexampleTruePrivateCoordinates_ae_atoms] with u hu
  obtain ⟨⟨x,a,b⟩, hz⟩ := hu
  have hx := congrArg (fun z : L1Vec 3 => z.ofLp 0) hz
  change -1 + (x.val : ℝ) = (blockProjection 0 u).ofLp ⟨0, by decide⟩ at hx
  have hcov := counterexampleTrueSCM_covariate (binaryAssignment t)
    (by simp [binaryAssignment]) u
  have hfix : -1 + counterexampleClamp ((blockProjection 0 u).ofLp ⟨0, by decide⟩ + 1) =
      (blockProjection 0 u).ofLp ⟨0, by decide⟩ := by
    rw [← hx]
    fin_cases x <;> norm_num [counterexampleClamp]
  rw [counterexampleTrueSCM_outcome (binaryAssignment t) (by simp [binaryAssignment]),
    counterexampleTrueSCM_treatment, hcov, hfix]
  rfl

-- @node: counterexampleTrueSCM_intervention_outcome_integrable
/-- For either binary treatment assignment, [the constructed true structural
causal model's outcome under intervention is integrable under its latent
distribution](goal). -/
lemma counterexampleTrueSCM_intervention_outcome_integrable (t : Bool) :
    Integrable (fun u => backdoorOutcome
      (intervenedEval counterexampleTrueSCM.toEuclideanSCM (binaryAssignment t) u))
      counterexampleTrueSCM.latentLaw := by
  have h := counterexampleTrueInterventionOutcome_integrable t
  rw [← counterexampleTruePrivateCoordinates_law] at h
  have hc := (integrable_map_measure
    (counterexampleTrueInterventionOutcome_measurable t).aestronglyMeasurable
    counterexampleTruePrivateCoordinates_measurable.aemeasurable).mp h
  exact hc.congr (counterexampleTrueSCM_intervention_outcome_ae t).symm

-- @node: counterexampleTrueSCM_effect_integrable
/-- [The individual treatment effect, computed as the constructed true structural
causal model's outcome under the true binary assignment minus its outcome under
the false binary assignment, is integrable under its latent distribution](goal). -/
lemma counterexampleTrueSCM_effect_integrable :
    Integrable (fun u =>
      backdoorOutcome (intervenedEval counterexampleTrueSCM.toEuclideanSCM (binaryAssignment true) u) -
      backdoorOutcome (intervenedEval counterexampleTrueSCM.toEuclideanSCM (binaryAssignment false) u))
      counterexampleTrueSCM.latentLaw :=
  (counterexampleTrueSCM_intervention_outcome_integrable true).sub
    (counterexampleTrueSCM_intervention_outcome_integrable false)

-- @node: counterexampleTrueSCM_ATE
/-- [The constructed true structural causal model's average treatment effect
is 19/30](goal). -/
lemma counterexampleTrueSCM_ATE :
    backdoorATE counterexampleTrueSCM.toEuclideanSCM = (19/30 : ℝ) := by
  change (∫ u,
    backdoorOutcome (intervenedEval counterexampleTrueSCM.toEuclideanSCM (binaryAssignment true) u) -
    backdoorOutcome (intervenedEval counterexampleTrueSCM.toEuclideanSCM (binaryAssignment false) u)
      ∂counterexampleTrueSCM.latentLaw) = _
  trans ∫ u, counterexampleTrueInterventionOutcome true (counterexampleTruePrivateCoordinates u) -
    counterexampleTrueInterventionOutcome false (counterexampleTruePrivateCoordinates u)
      ∂counterexampleTrueSCM.latentLaw
  · exact integral_congr_ae ((counterexampleTrueSCM_intervention_outcome_ae true).sub
      (counterexampleTrueSCM_intervention_outcome_ae false))
  have hm : Measurable (fun z => counterexampleTrueInterventionOutcome true z -
      counterexampleTrueInterventionOutcome false z) := by fun_prop
  rw [← integral_map counterexampleTruePrivateCoordinates_measurable.aemeasurable
    hm.aestronglyMeasurable, counterexampleTruePrivateCoordinates_law]
  exact counterexampleTrueFiniteATE

end
end Papers.TbsNeuralCausalPi
