module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleInterventions
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleApproximate
/-! # Observational laws of the canonical backdoor counterexample -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Suppose [the private input is measurable](hyp:hX), [the two treatment shocks are
measurable](hyp:hG), [the private input and shocks are independent](hyp:hind), and
[the shocks have the standard two-coordinate Gumbel law](hyp:hG_law). For
[nonnegative extended-real atom weights](hyp:w), assume [the private-input law is the
weighted sum of point masses at the specified atoms](hyp:hX_law), [the propensity vector
depends measurably on the private input](hyp:hp), [each propensity vector is a probability
vector](hyp:hps), [the selector's category count is positive whenever it equals two](hyp:hk),
and [the output for each treatment category is measurable in the private input](hyp:hv).
Then [the output law from the Gumbel selector is the sum, over private-input atoms and
treatment categories, of point masses at the corresponding outputs weighted by the atom
weight times the category's propensity](goal). -/
-- @node: counterexample_finite_selector_law
lemma counterexample_finite_selector_law
    {Ω Z Y I : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace Y]
    [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Z) (G : Ω → Fin 2 → ℝ) (hX : Measurable X) (hG : Measurable G)
    (hind : IndepFun X G μ) (hG_law : μ.map G = gumbelInputs 2)
    (w : I → ℝ≥0∞) (a : I → Z) (hX_law : μ.map X = ∑ i, w i • Measure.dirac (a i))
    (p : Z → L1Vec 2) (hp : Measurable p)
    (hps : ∀ z, (p z).ofLp ∈ probabilitySimplex 2)
    (hk : ∀ m, Sum.inr 2 = (Sum.inr m : NodeKind) → 0 < m)
    (v : Z → Fin 2 → Y) (hv : ∀ j, Measurable (fun z => v z j)) :
    μ.map (fun u => v (X u)
      (canonicalSelector (.inr 2) hk (p (X u)) (WithLp.toLp 1 (G u)))) =
      ∑ i, w i • (∑ j, ENNReal.ofReal ((p (a i)).ofLp j) • Measure.dirac (v (a i) j)) := by
  let F : Z × (Fin 2 → ℝ) → Y := fun z => v z.1
    (canonicalSelector (.inr 2) hk (p z.1) (WithLp.toLp 1 z.2))
  have hs : Measurable (fun z : Z × (Fin 2 → ℝ) =>
      canonicalSelector (.inr 2) hk (p z.1) (WithLp.toLp 1 z.2)) := by
    apply firstArgmax_getD_measurable
    intro j
    fun_prop
  have hv' : Measurable (fun z : Z × Fin 2 => v z.1 z.2) :=
    measurable_from_prod_countable_left hv
  have hF : Measurable F := hv'.comp (measurable_fst.prodMk hs)
  rw [show (fun u => v (X u)
      (canonicalSelector (.inr 2) hk (p (X u)) (WithLp.toLp 1 (G u)))) =
      F ∘ (fun u => (X u, G u)) from rfl,
    ← Measure.map_map hF (hX.prodMk hG),
    hind.map_prod_eq_prod_map_map hX.aemeasurable hG.aemeasurable, hG_law]
  let := Measure.isProbabilityMeasure_map (μ := μ) hX.aemeasurable
  rw [privateBlock_canonicalSelector_law (μ.map X) hk p hp (ae_of_all _ hps) v hv]
  ext s hs
  rw [Measure.bind_apply hs (categoricalEncodedKernel
    (fun z => (p z).ofLp) (by fun_prop) v hv).aemeasurable, hX_law]
  have hK := (categoricalEncodedKernel
    (fun z => (p z).ofLp) (by fun_prop) v hv).measurable_coe hs
  simp only [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac' _ hK]
  simp [categoricalEncodedKernel, Kernel.coe_mk, Measure.finsetSum_apply, mul_add]

/-- For [a three-coordinate vector of covariate, treatment, and outcome](hyp:z),
[its joint observation in the backdoor model](goal) assigns these coordinates to the
three corresponding scalar nodes in the same order. -/
-- @node: counterexampleJointOfVector
def counterexampleJointOfVector (z : L1Vec 3) : Joint backdoorKind :=
  WithLp.toLp 1 (fun i => z.ofLp i.1)

-- @node: counterexampleJointOfVector_measurable
/-- [Converting a three-coordinate vector into a joint observation of the backdoor model
is measurable](goal). -/
@[fun_prop] lemma counterexampleJointOfVector_measurable :
    Measurable counterexampleJointOfVector := by
  unfold counterexampleJointOfVector
  fun_prop

-- @node: counterexampleJointOfVector_edist
/-- [The extended distance between the joint observations corresponding to two
three-coordinate vectors equals the extended distance between the original vectors](goal). -/
lemma counterexampleJointOfVector_edist (x y : L1Vec 3) :
    edist (counterexampleJointOfVector x) (counterexampleJointOfVector y) = edist x y := by
  simp only [counterexampleJointOfVector, PiLp.edist_eq_of_L1,
    Fintype.sum_sigma]
  congr 1
  funext i
  fin_cases i <;> simp [backdoorKind, valueDim]

/-- If [the perturbation is nonnegative](hyp:hdelta), [the Wasserstein distance of order
one between the finite observation laws at zero and at that perturbation, expressed as
joint observations of the backdoor model, is at most half the perturbation](goal). -/
-- @node: counterexampleJointObservation_wasserstein_le
lemma counterexampleJointObservation_wasserstein_le (delta : ℝ) (hdelta : 0 ≤ delta) :
    wasserstein1 ((counterexampleFiniteObservationLaw 0).map counterexampleJointOfVector)
      ((counterexampleFiniteObservationLaw delta).map counterexampleJointOfVector) ≤
        ENNReal.ofReal (delta / 2) := by
  let F : L1Vec 3 × L1Vec 3 → Joint backdoorKind × Joint backdoorKind :=
    fun z => (counterexampleJointOfVector z.1, counterexampleJointOfVector z.2)
  have hF : Measurable F := by fun_prop
  have hc := counterexampleObservationCoupling_isCoupling delta
  let := hc.1
  have hcoupling : Causalean.Stat.IsCoupling ((counterexampleObservationCoupling delta).map F)
      ((counterexampleFiniteObservationLaw 0).map counterexampleJointOfVector)
      ((counterexampleFiniteObservationLaw delta).map counterexampleJointOfVector) := by
    refine ⟨Measure.isProbabilityMeasure_map hF.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hF, ← hc.2,
        Measure.map_map counterexampleJointOfVector_measurable measurable_fst]
      rfl
    · rw [Measure.map_map measurable_snd hF, ← hc.3,
        Measure.map_map counterexampleJointOfVector_measurable measurable_snd]
      rfl
  apply (Toolkit.Foundations.MeasureTheory.wasserstein1_le_cost hcoupling).trans
  rw [lintegral_map (by fun_prop) hF]
  simp only [F, counterexampleJointOfVector_edist]
  rw [counterexampleObservationCoupling_cost, abs_of_nonneg hdelta]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- For [an exogenous input to the backdoor model](hyp:u), [the treatment's two Gumbel
shocks](goal) are the two coordinates of the treatment node's categorical noise. -/
-- @node: counterexampleTreatmentGumbels
def counterexampleTreatmentGumbels (u : Exogenous backdoorKind counterexampleDims) : Fin 2 → ℝ :=
  fun l => (categoricalNoise 1 u).ofLp l

-- @node: counterexampleTreatmentGumbels_measurable
/-- [Extracting the treatment's two Gumbel shocks from an exogenous input is measurable](goal). -/
@[fun_prop] lemma counterexampleTreatmentGumbels_measurable :
    Measurable counterexampleTreatmentGumbels := by
  unfold counterexampleTreatmentGumbels
  fun_prop [categoricalNoise]

-- @node: counterexampleTreatmentGumbels_law
/-- [Under the latent law of any canonical structural causal model with the specified
backdoor structure and components, the treatment shocks have the standard two-coordinate
Gumbel law](goal). -/
lemma counterexampleTreatmentGumbels_law
    (M : CanonicalSCM backdoorKind counterexampleDims backdoorDAG ⊥ counterexampleComponents) :
    M.latentLaw.map counterexampleTreatmentGumbels = gumbelInputs 2 :=
  canonical_categorical_noise_law M 1 2 rfl

-- @node: counterexampleApproxSCM_treatment_observational
/-- [For any perturbation and exogenous input, the approximate model's treatment without
intervention equals one plus the category index selected using its propensity at the
private covariate and the treatment's Gumbel shocks](goal). -/
lemma counterexampleApproxSCM_treatment_observational (delta : ℝ)
    (u : Exogenous backdoorKind counterexampleDims) :
    (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (fun _ => none) u).ofLp
      ⟨1, ⟨0, by decide⟩⟩ =
      ((canonicalSelector (.inr 2) (fun m hm => by cases hm; decide)
        (counterexampleApproxPropensity delta ((blockProjection 0 u).ofLp ⟨0, by decide⟩))
        (WithLp.toLp 1 (counterexampleTreatmentGumbels u))).val + 1 : ℕ) := by
  rw [counterexample_intervened_coordinate, Option.getD_none]
  change (((canonicalSelector (.inr 2) (fun m hm => by cases hm; decide)
    (counterexampleApproxPropensity delta
      ((intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (fun _ => none) u).ofLp
        ⟨0, ⟨0, by decide⟩⟩)) (categoricalNoise 1 u)).val + 1 : ℕ) : ℝ) = _
  rw [counterexampleApproxSCM_covariate delta _ rfl]
  rfl

-- @node: counterexampleApproxObservation
/-- Given [a perturbation](hyp:delta), [a covariate value](hyp:x), and [one of the two
treatment category indices](hyp:j), [the approximate observation vector](goal) consists
of that covariate, the treatment encoded as the index plus one, and the approximate
outcome evaluated at that covariate and treatment. -/
def counterexampleApproxObservation (delta x : ℝ) (j : Fin 2) : L1Vec 3 :=
  WithLp.toLp 1 ![x, ((j.val + 1 : ℕ) : ℝ), counterexampleApproxOutcome delta
    (WithLp.toLp 1 ![x, ((j.val + 1 : ℕ) : ℝ)])]

-- @node: counterexampleApproxObservation_measurable
/-- [For any fixed perturbation and treatment category, the approximate observation
vector is a measurable function of the covariate](goal). -/
@[fun_prop] lemma counterexampleApproxObservation_measurable (delta : ℝ) (j : Fin 2) :
    Measurable (fun x => counterexampleApproxObservation delta x j) := by
  unfold counterexampleApproxObservation
  fun_prop

-- @node: counterexampleApproxSCM_observation
/-- [For every perturbation and exogenous input, the approximate model's joint observation
without intervention is the approximate observation vector formed from the private
covariate and the category selected using its approximate propensity and treatment Gumbel
shocks, converted into the backdoor model's joint coordinates](goal). -/
lemma counterexampleApproxSCM_observation (delta : ℝ)
    (u : Exogenous backdoorKind counterexampleDims) :
    intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (fun _ => none) u =
      counterexampleJointOfVector (counterexampleApproxObservation delta
        ((blockProjection 0 u).ofLp ⟨0, by decide⟩)
        (canonicalSelector (.inr 2) (fun m hm => by cases hm; decide)
          (counterexampleApproxPropensity delta ((blockProjection 0 u).ofLp ⟨0, by decide⟩))
          (WithLp.toLp 1 (counterexampleTreatmentGumbels u)))) := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  fin_cases i <;> change Fin 1 at j <;> fin_cases j
  · exact counterexampleApproxSCM_covariate delta _ rfl u
  · exact counterexampleApproxSCM_treatment_observational delta u
  · change backdoorOutcome _ = _
    rw [counterexampleApproxSCM_outcome delta _ rfl,
      counterexampleApproxSCM_covariate delta _ rfl,
      counterexampleApproxSCM_treatment_observational]
    rfl

-- @node: counterexampleApproxSCM_covariate_indep_gumbels
/-- [Under the approximate model's latent law, the private covariate is independent of
the treatment's two Gumbel shocks for every perturbation](goal). -/
lemma counterexampleApproxSCM_covariate_indep_gumbels (delta : ℝ) :
    IndepFun (fun u => (blockProjection 0 u).ofLp ⟨0, by decide⟩)
      counterexampleTreatmentGumbels (counterexampleApproxSCM delta).latentLaw := by
  have h := (canonical_latent_blocks_independent (counterexampleApproxSCM delta)).indepFun
    (i := Sum.inl (0 : Fin 3)) (j := Sum.inr (1 : Fin 3)) (by decide)
  exact h.comp (φ := fun x : L1Vec 1 => x.ofLp ⟨0, by decide⟩)
    (ψ := fun g : L1Vec 2 => g.ofLp) (by fun_prop) (by fun_prop)

set_option maxHeartbeats 1200000 in
-- @node: counterexampleApproxSCM_observationalLaw
/-- [For every perturbation, the approximate model's observational law equals its
explicit finite observation law converted into the backdoor model's joint coordinates](goal). -/
lemma counterexampleApproxSCM_observationalLaw (delta : ℝ) :
    observationalLaw (counterexampleApproxSCM delta).toEuclideanSCM =
      (counterexampleApproxFiniteObservationLaw delta).map counterexampleJointOfVector := by
  let μ := (counterexampleApproxSCM delta).latentLaw
  let := (counterexampleApproxSCM delta).latentLaw_probability
  let X := fun u : Exogenous backdoorKind counterexampleDims =>
    (blockProjection 0 u).ofLp ⟨0, by decide⟩
  let w : Fin 3 → ℝ≥0∞ := fun i => ENNReal.ofReal ((![(1/2 : ℝ),1/4,1/4]) i)
  let a : Fin 3 → ℝ := ![-1,0,delta]
  have hX : Measurable X := by dsimp [X]; fun_prop [blockProjection]
  have hlaw : μ.map X = ∑ i, w i • Measure.dirac (a i) := by
    rw [show μ.map X = _ from counterexampleApproxSCM_covariate_law delta]
    simp [w, a, Fin.sum_univ_succ, counterexampleApproxFiniteLatentLaw, add_assoc]
  have h := counterexample_finite_selector_law μ X counterexampleTreatmentGumbels hX
    counterexampleTreatmentGumbels_measurable
    (counterexampleApproxSCM_covariate_indep_gumbels delta)
    (counterexampleTreatmentGumbels_law _) w a hlaw
    (counterexampleApproxPropensity delta) (by fun_prop)
    (counterexampleApproxPropensity_simplex delta)
    (fun m hm => by cases hm; decide)
    (fun x j => counterexampleJointOfVector (counterexampleApproxObservation delta x j))
    (fun j => by fun_prop)
  change μ.map (intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (fun _ => none)) = _
  rw [show intervenedEval (counterexampleApproxSCM delta).toEuclideanSCM (fun _ => none) =
    (fun u => counterexampleJointOfVector (counterexampleApproxObservation delta (X u)
      (canonicalSelector (.inr 2) (fun m hm => by cases hm; decide)
        (counterexampleApproxPropensity delta (X u))
        (WithLp.toLp 1 (counterexampleTreatmentGumbels u))))) from
      funext (counterexampleApproxSCM_observation delta), h]
  rw [counterexampleApproxFiniteObservationLaw,
    Measure.map_finset_sum counterexampleJointOfVector_measurable.aemeasurable]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Measure.map_smul, Measure.map_add _ _ counterexampleJointOfVector_measurable,
    Measure.map_dirac' counterexampleJointOfVector_measurable]
  simp [Fin.sum_univ_succ, counterexampleApproxPropensity, counterexampleApproxObservation,
    counterexampleApproxInterventionOutcome, w, a, show (1 : ℝ) + 1 = 2 by norm_num]

-- @node: counterexampleTrueSCM_covariate_ae
/-- [Under the true model's latent law, the observed covariate without intervention
equals the first private coordinate almost surely](goal). -/
lemma counterexampleTrueSCM_covariate_ae :
    ∀ᵐ u ∂counterexampleTrueSCM.latentLaw,
      (intervenedEval counterexampleTrueSCM.toEuclideanSCM (fun _ => none) u).ofLp
        ⟨0, ⟨0, by decide⟩⟩ = (counterexampleTruePrivateCoordinates u).ofLp 0 := by
  filter_upwards [counterexampleTruePrivateCoordinates_ae_atoms] with u hu
  obtain ⟨⟨x,a,b⟩, hz⟩ := hu
  have hx := congrArg (fun z : L1Vec 3 => z.ofLp 0) hz
  change -1 + (x.val : ℝ) = (blockProjection 0 u).ofLp ⟨0, by decide⟩ at hx
  rw [counterexampleTrueSCM_covariate _ rfl]
  change -1 + counterexampleClamp ((blockProjection 0 u).ofLp ⟨0, by decide⟩ + 1) =
    (blockProjection 0 u).ofLp ⟨0, by decide⟩
  rw [← hx]
  fin_cases x <;> norm_num [counterexampleClamp]

-- @node: counterexampleTrueSCM_treatment_observational
/-- [For every exogenous input, the true model's treatment without intervention equals
one plus the category index selected using the true propensity at the observed covariate
and the treatment's Gumbel shocks](goal). -/
lemma counterexampleTrueSCM_treatment_observational
    (u : Exogenous backdoorKind counterexampleDims) :
    (intervenedEval counterexampleTrueSCM.toEuclideanSCM (fun _ => none) u).ofLp
      ⟨1, ⟨0, by decide⟩⟩ =
      ((canonicalSelector (.inr 2) (fun m hm => by cases hm; decide)
        (counterexampleTruePropensity
          ((intervenedEval counterexampleTrueSCM.toEuclideanSCM (fun _ => none) u).ofLp
            ⟨0, ⟨0, by decide⟩⟩))
        (WithLp.toLp 1 (counterexampleTreatmentGumbels u))).val + 1 : ℕ) := by
  rw [counterexample_intervened_coordinate, Option.getD_none]
  rfl

-- @node: counterexampleTrueObservation
/-- Given [a vector containing the private covariate and two private outcome inputs](hyp:z)
and [one of the two treatment category indices](hyp:j), [the true observation vector](goal)
consists of that covariate, the treatment encoded as the index plus one, and the true
outcome evaluated at that covariate, treatment, and the two private outcome inputs. -/
def counterexampleTrueObservation (z : L1Vec 3) (j : Fin 2) : L1Vec 3 :=
  WithLp.toLp 1 ![z.ofLp 0, ((j.val + 1 : ℕ) : ℝ), counterexampleTrueOutcome
    (WithLp.toLp 1 ![z.ofLp 0, ((j.val + 1 : ℕ) : ℝ), z.ofLp 1, z.ofLp 2])]

-- @node: counterexampleTrueObservation_measurable
/-- [For any fixed treatment category, the true observation vector is a measurable
function of the three private coordinates](goal). -/
@[fun_prop] lemma counterexampleTrueObservation_measurable (j : Fin 2) :
    Measurable (fun z => counterexampleTrueObservation z j) := by
  unfold counterexampleTrueObservation
  fun_prop

-- @node: counterexampleTrueSCM_observation_ae
/-- [Under the true model's latent law, its joint observation without intervention
almost surely equals the true observation vector formed from the private coordinates
and the category selected using the true propensity at the private covariate and the
treatment Gumbel shocks, converted into the backdoor model's joint coordinates](goal). -/
lemma counterexampleTrueSCM_observation_ae :
    (intervenedEval counterexampleTrueSCM.toEuclideanSCM (fun _ => none))
      =ᵐ[counterexampleTrueSCM.latentLaw] fun u =>
      counterexampleJointOfVector (counterexampleTrueObservation (counterexampleTruePrivateCoordinates u)
        (canonicalSelector (.inr 2) (fun m hm => by cases hm; decide)
          (counterexampleTruePropensity ((counterexampleTruePrivateCoordinates u).ofLp 0))
          (WithLp.toLp 1 (counterexampleTreatmentGumbels u)))) := by
  filter_upwards [counterexampleTrueSCM_covariate_ae] with u hu
  have ht := counterexampleTrueSCM_treatment_observational u
  rw [hu] at ht
  apply PiLp.ext
  rintro ⟨i,j⟩
  fin_cases i <;> change Fin 1 at j <;> fin_cases j
  · exact hu
  · exact ht
  · change backdoorOutcome _ = _
    rw [counterexampleTrueSCM_outcome _ rfl, hu, ht]
    rfl

-- @node: counterexampleTruePrivateCoordinates_indep_gumbels
/-- [Under the true model's latent law, the vector of the private covariate and two
private outcome inputs is independent of the treatment's two Gumbel shocks](goal). -/
lemma counterexampleTruePrivateCoordinates_indep_gumbels :
    IndepFun counterexampleTruePrivateCoordinates counterexampleTreatmentGumbels
      counterexampleTrueSCM.latentLaw := by
  have hm (j) : Measurable (namedLatent counterexampleTrueSCM.toEuclideanSCM j) := by
    cases j <;> fun_prop [namedLatent, blockProjection, categoricalNoise]
  have h := counterexampleTrueSCM_independent.indepFun_prodMk hm
    (Sum.inl (0 : Fin 3)) (Sum.inl (2 : Fin 3)) (Sum.inr (1 : Fin 3)) (by decide) (by decide)
  exact h.comp (φ := fun z : L1Vec 1 × L1Vec 2 =>
    WithLp.toLp 1 ![z.1.ofLp 0, z.2.ofLp 0, z.2.ofLp 1])
    (ψ := fun g : L1Vec 2 => g.ofLp) (by fun_prop) (by fun_prop)

set_option maxHeartbeats 1200000 in
-- @node: counterexampleTrueSCM_observationalLaw
/-- [The true model's observational law equals its explicit finite observation law
converted into the backdoor model's joint coordinates](goal). -/
lemma counterexampleTrueSCM_observationalLaw :
    observationalLaw counterexampleTrueSCM.toEuclideanSCM =
      counterexampleTrueFiniteObservationLaw.map counterexampleJointOfVector := by
  let μ := counterexampleTrueSCM.latentLaw
  let := counterexampleTrueSCM.latentLaw_probability
  have hp : Measurable (fun z : L1Vec 3 => counterexampleTruePropensity (z.ofLp 0)) := by
    fun_prop
  have h := counterexample_finite_selector_law μ counterexampleTruePrivateCoordinates
    counterexampleTreatmentGumbels counterexampleTruePrivateCoordinates_measurable
    counterexampleTreatmentGumbels_measurable counterexampleTruePrivateCoordinates_indep_gumbels
    (counterexampleTreatmentGumbels_law _) (fun i => ENNReal.ofReal (counterexampleTrueLatentWeight i))
    counterexampleTrueLatentAtom counterexampleTruePrivateCoordinates_law
    (fun z => counterexampleTruePropensity (z.ofLp 0)) hp
    (fun z => counterexampleTruePropensity_simplex _) (fun m hm => by cases hm; decide)
    (fun z j => counterexampleJointOfVector (counterexampleTrueObservation z j)) (fun j => by fun_prop)
  change μ.map (intervenedEval counterexampleTrueSCM.toEuclideanSCM (fun _ => none)) = _
  rw [Measure.map_congr counterexampleTrueSCM_observation_ae, h,
    counterexampleTrueFiniteObservationLaw,
    Measure.map_finset_sum counterexampleJointOfVector_measurable.aemeasurable]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Measure.map_smul, Measure.map_add _ _ counterexampleJointOfVector_measurable,
    Measure.map_dirac' counterexampleJointOfVector_measurable]
  simp [Fin.sum_univ_succ, counterexampleTruePropensity, counterexampleTrueObservation,
    counterexampleTrueInterventionOutcome, show (1 : ℝ) + 1 = 2 by norm_num]

-- @node: counterexampleSCM_observational_wasserstein_le
/-- If [the perturbation is strictly positive](hyp:hdelta), [the Wasserstein distance of
order one between the true and approximate models' observational laws is at most half
the perturbation](goal). -/
lemma counterexampleSCM_observational_wasserstein_le (delta : ℝ) (hdelta : 0 < delta) :
    wasserstein1 (observationalLaw counterexampleTrueSCM.toEuclideanSCM)
      (observationalLaw (counterexampleApproxSCM delta).toEuclideanSCM) ≤
        ENNReal.ofReal (delta / 2) := by
  rw [counterexampleTrueSCM_observationalLaw, counterexampleApproxSCM_observationalLaw,
    counterexampleTrueFiniteObservationLaw_eq, counterexampleApproxFiniteObservationLaw_eq delta hdelta]
  exact counterexampleJointObservation_wasserstein_le delta hdelta.le

end
end Papers.TbsNeuralCausalPi
