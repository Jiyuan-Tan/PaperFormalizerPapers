module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleCanonical
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseNonDescendant
/-! # Canonical counterexample coordinates and intervention evaluation -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: counterexample_intervened_coordinate
/-- For [a structural causal model](hyp:M), [an intervention](hyp:t),
[a latent realization](hyp:u), [a node](hyp:i), and [one of its coordinates](hyp:j),
[the intervened coordinate equals its assigned value when intervened upon, and otherwise
equals the structural equation evaluated at the intervened state and latent realization](goal). -/
lemma counterexample_intervened_coordinate {n b : ℕ} {kind : Fin n → NodeKind}
    {dims : Fin b → ℕ} (M : EuclideanSCM kind dims) (t : Intervention kind)
    (u : Exogenous kind dims) (i : Fin n) (j : Fin (valueDim (kind i))) :
    (intervenedEval M t u).ofLp ⟨i,j⟩ =
      ((t i).getD (nodeValue M i (intervenedEval M t u) u)).ofLp j := by
  have hx : structuralInput M i (evalSteps M t u (M.dag.topoOrder i)) u =
      structuralInput M i (intervenedEval M t u) u := by
    apply PiLp.ext
    rintro (⟨p,k⟩ | ⟨a,k⟩)
    · exact evalSteps_coordinate_eq_intervenedEval M t u p.val _
        (M.dag.topoOrder_lt _ _ (M.dag.mem_parents.mp p.property)) k
    · rfl
  have hn : nodeValue M i (evalSteps M t u (M.dag.topoOrder i)) u =
      nodeValue M i (intervenedEval M t u) u := by
    unfold nodeValue
    rw [hx]
  change (evalSteps M t u (n*n+n)).ofLp ⟨i,j⟩ = _
  rw [evalSteps_coordinate_after_visit M t u i _ (scm_topoOrder_lt_horizon M i) j]
  simp only [evalSteps, WithLp.ofLp_toLp, ite_true, hn]

-- @node: counterexampleTrueSCM_covariate
/-- Under [an intervention](hyp:t) that [leaves the covariate unassigned](hyp:ht),
for [a latent realization](hyp:u), [the counterexample covariate equals minus one plus
the clamp of its private latent coordinate shifted by one](goal). -/
lemma counterexampleTrueSCM_covariate (t : Intervention backdoorKind)
    (ht : t 0 = none) (u : Exogenous backdoorKind counterexampleDims) :
    (intervenedEval counterexampleTrueSCM.toEuclideanSCM t u).ofLp ⟨0,⟨0, by decide⟩⟩ =
      -1 + counterexampleClamp ((blockProjection 0 u).ofLp ⟨0, by decide⟩ + 1) := by
  rw [counterexample_intervened_coordinate, ht, Option.getD_none]
  rfl

-- @node: counterexampleTrueSCM_treatment
/-- For [a binary treatment choice](hyp:t) and [a latent realization](hyp:u),
[the counterexample's intervened treatment is category two for the true choice
and category one for the false choice](goal). -/
lemma counterexampleTrueSCM_treatment (t : Bool)
    (u : Exogenous backdoorKind counterexampleDims) :
    (intervenedEval counterexampleTrueSCM.toEuclideanSCM (binaryAssignment t) u).ofLp ⟨1,⟨0, by decide⟩⟩ =
      if t then 2 else 1 := by
  rw [counterexample_intervened_coordinate]
  simp [binaryAssignment]

-- @node: counterexampleTrueSCM_outcome
/-- Under [an intervention](hyp:t) that [leaves the outcome unassigned](hyp:ht),
for [a latent realization](hyp:u), [the counterexample outcome is its outcome function
applied to the intervened covariate and treatment and the two private outcome disturbances](goal). -/
lemma counterexampleTrueSCM_outcome (t : Intervention backdoorKind)
    (ht : t 2 = none) (u : Exogenous backdoorKind counterexampleDims) :
    backdoorOutcome (intervenedEval counterexampleTrueSCM.toEuclideanSCM t u) =
      counterexampleTrueOutcome (WithLp.toLp 1 ![
        (intervenedEval counterexampleTrueSCM.toEuclideanSCM t u).ofLp ⟨0,⟨0, by decide⟩⟩,
        (intervenedEval counterexampleTrueSCM.toEuclideanSCM t u).ofLp ⟨1,⟨0, by decide⟩⟩,
        (blockProjection 2 u).ofLp ⟨0, by decide⟩, (blockProjection 2 u).ofLp ⟨1, by decide⟩]) := by
  unfold backdoorOutcome
  rw [counterexample_intervened_coordinate, ht, Option.getD_none]
  rfl

-- @node: counterexampleTrueSCM_bernoulli_range
/-- [Almost surely under the counterexample's latent law, every coordinate of
the outcome's private latent block lies between zero and one, inclusive](goal). -/
lemma counterexampleTrueSCM_bernoulli_range :
    ∀ᵐ u ∂counterexampleTrueSCM.latentLaw, ∀ k,
      (blockProjection 2 u).ofLp k ∈ Set.Icc (0 : ℝ) 1 := by
  have hset : MeasurableSet {x : L1Vec (counterexampleDims 2) |
      ∀ k, x.ofLp k ∈ Set.Icc (0 : ℝ) 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_Icc.preimage (by fun_prop))
  have hm : Measurable (blockProjection (kind := backdoorKind) (dims := counterexampleDims) 2) := by
    fun_prop [blockProjection]
  apply (ae_map_iff hm.aemeasurable hset).mp
  rw [counterexampleTrueSCM_block_law]
  apply (ae_map_iff (counterexampleBlockProjection_measurable 2).aemeasurable hset).mpr
  filter_upwards [counterexampleTrueFiniteLatentLaw_ae_atoms] with z hz
  obtain ⟨⟨x,a,b⟩, rfl⟩ := hz
  intro k
  fin_cases k
  · change (a.val : ℝ) ∈ Set.Icc (0 : ℝ) 1
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.le_of_lt_succ a.isLt⟩
  · change (b.val : ℝ) ∈ Set.Icc (0 : ℝ) 1
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.le_of_lt_succ b.isLt⟩

-- @node: counterexampleTrueSCM_bernoulli_joint_law
/-- [The two private outcome disturbances in the counterexample have the product
of Bernoulli laws with success probabilities three fifths and one third, respectively](goal). -/
lemma counterexampleTrueSCM_bernoulli_joint_law :
    counterexampleTrueSCM.latentLaw.map (fun u =>
      ((blockProjection 2 u).ofLp ⟨0, by decide⟩,
       (blockProjection 2 u).ofLp ⟨1, by decide⟩)) =
      (ENNReal.ofReal (2/5 : ℝ) • Measure.dirac (0 : ℝ) +
       ENNReal.ofReal (3/5 : ℝ) • Measure.dirac 1).prod
      (ENNReal.ofReal (2/3 : ℝ) • Measure.dirac (0 : ℝ) +
       ENNReal.ofReal (1/3 : ℝ) • Measure.dirac 1) := by
  have hm : Measurable (blockProjection (kind := backdoorKind) (dims := counterexampleDims) 2) := by
    fun_prop [blockProjection]
  have he : Measurable (fun x : L1Vec (counterexampleDims 2) =>
      (x.ofLp ⟨0, by decide⟩, x.ofLp ⟨1, by decide⟩)) := by fun_prop
  rw [show (fun u : Exogenous backdoorKind counterexampleDims =>
      ((blockProjection 2 u).ofLp ⟨0, by decide⟩,
       (blockProjection 2 u).ofLp ⟨1, by decide⟩)) =
      (fun x : L1Vec (counterexampleDims 2) =>
        (x.ofLp ⟨0, by decide⟩, x.ofLp ⟨1, by decide⟩)) ∘ blockProjection 2 from rfl,
    ← Measure.map_map he hm, counterexampleTrueSCM_block_law]
  change ((counterexampleTrueFiniteLatentLaw.map (counterexampleBlockProjection 2)).map _) = _
  rw [Measure.map_map he (counterexampleBlockProjection_measurable 2)]
  rw [counterexampleTrueFiniteLatentLaw, ← Measure.sum_fintype,
    Measure.map_sum (he.comp (counterexampleBlockProjection_measurable 2)).aemeasurable,
    Measure.sum_fintype]
  simp only [Measure.map_smul, Measure.map_dirac' (he.comp (counterexampleBlockProjection_measurable 2))]
  simp only [Measure.prod_add, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.dirac_prod_dirac, smul_smul]
  change (∑ i : Fin 2 × Fin 2 × Fin 2, ENNReal.ofReal (counterexampleTrueLatentWeight i) •
    Measure.dirac ((i.2.1.val : ℝ), (i.2.2.val : ℝ))) = _
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, counterexampleTrueLatentWeight,
    smul_add, smul_smul]
  simp only [two_smul, ← add_smul]
  simp (disch := positivity) only [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul]
  norm_num
  ac_rfl

-- @node: counterexampleTrueSCM_first_bernoulli_law
/-- [The first private outcome disturbance in the counterexample is Bernoulli
with success probability three fifths](goal). -/
lemma counterexampleTrueSCM_first_bernoulli_law :
    counterexampleTrueSCM.latentLaw.map (fun u =>
      (blockProjection 2 u).ofLp ⟨0, by decide⟩) =
      ENNReal.ofReal (2/5 : ℝ) • Measure.dirac (0 : ℝ) +
      ENNReal.ofReal (3/5 : ℝ) • Measure.dirac 1 := by
  have hm : Measurable (fun u : Exogenous backdoorKind counterexampleDims =>
      ((blockProjection 2 u).ofLp ⟨0, by decide⟩,
       (blockProjection 2 u).ofLp ⟨1, by decide⟩)) := by fun_prop [blockProjection]
  have h := congrArg (fun mu : Measure (ℝ × ℝ) => mu.map Prod.fst)
    counterexampleTrueSCM_bernoulli_joint_law
  rw [Measure.map_map measurable_fst hm, Measure.map_fst_prod] at h
  norm_num [Measure.add_apply, Measure.smul_apply, ← ENNReal.ofReal_add] at h
  exact h

-- @node: counterexampleTrueSCM_second_bernoulli_law
/-- [The second private outcome disturbance in the counterexample is Bernoulli
with success probability one third](goal). -/
lemma counterexampleTrueSCM_second_bernoulli_law :
    counterexampleTrueSCM.latentLaw.map (fun u =>
      (blockProjection 2 u).ofLp ⟨1, by decide⟩) =
      ENNReal.ofReal (2/3 : ℝ) • Measure.dirac (0 : ℝ) +
      ENNReal.ofReal (1/3 : ℝ) • Measure.dirac 1 := by
  have hm : Measurable (fun u : Exogenous backdoorKind counterexampleDims =>
      ((blockProjection 2 u).ofLp ⟨0, by decide⟩,
       (blockProjection 2 u).ofLp ⟨1, by decide⟩)) := by fun_prop [blockProjection]
  have h := congrArg (fun mu : Measure (ℝ × ℝ) => mu.map Prod.snd)
    counterexampleTrueSCM_bernoulli_joint_law
  rw [Measure.map_map measurable_snd hm, Measure.map_snd_prod] at h
  norm_num [Measure.add_apply, Measure.smul_apply, ← ENNReal.ofReal_add] at h
  exact h

-- @node: counterexampleTrueSCM_bernoulli_coordinates
/-- [The counterexample's outcome block has two distinct, independent Bernoulli
coordinates with success probabilities three fifths and one third; the second
equals one with probability one third and zero with probability two thirds](goal). -/
lemma counterexampleTrueSCM_bernoulli_coordinates :
    counterexampleBernoulliCoordinates counterexampleTrueSCM 2 ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  letI := counterexampleTrueSCM.latentLaw_probability
  refine ⟨by decide, by simp [counterexampleComponents],
    counterexampleTrueSCM_first_bernoulli_law, counterexampleTrueSCM_second_bernoulli_law,
    ?_, ?_⟩
  · apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (by fun_prop [blockProjection]) (by fun_prop [blockProjection])).mpr
    rw [counterexampleTrueSCM_first_bernoulli_law, counterexampleTrueSCM_second_bernoulli_law]
    exact counterexampleTrueSCM_bernoulli_joint_law
  · have hm : Measurable (fun u : Exogenous backdoorKind counterexampleDims =>
        (blockProjection 2 u).ofLp ⟨1, by decide⟩) := by fun_prop [blockProjection]
    have h (r : ℝ) := congrArg (fun mu : Measure ℝ => mu {r})
      counterexampleTrueSCM_second_bernoulli_law
    simp only [Measure.map_apply hm (measurableSet_singleton _)] at h
    constructor
    · simpa [Measure.add_apply, Measure.smul_apply, Set.preimage] using h 1
    · simpa [Measure.add_apply, Measure.smul_apply, Set.preimage] using h 0

-- @node: counterexampleTrueSCM_outcome_connection
/-- [The counterexample admits a measurable, integrable, mean-zero outcome disturbance
such that, almost surely under either binary intervention, a zero covariate makes
the outcome equal the first private outcome coordinate for treatment category two
and the second otherwise, plus that disturbance](goal). -/
lemma counterexampleTrueSCM_outcome_connection :
    counterexampleOutcomeConnection counterexampleTrueSCM 2 ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  letI := counterexampleTrueSCM.latentLaw_probability
  refine ⟨fun _ => 0, by fun_prop, integrable_const 0, by simp, ?_⟩
  filter_upwards [counterexampleTrueSCM_bernoulli_range] with u hu
  intro t
  dsimp only
  intro hx
  have ht := counterexampleTrueSCM_treatment t u
  have hout := counterexampleTrueSCM_outcome (binaryAssignment t) (by simp [binaryAssignment]) u
  rw [hout, add_zero]
  apply counterexampleTrueOutcome_at_zero
  · exact hx
  · cases t <;> simp_all
  · exact hu ⟨0, by decide⟩
  · exact hu ⟨1, by decide⟩
end
end Papers.TbsNeuralCausalPi
